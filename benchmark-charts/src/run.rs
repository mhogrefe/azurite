//! Config-driven benchmark runner.
//!
//! Reads a TOML config, spawns `lake env .lake/build/bin/benchmark`, captures
//! stdout, writes a `.txt` with a `#`-prefixed metadata header, and renders an
//! SVG with the same metadata embedded as an XML comment.
//!
//! Currently emits a single chart shape: N-series semicolon-separated rows.
//! That's what the new benchmarks (incl. az_nat_square) emit.

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use plotters::prelude::*;
use serde::Deserialize;

// ── Config ──────────────────────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
pub struct BenchmarkConfig {
    /// Benchmark name passed to the Lean binary (e.g. "az_nat_square").
    pub benchmark: String,
    /// Number of input pairs/values.
    pub limit: u64,
    /// Chart title.
    pub title: String,
    /// X-axis label.
    pub x_label: String,
    /// Parameters forwarded to the Lean binary as "k1:v1,k2:v2".
    #[serde(default)]
    pub params: BTreeMap<String, toml::Value>,
}

impl BenchmarkConfig {
    /// Format `params` as the comma-separated key:value string the Lean
    /// benchmark expects.
    fn params_string(&self) -> String {
        self.params
            .iter()
            .map(|(k, v)| format!("{k}:{}", value_to_str(v)))
            .collect::<Vec<_>>()
            .join(",")
    }
}

fn value_to_str(v: &toml::Value) -> String {
    match v {
        toml::Value::String(s) => s.clone(),
        toml::Value::Integer(i) => i.to_string(),
        toml::Value::Float(f) => f.to_string(),
        toml::Value::Boolean(b) => b.to_string(),
        other => other.to_string(),
    }
}

// ── Multi-series row (mirrors main.rs) ──────────────────────────────────────

pub struct MultiRow {
    pub bucket: u64,
    pub series: Vec<(String, u64)>,
}

/// Parse N-series benchmark output. Lines starting with `#` are treated as
/// metadata and skipped.
fn parse_multi_series(content: &str) -> Vec<MultiRow> {
    let mut rows = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split(';').collect();
        if parts.len() < 2 {
            eprintln!("Skipping malformed line: {}", &line[..line.len().min(80)]);
            continue;
        }
        let Ok(bucket) = parts[0].parse::<u64>() else {
            eprintln!("Could not parse bucket: {}", &line[..line.len().min(80)]);
            continue;
        };
        let mut series = Vec::new();
        let mut ok = true;
        for part in &parts[1..] {
            if let Some((name, ns_str)) = part.split_once(',') {
                if let Ok(ns) = ns_str.parse::<u64>() {
                    series.push((name.to_string(), ns));
                } else {
                    eprintln!("Could not parse ns value in {:?}", part);
                    ok = false;
                    break;
                }
            } else {
                eprintln!("Malformed series entry: {:?}", part);
                ok = false;
                break;
            }
        }
        if ok && !series.is_empty() {
            rows.push(MultiRow { bucket, series });
        }
    }
    rows
}

// ── Stats ───────────────────────────────────────────────────────────────────

fn median(xs: &mut Vec<u64>) -> f64 {
    if xs.is_empty() {
        return 0.0;
    }
    xs.sort_unstable();
    let n = xs.len();
    if n % 2 == 0 {
        (xs[n / 2 - 1] + xs[n / 2]) as f64 / 2.0
    } else {
        xs[n / 2] as f64
    }
}

fn print_summary(rows: &[MultiRow]) {
    if rows.is_empty() {
        return;
    }
    let series_names: Vec<String> = rows[0].series.iter().map(|(n, _)| n.clone()).collect();
    let n_series = series_names.len();
    let non_trivial: Vec<&MultiRow> = rows
        .iter()
        .filter(|r| r.series.iter().any(|(_, ns)| *ns > 0))
        .collect();
    let n = non_trivial.len();
    if n == 0 {
        println!("No non-trivial rows to summarize.");
        return;
    }
    let mut totals = vec![0u64; n_series];
    for row in &non_trivial {
        for (i, (_, ns)) in row.series.iter().enumerate() {
            if i < n_series {
                totals[i] += ns;
            }
        }
    }
    println!("\n── Summary ({n} non-trivial rows) ──\n");
    println!("  {:<25} {:>10}", "Series", "Avg ns/op");
    println!("  {}", "─".repeat(37));
    for (i, name) in series_names.iter().enumerate() {
        let avg = totals[i] as f64 / n as f64;
        println!("  {:<25} {:>10.1}", name, avg);
    }
    println!("\n  Pairwise comparisons (row-by-row):\n");
    println!(
        "  {:<40} {:>7} {:>7} {:>7} {:>8}",
        "A vs B", "A wins", "B wins", "Ties", "B/A"
    );
    println!("  {}", "─".repeat(73));
    for i in 0..n_series {
        for j in (i + 1)..n_series {
            let mut a_wins = 0u64;
            let mut b_wins = 0u64;
            let mut ties = 0u64;
            for row in &non_trivial {
                let a_ns = row.series[i].1;
                let b_ns = row.series[j].1;
                if a_ns < b_ns {
                    a_wins += 1;
                } else if a_ns > b_ns {
                    b_wins += 1;
                } else {
                    ties += 1;
                }
            }
            let ratio = if totals[i] > 0 {
                totals[j] as f64 / totals[i] as f64
            } else {
                f64::NAN
            };
            println!(
                "  {:<40} {:>7} {:>7} {:>7} {:>7.2}×",
                format!("{} vs {}", series_names[i], series_names[j]),
                a_wins,
                b_wins,
                ties,
                ratio,
            );
        }
    }
    println!();
}

// ── Plotting ────────────────────────────────────────────────────────────────

const COLORS: [&RGBColor; 6] = [&BLUE, &RED, &GREEN, &MAGENTA, &CYAN, &BLACK];

fn plot_n_series(
    rows: &[MultiRow],
    out_path: &Path,
    title: &str,
    x_label: &str,
    metadata_block: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if rows.is_empty() {
        eprintln!("No data to plot.");
        return Ok(());
    }
    let series_names: Vec<String> = rows[0].series.iter().map(|(n, _)| n.clone()).collect();
    let n_series = series_names.len();

    let mut buckets: BTreeMap<u64, Vec<Vec<u64>>> = BTreeMap::new();
    for row in rows {
        let entry = buckets
            .entry(row.bucket)
            .or_insert_with(|| vec![Vec::new(); n_series]);
        for (i, (_, ns)) in row.series.iter().enumerate() {
            if i < n_series {
                entry[i].push(*ns);
            }
        }
    }

    let mut all_series: Vec<Vec<(u64, f64)>> = vec![Vec::new(); n_series];
    for (bucket, mut series_vecs) in buckets {
        for (i, vals) in series_vecs.iter_mut().enumerate() {
            all_series[i].push((bucket, median(vals)));
        }
    }

    let x_min = all_series[0].first().unwrap().0;
    let x_max = all_series[0].last().unwrap().0;
    let y_max = all_series
        .iter()
        .flat_map(|s| s.iter().map(|(_, y)| *y))
        .fold(0.0_f64, f64::max)
        * 1.15;
    let y_max = if y_max < 1.0 { 1.0 } else { y_max };

    let root = SVGBackend::new(out_path, (1024, 640)).into_drawing_area();
    root.fill(&WHITE)?;
    let mut chart = ChartBuilder::on(&root)
        .caption(title, ("sans-serif", 24).into_font())
        .margin(30)
        .x_label_area_size(50)
        .y_label_area_size(70)
        .build_cartesian_2d(x_min..x_max, 0.0_f64..y_max)?;
    chart
        .configure_mesh()
        .x_desc(x_label)
        .y_desc("Median nanoseconds / op")
        .draw()?;
    for (i, (name, data)) in series_names.iter().zip(all_series.iter()).enumerate() {
        let color = COLORS[i % COLORS.len()];
        chart
            .draw_series(LineSeries::new(data.iter().map(|(x, y)| (*x, *y)), color))?
            .label(name)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));
    }
    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;
    root.present()?;
    drop(chart);

    // Splice the metadata block in as an XML comment after the opening <svg ...> tag.
    let svg = fs::read_to_string(out_path)?;
    let with_meta = inject_svg_comment(&svg, metadata_block);
    fs::write(out_path, with_meta)?;

    println!("Chart written to {}", out_path.display());
    Ok(())
}

/// Insert an XML comment containing `block` immediately after the opening
/// `<svg ...>` tag. If we can't find one, prepend the comment to the file.
fn inject_svg_comment(svg: &str, block: &str) -> String {
    // Escape `--` inside block to keep the XML comment well-formed.
    let safe_block = block.replace("--", "- -");
    let comment = format!("\n<!--\n{}\n-->\n", safe_block.trim_end());
    if let Some(end) = svg.find('>').filter(|_| svg.trim_start().starts_with("<svg")) {
        let (head, tail) = svg.split_at(end + 1);
        format!("{head}{comment}{tail}")
    } else {
        format!("{comment}{svg}")
    }
}

// ── Driver ──────────────────────────────────────────────────────────────────

fn git_short_hash() -> Option<String> {
    let out = Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn git_dirty() -> bool {
    Command::new("git")
        .args(["diff", "--quiet", "HEAD"])
        .status()
        .map(|s| !s.success())
        .unwrap_or(false)
}

/// Repo root via `git rev-parse --show-toplevel`. The Lean benchmark binary
/// is invoked from there since `.lake/build/bin/benchmark` is a path relative
/// to the lakefile.
fn repo_root() -> Result<PathBuf, Box<dyn std::error::Error>> {
    let out = Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .map_err(|e| format!("failed to locate repo root via git: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "git rev-parse --show-toplevel failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )
        .into());
    }
    Ok(PathBuf::from(String::from_utf8_lossy(&out.stdout).trim()))
}

/// Build the metadata header that gets prepended to the .txt and embedded in
/// the SVG. Each line begins with `# ` so it's a comment in the .txt and
/// trivially skippable by the parser.
fn format_metadata(
    cfg: &BenchmarkConfig,
    git_hash: &str,
    dirty: bool,
    timestamp: &str,
    lake_cmd: &str,
) -> String {
    let mut s = String::new();
    s.push_str(&format!("# benchmark: {}\n", cfg.benchmark));
    s.push_str(&format!(
        "# git_hash:  {}{}\n",
        git_hash,
        if dirty { " (dirty)" } else { "" }
    ));
    s.push_str(&format!("# timestamp: {}\n", timestamp));
    s.push_str(&format!("# limit:     {}\n", cfg.limit));
    let params = cfg.params_string();
    if params.is_empty() {
        s.push_str("# params:    (none)\n");
    } else {
        s.push_str(&format!("# params:    {}\n", params));
    }
    s.push_str(&format!("# command:   {}\n", lake_cmd));
    s.push_str("#\n");
    s
}

pub fn run_from_config(config_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    // Canonicalize early so output paths stay valid regardless of any later
    // `current_dir` change on the spawned lake process.
    let config_path = fs::canonicalize(config_path)
        .map_err(|e| format!("cannot read {}: {e}", config_path.display()))?;
    let raw = fs::read_to_string(&config_path)
        .map_err(|e| format!("cannot read {}: {e}", config_path.display()))?;
    let cfg: BenchmarkConfig = toml::from_str(&raw)
        .map_err(|e| format!("invalid TOML in {}: {e}", config_path.display()))?;

    let stem = config_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or("config path has no file stem")?;
    let parent = config_path.parent().unwrap_or_else(|| Path::new("."));
    let svg_path: PathBuf = parent.join(format!("{stem}.svg"));
    let txt_path: PathBuf = parent.join(format!("{stem}.txt"));

    let root = repo_root()?;

    let git_hash = git_short_hash().unwrap_or_else(|| "unknown".to_string());
    let dirty = git_dirty();
    let timestamp = chrono::Utc::now()
        .format("%Y-%m-%dT%H:%M:%SZ")
        .to_string();

    let params = cfg.params_string();
    let mut lake_args = vec![
        "env".to_string(),
        ".lake/build/bin/benchmark".to_string(),
        cfg.benchmark.clone(),
        cfg.limit.to_string(),
    ];
    if !params.is_empty() {
        lake_args.push(params.clone());
    }
    let lake_cmd_display = format!("lake {}", shell_quote(&lake_args));
    let metadata = format_metadata(&cfg, &git_hash, dirty, &timestamp, &lake_cmd_display);

    println!("$ (cd {} && {lake_cmd_display})", root.display());
    let output = Command::new("lake")
        .args(&lake_args)
        .current_dir(&root)
        .output()
        .map_err(|e| format!("failed to spawn lake: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("lake benchmark exited {}: {stderr}", output.status).into());
    }
    let stdout = String::from_utf8(output.stdout)?;
    // Forward any Lean stderr (e.g. BUG: lines from correctness checks).
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.trim().is_empty() {
        eprint!("{stderr}");
    }

    // Write .txt with metadata header.
    {
        let mut f = fs::File::create(&txt_path)?;
        f.write_all(metadata.as_bytes())?;
        f.write_all(stdout.as_bytes())?;
    }
    println!("Raw data written to {}", txt_path.display());

    let rows = parse_multi_series(&stdout);
    println!("Parsed {} rows.", rows.len());
    print_summary(&rows);
    plot_n_series(&rows, &svg_path, &cfg.title, &cfg.x_label, metadata.trim_end())?;
    Ok(())
}

/// Minimal shell-quoting for display purposes only.
fn shell_quote(args: &[String]) -> String {
    args.iter()
        .map(|a| {
            if a.chars().any(|c| c.is_whitespace() || c == ':' || c == ',') {
                format!("\"{}\"", a.replace('"', "\\\""))
            } else {
                a.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

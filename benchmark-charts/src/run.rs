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
    /// Shorthand: if `chart` is empty, define a single default line chart
    /// using these.
    pub title: Option<String>,
    pub x_label: Option<String>,
    /// Parameters forwarded to the Lean binary as "k1:v1,k2:v2".
    #[serde(default)]
    pub params: BTreeMap<String, toml::Value>,
    /// One [[chart]] per output SVG. If empty, falls back to a default
    /// line chart synthesized from `title` and `x_label`.
    #[serde(default)]
    pub chart: Vec<ChartConfig>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct ChartConfig {
    /// "line" or "heatmap".
    #[serde(rename = "type", default = "default_chart_type")]
    pub kind: String,
    pub title: String,
    pub x_label: String,
    #[serde(default)]
    pub y_label: Option<String>,
    /// Filename suffix added to the config stem ("" for default).
    /// Example: stem="az_nat_mul_compare", suffix="_heatmap" -> az_nat_mul_compare_heatmap.svg.
    #[serde(default)]
    pub output_suffix: String,
    // Heatmap-specific:
    /// Bin width in bits. Default: derived from the data (~100 bins per axis).
    /// Set small (e.g. 64 = one limb) for essentially-no aggregation.
    #[serde(default)]
    pub bin_width: Option<u64>,
    /// Marker radius in pixels. Default ~3 px. Visual size is decoupled from
    /// bin_width so finer bins stay visible.
    #[serde(default)]
    pub point_size: Option<u32>,
    /// Names of the two series to compare (faster/slower). Default: the
    /// first two series in the row.
    #[serde(default)]
    pub comparison: Option<[String; 2]>,
}

fn default_chart_type() -> String {
    "line".to_string()
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

// ── Multi-series row ────────────────────────────────────────────────────────

pub struct MultiRow {
    /// One or more u64 coordinates from the row prefix. Length 1 = legacy
    /// single-bucket; length 2 = (bitsA, bitsB) for heatmaps.
    pub coords: Vec<u64>,
    pub series: Vec<(String, u64)>,
}

impl MultiRow {
    /// Convenience: sum of coords, used as the single-axis bucket for line
    /// charts.
    pub fn bucket(&self) -> u64 {
        self.coords.iter().sum()
    }
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
        // Prefix: one or more comma-separated u64s.
        let coords: Result<Vec<u64>, _> =
            parts[0].split(',').map(|s| s.parse::<u64>()).collect();
        let Ok(coords) = coords else {
            eprintln!("Could not parse coords: {}", &line[..line.len().min(80)]);
            continue;
        };
        if coords.is_empty() {
            eprintln!("Empty coord prefix: {}", &line[..line.len().min(80)]);
            continue;
        }
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
            rows.push(MultiRow { coords, series });
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
            .entry(row.bucket())
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

/// 2-D heatmap of which of two named series is faster on each (x, y) bin.
///
/// `chart.comparison` selects the two series to compare; default is the
/// first two series in row order. Color encodes `log2(A/B)` where (A, B) is
/// the comparison pair — so blue ≡ A faster, red ≡ B faster, white ≡ tie.
/// Populated bins are drawn as circular markers at fixed pixel size; empty
/// bins are left blank, so the populated region traces the boundary cleanly.
fn plot_heatmap(
    rows: &[MultiRow],
    out_path: &Path,
    chart: &ChartConfig,
    metadata_block: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if rows.is_empty() {
        eprintln!("No data to plot.");
        return Ok(());
    }
    let series_names: Vec<String> = rows[0].series.iter().map(|(n, _)| n.clone()).collect();
    if series_names.len() < 2 {
        eprintln!("Heatmap needs ≥ 2 series; got {}.", series_names.len());
        return Ok(());
    }
    // Pick which two series to compare.
    let (idx_a, idx_b) = match &chart.comparison {
        Some([a, b]) => {
            let ia = series_names
                .iter()
                .position(|s| s == a)
                .ok_or_else(|| format!("series {a:?} not found"))?;
            let ib = series_names
                .iter()
                .position(|s| s == b)
                .ok_or_else(|| format!("series {b:?} not found"))?;
            (ia, ib)
        }
        None => (0, 1),
    };
    let name_a = &series_names[idx_a];
    let name_b = &series_names[idx_b];

    // Need 2-D coordinates.
    let row0_dim = rows[0].coords.len();
    if row0_dim < 2 {
        eprintln!(
            "Heatmap needs ≥ 2 coords per row; data has {row0_dim}. \
             Re-run the benchmark with a 2-D prefix."
        );
        return Ok(());
    }

    // Choose bin width.
    let x_max = rows.iter().map(|r| r.coords[0]).max().unwrap_or(1);
    let y_max = rows.iter().map(|r| r.coords[1]).max().unwrap_or(1);
    let extent = x_max.max(y_max).max(1);
    let bin_width = chart.bin_width.unwrap_or_else(|| {
        // Aim for ≈ 120 bins along the longer axis, rounded to a multiple of
        // 64 (= one limb). Finer than the visual marker size so populated
        // regions look like a scatter cloud.
        let target_bins = 120u64;
        let raw = (extent / target_bins).max(64);
        ((raw + 63) / 64) * 64
    });
    let point_size = chart.point_size.unwrap_or(3);
    let nx = ((x_max / bin_width) + 1) as usize;
    let ny = ((y_max / bin_width) + 1) as usize;

    // Accumulate per-bin samples for the two series.
    let mut bins: BTreeMap<(usize, usize), (Vec<u64>, Vec<u64>)> = BTreeMap::new();
    for row in rows {
        let bx = (row.coords[0] / bin_width) as usize;
        let by = (row.coords[1] / bin_width) as usize;
        let ns_a = row.series.get(idx_a).map(|(_, ns)| *ns).unwrap_or(0);
        let ns_b = row.series.get(idx_b).map(|(_, ns)| *ns).unwrap_or(0);
        let entry = bins.entry((bx, by)).or_default();
        entry.0.push(ns_a);
        entry.1.push(ns_b);
    }
    // Per-bin log2 ratio: positive ⇒ B slower than A (so A faster).
    // We want positive ⇒ B faster, so flip: log2(A/B).
    // Convention: positive = B faster ⇒ red; negative = A faster ⇒ blue.
    let mut cells: BTreeMap<(usize, usize), f64> = BTreeMap::new();
    let mut count_a_faster = 0u64;
    let mut count_b_faster = 0u64;
    let mut count_tie = 0u64;
    for ((bx, by), (a_vals, b_vals)) in &bins {
        let mut a_sorted = a_vals.clone();
        let mut b_sorted = b_vals.clone();
        let med_a = median(&mut a_sorted);
        let med_b = median(&mut b_sorted);
        if med_a <= 0.0 && med_b <= 0.0 {
            continue;
        }
        // Avoid log(0); clamp at 1 ns.
        let a = med_a.max(1.0);
        let b = med_b.max(1.0);
        let log_ratio = (a / b).log2(); // a/b > 1 ⇒ A slower ⇒ B faster ⇒ red ⇒ positive
        cells.insert((*bx, *by), log_ratio);
        if log_ratio > 0.01 {
            count_b_faster += 1;
        } else if log_ratio < -0.01 {
            count_a_faster += 1;
        } else {
            count_tie += 1;
        }
    }
    let cap = cells
        .values()
        .map(|v| v.abs())
        .fold(0.5_f64, f64::max)
        .min(3.0); // cap saturation at ±3 (i.e. 8×)

    println!(
        "\nHeatmap: {} bins, bin_width = {} bits ({} cells with data)",
        nx * ny,
        bin_width,
        cells.len()
    );
    println!(
        "  {} faster: {}    {} faster: {}    ties: {}",
        name_a, count_a_faster, name_b, count_b_faster, count_tie
    );

    let x_label = &chart.x_label;
    let y_label = chart
        .y_label
        .clone()
        .unwrap_or_else(|| "significant_bits(b)".to_string());

    let root = SVGBackend::new(out_path, (1024, 800)).into_drawing_area();
    root.fill(&WHITE)?;
    let (chart_area, legend_area) = root.split_horizontally(880);

    let x_range = 0u64..((nx as u64) * bin_width);
    let y_range = 0u64..((ny as u64) * bin_width);
    let mut ch = ChartBuilder::on(&chart_area)
        .caption(&chart.title, ("sans-serif", 22).into_font())
        .margin(30)
        .x_label_area_size(60)
        .y_label_area_size(80)
        .build_cartesian_2d(x_range.clone(), y_range.clone())?;
    ch.configure_mesh().x_desc(x_label).y_desc(&y_label).draw()?;

    // Draw populated bins as fixed-pixel-size circles at the bin center.
    // Empty bins are skipped (background stays white) so the populated region
    // traces the boundary.
    ch.draw_series(cells.iter().map(|((bx, by), log_ratio)| {
        let x_center = (*bx as u64) * bin_width + bin_width / 2;
        let y_center = (*by as u64) * bin_width + bin_width / 2;
        let color = diverging_color(*log_ratio, cap);
        Circle::new((x_center, y_center), point_size as i32, color.filled())
    }))?;

    // Diagonal y = x for visual reference.
    let diag_extent = ((nx as u64) * bin_width).min((ny as u64) * bin_width);
    ch.draw_series(LineSeries::new(
        [(0u64, 0u64), (diag_extent, diag_extent)],
        BLACK.mix(0.25),
    ))?;

    drop(ch);

    // Colorbar in the legend area.
    draw_colorbar(&legend_area, cap, name_a, name_b)?;

    root.present()?;
    drop(root);

    let svg = fs::read_to_string(out_path)?;
    fs::write(out_path, inject_svg_comment(&svg, metadata_block))?;
    println!("Chart written to {}", out_path.display());
    Ok(())
}

/// Map a centered value in `[-cap, cap]` to a blue→white→red color.
fn diverging_color(v: f64, cap: f64) -> RGBColor {
    let t = (v / cap).clamp(-1.0, 1.0);
    // Anchor stops: deep blue (50,100,200), white (250,250,250), deep red (200,60,60).
    let blue = (50.0, 100.0, 200.0);
    let white = (250.0, 250.0, 250.0);
    let red = (200.0, 60.0, 60.0);
    let (r, g, b) = if t < 0.0 {
        let a = -t; // 0 = white, 1 = blue
        (
            white.0 * (1.0 - a) + blue.0 * a,
            white.1 * (1.0 - a) + blue.1 * a,
            white.2 * (1.0 - a) + blue.2 * a,
        )
    } else {
        let a = t;
        (
            white.0 * (1.0 - a) + red.0 * a,
            white.1 * (1.0 - a) + red.1 * a,
            white.2 * (1.0 - a) + red.2 * a,
        )
    };
    RGBColor(r.round() as u8, g.round() as u8, b.round() as u8)
}

fn draw_colorbar(
    area: &DrawingArea<SVGBackend, plotters::coord::Shift>,
    cap: f64,
    name_a: &str,
    name_b: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let (w, h) = area.dim_in_pixel();
    let bar_x0 = 20i32;
    let bar_x1 = 60i32;
    let bar_y0 = 80i32;
    let bar_y1 = (h as i32) - 80;
    let steps = 100i32;
    for i in 0..steps {
        // top = +cap (B faster, red), bottom = -cap (A faster, blue).
        let t = 1.0 - 2.0 * (i as f64) / (steps as f64);
        let v = t * cap;
        let color = diverging_color(v, cap);
        let y0 = bar_y0 + ((bar_y1 - bar_y0) * i) / steps;
        let y1 = bar_y0 + ((bar_y1 - bar_y0) * (i + 1)) / steps;
        area.draw(&Rectangle::new(
            [(bar_x0, y0), (bar_x1, y1)],
            color.filled(),
        ))?;
    }
    // Border.
    area.draw(&Rectangle::new(
        [(bar_x0, bar_y0), (bar_x1, bar_y1)],
        BLACK.stroke_width(1),
    ))?;
    // Tick labels at top, middle, bottom.
    let style = ("sans-serif", 13).into_font().color(&BLACK);
    let label = |area: &DrawingArea<SVGBackend, plotters::coord::Shift>,
                 y: i32,
                 text: String|
     -> Result<(), Box<dyn std::error::Error>> {
        area.draw(&plotters::element::Text::new(text, (bar_x1 + 5, y - 6), style.clone()))?;
        Ok(())
    };
    label(area, bar_y0, format!("{name_b} ≥{:.1}× faster", 2f64.powf(cap)))?;
    label(area, (bar_y0 + bar_y1) / 2, "tie".to_string())?;
    label(area, bar_y1, format!("{name_a} ≥{:.1}× faster", 2f64.powf(cap)))?;
    // Caption.
    let cap_style = ("sans-serif", 14).into_font().color(&BLACK);
    area.draw(&plotters::element::Text::new(
        "log₂(faster ratio)".to_string(),
        (10, 50),
        cap_style,
    ))?;
    let _ = w;
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

pub struct RunOptions {
    /// If true and the .txt already exists, skip the Lean run and re-render
    /// charts from the existing data.
    pub reuse: bool,
}

pub fn run_from_config(
    config_path: &Path,
    opts: &RunOptions,
) -> Result<(), Box<dyn std::error::Error>> {
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
    let txt_path: PathBuf = parent.join(format!("{stem}.txt"));

    // Resolve the list of charts to render.
    let charts: Vec<ChartConfig> = if cfg.chart.is_empty() {
        // Legacy shorthand: build a single default line chart from title/x_label.
        let title = cfg
            .title
            .clone()
            .ok_or("config has no [[chart]] and no top-level `title`")?;
        let x_label = cfg
            .x_label
            .clone()
            .ok_or("config has no [[chart]] and no top-level `x_label`")?;
        vec![ChartConfig {
            kind: "line".to_string(),
            title,
            x_label,
            y_label: None,
            output_suffix: String::new(),
            bin_width: None,
            point_size: None,
            comparison: None,
        }]
    } else {
        cfg.chart.clone()
    };

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

    // Decide whether to (re-)run Lean.
    let stdout = if opts.reuse && txt_path.exists() {
        println!(
            "--reuse: skipping Lean run; reading existing {}",
            txt_path.display()
        );
        fs::read_to_string(&txt_path)?
    } else {
        if opts.reuse {
            println!(
                "--reuse set but {} does not exist; running benchmark.",
                txt_path.display()
            );
        }
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
        // The body we hand to the parser doesn't include the header (parser
        // skips `#` lines anyway, so either works).
        stdout
    };

    let rows = parse_multi_series(&stdout);
    println!("Parsed {} rows.", rows.len());
    print_summary(&rows);

    // For SVG metadata: prefer the freshly-built block, otherwise pull the
    // header out of the existing .txt so the chart still carries it.
    let svg_metadata = if opts.reuse && txt_path.exists() {
        extract_header_block(&fs::read_to_string(&txt_path)?)
    } else {
        metadata.trim_end().to_string()
    };

    for chart in &charts {
        let svg_path = parent.join(format!("{stem}{}.svg", chart.output_suffix));
        match chart.kind.as_str() {
            "line" => plot_n_series(
                &rows,
                &svg_path,
                &chart.title,
                &chart.x_label,
                &svg_metadata,
            )?,
            "heatmap" => plot_heatmap(&rows, &svg_path, chart, &svg_metadata)?,
            other => {
                eprintln!(
                    "Unknown chart type {:?}; skipping ({})",
                    other,
                    svg_path.display()
                );
            }
        }
    }
    Ok(())
}

/// Pull the contiguous `# ...` header block off the top of a .txt for
/// embedding back into freshly-rendered SVGs when re-using data.
fn extract_header_block(content: &str) -> String {
    let mut header = String::new();
    for line in content.lines() {
        if line.starts_with('#') {
            header.push_str(line);
            header.push('\n');
        } else if line.trim().is_empty() {
            header.push('\n');
        } else {
            break;
        }
    }
    header.trim_end().to_string()
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

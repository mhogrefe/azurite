mod dense_poly;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::str::FromStr;

use malachite_base::num::logic::traits::SignificantBits;
use malachite_q::Rational;
use plotters::prelude::*;

// ── Data models ──────────────────────────────────────────────────────────────

/// Two-series row (for rat_cmp).
struct Row {
    bucket: u64,
    default_ns: u64,
    azurite_ns: u64,
}

/// N-series row (for benchmarks with variable number of implementations).
struct MultiRow {
    bucket: u64,
    /// (series_name, ns_value)
    series: Vec<(String, u64)>,
}

// ── Parsing ──────────────────────────────────────────────────────────────────

/// Parse rat_cmp benchmark output.
fn parse_rat_cmp_file(content: &str) -> Vec<Row> {
    let mut rows = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Format (6 fields): rat1,rat2,default,ns1,azurite,ns2
        let parts: Vec<&str> = line.splitn(9, ',').collect();
        let (rat1, rat2, ns1_str, ns2_str) = match parts.len() {
            6 => (parts[0], parts[1], parts[3], parts[5]),
            8 => (parts[0], parts[1], parts[3], parts[6]),
            _ => {
                eprintln!("Skipping malformed line ({} fields): {}", parts.len(), &line[..line.len().min(80)]);
                continue;
            }
        };
        let (Ok(a), Ok(b)) = (
            Rational::from_str(rat1),
            Rational::from_str(rat2),
        ) else {
            eprintln!("Could not parse rationals on line: {}", &line[..line.len().min(80)]);
            continue;
        };
        let (Ok(default_ns), Ok(azurite_ns)) = (
            ns1_str.parse::<u64>(),
            ns2_str.parse::<u64>(),
        ) else {
            eprintln!("Could not parse timings on line: {}", &line[..line.len().min(80)]);
            continue;
        };
        let bucket = a.significant_bits() + b.significant_bits();
        rows.push(Row { bucket, default_ns, azurite_ns });
    }
    rows
}

/// Parse semicolon-separated N-series benchmark output.
/// Format: `<bucket>;name1,ns1;name2,ns2;...;nameN,nsN`
fn parse_multi_series_file(content: &str) -> Vec<MultiRow> {
    let mut rows = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
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

// ── Statistics ───────────────────────────────────────────────────────────────

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

/// Print a text summary of N-series benchmark results.
fn print_summary(rows: &[MultiRow]) {
    if rows.is_empty() {
        return;
    }
    let series_names: Vec<String> = rows[0].series.iter().map(|(n, _)| n.clone()).collect();
    let n_series = series_names.len();

    // Collect per-series timings (excluding rows where all are 0 — trivial inputs)
    let non_trivial: Vec<&MultiRow> = rows.iter()
        .filter(|r| r.series.iter().any(|(_, ns)| *ns > 0))
        .collect();
    let n = non_trivial.len();
    if n == 0 {
        println!("No non-trivial rows to summarize.");
        return;
    }

    // Per-series averages
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

    // Pairwise comparisons
    println!("\n  Pairwise comparisons (row-by-row):\n");
    println!("  {:<40} {:>7} {:>7} {:>7} {:>8}", "A vs B", "A wins", "B wins", "Ties", "B/A");
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
            println!("  {:<40} {:>7} {:>7} {:>7} {:>7.2}×",
                format!("{} vs {}", series_names[i], series_names[j]),
                a_wins, b_wins, ties, ratio,
            );
        }
    }
    println!();
}

// ── Plotting ─────────────────────────────────────────────────────────────────

const COLORS: [&RGBColor; 6] = [&BLUE, &RED, &GREEN, &MAGENTA, &CYAN, &BLACK];

/// Generic N-series line chart.
fn plot_n_series(
    rows: Vec<MultiRow>,
    out_path: &str,
    title: &str,
    x_label: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if rows.is_empty() {
        eprintln!("No data to plot.");
        return Ok(());
    }

    // Discover series names from the first row
    let series_names: Vec<String> = rows[0].series.iter().map(|(n, _)| n.clone()).collect();
    let n_series = series_names.len();

    // Bucket → Vec<Vec<u64>>  (one vec per series)
    let mut buckets: BTreeMap<u64, Vec<Vec<u64>>> = BTreeMap::new();
    for row in &rows {
        let entry = buckets.entry(row.bucket).or_insert_with(|| vec![Vec::new(); n_series]);
        for (i, (_, ns)) in row.series.iter().enumerate() {
            if i < n_series {
                entry[i].push(*ns);
            }
        }
    }

    // Compute per-bucket medians for each series
    let mut all_series: Vec<Vec<(u64, f64)>> = vec![Vec::new(); n_series];
    for (bucket, mut series_vecs) in buckets {
        for (i, vals) in series_vecs.iter_mut().enumerate() {
            all_series[i].push((bucket, median(vals)));
        }
    }

    let x_min = all_series[0].first().unwrap().0;
    let x_max = all_series[0].last().unwrap().0;
    let y_max = all_series.iter()
        .flat_map(|s| s.iter().map(|(_, y)| *y))
        .fold(0.0_f64, f64::max) * 1.15;
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
            .draw_series(LineSeries::new(
                data.iter().map(|(x, y)| (*x, *y)),
                color,
            ))?
            .label(name)
            .legend(move |(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], color));
    }

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    root.present()?;
    println!("Chart written to {out_path}");
    Ok(())
}

/// Two-series line chart (legacy, for rat_cmp).
fn plot_two_series(
    rows: Vec<Row>,
    out_path: &str,
    title: &str,
    x_label: &str,
    series1_label: &str,
    series2_label: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // Convert to MultiRow format
    let multi_rows: Vec<MultiRow> = rows.into_iter().map(|r| MultiRow {
        bucket: r.bucket,
        series: vec![
            (series1_label.to_string(), r.default_ns),
            (series2_label.to_string(), r.azurite_ns),
        ],
    }).collect();
    plot_n_series(multi_rows, out_path, title, x_label)
}

// ── Main ─────────────────────────────────────────────────────────────────────

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} <benchmark> <input_file> [output_svg]", args[0]);
        eprintln!("  benchmarks: rat_cmp, dense_poly_mul");
        std::process::exit(1);
    }
    let benchmark = &args[1];
    let input_path = &args[2];
    let output_path = if args.len() >= 4 { &args[3] } else { "chart.svg" };

    let content = fs::read_to_string(input_path)
        .map_err(|e| format!("Cannot read {input_path}: {e}"))?;

    match benchmark.as_str() {
        "rat_cmp" => {
            let rows = parse_rat_cmp_file(&content);
            println!("Parsed {} rows.", rows.len());
            let series1_label = "default (Lean baseline)";
            let series2_label = "azurite";
            // Summary
            let multi: Vec<MultiRow> = rows.iter().map(|r| MultiRow {
                bucket: r.bucket,
                series: vec![
                    (series1_label.to_string(), r.default_ns),
                    (series2_label.to_string(), r.azurite_ns),
                ],
            }).collect();
            print_summary(&multi);
            plot_two_series(
                rows, output_path,
                "rat_cmp: median ns/op by input size",
                "Input size (significant_bits of both rationals)",
                series1_label, series2_label,
            )?;
        }
        "dense_poly_mul" | "dense_poly_karatsuba" => {
            let rows = parse_multi_series_file(&content);
            println!("Parsed {} rows.", rows.len());
            print_summary(&rows);
            plot_n_series(
                rows, output_path,
                &format!("{benchmark}: median ns/op by input size"),
                "Input size (significant_bits of both polynomials)",
            )?;
        }
        other => {
            eprintln!("Unknown benchmark: {other:?}");
            eprintln!("Valid benchmarks: rat_cmp, dense_poly_mul, dense_poly_karatsuba");
            std::process::exit(1);
        }
    }
    Ok(())
}

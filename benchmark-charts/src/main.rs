use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::str::FromStr;

use malachite_base::num::logic::traits::SignificantBits;
use malachite_q::Rational;
use plotters::prelude::*;

// ── Data model ───────────────────────────────────────────────────────────────

struct Row {
    bucket: u64,
    default_ns: u64,
    azurite_ns: u64,
}

// ── Parsing ──────────────────────────────────────────────────────────────────

fn parse_file(content: &str) -> Vec<Row> {
    let mut rows = Vec::new();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Old format (6 fields): rat1,rat2,default,ns1,azurite,ns2
        // New format (8 fields): rat1,rat2,default,ns1,chk1,azurite,ns2,chk2
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

// ── Plotting ─────────────────────────────────────────────────────────────────

fn plot_rat_cmp(rows: Vec<Row>, out_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    // Bucket → (default times, azurite times)
    let mut buckets: BTreeMap<u64, (Vec<u64>, Vec<u64>)> = BTreeMap::new();
    for row in rows {
        let entry = buckets.entry(row.bucket).or_default();
        entry.0.push(row.default_ns);
        entry.1.push(row.azurite_ns);
    }

    if buckets.is_empty() {
        eprintln!("No data to plot.");
        return Ok(());
    }

    // Compute per-bucket medians
    let mut default_series: Vec<(u64, f64)> = Vec::new();
    let mut azurite_series: Vec<(u64, f64)> = Vec::new();
    for (bucket, (mut def, mut az)) in buckets {
        default_series.push((bucket, median(&mut def)));
        azurite_series.push((bucket, median(&mut az)));
    }

    let x_min = default_series.first().unwrap().0;
    let x_max = default_series.last().unwrap().0;
    let all_y: Vec<f64> = default_series.iter().chain(azurite_series.iter())
        .map(|(_, y)| *y).collect();
    let y_max = all_y.iter().cloned().fold(0.0_f64, f64::max) * 1.15;
    let y_max = if y_max < 1.0 { 1.0 } else { y_max };

    let root = SVGBackend::new(out_path, (1024, 640)).into_drawing_area();
    root.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&root)
        .caption("rat_cmp: median ns/op by input size", ("sans-serif", 24).into_font())
        .margin(30)
        .x_label_area_size(50)
        .y_label_area_size(70)
        .build_cartesian_2d(x_min..x_max, 0.0_f64..y_max)?;

    chart
        .configure_mesh()
        .x_desc("Input size (significant_bits of both rationals)")
        .y_desc("Median nanoseconds / op")
        .draw()?;

    // default (Lean baseline) — blue
    chart
        .draw_series(LineSeries::new(
            default_series.iter().map(|(x, y)| (*x, *y)),
            &BLUE,
        ))?
        .label("default (Lean baseline)")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &BLUE));

    // azurite — red
    chart
        .draw_series(LineSeries::new(
            azurite_series.iter().map(|(x, y)| (*x, *y)),
            &RED,
        ))?
        .label("azurite")
        .legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], &RED));

    chart
        .configure_series_labels()
        .background_style(&WHITE.mix(0.8))
        .border_style(&BLACK)
        .draw()?;

    root.present()?;
    println!("Chart written to {out_path}");
    Ok(())
}

// ── Main ─────────────────────────────────────────────────────────────────────

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} <benchmark> <input_file> [output_svg]", args[0]);
        eprintln!("  benchmark: rat_cmp");
        std::process::exit(1);
    }
    let benchmark = &args[1];
    let input_path = &args[2];
    let output_path = if args.len() >= 4 { &args[3] } else { "chart.svg" };

    let content = fs::read_to_string(input_path)
        .map_err(|e| format!("Cannot read {input_path}: {e}"))?;

    match benchmark.as_str() {
        "rat_cmp" => {
            let rows = parse_file(&content);
            println!("Parsed {} rows.", rows.len());
            plot_rat_cmp(rows, output_path)?;
        }
        other => {
            eprintln!("Unknown benchmark: {other:?}");
            eprintln!("Valid benchmarks: rat_cmp");
            std::process::exit(1);
        }
    }
    Ok(())
}

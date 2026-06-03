#!/usr/bin/env python3
"""Plot Chapter 7 derivative-size CSV files by k, comparing metrics directly."""

from __future__ import annotations

import argparse
import csv
import html
import math
from collections import OrderedDict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


Point = Tuple[int, float]


COLORS = {
    "strongTree": "#1f77b4",
    "strongMemoTree": "#2ca02c",
    "cubicTree": "#d62728",
    "strongDag": "#6baed6",
    "strongMemoDag": "#74c476",
    "cubicDag": "#fb6a4a",
    "strongShape": "#9ecae1",
    "strongMemoShape": "#a1d99b",
    "cubicShape": "#fcae91",
    "sharedShapeStatePool": "#9467bd",
    "langContPruneShapeStatePool": "#ff7f0e",
}

FALLBACK_COLORS = [
    "#1f77b4",
    "#d62728",
    "#2ca02c",
    "#9467bd",
    "#ff7f0e",
    "#17becf",
    "#8c564b",
    "#e377c2",
    "#7f7f7f",
    "#bcbd22",
]


def nice_name(metric: str) -> str:
    names = {
        "strongTree": "thesis bsimpStrong tree",
        "strongDag": "thesis bsimpStrong DAG",
        "strongShape": "thesis bsimpStrong shape DAG",
        "strongMemoTree": "deferred memo strong tree",
        "strongMemoDag": "deferred memo strong DAG",
        "strongMemoShape": "deferred memo strong shape DAG",
        "strongMemoStates": "deferred memo states",
        "strongMemoSplitProbes": "deferred memo split probes",
        "strongMemoSpanBound": "deferred memo span bound",
        "strongMemoSplitBound": "deferred memo split bound",
        "cubicTree": "current bsimpCubic tree",
        "cubicDag": "current bsimpCubic DAG",
        "cubicShape": "current bsimpCubic shape DAG",
        "sharedShapeStatePool": "shared prefix shape pool",
        "langContPruneShapeStatePool": "language-continuation shape pool",
    }
    return names.get(metric, metric)


def load_rows(csv_path: Path) -> Tuple[Dict[int, OrderedDict[str, List[Point]]], List[str], List[str]]:
    by_k: Dict[int, OrderedDict[str, List[Point]]] = {}
    metric_order: List[str] = []
    seq_modes: List[str] = []
    with csv_path.open(newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            k = int(row["k"])
            n = int(row["n"])
            metric = row["metric"]
            value = float(row["value"])
            seq_mode = row.get("seqMode", "")
            if metric not in metric_order:
                metric_order.append(metric)
            if seq_mode and seq_mode not in seq_modes:
                seq_modes.append(seq_mode)
            by_k.setdefault(k, OrderedDict()).setdefault(metric, []).append((n, value))
    for metrics in by_k.values():
        for points in metrics.values():
            points.sort()
    return by_k, metric_order, seq_modes


def ticks(min_v: float, max_v: float, count: int = 5) -> List[float]:
    if min_v == max_v:
        return [min_v]
    raw_step = (max_v - min_v) / max(1, count - 1)
    mag = 10 ** math.floor(math.log10(raw_step))
    norm = raw_step / mag
    if norm <= 1:
        step = mag
    elif norm <= 2:
        step = 2 * mag
    elif norm <= 5:
        step = 5 * mag
    else:
        step = 10 * mag
    start = math.floor(min_v / step) * step
    out: List[float] = []
    v = start
    while v <= max_v + 0.5 * step:
        if v >= min_v - 0.5 * step:
            out.append(v)
        v += step
    return out[: count + 2]


def line_path(points: Iterable[Point], x_map, y_map) -> str:
    parts: List[str] = []
    for i, (x, y) in enumerate(points):
        cmd = "M" if i == 0 else "L"
        parts.append(f"{cmd}{x_map(x):.2f},{y_map(y):.2f}")
    return " ".join(parts)


def color_for(metric: str, index: int) -> str:
    return COLORS.get(metric, FALLBACK_COLORS[index % len(FALLBACK_COLORS)])


def render_svg(
    k: int,
    series: OrderedDict[str, List[Point]],
    metric_order: List[str],
    out_path: Path,
    title_prefix: str,
    log_y: bool,
) -> None:
    width, height = 1040, 610
    left, right, top, bottom = 82, 260, 58, 78
    plot_w = width - left - right
    plot_h = height - top - bottom

    xs = [x for points in series.values() for x, _ in points]
    ys = [y for points in series.values() for _, y in points]
    if not xs or not ys:
        return

    x_min, x_max = min(xs), max(xs)
    if x_min == x_max:
        x_max = x_min + 1

    if log_y:
        positive = [y for y in ys if y > 0]
        if positive:
            y_min = min(positive)
            y_max = max(positive)
        else:
            log_y = False
    if not log_y:
        y_min = 0.0
        y_max = max(ys)
    if y_min == y_max:
        y_max = y_min + 1

    def x_map(x: float) -> float:
        return left + (x - x_min) / (x_max - x_min) * plot_w

    if log_y:
        ly_min = math.log10(y_min)
        ly_max = math.log10(y_max)

        def y_map(y: float) -> float:
            safe = max(y, y_min)
            return top + (ly_max - math.log10(safe)) / (ly_max - ly_min) * plot_h

        y_tick_values = [10 ** t for t in ticks(ly_min, ly_max)]
        y_label = "size (log10)"
    else:

        def y_map(y: float) -> float:
            return top + (y_max - y) / (y_max - y_min) * plot_h

        y_tick_values = ticks(y_min, y_max)
        y_label = "size"

    x_tick_values = ticks(x_min, x_max)
    esc_title = html.escape(f"{title_prefix}: k={k}")
    y_suffix = " log" if log_y else ""

    svg: List[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{left}" y="30" font-family="Arial, sans-serif" font-size="18" font-weight="700">{esc_title}</text>',
        f'<text x="{left}" y="50" font-family="Arial, sans-serif" font-size="12" fill="#555">x: input length n for a^n, y: simplified derivative {html.escape(y_label)}, baseline: thesis bsimpStrong</text>',
        f'<rect x="{left}" y="{top}" width="{plot_w}" height="{plot_h}" fill="#fbfbfb" stroke="#222" stroke-width="1"/>',
    ]

    for xt in x_tick_values:
        x = x_map(xt)
        svg.append(f'<line x1="{x:.2f}" y1="{top}" x2="{x:.2f}" y2="{top + plot_h}" stroke="#e5e5e5" stroke-width="1"/>')
        svg.append(f'<text x="{x:.2f}" y="{top + plot_h + 24}" text-anchor="middle" font-family="Arial, sans-serif" font-size="11">{xt:g}</text>')

    for yt in y_tick_values:
        y = y_map(yt)
        label = f"{yt:.3g}" if log_y else f"{yt:g}"
        svg.append(f'<line x1="{left}" y1="{y:.2f}" x2="{left + plot_w}" y2="{y:.2f}" stroke="#e5e5e5" stroke-width="1"/>')
        svg.append(f'<text x="{left - 10}" y="{y + 4:.2f}" text-anchor="end" font-family="Arial, sans-serif" font-size="11">{html.escape(label)}</text>')

    svg.append(f'<text x="{left + plot_w / 2:.2f}" y="{height - 22}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">n</text>')
    svg.append(f'<text x="18" y="{top + plot_h / 2:.2f}" transform="rotate(-90 18,{top + plot_h / 2:.2f})" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">size{y_suffix}</text>')

    for i, metric in enumerate(metric_order):
        points = series.get(metric)
        if not points:
            continue
        color = color_for(metric, i)
        width_px = "3.0" if metric == "strongTree" else "2.2"
        dash = ' stroke-dasharray="7 5"' if metric == "strongTree" else ""
        svg.append(f'<path d="{line_path(points, x_map, y_map)}" fill="none" stroke="{color}" stroke-width="{width_px}"{dash}/>')
        for x, y in points:
            svg.append(f'<circle cx="{x_map(x):.2f}" cy="{y_map(y):.2f}" r="2.4" fill="{color}"/>')

    legend_x = left + plot_w + 24
    legend_y = top + 8
    svg.append(f'<text x="{legend_x}" y="{legend_y}" font-family="Arial, sans-serif" font-size="13" font-weight="700">metric</text>')
    legend_i = 0
    for i, metric in enumerate(metric_order):
        if metric not in series:
            continue
        color = color_for(metric, i)
        y = legend_y + 24 + legend_i * 24
        dash = ' stroke-dasharray="7 5"' if metric == "strongTree" else ""
        svg.append(f'<line x1="{legend_x}" y1="{y - 4}" x2="{legend_x + 28}" y2="{y - 4}" stroke="{color}" stroke-width="2.4"{dash}/>')
        svg.append(f'<text x="{legend_x + 36}" y="{y}" font-family="Arial, sans-serif" font-size="12">{html.escape(nice_name(metric))}</text>')
        legend_i += 1

    svg.append("</svg>")
    out_path.write_text("\n".join(svg), encoding="utf-8")


def point_map(points: List[Point]) -> Dict[int, float]:
    return {n: value for n, value in points}


def write_summary(
    out_dir: Path,
    by_k: Dict[int, OrderedDict[str, List[Point]]],
    metric_order: List[str],
    baseline: str,
) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    for k in sorted(by_k):
        series = by_k[k]
        base_points = point_map(series.get(baseline, []))
        for metric in metric_order:
            points = series.get(metric)
            if not points:
                continue
            n_max = max(n for n, _ in points)
            values = point_map(points)
            final = values[n_max]
            base_final = base_points.get(n_max)
            ratios = [
                value / base_points[n]
                for n, value in points
                if n in base_points and base_points[n] != 0
            ]
            max_ratio = max(ratios) if ratios else float("nan")
            verdict = ""
            if metric == baseline:
                verdict = "baseline"
            elif ratios:
                verdict = "within baseline" if max_ratio <= 1.0 else "larger than baseline"
            rows.append(
                {
                    "k": str(k),
                    "metric": metric,
                    "n_max": str(n_max),
                    "value_at_n_max": f"{final:g}",
                    "baseline_at_n_max": "" if base_final is None else f"{base_final:g}",
                    "ratio_at_n_max": "" if base_final in (None, 0) else f"{final / base_final:.4g}",
                    "max_ratio_to_baseline": "" if math.isnan(max_ratio) else f"{max_ratio:.4g}",
                    "verdict": verdict,
                }
            )

    with (out_dir / "comparison_summary.csv").open("w", newline="", encoding="utf-8") as f:
        fieldnames = [
            "k",
            "metric",
            "n_max",
            "value_at_n_max",
            "baseline_at_n_max",
            "ratio_at_n_max",
            "max_ratio_to_baseline",
            "verdict",
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    return rows


def write_index(
    out_dir: Path,
    files: List[Path],
    rows: List[Dict[str, str]],
    title: str,
    seq_modes: List[str],
    baseline: str,
) -> None:
    mode_text = ", ".join(seq_modes) if seq_modes else "unknown"
    table_rows = "\n".join(
        "<tr>"
        + "".join(f"<td>{html.escape(row[key])}</td>" for key in [
            "k",
            "metric",
            "n_max",
            "value_at_n_max",
            "baseline_at_n_max",
            "ratio_at_n_max",
            "max_ratio_to_baseline",
            "verdict",
        ])
        + "</tr>"
        for row in rows
    )
    image_sections = "\n".join(
        f'<section><h2>{html.escape(path.stem)}</h2><img src="{html.escape(path.name)}" alt="{html.escape(path.stem)}"></section>'
        for path in files
    )
    html_text = f"""<!doctype html>
<meta charset="utf-8">
<title>{html.escape(title)}</title>
<style>
body {{ font-family: Arial, sans-serif; margin: 28px; color: #222; }}
p {{ max-width: 920px; }}
table {{ border-collapse: collapse; margin: 18px 0 32px; font-size: 13px; }}
th, td {{ border: 1px solid #ddd; padding: 6px 8px; text-align: right; }}
th:nth-child(2), td:nth-child(2), th:last-child, td:last-child {{ text-align: left; }}
th {{ background: #f3f3f3; }}
section {{ margin: 0 0 36px; }}
img {{ max-width: 100%; border: 1px solid #ddd; }}
</style>
<h1>{html.escape(title)}</h1>
<p>CSV source: <code>ch7_size_grid.csv</code>. Sequence mode: <code>{html.escape(mode_text)}</code>. Baseline for ratios: <code>{html.escape(baseline)}</code>.</p>
<table>
<thead><tr><th>k</th><th>metric</th><th>n max</th><th>value</th><th>baseline</th><th>ratio at n max</th><th>max ratio</th><th>verdict</th></tr></thead>
<tbody>
{table_rows}
</tbody>
</table>
{image_sections}
"""
    (out_dir / "index.html").write_text(html_text, encoding="utf-8")


def safe_k_filename(k: int, log_y: bool) -> str:
    suffix = "_log" if log_y else ""
    return f"k_{k}_derivative_size{suffix}.svg"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--title-prefix", default="Chapter 7 derivative-size comparison")
    parser.add_argument("--baseline", default="strongTree")
    parser.add_argument("--log-y", action="store_true")
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    by_k, metric_order, seq_modes = load_rows(args.csv)
    written: List[Path] = []
    for k in sorted(by_k):
        out = args.out_dir / safe_k_filename(k, args.log_y)
        render_svg(k, by_k[k], metric_order, out, args.title_prefix, args.log_y)
        written.append(out)
    rows = write_summary(args.out_dir, by_k, metric_order, args.baseline)
    write_index(args.out_dir, written, rows, args.title_prefix, seq_modes, args.baseline)
    for path in written:
        print(path)
    print(args.out_dir / "comparison_summary.csv")
    print(args.out_dir / "index.html")


if __name__ == "__main__":
    main()

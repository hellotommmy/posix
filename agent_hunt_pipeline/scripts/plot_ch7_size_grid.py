#!/usr/bin/env python3
"""Plot Chapter 7 derivative-size CSV files as dependency-free SVG charts."""

from __future__ import annotations

import argparse
import csv
import html
import math
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


Point = Tuple[int, float]


COLORS = [
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
        "strongTree": "bsimpStrong tree",
        "strongDag": "bsimpStrong DAG",
        "strongShape": "bsimpStrong shape DAG",
        "strongSafeTree": "bsimpStrongSafe tree",
        "strongSafeDag": "bsimpStrongSafe DAG",
        "strongSafeShape": "bsimpStrongSafe shape DAG",
        "cubicTree": "current bsimpCubic tree",
        "cubicDag": "current bsimpCubic DAG",
        "cubicShape": "current bsimpCubic shape DAG",
        "sharedTree": "shared direct tree",
        "sharedDag": "shared direct DAG",
        "sharedShape": "shared direct shape DAG",
        "sharedStatePool": "shared prefix state pool",
        "sharedShapeStatePool": "shared prefix shape pool",
        "langContPruneShapeStatePool": "language-continuation shape pool",
        "langAtomicContPruneShapeStatePool": "atomic language-continuation shape pool",
    }
    return names.get(metric, metric)


def load_rows(csv_path: Path) -> Dict[str, Dict[int, List[Point]]]:
    by_metric: Dict[str, Dict[int, List[Point]]] = {}
    with csv_path.open(newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            metric = row["metric"]
            k = int(row["k"])
            n = int(row["n"])
            value = float(row["value"])
            by_metric.setdefault(metric, {}).setdefault(k, []).append((n, value))
    for series in by_metric.values():
        for points in series.values():
            points.sort()
    return by_metric


def line_path(points: Iterable[Point], x_map, y_map) -> str:
    parts = []
    for i, (x, y) in enumerate(points):
        cmd = "M" if i == 0 else "L"
        parts.append(f"{cmd}{x_map(x):.2f},{y_map(y):.2f}")
    return " ".join(parts)


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
    out = []
    v = start
    while v <= max_v + 0.5 * step:
        if v >= min_v - 0.5 * step:
            out.append(v)
        v += step
    return out[: count + 2]


def render_svg(
    metric: str,
    series: Dict[int, List[Point]],
    out_path: Path,
    title_prefix: str,
    log_y: bool,
) -> None:
    width, height = 960, 580
    left, right, top, bottom = 82, 190, 54, 76
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
        if not positive:
            log_y = False
        else:
            y_min = min(positive)
            y_max = max(positive)
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
        y_label = "value (log10)"
    else:

        def y_map(y: float) -> float:
            return top + (y_max - y) / (y_max - y_min) * plot_h

        y_tick_values = ticks(y_min, y_max)
        y_label = "value"

    x_tick_values = ticks(x_min, x_max)
    esc_title = html.escape(f"{title_prefix}: {nice_name(metric)}")
    y_suffix = " log" if log_y else ""

    svg: List[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{left}" y="28" font-family="Arial, sans-serif" font-size="18" font-weight="700">{esc_title}</text>',
        f'<text x="{left}" y="48" font-family="Arial, sans-serif" font-size="12" fill="#555">x: input length n, lines: Chapter 7 evil family parameter k, y: {html.escape(y_label)}</text>',
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

    svg.append(f'<text x="{left + plot_w / 2:.2f}" y="{height - 20}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">n</text>')
    svg.append(f'<text x="18" y="{top + plot_h / 2:.2f}" transform="rotate(-90 18,{top + plot_h / 2:.2f})" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">size{y_suffix}</text>')

    for i, k in enumerate(sorted(series)):
        color = COLORS[i % len(COLORS)]
        points = series[k]
        svg.append(f'<path d="{line_path(points, x_map, y_map)}" fill="none" stroke="{color}" stroke-width="2.2"/>')
        for x, y in points:
            svg.append(f'<circle cx="{x_map(x):.2f}" cy="{y_map(y):.2f}" r="2.6" fill="{color}"/>')

    legend_x = left + plot_w + 24
    legend_y = top + 8
    svg.append(f'<text x="{legend_x}" y="{legend_y}" font-family="Arial, sans-serif" font-size="13" font-weight="700">k</text>')
    for i, k in enumerate(sorted(series)):
        color = COLORS[i % len(COLORS)]
        y = legend_y + 22 + i * 22
        svg.append(f'<line x1="{legend_x}" y1="{y - 4}" x2="{legend_x + 26}" y2="{y - 4}" stroke="{color}" stroke-width="2.2"/>')
        svg.append(f'<text x="{legend_x + 34}" y="{y}" font-family="Arial, sans-serif" font-size="12">k={k}</text>')

    svg.append("</svg>")
    out_path.write_text("\n".join(svg), encoding="utf-8")


def safe_metric_filename(metric: str, log_y: bool) -> str:
    suffix = "_log" if log_y else ""
    safe = "".join(c if c.isalnum() or c in "-_" else "_" for c in metric)
    return f"{safe}{suffix}.svg"


def write_index(out_dir: Path, files: List[Path], title: str) -> None:
    links = "\n".join(
        f'<section><h2>{html.escape(path.stem)}</h2><img src="{html.escape(path.name)}" alt="{html.escape(path.stem)}"></section>'
        for path in files
    )
    html_text = f"""<!doctype html>
<meta charset="utf-8">
<title>{html.escape(title)}</title>
<style>
body {{ font-family: Arial, sans-serif; margin: 28px; color: #222; }}
section {{ margin: 0 0 36px; }}
img {{ max-width: 100%; border: 1px solid #ddd; }}
</style>
<h1>{html.escape(title)}</h1>
{links}
"""
    (out_dir / "index.html").write_text(html_text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--title-prefix", default="Chapter 7 derivative size")
    parser.add_argument("--log-y", action="store_true")
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    by_metric = load_rows(args.csv)
    written: List[Path] = []
    for metric, series in by_metric.items():
        out = args.out_dir / safe_metric_filename(metric, args.log_y)
        render_svg(metric, series, out, args.title_prefix, args.log_y)
        written.append(out)
    write_index(args.out_dir, written, args.title_prefix)
    for path in written:
        print(path)
    print(args.out_dir / "index.html")


if __name__ == "__main__":
    main()

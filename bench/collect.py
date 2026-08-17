#!/usr/bin/env python3
"""Fold one bench/run.sh output directory into index.json, MANIFEST.json, AGENT.md.

Usage: collect.py <results-dir>

Idempotent — run.sh calls it after every bench target so a spot interruption
still leaves a readable directory.
"""

import json
import re
import sys
from pathlib import Path

NUM = re.compile(r"[\d,]+")


def read(p: Path) -> str:
    try:
        return p.read_text(errors="replace")
    except OSError:
        return ""


def load(p: Path):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


def num(s: str):
    m = NUM.search(s)
    return int(m.group().replace(",", "")) if m else None


# --------------------------------------------------------------- criterion
def criterion_rows(out: Path) -> list[dict]:
    """Every measured benchmark, flattened. This is the core agent affordance."""
    rows = []
    for est_path in sorted(out.glob("criterion/*/**/new/estimates.json")):
        est = load(est_path)
        meta = load(est_path.parent / "benchmark.json") or {}
        if not est:
            continue
        tag = est_path.relative_to(out / "criterion").parts[0]
        crate, _, bench = tag.partition("__")
        mean = est.get("mean", {})
        ci = mean.get("confidence_interval", {})
        thr = meta.get("throughput") or {}
        thr_unit, thr_val = next(iter(thr.items()), (None, None))
        point = mean.get("point_estimate")
        row = {
            "crate": crate,
            "bench_target": bench,
            "id": meta.get("full_id") or str(est_path.parent.parent),
            "group": meta.get("group_id"),
            "function": meta.get("function_id"),
            "param": meta.get("value_str"),
            "mean_ns": point,
            "median_ns": est.get("median", {}).get("point_estimate"),
            "std_dev_ns": est.get("std_dev", {}).get("point_estimate"),
            "mad_ns": est.get("median_abs_dev", {}).get("point_estimate"),
            "ci95_lo_ns": ci.get("lower_bound"),
            "ci95_hi_ns": ci.get("upper_bound"),
            "throughput_unit": thr_unit,
            "throughput_value": thr_val,
            "dir": str(est_path.parent.relative_to(out)),
        }
        if point and thr_val:
            row["ns_per_unit"] = point / thr_val
            row["units_per_sec"] = thr_val / (point / 1e9)
        if point and est.get("std_dev", {}).get("point_estimate"):
            row["noise_pct"] = 100 * est["std_dev"]["point_estimate"] / point
        rows.append(row)
    return rows


# ------------------------------------------------------------------ tools
def perf_counters(p: Path) -> dict:
    """`perf stat` text -> {event: count | '<not supported>'}."""
    counters = {}
    for line in read(p).splitlines():
        m = re.match(r"\s*([\d,.]+|<not \w+>)\s+([\w\-./:]+)", line)
        if m and not line.lstrip().startswith("#"):
            v = m.group(1)
            counters[m.group(2)] = num(v) if v[0].isdigit() else v
    c, i = counters.get("cycles"), counters.get("instructions")
    if isinstance(c, int) and isinstance(i, int) and c:
        counters["ipc"] = round(i / c, 3)
    return counters


def summary_lines(p: Path, keys: tuple) -> dict:
    """Pull `==pid== Label: 1,234 ...` lines out of a valgrind stderr log."""
    got = {}
    for line in read(p).splitlines():
        line = re.sub(r"^==\d+==\s*", "", line)
        for k in keys:
            if line.startswith(k):
                got[k.rstrip(":")] = line[len(k):].strip()
    return got


CALLGRIND_KEYS = ("I   refs:", "I1  misses:", "LLi misses:", "D   refs:",
                  "D1  misses:", "LLd misses:", "LL refs:", "LL misses:",
                  "Branches:", "Mispredicts:")
DHAT_KEYS = ("Total:", "At t-gmax:", "At t-end:", "Reads:", "Writes:")


# -------------------------------------------------------------------- env
def env_facts(out: Path) -> dict:
    lscpu = read(out / "env/lscpu.txt")

    def field(name):
        m = re.search(rf"^{name}:\s*(.+)$", lscpu, re.M)
        return m.group(1).strip() if m else None

    tuning = dict(
        re.findall(r"^(\S+) = (.+)$", read(out / "env/tuning.txt"), re.M)
    )
    feats = sorted(set(re.findall(r'target_feature="([^"]+)"',
                                  read(out / "env/target-features.txt"))))
    return {
        "host": read(out / "env/uname.txt").strip().split("\n")[0],
        "cpu": field("Model name"),
        "cpus": field(r"CPU\(s\)"),
        "threads_per_core": field(r"Thread\(s\) per core"),
        "numa_nodes": field(r"NUMA node\(s\)"),
        "l3_cache": field("L3 cache"),
        "rustc": read(out / "env/rustc.txt").strip().split("\n")[0],
        "run": dict(re.findall(r"^(\w+)=(.*)$", read(out / "env/run.txt"), re.M)),
        "tuning": tuning,
        "target_features": feats,
        "write_cache": {k: v for k, v in tuning.items() if "write_cache" in k},
    }


# ------------------------------------------------------------------- main
def main(out: Path) -> None:
    steps = [l.split("\t") for l in read(out / "status.tsv").splitlines() if l]
    rows = criterion_rows(out)
    env = env_facts(out)

    targets: dict[str, dict] = {}
    for s in steps:
        tag, phase, status = s[0], s[1], s[2]
        t = targets.setdefault(tag, {"steps": {}})
        t["steps"][phase] = {"status": status, "seconds": int(s[3] or 0),
                             "note": s[4] if len(s) > 4 else ""}

    for tag, t in targets.items():
        t["benchmarks"] = sum(1 for r in rows if f'{r["crate"]}__{r["bench_target"]}' == tag)
        stat = out / f"perf/{tag}/stat.txt"
        if stat.exists():
            t["perf"] = perf_counters(stat)
        cg = out / f"valgrind/{tag}/callgrind.log"
        if cg.exists():
            t["callgrind"] = summary_lines(cg, CALLGRIND_KEYS)
        dh = out / f"valgrind/{tag}/dhat.log"
        if dh.exists():
            t["dhat"] = summary_lines(dh, DHAT_KEYS)

    caveats = []
    for tag, t in targets.items():
        for phase, s in t["steps"].items():
            # "absent" = the knob does not exist on this platform, not a problem.
            if s["status"] not in ("ok", "absent"):
                caveats.append(f"`{tag}` / **{phase}**: {s['status']}"
                               + (f" — {s['note']}" if s["note"] else ""))
    if any("back" in v for v in env["write_cache"].values()):
        caveats.append("A block device reports `write_cache = write back`: fsync "
                       "may be landing in a volatile cache, so chainfold and "
                       "rotortree durability numbers are optimistic. See "
                       "`env/tuning.txt`.")
    gov = env["tuning"].get("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
    if env["cpu"] and gov != "performance":  # env["cpu"] set => lscpu ran => Linux
        caveats.append(f"CPU governor is `{gov}`, not `performance` — expect "
                       "frequency drift between samples.")

    manifest = {"env": env, "targets": targets, "caveats": caveats,
                "benchmark_count": len(rows)}
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (out / "index.json").write_text(json.dumps(rows, indent=2) + "\n")
    (out / "AGENT.md").write_text(agent_md(out, manifest, rows))
    print(f"{len(rows)} benchmarks, {len(targets)} targets -> {out}")


def agent_md(out: Path, m: dict, rows: list[dict]) -> str:
    e = m["env"]
    slowest = sorted((r for r in rows if r.get("mean_ns")),
                     key=lambda r: -r["mean_ns"])[:15]
    noisiest = sorted((r for r in rows if r.get("noise_pct")),
                      key=lambda r: -r["noise_pct"])[:10]

    def table(rs, extra, extra_key):
        out_ = [f"| id | mean | {extra} |", "|---|---:|---:|"]
        for r in rs:
            out_.append(f'| `{r["id"]}` | {r["mean_ns"] / 1e3:,.1f} µs | {extra_key(r)} |')
        return "\n".join(out_)

    return f"""# Benchmark results — read this first

Produced by `bench/run.sh`. Everything here is machine-readable; nothing needs
a browser.

- **CPU** {e['cpu']} ({e['cpus']} logical, {e['threads_per_core']} thread/core, L3 {e['l3_cache']}, NUMA {e['numa_nodes']})
- **Host** `{e['host']}`
- **Toolchain** `{e['rustc']}`, `RUSTFLAGS={e['run'].get('RUSTFLAGS', '')}`, profile `{e['run'].get('CARGO_PROFILE', '')}` (release + debug symbols)
- **Commit** `{e['run'].get('git', '?')}` · **UTC** `{e['run'].get('date_utc', '?')}`
- **{m['benchmark_count']} benchmarks** across {len(m['targets'])} bench targets

## Files

| path | what it is |
|---|---|
| `index.json` | **Start here.** Every benchmark flattened: `crate`, `bench_target`, `id`, `mean_ns`, `median_ns`, `std_dev_ns`, `ci95_*`, `throughput_*`, `ns_per_unit`, `noise_pct`. |
| `MANIFEST.json` | Environment, per-target step status, perf counters, callgrind and DHAT summaries, caveats. |
| `criterion/<crate>__<bench>/` | Raw criterion tree. `*/new/sample.json` has the individual `(iters, time)` pairs if you need the distribution. |
| `perf/<crate>__<bench>/stat.txt` | Hardware counters over the iteration loop only. |
| `perf/<crate>__<bench>/flat.txt` | Flat symbol profile — self time per symbol. The fastest read for "where does the time go". |
| `perf/<crate>__<bench>/callers.txt` | Same profile with call graphs (dwarf unwind). |
| `perf/<crate>__<bench>/annotate.txt` | Source-line and instruction level attribution. |
| `perf/<crate>__<bench>/perf.data` | Raw; re-query with `perf report -i ...`. |
| `valgrind/<crate>__<bench>/callgrind.txt` | Exact instruction, cache and branch-miss counts per function. Deterministic — no PMU needed, unaffected by frequency scaling. |
| `valgrind/<crate>__<bench>/dhat.json` | Full allocation profile: every allocation site, block counts, sizes, lifetimes, read/write access counts. Load in the DHAT viewer or parse directly. |
| `env/` | Raw machine capture: `lscpu`, `/proc/cmdline`, `tuning.txt` (governor, turbo, THP, write_cache), `target-features.txt`. |
| `status.tsv` | `tag, phase, status, seconds, log` for every step. |

## How to read the numbers

- `mean_ns` is per **iteration**, and one iteration is whatever the bench body
  does — often a whole batch. Divide by `throughput_value` (`ns_per_unit`) for
  per-element cost.
- `noise_pct` = std-dev over mean. Above ~5% treat a comparison as inconclusive.
- perf counters cover the `--profile-time` run (iteration loop only, criterion's
  statistics excluded), and aggregate **all** benchmarks in that target unless a
  filter was set — use them for target-level ratios (IPC, miss rates), not to
  attribute cost to one benchmark.
- callgrind numbers are simulated, exact and repeatable; perf numbers are
  sampled, real and noisy. When they disagree, callgrind is right about *counts*
  and perf is right about *time*.

## Caveats
{chr(10).join('- ' + c for c in m['caveats']) or '- none recorded.'}

## Slowest benchmarks
{table(slowest, "throughput", lambda r: f'{r["units_per_sec"]:,.0f} {r["throughput_unit"]}/s' if r.get("units_per_sec") else "—")}

## Noisiest benchmarks (treat comparisons here with suspicion)
{table(noisiest, "noise", lambda r: f'{r["noise_pct"]:.1f}%')}

## Drilling down

The bench binaries are still on disk; `build/<tag>.path` has each path. The
feature flags matter — several benches have `#[cfg(feature = ...)]` arms that
are *not* in their `required-features`, so rebuild through `bench/run.sh`
rather than a bare `cargo bench`.

```sh
cd {out}          # paths below are relative to this results directory
BIN=$(cat build/sealring__scan.path)

# one benchmark, hardware counters
perf stat -e cycles,instructions,cache-misses -- "$BIN" --bench --profile-time 10 'adapter=k256'

# one benchmark, exact instruction counts per function
valgrind --tool=callgrind --cache-sim=yes --callgrind-out-file=/tmp/cg.out -- \\
    "$BIN" --bench --profile-time 1 'adapter=k256'
callgrind_annotate /tmp/cg.out | head -60

# re-time one benchmark against this run as the baseline
CRITERION_HOME=criterion/sealring__scan "$BIN" --bench --baseline new 'adapter=k256'
```

If a valgrind step failed on `binius-mayo`, the usual cause is AVX-512:
valgrind cannot execute some of those instructions and the build targets
`-C target-cpu=native` by necessity (binius64 has no runtime dispatch). Use
perf there instead.
"""


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: collect.py <results-dir>")
    main(Path(sys.argv[1]))

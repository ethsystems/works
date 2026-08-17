#!/usr/bin/env bash
# One-command benchmark + profile sweep for the `works` crates.
#
#   ./bench/run.sh                     # every crate
#   ./bench/run.sh sealring rotortree  # a subset (also: bench-target names)
#   ./bench/run.sh --quick             # short criterion runs, smoke the pipeline
#   ./bench/run.sh --precondition      # sequential NVMe write pass first
#
# Env knobs:
#   OUT_DIR=...          results root            (default bench-results/)
#   BENCH_ARGS="..."     extra criterion args    (e.g. --measurement-time 20)
#   PROFILE_TIME=5       seconds per bench under perf
#   VG_PROFILE_TIME=1    seconds per bench under valgrind
#   VG_TIMEOUT=1800      per-tool valgrind wall clock cap
#   TMPDIR=/mnt/nvme     where storage benches put their temp files
#   SKIP_PERF=1 SKIP_VALGRIND=1 SKIP_PREP=1
#
# Needs: cargo, python3. Optional: perf, valgrind — each missing tool degrades
# to a recorded "skipped", never a failure. Prep needs passwordless sudo; every
# prep step is best-effort and recorded in MANIFEST.json.
#
# Results land in one self-describing directory; read its AGENT.md first.
set -uo pipefail

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$REPO" || exit 1

# crate|bench target|features|kind|profiling filter
# Features are pinned here on purpose: several benches carry #[cfg(feature)]
# arms that are NOT in their required-features, so a plain `cargo bench`
# silently compiles them out (this already happened once with sealring's
# `parallel` arm). Keep this table in sync with the bench sources.
TARGETS='
binius-mayo|prove_verify||cpu|
chainfold|apply|std,test-helpers|cpu|
chainfold|snapshot|std,wincode,test-helpers|cpu|
rotortree|tree_bench|blake3|cpu|
rotortree|tree_bench_concurrent|concurrent,blake3|cpu|
rotortree|tree_bench_parallel|parallel,blake3|cpu|
rotortree|tree_bench_all|concurrent,parallel,blake3|cpu|
rotortree|tree_bench_storage|storage,parallel,blake3|io|
sealring|scan|x25519,k256,grumpkin,test-helpers,std,parallel|cpu|
sealring|seal|x25519,k256,grumpkin,test-helpers,std,parallel|cpu|
sealring|micro|x25519,k256,grumpkin,test-helpers,std,parallel|cpu|
'

PROFILE_TIME=${PROFILE_TIME:-5}
VG_PROFILE_TIME=${VG_PROFILE_TIME:-1}
VG_TIMEOUT=${VG_TIMEOUT:-1800}
BENCH_ARGS=${BENCH_ARGS:-}
PRECONDITION=
SELECT=()

while [ $# -gt 0 ]; do
    case $1 in
    --quick) BENCH_ARGS="$BENCH_ARGS --quick" ;;
    --precondition) PRECONDITION=1 ;;
    --no-prep) SKIP_PREP=1 ;;
    -h | --help)
        sed -n '2,25p' "$0"
        exit 0
        ;;
    -*)
        echo "unknown flag: $1" >&2
        exit 2
        ;;
    *) SELECT+=("$1") ;;
    esac
    shift
done

SHA=$(git rev-parse --short HEAD 2>/dev/null || echo nogit)
git diff --quiet 2>/dev/null || SHA="$SHA-dirty"
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
OUT="${OUT_DIR:-$REPO/bench-results}/$STAMP-$(hostname -s)-$SHA"
mkdir -p "$OUT"/{env,build,bench,criterion,perf,valgrind} || exit 1
: >"$OUT/status.tsv"

# Required by binius64 (no runtime CPU dispatch — the build machine's ISA picks
# which code compiles) and free elsewhere.
export RUSTFLAGS="${RUSTFLAGS:-} -C target-cpu=native"
# release + debug=true: same codegen as `bench`, but perf and valgrind get symbols.
CARGO_PROFILE=profiling

note() { printf '\033[1;34m==>\033[0m %s\n' "$*"; }

# tag, phase, status, seconds, note -> status.tsv (folded into MANIFEST.json)
record() { printf '%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "${4:-0}" "${5:-}" >>"$OUT/status.tsv"; }

# run_step <tag> <phase> <logfile> <cmd...>
run_step() {
    local tag=$1 phase=$2 log=$3 t0=$SECONDS st
    shift 3
    if "$@" >"$log" 2>&1; then st=ok; else st="fail:$?"; fi
    record "$tag" "$phase" "$st" "$((SECONDS - t0))" "${log#"$OUT"/}"
    [ "$st" = ok ]
}

cap() { # cap <file> <cmd...>  — capture environment, never fatal
    "${@:2}" >"$OUT/env/$1" 2>&1 || echo "(unavailable: ${*:2})" >>"$OUT/env/$1"
}

# ---------------------------------------------------------------- environment
note "capturing environment -> $OUT/env"
cap uname.txt uname -a
cap lscpu.txt lscpu
cap cpuinfo.txt cat /proc/cpuinfo
cap meminfo.txt cat /proc/meminfo
cap cmdline.txt cat /proc/cmdline
cap numa.txt numactl --hardware
cap rustc.txt rustc -vV
cap cargo.txt cargo -V
cap toolchain.txt cat rust-toolchain.toml
cap perf-version.txt perf --version
cap valgrind-version.txt valgrind --version
cap df.txt df -h
cap mounts.txt findmnt -no SOURCE,TARGET,FSTYPE,OPTIONS
cap nvme.txt nvme list
cap blockdev.txt lsblk -o NAME,MODEL,SIZE,ROTA,SCHED,MOUNTPOINT
cap sysctl.txt sysctl -a
cap dmidecode.txt sudo -n dmidecode -t processor -t memory

{
    echo "RUSTFLAGS=$RUSTFLAGS"
    echo "CARGO_PROFILE=$CARGO_PROFILE"
    echo "BENCH_ARGS=$BENCH_ARGS"
    echo "TMPDIR=${TMPDIR:-/tmp}"
    echo "git=$SHA"
    echo "date_utc=$STAMP"
} >"$OUT/env/run.txt"

# The memory's open question: "write back" here means fsync may be landing in a
# volatile cache and chainfold/rotortree durability numbers are optimistic.
{
    for q in /sys/block/*/queue/write_cache; do
        [ -r "$q" ] && echo "$q = $(cat "$q")"
    done
    for f in /sys/kernel/mm/transparent_hugepage/enabled \
        /sys/kernel/mm/transparent_hugepage/defrag \
        /sys/devices/system/cpu/intel_pstate/no_turbo \
        /sys/devices/system/cpu/cpufreq/boost \
        /proc/sys/kernel/randomize_va_space \
        /proc/sys/kernel/perf_event_paranoid \
        /proc/sys/kernel/nmi_watchdog \
        /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor; do
        [ -r "$f" ] && echo "$f = $(cat "$f")"
    done
} >"$OUT/env/tuning.txt" 2>&1

# ISA gate: binius64 has no runtime dispatch, so a box without these compiles a
# scalar fallback and benchmarks a lie.
rustc --print cfg -C target-cpu=native >"$OUT/env/target-features.txt" 2>&1
BINIUS_OK=1
if grep -q 'target_arch="x86_64"' "$OUT/env/target-features.txt"; then
    for feat in vpclmulqdq gfni avx512f; do
        grep -q "target_feature=\"$feat\"" "$OUT/env/target-features.txt" || {
            BINIUS_OK=
            record binius-mayo isa-gate "fail:missing $feat" 0 env/target-features.txt
        }
    done
fi

# ------------------------------------------------------------------- machine prep
if [ -z "${SKIP_PREP:-}" ]; then
    note "machine prep (best-effort, needs passwordless sudo)"
    prep() { # prep <name> <value> <path-glob>
        local n=$1 v=$2 p=$3 ok=absent f
        for f in $p; do
            [ -e "$f" ] || continue
            if { echo "$v" >"$f"; } 2>/dev/null ||
                sudo -n tee "$f" <<<"$v" >/dev/null 2>&1; then
                [ "$ok" = absent ] && ok=ok
            else
                ok=fail
            fi
        done
        record machine "prep:$n" "$ok" 0 "wanted $v"
    }
    prep governor performance '/sys/devices/system/cpu/cpu*/cpufreq/scaling_governor'
    prep no_turbo 1 /sys/devices/system/cpu/intel_pstate/no_turbo
    prep amd_boost 0 /sys/devices/system/cpu/cpufreq/boost
    prep perf_paranoid -1 /proc/sys/kernel/perf_event_paranoid
    prep nmi_watchdog 0 /proc/sys/kernel/nmi_watchdog
    # THP is recorded, never changed: flipping it moves numbers in ways that are
    # hard to attribute afterwards.
fi

if [ -n "$PRECONDITION" ]; then
    note "preconditioning ${TMPDIR:-/tmp} (first-write penalty pass)"
    t0=$SECONDS
    dd if=/dev/zero of="${TMPDIR:-/tmp}/.precondition" bs=1M count=32768 \
        oflag=direct status=none 2>"$OUT/env/precondition.txt" &&
        st=ok || st=fail
    rm -f "${TMPDIR:-/tmp}/.precondition"
    record machine precondition "$st" "$((SECONDS - t0))" env/precondition.txt
fi

# ------------------------------------------------------------------- perf probe
PERF_EVENTS=
if [ -z "${SKIP_PERF:-}" ] && command -v perf >/dev/null; then
    for ev in \
        "task-clock,context-switches,cpu-migrations,page-faults,cycles,instructions,branches,branch-misses,cache-references,cache-misses,stalled-cycles-frontend,stalled-cycles-backend,L1-dcache-loads,L1-dcache-load-misses,LLC-loads,LLC-load-misses,dTLB-loads,dTLB-load-misses" \
        "task-clock,context-switches,page-faults,cycles,instructions,branches,branch-misses,cache-references,cache-misses" \
        "task-clock,context-switches,cpu-migrations,page-faults"; do
        if perf stat -e "$ev" -- true >/dev/null 2>&1; then
            PERF_EVENTS=$ev
            break
        fi
    done
fi
case "$PERF_EVENTS" in
"") record machine perf-events skipped 0 "$([ -n "${SKIP_PERF:-}" ] && echo 'disabled via SKIP_PERF' || echo 'perf missing or no usable PMU')" ;;
*cycles*) record machine perf-events ok 0 "$PERF_EVENTS" ;;
*) record machine perf-events degraded 0 "software events only — no hardware PMU (expected on virtualised EC2); use valgrind/callgrind for cache and branch numbers" ;;
esac

# ------------------------------------------------------------------------- run
# Accepts a crate name, a bench-target name, or the combined `crate__bench` tag.
selected() {
    [ ${#SELECT[@]} -eq 0 ] && return 0
    local s
    for s in "${SELECT[@]}"; do
        case $s in "$1" | "$2" | "${1}__${2}") return 0 ;; esac
    done
    return 1
}

while IFS='|' read -r crate bench features kind filter; do
    [ -n "$crate" ] || continue
    selected "$crate" "$bench" || continue
    tag="${crate}__${bench}"
    if [ "$crate" = binius-mayo ] && [ -z "$BINIUS_OK" ]; then
        note "SKIP $tag — CPU lacks the ISA binius64 compiles against"
        record "$tag" all skipped 0 "isa-gate failed; benchmarking a scalar fallback would be meaningless"
        continue
    fi

    # Scalar, not an array: bash 3.2 (macOS) treats "${arr[@]}" of an empty
    # array as unbound under `set -u` and kills the script. Feature lists never
    # contain spaces, so unquoted word splitting is enough — same as $filter.
    feat_args=
    [ -n "$features" ] && feat_args="--features $features"

    note "build $tag [${features:-default}]"
    if ! run_step "$tag" build "$OUT/build/$tag.json" \
        cargo bench -p "$crate" --bench "$bench" $feat_args \
        --profile "$CARGO_PROFILE" --no-run --message-format=json; then
        continue
    fi
    BIN=$(python3 - "$OUT/build/$tag.json" "$bench" <<'PY'
import json, sys
want = sys.argv[2]
hit = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    t = m.get("target") or {}
    if m.get("executable") and "bench" in (t.get("kind") or []) and t.get("name") == want:
        hit = m["executable"]
print(hit or "")
PY
    )
    [ -n "$BIN" ] || {
        record "$tag" locate-binary fail 0 "build/$tag.json"
        continue
    }
    echo "$BIN" >"$OUT/build/$tag.path"

    # Storage benches: start from a cold page cache so the numbers include real IO.
    if [ "$kind" = io ]; then
        sync
        sudo -n tee /proc/sys/vm/drop_caches <<<3 >/dev/null 2>&1 &&
            record "$tag" drop-caches ok || record "$tag" drop-caches fail 0 "page cache still warm — IO numbers are optimistic"
    fi

    # --- timing: the numbers of record. Own CRITERION_HOME per target, because
    # rotortree reuses group ids (insert_single/n2 ...) across bench targets and
    # a shared directory would let them overwrite each other.
    note "bench $tag"
    CRITERION_HOME="$OUT/criterion/$tag" run_step "$tag" criterion "$OUT/bench/$tag.log" \
        "$BIN" --bench --noplot $BENCH_ARGS

    # --- perf: --profile-time runs the iteration loop only, no criterion
    # statistics, so the profile is the workload and nothing else.
    if [ -n "$PERF_EVENTS" ]; then
        mkdir -p "$OUT/perf/$tag"
        note "perf $tag"
        run_step "$tag" perf-stat "$OUT/perf/$tag/stat.txt" \
            perf stat -e "$PERF_EVENTS" -- \
            "$BIN" --bench --profile-time "$PROFILE_TIME" $filter
        if run_step "$tag" perf-record "$OUT/perf/$tag/record.log" \
            perf record -q -F 499 --call-graph dwarf,8192 -o "$OUT/perf/$tag/perf.data" -- \
            "$BIN" --bench --profile-time "$PROFILE_TIME" $filter; then
            perf report -i "$OUT/perf/$tag/perf.data" --stdio --no-children -g none \
                --percent-limit 0.05 >"$OUT/perf/$tag/flat.txt" 2>/dev/null
            perf report -i "$OUT/perf/$tag/perf.data" --stdio --no-children \
                -g graph,0.5,caller --percent-limit 0.5 >"$OUT/perf/$tag/callers.txt" 2>/dev/null
            perf annotate -i "$OUT/perf/$tag/perf.data" --stdio -l --percent-limit 1 \
                >"$OUT/perf/$tag/annotate.txt" 2>/dev/null
        fi
    else
        record "$tag" perf skipped
    fi

    # --- valgrind: exact instruction/cache/branch counts (no PMU needed) and a
    # full allocation profile. 30-100x slower, hence the tiny profile-time.
    if [ -z "${SKIP_VALGRIND:-}" ] && command -v valgrind >/dev/null; then
        mkdir -p "$OUT/valgrind/$tag"
        note "valgrind $tag"
        if run_step "$tag" callgrind "$OUT/valgrind/$tag/callgrind.log" \
            timeout "$VG_TIMEOUT" valgrind --tool=callgrind --cache-sim=yes --branch-sim=yes \
            --callgrind-out-file="$OUT/valgrind/$tag/callgrind.out" -- \
            "$BIN" --bench --profile-time "$VG_PROFILE_TIME" $filter; then
            callgrind_annotate --auto=no "$OUT/valgrind/$tag/callgrind.out" \
                >"$OUT/valgrind/$tag/callgrind.txt" 2>&1
        fi
        run_step "$tag" dhat "$OUT/valgrind/$tag/dhat.log" \
            timeout "$VG_TIMEOUT" valgrind --tool=dhat \
            --dhat-out-file="$OUT/valgrind/$tag/dhat.json" -- \
            "$BIN" --bench --profile-time "$VG_PROFILE_TIME" $filter
    else
        record "$tag" valgrind skipped 0 "$([ -n "${SKIP_VALGRIND:-}" ] && echo 'disabled via SKIP_VALGRIND' || echo 'valgrind not installed')"
    fi

    # Collate after every target: on a spot box an interruption then costs one
    # crate, not the whole sweep.
    python3 "$REPO/bench/collect.py" "$OUT" >/dev/null 2>&1
done <<<"$TARGETS"

note "collating"
python3 "$REPO/bench/collect.py" "$OUT" || exit 1
note "done -> $OUT"
echo "   start here: $OUT/AGENT.md"

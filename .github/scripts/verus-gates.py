#!/usr/bin/env python3
"""Static gates for a crate verified in place with Verus attribute mode.

Usage: verus-gates.py <crate-dir>
       verus-gates.py --results <crate-dir> <verus-stdout>
       verus-gates.py --no-cheating <crate-dir> <verus-stderr>
       verus-gates.py --update <crate-dir> [<verus-stdout>]
       verus-gates.py --features <crate-dir>
       verus-gates.py --self-test

(a) No trusted construct outside src/verus/tcb.rs. Two independent checks:
    regexes over the sources, and `--no-cheating`, which reads the errors of a
    Verus run with that flag. Verus names there every assume, admit,
    external_body and assume_specification it compiled, whatever macro built
    it; each must be in tcb.rs, an `uninterp` spec fn, or the wrapper Verus
    makes for a fn with ghost args. The flag ignores `#[verifier::external]`;
    `--results` catches that as a fn that no longer verifies. Nothing that
    hides code from the regexes either: `#[path]`, `include!`, `macro_rules!`,
    a build script, a nightly feature not on FEATURES, or in in-scope code a
    macro, attribute or derive from a crate not on MACRO_CRATES (`paste`
    builds identifiers), a glob import from another crate, or a `use` or
    `extern crate` that binds a trusted macro or crate name to something else.
(b) Every `src/**/*.rs` is in scope, out of scope, or tcb.rs. Every fn in an
    in-scope file carries a verifying attribute, or sits in an impl/trait
    marked `verus_verify`, or is listed as out of scope. Attribute mode
    silently treats an unannotated fn as external (unverified). Attributes are
    read the way rustc applies them in the Verus run (VERUS_CFG, derived from
    [features] and the config's `features`), so a fn that cfg drops from the
    Verus build, or that has a second body for another cfg, counts as
    unverified. Specs do not cover bodies, so in a body
    `cfg(verus_keep_ghost)` may gate only `proof!`, `proof_decl!` or
    `proof_with!`, `cfg_attr(verus_keep_ghost, ..)` may only add a Verus
    annotation, and no other cfg, no `cfg!` and no cfg in a `verus!` block is
    allowed. An out-of-scope file uses no Verus at all. Every trait an
    in-scope file declares is on `trusted-traits`, since its spec is assumed
    for every unverified impl.
(c) The crate's `verus-manifest.txt` matches the sources: the tcb.rs items,
    the name of every entry of every dependency table (target, build and dev
    ones too), and a hash of every spec (each `verus_spec`, the signature and
    contract of each fn in a `verus!` block, each spec fn body),
    and the gate config: every [features] entry, the Verus run's cfgs, the
    scope lists and trusted-traits. `--results` checks a Verus run against the
    same file: the verified count and the exact set of fns Verus verified.

Config lives in the crate's Cargo.toml:

    [package.metadata.verus-gates]
    in-scope = ["src/ring.rs"]
    out-of-scope-files = { "src/storage.rs" = "why" }
    trusted-traits = ["Fold"]
    features = ["verus"]  # of the Verus run; `--features` prints them for CI
    out-of-scope = { "src/ring.rs::BlockRing::push" = "why" }

Test code (items under an exact `#[cfg(test)]`) and `verus! { ... }` blocks
are skipped by (b).

To update the manifest after a change to specs, tcb.rs, dependencies or the
verified fns, run from the workspace root with the pinned Verus on PATH:

    cargo clean -p chainfold
    cargo verus verify -p chainfold --check-toolchain \\
        --features "$(python3 .github/scripts/verus-gates.py --features crates/chainfold)" \\
        --fwd-verus-args-to roots -- --output-json --time-expanded > verus.out
    python3 .github/scripts/verus-gates.py --update crates/chainfold verus.out

Without the Verus output, `--update` refreshes only the lines the sources fix.
Review the manifest diff: each line names the item that changed.
"""

import hashlib
import json
import re
import sys
import tempfile
import tomllib
from pathlib import Path

TCB = Path("src/verus/tcb.rs")
MANIFEST = "verus-manifest.txt"
# Regexes, whitespace-tolerant: Verus accepts `assume (x)`, `vstd::prelude::assume_(x)`,
# `admit ()` and the old `#[verifier(external)]` form, and each proves `false` unchecked.
TRUSTED = [
    r"\bassume\w*",  # assume(, assume_(, assume_new, assume_specification, assume_termination
    r"\badmit\w*",
    r"\bexternal\w*",  # external_body, verifier::external, verifier(external), external_*_specification
    r"\bexec_allows_no_decreases_clause\b",
    r"\baxiom\s+fn\b",
    # A hand-written cmp/eq spec impl over a derived (unverified) impl is an assumption.
    r"SpecImpl\s+for\b",
]
# Code these regexes would never read: another file, or tokens a macro builds.
OPAQUE = [
    r"#\s*!?\s*\[[^\]]*\bpath\s*=",
    r"\binclude\s*!",
    r"\bmacro_rules\b",
    r"\bconcat_idents\b",
]
# The crates in-scope code may take macros, attributes and derives from. A macro from any
# other crate (`paste`) can build tokens, `assume` among them, that these regexes never see.
MACRO_CRATES = {"std", "core", "alloc", "vstd", "verifier", "rustfmt", "clippy", "serde", "wincode", "include_utils"}
MACROS = {
    *("assert", "assert_eq", "assert_ne", "debug_assert", "debug_assert_eq", "debug_assert_ne"),
    *("format", "matches", "panic", "unreachable", "vec", "write", "writeln"),
    *("verus", "proof", "proof_decl", "proof_with", "seq"),
}
ATTRS = {
    *("cfg", "cfg_attr", "cfg_eval", "derive", "doc", "allow", "warn", "deny", "forbid", "expect", "feature"),
    *("inline", "cold", "must_use", "repr", "non_exhaustive", "track_caller", "test", "no_std", "deprecated"),
    *("trigger", "verus_spec", "verus_verify", "serde", "wincode"),
}
DERIVES = {"Clone", "Copy", "Debug", "Default", "Eq", "Hash", "Ord", "PartialEq", "PartialOrd", "StructuralEq"}
# Words a `!` can follow that are not macro names: `if !(x)`, `ensures !(x)`.
NOT_MACROS = {"if", "while", "match", "return", "in", "else", "break", "let", "mut", "move", "yield"}
NOT_MACROS |= {"requires", "ensures", "invariant", "decreases", "recommends", "returns", "when", "via"}
FEATURES = {"proc_macro_hygiene", "cfg_eval", "allocator_api", "doc_cfg"}
# The cfgs of the Verus run, `cargo verus verify --features <the crate's `features` list>`.
# `load` derives them from the crate's [features].
VERUS_CFG = {"verus_keep_ghost", "verus_keep_ghost_body"}
VERIFYING = ("verus_spec", "verus_verify")
USE = re.compile(r"\s*(pub(\s*\([^)]*\))?\s+)?use\b")
# What a `verus!` item can start with; a `}` followed by one of these ends the item.
ITEM_START = re.compile(
    r"#|\}|(pub|fn|proof|spec|open|closed|exec|uninterp|broadcast|impl|struct|enum|trait|use"
    r"|mod|const|static|type|axiom|tracked|global|layout|unsafe|assume_specification)\b"
)


def strip(src: str, strings: bool = True) -> str:
    """Blank out comments and, if `strings`, string/char literals, keeping offsets and newlines."""
    out = list(src)
    i, n = 0, len(src)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif m := re.compile(r'b?r(#*)"').match(src, i):
            end = src.find('"' + m.group(1), m.end())
            j = n if end < 0 else end + 1 + len(m.group(1))
            if strings:
                blank(i, j)
            i = j
        elif src[i] == '"' or src.startswith('b"', i):
            j = i + (2 if src[i] == "b" else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if strings:
                blank(i, j + 1)
            i = j + 1
        elif m := re.compile(r"b?'(\\.[^']*|[^\\'])'").match(src, i):
            if strings:
                blank(i, m.end())
            i = m.end()
        else:
            i += 1
    return "".join(out)


def line_of(src: str, pos: int) -> int:
    return src.count("\n", 0, pos) + 1


def norm(text: str) -> str:
    return " ".join(text.split())


def digest(text: str) -> str:
    return hashlib.sha256(norm(text).encode()).hexdigest()[:12]


def split_top(s: str) -> list[str]:
    """Splits on commas outside any bracket."""
    parts, depth, start = [], 0, 0
    for k, c in enumerate(s):
        depth += {"(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1}.get(c, 0)
        if c == "," and depth == 0:
            parts.append(s[start:k])
            start = k + 1
    parts.append(s[start:])
    return [p.strip() for p in parts if p.strip()]


def cfg_true(pred: str) -> bool:
    """Evaluates a cfg predicate under VERUS_CFG."""
    toks = re.findall(r'\w+\s*=\s*"[^"]*"|\w+|[(),]', pred)
    pos = 0

    def expr() -> bool:
        nonlocal pos
        tok = toks[pos]
        pos += 1
        if tok in ("all", "any", "not") and pos < len(toks) and toks[pos] == "(":
            pos += 1
            args = []
            while toks[pos] != ")":
                args.append(expr())
                if toks[pos] == ",":
                    pos += 1
            pos += 1
            return all(args) if tok == "all" else any(args) if tok == "any" else not args[0]
        return re.sub(r"\s+", "", tok) in VERUS_CFG

    return expr()


def applied(attr: str) -> list[str]:
    """The attributes rustc applies under VERUS_CFG, with `cfg_attr` expanded."""
    m = re.fullmatch(r"cfg_attr\s*\((.*)\)", attr.strip(), re.S)
    if not m:
        return [attr.strip()]
    pred, *rest = split_top(m.group(1))
    return [a for r in rest for a in applied(r)] if cfg_true(pred) else []


def cfg_of(attrs: list[str]) -> bool:
    return all(cfg_true(m.group(1)) for a in attrs if (m := re.fullmatch(r"cfg\s*\((.*)\)", a, re.S)))


def body_attr_ok(attr: str, header: str) -> bool:
    """Whether an attribute inside a fn body leaves the compiled code the same in every build:
    `cfg(verus_keep_ghost)` only on a ghost macro, `cfg_attr` only to add a Verus annotation."""
    attr = attr.strip()
    if re.fullmatch(r"cfg\s*\(\s*verus_keep_ghost\s*\)", attr):
        return bool(re.fullmatch(r"\s*(proof|proof_decl|proof_with)\s*!\s*", header))
    if m := re.fullmatch(r"cfg_attr\s*\((.*)\)", attr, re.S):
        pred, *rest = split_top(m.group(1))
        return norm(pred) == "verus_keep_ghost" and not any(re.match(r"cfg(_attr)?\b", a) for a in rest)
    return not re.match(r"cfg\b", attr)


def macro_uses(src: str) -> list[tuple[int, str, str]]:
    """(offset, path, kind) of every macro call, attribute (with `cfg_attr` expanded) and derive."""
    path = r"(?:::)?\w+(?:\s*::\s*\w+)*"
    found = [
        (m.start(), re.sub(r"\s+", "", m.group(1)), "macro")
        for m in re.finditer(rf"(?<![\w:])({path})\s*!\s*[(\[{{]", src)
        if m.group(1) not in NOT_MACROS
    ]
    for m in re.finditer(r"#\s*!?\s*\[", src):
        depth, j = 1, m.end()
        while j < len(src) and depth:
            depth += {"[": 1, "]": -1}.get(src[j], 0)
            j += 1
        todo = [src[m.end() : j - 1]]
        while todo:
            attr = todo.pop().strip()
            if call := re.fullmatch(r"(cfg_attr|derive)\s*\((.*)\)", attr, re.S):
                args = split_top(call.group(2))
                if call.group(1) == "cfg_attr":
                    todo += args[1:]
                else:
                    found += [(m.start(), re.sub(r"\s+", "", d), "derive") for d in args]
            elif name := re.match(path, attr):
                found.append((m.start(), re.sub(r"\s+", "", name.group(0)), "attr"))
    return found


def macro_ok(path: str, kind: str) -> bool:
    root, *rest = path.removeprefix("::").split("::")
    return root in MACRO_CRATES if rest else path in {"macro": MACROS, "attr": ATTRS, "derive": DERIVES}[kind]


def use_names(text: str, prefix: str = "") -> list[tuple[str, str]]:
    """(path, bound name) of each name a `use` item imports."""
    tree = re.sub(r"\s*(::|,|\{|\})\s*", r"\1", re.sub(r"^(pub(\(.*?\))?\s+)?use\s+", "", text.strip()))
    if tree.endswith("}"):
        head, _, inner = tree.partition("{")
        return [n for part in split_top(inner[:-1]) for n in use_names(part, prefix + head)]
    m = re.fullmatch(r"(.*?)(?:\s+as\s+(\w+))?", tree, re.S)
    full = (prefix + m.group(1)).removesuffix("::self")
    return [(full, m.group(2) or full.split("::")[-1])]


def self_type(impl_rest: str) -> tuple[str, str]:
    """(self type, trait) of an impl header after `impl`."""
    rest = impl_rest.strip()
    if rest.startswith("<"):
        depth = 0
        for k, c in enumerate(rest):
            depth += {"<": 1, ">": -1}.get(c, 0)
            if depth == 0:
                rest = rest[k + 1 :]
                break
    rest = re.sub(r"\bwhere\b.*", "", rest, flags=re.S)
    parts = re.split(r"\bfor\b", rest)
    ty = re.findall(r"(\w+)\s*(?:<.*)?$", parts[-1].strip(), re.S)
    trait = re.findall(r"(\w+)\s*(?:<.*)?$", parts[0].strip(), re.S) if len(parts) > 1 else []
    return (ty[0] if ty else "?"), (trait[0] if trait else "")


def items(src: str, orig: str) -> dict:
    """Walks one file. `src` is stripped; `orig` has only comments stripped (same offsets).

    Returns fns as (qualified name, line, verified, live, spec text), traits, `use` and `mod`
    declarations as (name or text, line, live), `verus!` blocks as [start, end, line, live],
    and the attributes in fn bodies that change code between builds as (text, line).
    `live` means rustc compiles the item under VERUS_CFG.
    """
    out = {"fns": [], "traits": [], "uses": [], "mods": [], "verus": [], "body_cfgs": []}
    # Scope stack entries: (kind, name, verified, live, start). Kinds: item, impl, trait,
    # skip, verus, body (a fn body, or a block in one), block.
    stack = [("item", "", False, True, 0)]
    header_start, attrs = 0, []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("#[", i) or src.startswith("#![", i):
            depth, j = 0, src.index("[", i)
            while j < n:
                depth += {"[": 1, "]": -1}.get(src[j], 0)
                j += 1
                if depth == 0:
                    break
            inner = orig[src.index("[", i) + 1 : j - 1]
            if src[i + 1] == "!":
                # An inner attribute applies to the enclosing scope.
                kind, name, verified, live, start = stack[-1]
                stack[-1] = (kind, name, verified, live and cfg_of(applied(inner)), start)
            else:
                attrs.append(inner)
            i = header_start = j
            continue
        if c in "{};":
            header = src[header_start:i]
            if c == "{" and USE.match(header):
                # A braced import ends at its `;`.
                depth = 0
                while i < n and not (src[i] == ";" and depth == 0):
                    depth += {"{": 1, "}": -1}.get(src[i], 0)
                    i += 1
                c, header = ";", src[header_start:i]
            kind, name, verified, live, _ = stack[-1]
            eff = [a for raw in attrs for a in applied(raw)]
            is_test = any(re.fullmatch(r"cfg\s*\(\s*test\s*\)", raw.strip()) for raw in attrs)
            live = live and cfg_of(eff)
            marked = any(re.match(r"\w+", a) and re.match(r"\w+", a).group(0) in VERIFYING for a in eff)
            spec = " ".join(a for a in eff if a.startswith("verus_spec"))
            fn = re.search(r"\bfn\s+(\w+)", header)
            offset = fn.start() if fn else len(header) - len(header.lstrip())
            line = line_of(src, header_start + offset)
            scanned = kind not in ("skip", "verus") and not is_test
            if kind == "body":
                out["body_cfgs"] += [(norm(raw), line) for raw in attrs if not body_attr_ok(raw, header)]
            if scanned:
                if fn and c in "{;":
                    qual = f"{name}::{fn.group(1)}" if name else fn.group(1)
                    out["fns"].append((qual, line, verified or marked, live, spec))
                elif c == ";" and USE.match(header):
                    out["uses"].append((norm(orig[header_start:i]), line, live))
                elif c == ";" and (m := re.search(r"\bmod\s+(\w+)\s*$", header)):
                    out["mods"].append((m.group(1), line, live))
                elif m := re.search(r"\btrait\s+(\w+)", header):
                    out["traits"].append((m.group(1), line, live))
            if c == "{":
                if not scanned:
                    stack.append(("skip", "", False, live, i))
                elif re.search(r"\bverus\s*!\s*$", header):
                    stack.append(("verus", "", False, live, i))
                    out["verus"].append([i + 1, None, line, live])
                elif fn:
                    stack.append(("body", fn.group(1), False, live, i))
                elif m := re.search(r"\bimpl\b(.*)$", header, re.S):
                    stack.append(("impl", self_type(m.group(1))[0], marked, live, i))
                elif m := re.search(r"\btrait\s+(\w+)", header):
                    stack.append(("trait", m.group(1), marked, live, i))
                elif re.search(r"\bmod\s+\w+\s*$", header):
                    stack.append(("item", "", False, live, i))
                else:
                    stack.append(("body" if kind == "body" else "block", name, False, live, i))
            elif c == "}" and len(stack) > 1:
                if stack[-1][0] == "verus":
                    for block in out["verus"]:
                        if block[0] == stack[-1][4] + 1:
                            block[1] = i
                stack.pop()
            header_start, attrs = i + 1, []
        i += 1
    return out


def verus_items(src: str, orig: str, a: int, b: int, scope: str = "") -> list[tuple[str, str]]:
    """(key, spec text) for each item of a `verus!` block: the whole of a spec fn or a non-fn
    item, and the signature and contract, without the body, of a proof or exec fn."""
    found, i = [], a
    while i < b:
        while i < b and src[i].isspace():
            i += 1
        if i >= b:
            break
        start, depth, last_group = i, 0, None
        while i < b:
            c = src[i]
            if c in "([{":
                if c == "{" and depth == 0:
                    last_group = i
                depth += 1
            elif c in ")]}":
                depth -= 1
                if depth == 0 and c == "}":
                    j = i + 1
                    while j < b and src[j].isspace():
                        j += 1
                    if j >= b or ITEM_START.match(src, j):
                        i += 1
                        break
            elif c == ";" and depth == 0:
                i += 1
                break
            i += 1
        item, bodied = orig[start:i], src[start:i].rstrip().endswith("}")
        head = orig[start:last_group] if bodied and last_group is not None else item
        fn = re.search(r"\bfn\s+(\w+)", src[start : last_group if bodied and last_group else i])
        if not fn and bodied and (m := re.search(r"\bimpl\b(.*)$", src[start:last_group], re.S)):
            ty, trait = self_type(m.group(1))
            inner = f"{scope}{ty}" + (f"[{trait}]" if trait else "")
            if trait:
                found.append((inner, head))
            found += verus_items(src, orig, last_group + 1, i - 1, inner + "::")
        elif fn:
            found.append((f"{scope}{fn.group(1)}", item if re.search(r"\bspec\s+fn\b", head) else head))
        elif not USE.match(item):
            if m := re.search(r"assume_specification\b[^\[]*\[", item):
                # The spec'd path, up to the bracket that closes the one after the generics.
                depth, j = 1, m.end()
                while depth:
                    depth += {"[": 1, "]": -1}.get(item[j], 0)
                    j += 1
                key = item[m.end() : j - 1]
            elif m := re.search(r"\b(?:struct|enum|trait|type|const|static|group)\s+(\w+)", item):
                key = m.group(1)
            else:
                key = norm(item)[:40]
            found.append((scope + key, item))
    return [(re.sub(r"\s+", "", key), text) for key, text in found]


def unique(pairs: list[tuple[str, str]]) -> list[tuple[str, str]]:
    seen: dict[str, int] = {}
    out = []
    for key, value in pairs:
        seen[key] = seen.get(key, 0) + 1
        out.append((key if seen[key] == 1 else f"{key}#{seen[key]}", value))
    return out


def parse(path: Path) -> tuple[str, str, dict]:
    orig = strip(path.read_text(), strings=False)
    src = strip(orig)
    return src, orig, items(src, orig)


def verus_cfg(toml: dict, config: dict) -> set[str]:
    """The cfgs rustc gets with the default features and the config's `features` on."""
    features = dict(toml.get("features", {}))
    named = {entry for entries in features.values() for entry in entries}
    tables = [toml, *toml.get("target", {}).values()]
    for name, spec in [d for t in tables for k in ("dependencies", "build-dependencies") for d in t.get(k, {}).items()]:
        if isinstance(spec, dict) and spec.get("optional") and f"dep:{name}" not in named:
            features.setdefault(name, [])  # an optional dep's implicit feature
    on, todo = set(), ["default", *config.get("features", [])]
    while todo:
        feature = todo.pop()
        if feature in features and feature not in on:
            on.add(feature)
            todo += [e.split("/")[0] for e in features[feature] if not e.startswith("dep:") and "?/" not in e]
    return {"verus_keep_ghost", "verus_keep_ghost_body"} | {f'feature="{f}"' for f in on}


def load(crate: Path) -> tuple[dict, dict]:
    global VERUS_CFG
    with (crate / "Cargo.toml").open("rb") as fh:
        toml = tomllib.load(fh)
    config = toml.get("package", {}).get("metadata", {}).get("verus-gates", {})
    VERUS_CFG = verus_cfg(toml, config)
    return toml, config


def workspace(crate: Path) -> Path:
    """The root of the workspace the crate is in, or the crate."""
    for d in [crate.resolve(), *crate.resolve().parents]:
        if (d / "Cargo.toml").is_file():
            with (d / "Cargo.toml").open("rb") as fh:
                if "workspace" in tomllib.load(fh):
                    return d
    return crate


def dep_lines(toml: dict) -> list[str]:
    """One line per entry of every dependency table: the table and name."""
    kinds = ("dependencies", "build-dependencies", "dev-dependencies", "build_dependencies", "dev_dependencies")
    tables = [(k, toml.get(k, {})) for k in kinds]
    tables += [(f"target.{cfg}.{k}", t.get(k, {})) for cfg, t in toml.get("target", {}).items() for k in kinds]
    return sorted("dep " + re.sub(r"\s+", "", f"{table}/{name}") for table, entries in tables for name in entries)


def static_manifest(crate: Path, config: dict, toml: dict) -> list[str]:
    """The manifest lines the sources fix: tcb items, dependencies, spec hashes."""
    lines = []
    if (crate / TCB).is_file():
        src, orig, found = parse(crate / TCB)
        rest, pairs = list(orig), []
        for a, b, _, _ in found["verus"]:
            pairs += verus_items(src, orig, a, b)
            rest[a:b] = " " * (b - a)
        pairs.append(("(outside-verus!)", "".join(rest)))
        lines += [f"tcb {digest(t)} {k}" for k, t in unique(pairs)]
    lines += dep_lines(toml)
    features = sorted(toml.get("features", {}).items())
    lines += [f"feature {json.dumps(v, separators=(',', ':'))} {k}" for k, v in features]
    lines += [f"cfg {c}" for c in sorted(VERUS_CFG)]
    lines += [f"scope in {rel}" for rel in sorted(config.get("in-scope", []))]
    out = {**config.get("out-of-scope-files", {}), **config.get("out-of-scope", {})}
    lines += [f"scope out {key}" for key in sorted(out)]
    lines += [f"trusted-trait {name}" for name in sorted(config.get("trusted-traits", []))]
    for rel in sorted(config.get("in-scope", [])):
        if not (crate / rel).is_file():
            continue
        src, orig, found = parse(crate / rel)
        pairs = [(qual, spec) for qual, _, _, _, spec in found["fns"] if spec]
        for a, b, _, _ in found["verus"]:
            pairs += verus_items(src, orig, a, b)
        lines += [f"spec {digest(t)} {rel}::{k}" for k, t in unique(pairs)]
    return lines


def read_manifest(crate: Path) -> list[str]:
    path = crate / MANIFEST
    if not path.is_file():
        return []
    return [line for line in path.read_text().splitlines() if line and not line.startswith("#")]


def is_static(line: str) -> bool:
    return line.split(" ", 1)[0] in ("tcb", "dep", "feature", "cfg", "scope", "trusted-trait", "spec")


def diff(want: list[str], have: list[str], what: str) -> list[str]:
    """Names each item added, dropped or changed; a line's key is its first and last field."""

    def keyed(lines: list[str]) -> dict[str, str]:
        return {f"{line.split(' ')[0]} {line.split(' ')[-1]}": line for line in lines}

    want_k, have_k = keyed(want), keyed(have)
    errors = []
    for key in sorted(want_k.keys() | have_k.keys()):
        if key not in have_k:
            errors.append(f"{what}: `{key}` is new")
        elif key not in want_k:
            errors.append(f"{what}: `{key}` is gone")
        elif want_k[key] != have_k[key]:
            errors.append(f"{what}: `{key}` changed")
    return errors


def check(crate: Path) -> list[str]:
    errors = []
    toml, config = load(crate)
    if "build" in toml.get("package", {}) or (crate / "build.rs").exists():
        errors.append("a build script can generate code these gates never read")
    if toml.get("lib", {}).get("path", "src/lib.rs") != "src/lib.rs":
        errors.append("[lib] path must be src/lib.rs")

    in_scope = set(config.get("in-scope", []))
    out_files = dict(config.get("out-of-scope-files", {}))
    trusted_traits = set(config.get("trusted-traits", []))
    listed = sorted(in_scope | out_files.keys())
    errors += [f"listed file {rel} not found" for rel in listed if not (crate / rel).is_file()]

    for path in sorted((crate / "src").rglob("*.rs")):
        rel = path.relative_to(crate)
        src = strip(path.read_text())
        if rel != TCB and str(rel) not in in_scope | out_files.keys():
            errors.append(f"{rel}: not listed in in-scope or out-of-scope-files")
        for construct in TRUSTED if rel != TCB else []:
            for m in re.finditer(construct, src):
                errors.append(f"{rel}:{line_of(src, m.start())}: trusted `{m.group(0)}` outside {TCB}")
        for construct in OPAQUE:
            for m in re.finditer(construct, src):
                errors.append(f"{rel}:{line_of(src, m.start())}: `{norm(m.group(0))}` hides code from these gates")
        for m in re.finditer(r"\bfeature\s*\(([^)]*)\)", src):
            for feature in split_top(m.group(1)):
                if feature not in FEATURES:
                    errors.append(f"{rel}:{line_of(src, m.start())}: feature `{feature}` is not on the allowed list")
        # A name MACROS or MACRO_CRATES trusts, bound to another crate's item.
        for m in re.finditer(r"\bextern\s+crate\s+(\w+)(\s+as\b)?", src):
            if m.group(2) or m.group(1) not in ("std", "core", "alloc"):
                errors.append(f"{rel}:{line_of(src, m.start())}: `{norm(m.group(0))}` can rename a crate")
        for text, line, _ in items(src, strip(path.read_text(), strings=False))["uses"]:
            for full, name in use_names(text):
                std = full.split("::")[0] in ("std", "core", "alloc", "vstd")
                if name in MACROS | ATTRS | DERIVES | MACRO_CRATES and not std:
                    errors.append(f"{rel}:{line}: `use {full}` binds `{name}`, a macro or macro crate name")
        if str(rel) in out_files:
            for m in re.finditer(r"\bverus\w*", src):
                errors.append(f"{rel}:{line_of(src, m.start())}: out-of-scope file uses `{m.group(0)}`")

    out_of_scope = dict(config.get("out-of-scope", {}))
    used = set()
    for rel in sorted(in_scope):
        path = crate / rel
        if not path.is_file():
            continue
        src, _, found = parse(path)
        seen: dict[str, int] = {}
        for qual, line, ok, live, _ in found["fns"]:
            key = f"{rel}::{qual}"
            seen[key] = seen.get(key, 0) + 1
            if key in out_of_scope:
                used.add(key)
                if ok and live:
                    errors.append(f"{rel}:{line}: `{qual}` is verified but listed as out of scope")
            elif not ok:
                errors.append(f"{rel}:{line}: `{qual}` has no verus_spec/verus_verify and is not out of scope")
            elif not live:
                errors.append(f"{rel}:{line}: `{qual}` is cfg'd out of the Verus build, so never verified")
            elif seen[key] > 1:
                errors.append(f"{rel}:{line}: `{qual}` has a second body; Verus checks only one")
        traits = [(name, line) for name, line, _ in found["traits"]]
        for a, b, _, _ in found["verus"]:
            traits += [(m.group(1), line_of(src, a + m.start())) for m in re.finditer(r"\btrait\s+(\w+)", src[a:b])]
        for name, line in traits:
            if name not in trusted_traits:
                errors.append(f"{rel}:{line}: trait `{name}` is not on trusted-traits; its spec binds unverified impls")
        for text, line, live in found["uses"]:
            # A cfg'd import may differ only in its std/core/alloc path, or link a crate unused.
            imported = re.sub(r"^(pub(\(.*?\))?\s+)?use\s+", "", text)
            if not live and not re.fullmatch(r"(::)?(std|core|alloc)\b.*|\w+\s+as\s+_", imported, re.S):
                errors.append(f"{rel}:{line}: `{text}` is cfg'd out of the Verus build and imports crate code")
        for name, line, live in found["mods"]:
            base = path.parent if path.name in ("lib.rs", "mod.rs") else path.with_suffix("")
            targets = {str((base / f"{name}.rs").relative_to(crate)), str((base / name / "mod.rs").relative_to(crate))}
            if not live and not targets & out_files.keys():
                errors.append(f"{rel}:{line}: `mod {name}` is cfg'd out of the Verus build")
        for a, b, line, live in found["verus"]:
            if not live:
                errors.append(f"{rel}:{line}: `verus!` block is cfg'd out of the Verus build")
            for m in re.finditer(r"#\s*!?\s*\[\s*cfg", src[a:b]):
                errors.append(f"{rel}:{line_of(src, a + m.start())}: cfg in a `verus!` block")
        for pos, name, kind in macro_uses(src):
            if not macro_ok(name, kind):
                errors.append(f"{rel}:{line_of(src, pos)}: {kind} `{name}` is not from a crate on MACRO_CRATES")
        for text, line, _ in found["uses"]:
            for full, name in use_names(text):
                if name == "*" and full.split("::")[0] not in ("vstd", "crate", "self", "super"):
                    errors.append(f"{rel}:{line}: glob import `{full}` can shadow a macro name")
        for text, line in found["body_cfgs"]:
            errors.append(f"{rel}:{line}: `#[{text}]` in a fn body makes the build differ from the verified one")
        for m in re.finditer(r"\bcfg\s*!", src):
            errors.append(f"{rel}:{line_of(src, m.start())}: `cfg!` makes the build differ from the verified one")
    errors += [f"out-of-scope entry `{key}` matches no fn" for key in out_of_scope if key not in used]

    want = static_manifest(crate, config, toml)
    have = [line for line in read_manifest(crate) if is_static(line)]
    if not have:
        errors.append(f"{MANIFEST} missing or empty")
    elif mismatch := diff(want, have, MANIFEST):
        errors += mismatch + ["run `verus-gates.py --update` and review the manifest diff"]
    return errors


def verus_report(stdout: str) -> dict:
    """The one JSON report `--output-json` prints. On a fresh target dir, dependencies that
    Verus also verifies print a plain results line first; this skips it."""
    starts = [m.start() for m in re.finditer(r"^\{$", stdout, re.M)]
    if len(starts) != 1:
        raise ValueError(f"expected one Verus JSON report, found {len(starts)}")
    return json.JSONDecoder().raw_decode(stdout, starts[0])[0]


def verified_fns(report: dict, crate_name: str) -> list[str]:
    fns = []
    for module in report.get("times-ms", {}).get("smt", {}).get("smt-run-module-times", []):
        for f in module.get("function-breakdown", []):
            if f["function"].startswith(f"{crate_name}::") and f.get("success"):
                # A fn with `with` ghost args verifies under a prefixed name.
                name = f["function"].replace("::_VERUS_VERIFIED_", "::")
                fns.append(f"fn {f.get('mode:') or '?'} {name}")
    return sorted(fns)


def clean_run(report: dict) -> bool:
    res = report.get("verification-results", {})
    return bool(res.get("success") and res.get("errors") == 0 and res.get("is-verifying-entire-crate"))


def results(crate: Path, stdout: str) -> list[str]:
    toml, config = load(crate)
    try:
        report = verus_report(stdout)
    except ValueError as error:
        return [str(error)]
    res = report.get("verification-results", {})
    if not clean_run(report):
        return [f"Verus did not verify the whole crate cleanly: {res}"]
    name = toml["package"]["name"].replace("-", "_")
    have = read_manifest(crate)
    want = next((line.split()[1] for line in have if line.startswith("verified ")), None)
    errors = [] if str(res.get("verified")) == want else [f"{res.get('verified')} verified, {MANIFEST} says {want}"]
    got = verified_fns(report, name)
    errors += diff(got, [line for line in have if line.startswith("fn ")], "verified fns")
    for key in config.get("out-of-scope", {}):
        rel, qual = key.split(".rs::", 1)
        module = re.sub(r"(^|/)(lib|mod)$", "", rel.removeprefix("src/")).replace("/", "::")
        path = "::".join(p for p in (name, module, qual) if p)
        if any(line.endswith(f" {path}") for line in got):
            errors.append(f"out-of-scope entry `{key}` is verified by Verus")
    return errors


def cheats(crate: Path, stderr: str) -> list[str]:
    """Checks a `--no-cheating` Verus run. Verus names every trusted item it compiled there,
    however a macro spelled it; each must be in tcb.rs, an `uninterp` spec fn, or the
    external wrapper Verus makes for a fn with ghost (`with`) args."""
    load(crate)
    found = re.findall(r"^error: (.*not allowed with --no-cheating)\n\s*--> ([^\n]+?):(\d+):\d+$", stderr, re.M)
    total = re.search(r"^error: could not compile `[^`]+` \(lib\) due to (\d+) previous errors?", stderr, re.M)
    if not total:
        return ["the --no-cheating run rejected nothing, so it never compiled tcb.rs (cached?)"]
    errors = [] if int(total.group(1)) == len(found) else [f"{total.group(1)} errors, {len(found)} from --no-cheating"]
    root = workspace(crate)
    for what, file, line in found:
        rel = (root / file).resolve().relative_to(crate.resolve())
        src, _, parsed = parse(crate / rel)
        text = src.splitlines()[int(line) - 1]
        allowed = rel == TCB or "external_body" in what and (
            re.match(r"\s*(pub(\s*\([^)]*\))?\s+)?uninterp\s+spec\s+fn\b", text)
            or any(n == int(line) and re.search(r"\bwith\b", spec) for _, n, _, _, spec in parsed["fns"])
        )
        if not allowed:
            errors.append(f"{rel}:{line}: Verus says `{what}`")
    return errors


def update(crate: Path, stdout: str | None) -> None:
    toml, config = load(crate)
    dynamic = [line for line in read_manifest(crate) if not is_static(line)]
    if stdout is not None:
        report = verus_report(stdout)
        if not clean_run(report):
            sys.exit(f"verus-gates: the Verus run failed: {report.get('verification-results')}")
        name = toml["package"]["name"].replace("-", "_")
        dynamic = [f"verified {report['verification-results']['verified']}"] + verified_fns(report, name)
    header = [
        "# Checked by .github/scripts/verus-gates.py; regenerate it with `--update` (see there).",
        "# tcb and spec lines: hash of the normalized text, then the item. fn lines: from Verus.",
    ]
    (crate / MANIFEST).write_text("\n".join(header + dynamic + static_manifest(crate, config, toml)) + "\n")


def self_test() -> None:
    body = """
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures match r { None => true, Some(_) => true }))]
fn f() -> Option<u8> { let x = '{'; None }
#[cfg(verus_keep_ghost)]
verus! { spec fn s() -> bool { true } proof fn p() ensures s() { } }
#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<'a> Iterator for It<'a> { fn next(&mut self) -> Option<u8> { None } }
#[cfg_attr(verus_keep_ghost, verus_verify)]
trait T { fn t(&self); }
#[cfg(not(feature = "std"))]
use alloc::{vec::Vec, boxed::Box};
#[cfg(feature = "std")]
use std::{vec::Vec, boxed::Box};
#[cfg(test)]
mod tests { fn helper() {} }
"""
    tcb = "verus! { pub assume_specification[ f ]() -> u8; }\n"
    spec = "#[cfg_attr(verus_keep_ghost, verus_spec(ensures true))]"
    fw = spec + "\nfn w(a: u8) -> u8 {\n"
    # name: (appended to src/a.rs, out-of-scope entries, extra files, passes)
    cases = {
        "clean": ("", "", {}, True),
        "assume": ("fn f() { proof! { assume(false); } }", "", {}, False),
        "commented": ("// assume(false) is fine in a comment\n", "", {}, True),
        "specimpl": ("verus! { impl OrdSpecImpl for P {} }", "", {}, False),
        "specimpl_newline": ("verus! { impl OrdSpecImpl\nfor P {} }", "", {}, False),
        "assume_space": ("verus! { proof fn f() ensures false { assume (false); } }", "", {}, False),
        "assume_builtin": ("verus! { proof fn f() ensures false { vstd::prelude::assume_(false); } }", "", {}, False),
        "admit_space": ("verus! { proof fn f() ensures false { admit (); } }", "", {}, False),
        "external_paren": ("verus! { #[verifier(external)] fn f() {} }", "", {}, False),
        "undeclared_trait_lint_ok": ("#[allow(undeclared_external_trait)]\nfn g() {}", '"src/a.rs::g" = "x"', {}, True),
        "unannotated": ("impl S { fn g(&self) {} }", "", {}, False),
        "listed": ("impl S { fn g(&self) {} }", '"src/a.rs::S::g" = "later"', {}, True),
        "stale": ("", '"src/a.rs::S::gone" = "later"', {}, False),
        "listed_but_verified": ("", '"src/a.rs::f" = "x"', {}, False),
        # Code the regexes would not read.
        "path_attr": ('#[path = "../evil.rs"]\nmod evil;', "", {}, False),
        "path_cfg_attr": ('#[cfg_attr(verus_keep_ghost, path = "../evil.rs")]\nmod evil;', "", {}, False),
        "include": ('include!("../evil.rs");', "", {}, False),
        "macro_concat": ("macro_rules! m { () => { ${concat(ass, ume)}(false) } }", "", {}, False),
        "feature_concat": ("#![cfg_attr(verus_keep_ghost, feature(macro_metavar_expr_concat))]", "", {}, False),
        "build_script": ("", "", {"build.rs": "fn main() {}"}, False),
        "unlisted_file": ("", "", {"src/oracle.rs": "impl Oracle for u8 { fn boom(&self) {} }"}, False),
        "out_of_scope_file_uses_verus": ("", "", {"src/o.rs": spec + "\nfn h() {}"}, False),
        # A trait's spec is assumed for every unverified impl.
        "untrusted_trait": ("#[cfg_attr(verus_keep_ghost, verus_verify)]\ntrait O { fn boom(&self); }", "", {}, False),
        "untrusted_trait_in_verus": ("verus! { pub trait Oracle { proof fn boom() ensures false; } }", "", {}, False),
        # Unverified fns that look verified, or that sit where the walk once never looked.
        "cfg_attr_cfg_test": ("#[cfg_attr(any(), cfg(test))]\nimpl S { fn u(x: u64) -> u64 { x + 1 } }", "", {}, False),
        "fake_verify": ("#[cfg_attr(any(), verus_verify)]\nimpl S { fn g(&self) {} }", "", {}, False),
        "fn_in_macro": ("m! { pub fn u(x: u64) -> u64 { x + 1 } }", "", {}, False),
        "fn_in_macro_parens": ("m!(pub fn u(x: u64) -> u64 { x + 1 });", "", {}, False),
        "fn_in_const": ("const _: () = { impl S { pub fn u(x: u64) -> u64 { x + 1 } } };", "", {}, False),
        "nested_fn": (spec + "\nfn o() { fn u(x: u64) -> u64 { x + 1 } }", "", {}, False),
        "body_swap": (
            f"#[cfg(verus_keep_ghost)]\n{spec}\nfn w(x: u64) -> u64 {{ x }}\n"
            f"#[cfg(not(verus_keep_ghost))]\n{spec}\nfn w(x: u64) -> u64 {{ x + 1 }}",
            "",
            {},
            False,
        ),
        "feature_swap": (
            f'#[cfg(not(feature = "std"))]\n{spec}\nfn w() {{}}\n#[cfg(feature = "std")]\n{spec}\nfn w() {{}}',
            "",
            {},
            False,
        ),
        "second_body": (f"{spec}\nfn w() {{}}\n{spec}\nfn w() {{}}", "", {}, False),
        "cfg_dead_fn": (f'#[cfg(feature = "std")]\n{spec}\nfn w() {{}}', "", {}, False),
        "cfg_dead_mod": (f'#[cfg(feature = "std")]\nmod m {{ {spec}\nfn w() {{}} }}', "", {}, False),
        "cfg_dead_mod_decl": ('#[cfg(feature = "std")]\nmod m;', "", {}, False),
        "cfg_dead_verus": ("#[cfg(not(verus_keep_ghost))]\nverus! { fn w() {} }", "", {}, False),
        "use_swap": ("#[cfg(not(verus_keep_ghost))]\nuse crate::o::w;", "", {}, False),
        "use_link_ok": ('#[cfg(feature = "std")]\nuse crc as _;', "", {}, True),
        # A statement or expression cfg ships a body Verus never checked.
        "body_cfg": (fw + '#[cfg(feature = "std")]\nif a == 0 { return 1; }\na }', "", {}, False),
        "body_cfg_block": (fw + '#[cfg(feature = "std")]\n{ return 1; }\na }', "", {}, False),
        "body_cfg_let": (fw + "#[cfg(not(verus_keep_ghost))]\nlet a = 0;\na }", "", {}, False),
        "body_cfg_ghost_let": (fw + "#[cfg(verus_keep_ghost)]\nlet a = 0;\na }", "", {}, False),
        "body_cfg_expr": (spec + '\nfn w(a: u8) -> u8 { let b = #[cfg(feature = "std")] 0; a }', "", {}, False),
        "body_cfg_tail": (spec + '\nfn w(a: u8) -> u8 { #[cfg(feature = "std")] a }', "", {}, False),
        "body_cfg_attr": (fw + '#[cfg_attr(verus_keep_ghost, cfg(any()))]\nlet a = 0;\na }', "", {}, False),
        "body_cfg_attr_std": (fw + '#[cfg_attr(feature = "std", allow(unused))]\nlet a = 0;\na }', "", {}, False),
        "body_cfg_macro": (spec + '\nfn w(a: u8) -> u8 { if cfg!(feature = "std") { return 0; } a }', "", {}, False),
        "verus_cfg": ('verus! { fn w(a: u8) -> u8 {\n#[cfg(feature = "std")]\nlet a = 0;\na } }', "", {}, False),
        # Macros from a dependency can build any token, `assume` included.
        "macro_dep": (spec + "\nfn w() { paste::paste! { [<ass ume>](false); } }", "", {}, False),
        "macro_dep_bare": ("use paste::paste;\n" + spec + "\nfn w() { paste! { [<ass ume>](false); } }", "", {}, False),
        "macro_renamed": ("use paste::paste as vec;\n" + spec + "\nfn w() { vec! { [<ass ume>](0); } }", "", {}, False),
        "macro_crate_renamed": ("use paste as vstd;\n" + spec + "\nfn w() { vstd::paste! { } }", "", {}, False),
        "macro_extern_crate": ("extern crate paste as vstd;", "", {}, False),
        "macro_glob": ("use paste::*;", "", {}, False),
        "attr_dep": ("#[paste::item]\n" + spec + "\nfn w() {}", "", {}, False),
        "attr_bare": ("use evil::rewrite;\n#[rewrite]\n" + spec + "\nfn w() {}", "", {}, False),
        "derive_dep": ("#[derive(Clone, evil::Evil)]\nstruct Z;", "", {}, False),
        "macro_std_ok": (
            "#[derive(Clone, wincode::SchemaWrite)]\nstruct Z;\n"
            + spec
            + "\nfn w() -> Vec<u8> { assert!(true); if !(true) {} vstd::prelude::proof! { } vec![1] }",
            "",
            {},
            True,
        ),
        "body_ghost_ok": (
            fw + "#[cfg(verus_keep_ghost)]\nproof! { assert(true); }\n"
            "#[cfg(verus_keep_ghost)]\nproof_decl! { let ghost g = 0int; }\n"
            "#[cfg(verus_keep_ghost)]\nproof_with! {Tracked(&mut g)}\nlet b = h(a);\n"
            "#[cfg_attr(verus_keep_ghost, verus_spec(invariant true))]\nwhile false {}\na }",
            "",
            {},
            True,
        ),
    }
    for name, (extra, listed, files, want_ok) in cases.items():
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp)
            (crate / "src/verus").mkdir(parents=True)
            (crate / "src/verus/tcb.rs").write_text(tcb)
            (crate / "src/a.rs").write_text(body + extra)
            for rel, text in files.items():
                (crate / rel).write_text(text)
            out_files = '"src/o.rs" = "x"' if "src/o.rs" in files else ""
            (crate / "Cargo.toml").write_text(
                '[package]\nname = "t"\n[package.metadata.verus-gates]\nin-scope = ["src/a.rs"]\n'
                f'trusted-traits = ["T"]\nout-of-scope-files = {{ {out_files} }}\n'
                f"out-of-scope = {{ {listed} }}\n"
            )
            # The manifest follows the change, so each case fails on its own rule.
            update(crate, None)
            errors = check(crate)
            assert (not errors) == want_ok, f"self-test `{name}`: {errors}"

    # Cargo's feature rules: `dep:` and `?/` enable no feature, an optional dep without `dep:`
    # has an implicit one, and default features are on.
    cfg = verus_cfg(
        tomllib.loads(
            '[features]\ndefault = ["a"]\na = ["dep:x", "y/z", "w?/v", "c"]\nb = []\nc = []\nd = []\n'
            '[dependencies]\nx = { version = "1", optional = true }\ny = { version = "1", optional = true }\n'
        ),
        {"features": ["b"]},
    )
    want = VERUS_CFG | {f'feature="{f}"' for f in ("default", "a", "b", "c", "y")}
    assert cfg == want, f"self-test `verus_cfg`: {cfg}"

    # The manifest pins the tcb.rs items, the specs, every dependency table and the gate config.
    toml = '[package]\nname = "t"\n[package.metadata.verus-gates]\nin-scope = ["src/a.rs"]\ntrusted-traits = ["T"]\n'
    toml += 'features = ["verus"]\n'
    toml += '[features]\nverus = []\nstd = []\n'
    toml += '[dependencies]\ncrc = { version = "3.4", default-features = false }\nwincode = { workspace = true }\n'
    root = '[workspace]\nmembers = ["c"]\n[workspace.dependencies]\nwincode = "0.6"\n'
    pinned = {
        "tcb_added_item": ("src/verus/tcb.rs", tcb + "verus! { pub proof fn z() ensures false { assume(false); } }\n"),
        "tcb_changed_item": ("src/verus/tcb.rs", tcb.replace("-> u8", "-> u16")),
        "tcb_outside_verus": ("src/verus/tcb.rs", tcb + "#[verifier::external_body]\nfn z() {}\n"),
        "spec_weakened": ("src/a.rs", body.replace("ensures s()", "ensures true")),
        "spec_fn_weakened": ("src/a.rs", body.replace("{ true } proof", "{ 1 == 1 } proof")),
        "attr_spec_weakened": ("src/a.rs", body.replace("Some(_) => true", "Some(_) => 1 == 1")),
        "dep_added": ("Cargo.toml", toml + 'paste = "1"\n'),
        "dep_target_added": ("Cargo.toml", toml + "[target.'cfg(all())'.dependencies]\npaste = \"1\"\n"),
        "dep_build_added": ("Cargo.toml", toml + '[build-dependencies]\npaste = "1"\n'),
        "dep_dev_added": ("Cargo.toml", toml + "[target.'cfg(verus_keep_ghost)'.dev-dependencies]\npaste = \"1\"\n"),
        # The gate config: what is out of scope, which traits are trusted, the Verus cfgs.
        "scope_fn_added": (
            "src/a.rs",
            body + "impl S { fn g(&self) {} }",
            "Cargo.toml",
            toml + '[package.metadata.verus-gates.out-of-scope]\n"src/a.rs::S::g" = "x"\n',
        ),
        "scope_file_added": (
            "src/b.rs",
            "fn h() {}",
            "Cargo.toml",
            toml + '[package.metadata.verus-gates.out-of-scope-files]\n"src/b.rs" = "x"\n',
        ),
        "trusted_trait_added": (
            "src/a.rs",
            body + "#[cfg_attr(verus_keep_ghost, verus_verify)]\ntrait O { fn o(&self); }",
            "Cargo.toml",
            toml.replace('["T"]', '["T", "O"]'),
        ),
        "feature_changed": ("Cargo.toml", toml.replace("verus = []", 'verus = ["std"]')),
    }
    for name, change in pinned.items():
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp) / "c"
            (crate / "src/verus").mkdir(parents=True)
            (crate / "src/verus/tcb.rs").write_text(tcb)
            (crate / "src/a.rs").write_text(body)
            (crate / "Cargo.toml").write_text(toml)
            (crate / "../Cargo.toml").write_text(root)
            update(crate, None)
            assert not check(crate), f"self-test `{name}` before: {check(crate)}"
            for rel, text in zip(change[::2], change[1::2]):
                (crate / rel).write_text(text)
            assert check(crate), f"self-test `{name}`: not caught"

    def report(verified: int, errors: int, fns: list[str]) -> str:
        breakdown = [{"function": f, "mode:": "exec", "success": True} for f in fns]
        res = {"success": errors == 0, "verified": verified, "errors": errors, "is-verifying-entire-crate": True}
        smt = {"smt-run-module-times": [{"module": "a", "function-breakdown": breakdown}]}
        return json.dumps({"verification-results": res, "times-ms": {"smt": smt}}, indent=2) + "\n"

    # On a fresh target dir, vstd prints its own plain results line first.
    vstd = "verification results:: 1907 verified, 0 errors\n"
    runs = {
        "fresh_target_dir": (vstd + report(2, 0, ["t::f", "t::g"]), True),
        "cached": (vstd, False),
        "error": (vstd + report(2, 1, ["t::f", "t::g"]), False),
        "count_changed": (report(3, 0, ["t::f", "t::g"]), False),
        "fn_swapped": (report(2, 0, ["t::f", "t::h"]), False),
        "two_reports": (report(2, 0, ["t::f", "t::g"]) * 2, False),
        "listed_but_verified": (report(2, 0, ["t::f", "t::g"]), False),
    }
    for name, (stdout, want_ok) in runs.items():
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp)
            (crate / "src").mkdir()
            listed = '"src/lib.rs::g" = "x"' if name == "listed_but_verified" else ""
            (crate / "Cargo.toml").write_text(
                f'[package]\nname = "t"\n[package.metadata.verus-gates]\nin-scope = []\nout-of-scope = {{ {listed} }}\n'
            )
            update(crate, report(2, 0, ["t::f", "t::g", "vstd::x"]))
            errors = results(crate, stdout)
            assert (not errors) == want_ok, f"self-test `{name}`: {errors}"
    # Verus's own list of trusted items, from a --no-cheating run.
    a_rs = (
        "verus! {\npub uninterp spec fn u() -> int;\n}\n"
        "#[cfg_attr(verus_keep_ghost, verus_spec(with Tracked(s): Tracked<&mut int>))]\nfn w() {}\nfn x() {}\n"
    )

    def nc(*errs: tuple[str, str, int]) -> str:
        out = "".join(f"error: {w} not allowed with --no-cheating\n  --> {f}:{n}:1\n   |\n\n" for w, f, n in errs)
        return out + f"error: could not compile `t` (lib) due to {len(errs)} previous errors\n"

    eb, aa = "external_body/assume_specification", "assume/admit"
    trusted = [(eb, "src/verus/tcb.rs", 1), (eb, "src/a.rs", 2), (eb, "src/a.rs", 5)]
    nc_runs = {
        "trusted_only": (nc(*trusted), True),
        "assume": (nc(*trusted, (aa, "src/a.rs", 6)), False),
        "external_body": (nc(*trusted, (eb, "src/a.rs", 6)), False),
        "external_body_on_decl": (nc(*trusted, (eb, "src/a.rs", 1)), False),
        "other_error": (nc(*trusted).replace("due to 3", "due to 4"), False),
        "cached": ("", False),
    }
    for name, (stderr, want_ok) in nc_runs.items():
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp)
            (crate / "src/verus").mkdir(parents=True)
            (crate / "src/verus/tcb.rs").write_text(tcb)
            (crate / "src/a.rs").write_text(a_rs)
            (crate / "Cargo.toml").write_text('[package]\nname = "t"\n')
            errors = cheats(crate, stderr.replace("src/", f"{crate}/src/"))
            assert (not errors) == want_ok, f"self-test `{name}`: {errors}"
    print("verus-gates self-test: ok")


def main() -> None:
    args = sys.argv[1:]
    if args == ["--self-test"]:
        self_test()
        return
    if args[:1] == ["--features"] and len(args) == 2:
        print(",".join(load(Path(args[1]))[1].get("features", [])))
        return
    if args[:1] == ["--update"] and len(args) in (2, 3):
        update(Path(args[1]), Path(args[2]).read_text() if len(args) == 3 else None)
        print(f"verus-gates: wrote {Path(args[1]) / MANIFEST}")
        return
    if args[:1] == ["--results"] and len(args) == 3:
        errors = results(Path(args[1]), Path(args[2]).read_text())
    elif args[:1] == ["--no-cheating"] and len(args) == 3:
        errors = cheats(Path(args[1]), Path(args[2]).read_text())
    elif len(args) == 1 and not args[0].startswith("--"):
        errors = check(Path(args[0]))
    else:
        sys.exit(
            "usage: verus-gates.py <crate-dir> | --results <crate-dir> <verus-stdout>"
            " | --no-cheating <crate-dir> <verus-stderr>"
            " | --update <crate-dir> [<verus-stdout>] | --features <crate-dir> | --self-test"
        )
    for error in errors:
        print(f"verus-gates: {error}", file=sys.stderr)
    if errors:
        sys.exit(1)
    print("verus-gates: ok")


if __name__ == "__main__":
    main()

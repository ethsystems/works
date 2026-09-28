#!/usr/bin/env python3
"""Static gates for a crate verified in place with Verus attribute mode.

Usage: verus-gates.py <crate-dir>
       verus-gates.py --self-test

(a) No trusted construct outside src/verus/tcb.rs. `--no-cheating` cannot do
    this: it also rejects the tcb.rs entries and `uninterp` spec fns, and it
    ignores `#[verifier::external]`.
(b) Every fn in an in-scope file carries a verifying attribute, or sits in an
    impl/trait marked `verus_verify`, or is listed as out of scope. Attribute
    mode silently treats an unannotated fn as external (unverified).

Config lives in the crate's Cargo.toml:

    [package.metadata.verus-gates]
    in-scope = ["src/ring.rs"]
    out-of-scope = { "src/ring.rs::BlockRing::push" = "why" }

Test code (`#[cfg(test)]` items) and `verus! { ... }` blocks are skipped by (b).
"""

import re
import sys
import tempfile
import tomllib
from pathlib import Path

TCB = Path("src/verus/tcb.rs")
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
VERIFYING = ("verus_spec", "verus_verify")


def strip(src: str) -> str:
    """Blank out comments and string/char literals, keeping offsets and newlines."""
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
            blank(i, j)
            i = j
        elif src[i] == '"' or src.startswith('b"', i):
            j = i + (2 if src[i] == "b" else 1)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i, j + 1)
            i = j + 1
        elif m := re.compile(r"b?'(\\.[^']*|[^\\'])'").match(src, i):
            blank(i, m.end())
            i = m.end()
        else:
            i += 1
    return "".join(out)


def line_of(src: str, pos: int) -> int:
    return src.count("\n", 0, pos) + 1


def item_fns(src: str) -> list[tuple[str, int, bool]]:
    """(qualified name, line, verified) for every non-test item fn outside `verus!`."""
    fns = []
    # Scope stack entries: (kind, name, verified). Kinds: item, impl, trait, skip, block.
    stack = [("item", "", False)]
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
            attrs.append(src[i:j])
            i = j
            continue
        if c in "{};":
            header = src[header_start:i]
            kind, name, verified = stack[-1]
            at_item_level = kind in ("item", "impl", "trait")
            attr_text = " ".join(attrs)
            fn = re.search(r"\bfn\s+(\w+)", header)
            is_test = re.search(r"\bcfg\s*\(\s*test\s*\)", attr_text)
            if at_item_level and fn and c in "{;" and not is_test:
                qual = f"{name}::{fn.group(1)}" if name else fn.group(1)
                ok = verified or any(v in attr_text for v in VERIFYING)
                fns.append((qual, line_of(src, header_start + fn.start()), ok))
            if c == "{":
                if not at_item_level:
                    stack.append(("block", "", False))
                elif is_test or re.search(r"\bverus\s*!\s*$", header):
                    stack.append(("skip", "", False))
                elif fn:
                    stack.append(("block", "", False))
                elif m := re.search(r"\bimpl\b(.*)$", header, re.S):
                    self_ty = re.split(r"\bfor\b", m.group(1))[-1]
                    self_ty = re.sub(r"\bwhere\b.*", "", self_ty, flags=re.S)
                    ty = re.findall(r"(\w+)\s*(?:<.*)?$", self_ty.strip(), re.S)
                    stack.append(("impl", ty[0] if ty else "?", "verus_verify" in attr_text))
                elif m := re.search(r"\btrait\s+(\w+)", header):
                    stack.append(("trait", m.group(1), "verus_verify" in attr_text))
                elif re.search(r"\bmod\s+\w+\s*$", header):
                    stack.append(("item", "", False))
                else:
                    stack.append(("block", "", False))
            elif c == "}" and len(stack) > 1:
                stack.pop()
            header_start, attrs = i + 1, []
        i += 1
    return fns


def check(crate: Path) -> list[str]:
    errors = []
    with (crate / "Cargo.toml").open("rb") as fh:
        meta = tomllib.load(fh).get("package", {}).get("metadata", {})
    config = meta.get("verus-gates", {})

    for path in sorted((crate / "src").rglob("*.rs")):
        rel = path.relative_to(crate)
        if rel == TCB:
            continue
        src = strip(path.read_text())
        for construct in TRUSTED:
            for m in re.finditer(construct, src):
                errors.append(f"{rel}:{line_of(src, m.start())}: trusted `{m.group(0)}` outside {TCB}")

    out_of_scope = dict(config.get("out-of-scope", {}))
    used = set()
    for rel in config.get("in-scope", []):
        path = crate / rel
        if not path.is_file():
            errors.append(f"in-scope file {rel} not found")
            continue
        for qual, line, ok in item_fns(strip(path.read_text())):
            key = f"{rel}::{qual}"
            # A cfg-split fn (one body per feature) appears twice under one key.
            if key in out_of_scope:
                used.add(key)
                continue
            if not ok:
                errors.append(f"{rel}:{line}: `{qual}` has no verus_spec/verus_verify and is not out of scope")
    errors += [f"out-of-scope entry `{key}` matches no fn" for key in out_of_scope if key not in used]
    return errors


def self_test() -> None:
    cases = {
        "clean": ("", "", True),
        "assume": ("fn f() { proof! { assume(false); } }", "", False),
        "commented": ("// assume(false) is fine in a comment\n", "", True),
        "specimpl": ("verus! { impl OrdSpecImpl for P {} }", "", False),
        "specimpl_newline": ("verus! { impl OrdSpecImpl\nfor P {} }", "", False),
        "assume_space": ("verus! { proof fn f() ensures false { assume (false); } }", "", False),
        "assume_builtin": ("verus! { proof fn f() ensures false { vstd::prelude::assume_(false); } }", "", False),
        "admit_space": ("verus! { proof fn f() ensures false { admit (); } }", "", False),
        "external_paren": ("verus! { #[verifier(external)] fn f() {} }", "", False),
        "undeclared_trait_lint_ok": ("#[allow(undeclared_external_trait)]\nfn g() {}", '"src/a.rs::g" = "x"', True),
        "unannotated": ("", "", False),
        "listed": ("", '"src/a.rs::S::g" = "later"', True),
        "stale": ("", '"src/a.rs::S::gone" = "later"', False),
    }
    body = """
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures match r { None => true, Some(_) => true }))]
fn f() -> Option<u8> { let x = '{'; None }
#[cfg(verus_keep_ghost)]
verus! { spec fn s() -> bool { true } }
#[cfg_attr(verus_keep_ghost, cfg_eval, verus_verify)]
impl<'a> Iterator for It<'a> { fn next(&mut self) -> Option<u8> { None } }
#[cfg_attr(verus_keep_ghost, verus_verify)]
trait T { fn t(&self); }
impl S { fn g(&self) {} }
#[cfg(test)]
mod tests { fn helper() {} }
"""
    for name, (extra, listed, want_ok) in cases.items():
        with tempfile.TemporaryDirectory() as tmp:
            crate = Path(tmp)
            (crate / "src/verus").mkdir(parents=True)
            (crate / "src/verus/tcb.rs").write_text("verus! { pub assume_specification[ f ]() -> u8; }\n")
            src = body if name in ("unannotated", "listed", "stale") else body.replace("impl S { fn g(&self) {} }", "")
            (crate / "src/a.rs").write_text(src + extra)
            (crate / "Cargo.toml").write_text(
                '[package]\nname = "t"\n[package.metadata.verus-gates]\nin-scope = ["src/a.rs"]\n'
                f"out-of-scope = {{ {listed} }}\n"
            )
            errors = check(crate)
            assert (not errors) == want_ok, f"self-test `{name}`: {errors}"
    print("verus-gates self-test: ok")


def main() -> None:
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        return
    if len(sys.argv) != 2:
        sys.exit("usage: verus-gates.py <crate-dir> | --self-test")
    errors = check(Path(sys.argv[1]))
    for error in errors:
        print(f"verus-gates: {error}", file=sys.stderr)
    if errors:
        sys.exit(1)
    print("verus-gates: ok")


if __name__ == "__main__":
    main()

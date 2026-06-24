#!/usr/bin/env python3
"""Layer-2 gate (vendored, self-contained): anti-vacuity lint for the PCC spec.

A formal layer that can be vacuous is worse than none: it manufactures false
confidence. This lint rejects, in committed Lean, anything that would let a
"theorem" verify nothing:
  - `sorry` / `admit` (proof holes), outside comments and strings;
  - `axiom` declarations (would silently enlarge the trusted base);
  - `: Prop := True` and `.formal := True` (vacuous-true specs);
  - `native_decide` (extends trust to the Lean compiler, outside the kernel TCB; use `decide`).

Canonical source of the full gate: life-core scripts/gates/anti_theatre.py. This
trimmed copy ships in the repo so the artefact self-verifies with no external
dependency (the 2-month walk-away test). stdlib only.

Usage: python3 tools/vacuity_lint.py <lean-dir>   (default: lean)
"""
import os
import re
import sys

SKIP = {".lake", "build", ".git"}
PATS = [
    ("sorry/admit", re.compile(r"\b(sorry|admit)\b")),
    ("axiom", re.compile(r"^\s*axiom\b", re.M)),
    ("vacuous-True", re.compile(r":\s*Prop\s*:=\s*True\b|\.formal\s*:?=?\s*True\b")),
    ("native_decide-trust", re.compile(r"\bnative_decide\b")),  # extends trust to the compiler (injects ofReduceBool axiom), outside the kernel TCB; use decide
]


def strip(src):
    """Remove string literals first, then comments (order matters)."""
    out, i, n = [], 0, len(src)
    in_str = lc = False
    depth = 0
    while i < n:
        c, nx = src[i], (src[i + 1] if i + 1 < n else "")
        if lc:
            if c == "\n":
                lc = False; out.append(c)
            i += 1; continue
        if depth:
            if c == "/" and nx == "-": depth += 1; i += 2; continue
            if c == "-" and nx == "/": depth -= 1; i += 2; continue
            i += 1; continue
        if in_str:
            if c == "\\": i += 2; continue
            if c == '"': in_str = False
            i += 1; continue
        if c == '"': in_str = True; i += 1; continue
        if c == "-" and nx == "-": lc = True; i += 2; continue
        if c == "/" and nx == "-": depth = 1; i += 2; continue
        out.append(c); i += 1
    return "".join(out)


def main(argv):
    root = argv[0] if argv else "lean"
    findings = []
    for dp, dns, fns in os.walk(root):
        dns[:] = [d for d in dns if d not in SKIP]
        for fn in fns:
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(dp, fn)
            code = strip(open(p, encoding="utf-8", errors="replace").read())
            for kind, pat in PATS:
                if pat.search(code):
                    findings.append(f"{p}: {kind}")
    if findings:
        print("[vacuity_lint] FAIL:")
        for f in findings:
            print("  -", f)
        return 1
    print("[vacuity_lint] PASS: spec is sorry-free, axiom-free, and non-vacuous.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

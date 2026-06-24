#!/usr/bin/env python3
"""Layer-2 gate (vendored, self-contained): proof-claim-map (scope-aware).

Claims cannot outrun proofs. Every `[proof: NAME]` marker in the proposal must
map to a theorem/lemma declared in the Lean spec. Run AFTER `lake build` and the
vacuity lint, so a mapped name is also a genuinely-proven, sorry-free theorem.

Scope awareness (closes the gap an adversarial review found: name-match alone let
an INSTANCE theorem back a UNIVERSAL prose claim). A marker may declare scope:
  [proof: NAME]              unscoped  - only existence checked (back-compatible)
  [proof: NAME | universal]  the named theorem MUST carry a binder (forall/exists
                             or an explicit (x : T) parameter) - a fixed-instance
                             theorem fails this
  [proof: NAME | instance]   explicitly an instance fact (no scope requirement)

Canonical source of the full gate: life-core scripts/gates/proof_claim_map.py.
This trimmed copy ships in the repo so the artefact self-verifies. stdlib only.

Usage: python3 tools/proof_claim_map.py   (spec=lean, proposals=proposal/*.md)
"""
import glob
import os
import re
import sys

CLAIM = re.compile(r"\[proof:\s*([^\]]+)\]")
# name + statement (group(2) = binders+type). Terminate at the proof binding ':='
# OR at an equation/pattern-matching clause '\n  | ...' (those theorems have NO ':=',
# e.g. `theorem foo : ... \n | 0 => ... | n+1 => ...`). Without the second
# alternative the non-greedy capture would run past the equation-form theorem and
# swallow the NEXT theorem's name, hiding it from the map (false-negative).
DECL = re.compile(
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)((?:.|\n)*?)(?=:=|\n\s*\|)", re.M)
# A `| universal` claim must carry a genuine universal binder: a `∀` or an explicit
# `(x : T)` parameter. A bare `∃` does NOT qualify - an existential is a single
# witness (an instance fact), so existential theorems must be tagged `| instance`.
# (Caught 2026-06-24: non_compositional / per_agent_safety_insufficient are ∃-theorems
# that were passing the universal check on their ∃ binder and reading as ∀ in prose.)
BINDER = re.compile(r"∀|[({]\s*[A-Za-z_][A-Za-z0-9_']*\s*:")
FENCE = re.compile(r"^\s*```")
PLACEHOLDERS = {"NAME", "NAME1", "NAME2", "THEOREM", "..."}
SKIP = {".lake", "build", ".git"}


def strip(src):
    out, i, n = [], 0, len(src)
    in_str = lc = False
    depth = 0
    while i < n:
        c, nx = src[i], (src[i + 1] if i + 1 < n else "")
        if lc:
            if c == "\n": lc = False
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


def declared(spec_dir):
    """name -> {'universal': bool}. Universal iff the statement carries a binder."""
    out = {}
    for dp, dns, fns in os.walk(spec_dir):
        dns[:] = [d for d in dns if d not in SKIP]
        for fn in fns:
            if not fn.endswith(".lean"):
                continue
            code = strip(open(os.path.join(dp, fn), encoding="utf-8", errors="replace").read())
            for m in DECL.finditer(code):
                full = m.group(1)
                stmt = m.group(2)
                # universal iff it carries a binder AND is not an existential statement
                # (a bare `∃ ...` is a single-witness instance fact, even though `∃ (x:T)`
                # matches the typed-binder branch of BINDER; require no top-level `∃`
                # unless a `∀` is also present, e.g. `∀ x, ∃ y, ...`).
                universal = bool(BINDER.search(stmt)) and not ("∃" in stmt and "∀" not in stmt)
                for nm in (full, full.split(".")[-1]):
                    cur = out.get(nm)
                    out[nm] = {"universal": (cur["universal"] or universal) if cur else universal}
    return out


def claims(paths):
    """name -> list of (loc, scope). scope in {None, 'universal', 'instance'}."""
    out = {}
    for p in paths:
        in_fence = False
        for ln, line in enumerate(open(p, encoding="utf-8", errors="replace").read().splitlines(), 1):
            if FENCE.match(line):
                in_fence = not in_fence; continue
            if in_fence:
                continue
            for m in CLAIM.finditer(line):
                inner = m.group(1)
                scope = None
                if "|" in inner:
                    inner, _, sc = inner.partition("|")
                    sc = sc.strip().lower()
                    scope = sc if sc in ("universal", "instance") else None
                for nm in inner.split(","):
                    nm = nm.strip()
                    if nm and nm not in PLACEHOLDERS:
                        out.setdefault(nm, []).append((f"{os.path.basename(p)}:{ln}", scope))
    return out


def main():
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    spec = os.path.join(here, "lean")
    props = sorted(set(glob.glob(os.path.join(here, "proposal", "*.md")) + glob.glob(os.path.join(here, "*.md"))))
    decl = declared(spec)
    cl = claims(props)
    missing, scope_viol = {}, {}
    for nm, occs in cl.items():
        if nm not in decl:
            missing[nm] = [loc for loc, _ in occs]
            continue
        for loc, scope in occs:
            if scope == "universal" and not decl[nm]["universal"]:
                scope_viol.setdefault(nm, []).append(loc)
    if missing or scope_viol:
        print("[proof_claim_map] FAIL:")
        for nm, w in sorted(missing.items()):
            print(f"  - [proof: {nm}] has NO matching theorem ({'; '.join(w)})")
        for nm, w in sorted(scope_viol.items()):
            print(f"  - [proof: {nm} | universal] but '{nm}' is a fixed-instance theorem (no binder) ({'; '.join(w)})")
        return 1
    print(f"[proof_claim_map] PASS: {len(cl)} proof-claim(s) all map to declared theorems "
          f"(scope-checked).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Layer-2 gate: axiom allowlist for the PCC spec.

The repo's headline promise is "the kernel, not anyone's assertion, makes this
trustworthy." A peer review (2026-06-24) found that promise was FALSE as shipped:
`native_decide` discharges a goal by trusting the COMPILER, injecting an
`ofReduceBool`/`*._native.native_decide.ax` axiom that sits OUTSIDE the kernel's
trusted base - and the string-grep vacuity lint could not see it (the axiom never
appears as the keyword `axiom`). This gate closes that hole: it `#print axioms` on
every theorem and FAILS if any depends on an axiom outside the allowlist.

Allowlist = Lean's standard logical axioms only:
  propext, Quot.sound, Classical.choice
Anything else (notably any `native_decide` / `ofReduceBool` compiler-trust axiom,
or a user-declared axiom) is a trusted-base extension and fails the gate.

Run from the repo root: python3 tools/axiom_check.py   (builds via `lake env lean`)
stdlib only.
"""
import os, re, subprocess, sys, tempfile

ALLOW = {"propext", "Quot.sound", "Classical.choice"}
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(HERE, "lean")
# theorem-bearing files -> namespace prefix
FILES = {"Spec/Theorems.lean": "ARIA.", "Spec/PRD.lean": "ARIA.PRD."}
DECL = re.compile(r"^\s*theorem\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)


def theorem_names():
    out = []
    for rel, pref in FILES.items():
        p = os.path.join(LEAN, rel)
        if not os.path.exists(p):
            continue
        src = open(p, encoding="utf-8").read()
        for m in DECL.finditer(src):
            out.append(pref + m.group(1))
    return out


def main():
    names = theorem_names()
    if not names:
        print("[axiom_check] no theorems found"); return 1
    body = "import Spec\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n"
    chk = os.path.join(LEAN, "AxiomCheck.lean")
    open(chk, "w").write(body)
    try:
        r = subprocess.run(["lake", "env", "lean", "AxiomCheck.lean"],
                           cwd=LEAN, capture_output=True, text=True, timeout=600)
    finally:
        try: os.remove(chk)
        except OSError: pass
    out = r.stdout + r.stderr
    if r.returncode != 0 and "depends on axioms" not in out and "does not depend" not in out:
        print("[axiom_check] FAIL: could not elaborate axiom check\n" + out[-1500:]); return 1

    bad = []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        thm, axioms = m.group(1), [a.strip() for a in m.group(2).split(",") if a.strip()]
        for ax in axioms:
            if ax not in ALLOW:
                bad.append((thm, ax))
    if bad:
        print("[axiom_check] FAIL: theorems depend on axioms outside the allowlist "
              f"({sorted(ALLOW)}):")
        for thm, ax in bad:
            tag = " <-- native_decide/compiler trust" if ("native" in ax or "ofReduce" in ax) else ""
            print(f"  - {thm}: {ax}{tag}")
        print("Fix: replace `native_decide` with `decide` (kernel reduction), or remove the axiom.")
        return 1
    print(f"[axiom_check] PASS: all {len(names)} theorems depend only on the allowlist "
          f"({', '.join(sorted(ALLOW))}); no compiler-trust or user axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

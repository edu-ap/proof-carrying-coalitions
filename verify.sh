#!/usr/bin/env bash
# Reproducible verification harness for the ARIA PCC application.
#
# One command for an auditor (ARIA Red Team or anyone): clone, install Lean
# v4.29.1 via elan, run ./verify.sh. It performs BOTH verification layers:
#   Layer 1 (the proof):  lake build  -> the Lean kernel checks every theorem.
#   Layer 2 (the harness): vacuity lint (no sorry/axiom/vacuous-True) and
#                          proof-claim-map (no proposal claim outruns a proof),
#                          plus prd.json well-formedness.
# Self-contained: no dependency on the life-core monorepo. Exit 0 iff everything
# the proposal asserts as proven is, in fact, kernel-checked.
set -euo pipefail
cd "$(dirname "$0")"

echo "== ARIA PCC verification =="
echo "Lean toolchain: $(cat lean/lean-toolchain)"
echo

echo "[1/4] Layer 1 - lake build (kernel checks all theorems)"
( cd lean && lake build )
echo

echo "[2/4] Layer 2 - vacuity lint (no sorry / axiom / vacuous-True)"
python3 tools/vacuity_lint.py lean
echo

echo "[3/4] Layer 2 - proof-claim-map (claims cannot outrun proofs)"
python3 tools/proof_claim_map.py
echo

echo "[4/4] Layer 2 - axiom allowlist (no compiler-trust / user axioms)"
python3 tools/axiom_check.py
echo

echo "== ALL CHECKS PASSED: every asserted proof is kernel-checked, no claim outruns a proof. =="

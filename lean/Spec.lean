/-
  Proof-Carrying Coalitions (PCC) — formal specification root.
  =========================================================

  Pure Lean 4 (no Mathlib, no external requires), Lean v4.29.1. Builds in
  seconds; every claim is kernel-checked. Proofs use `decide` (kernel reduction),
  NOT `native_decide`, so no trust is extended to the compiler; every theorem
  depends only on Lean's standard axioms (propext, Quot.sound). NO `sorry`, NO
  user `axiom`, NO vacuous `True` (enforced by tools/vacuity_lint.py +
  tools/axiom_check.py).

  Modules:
    Spec.Model     — the coalition-safety model: agents, conjunctive closure,
                     the security property Cl(A) ∩ F = ∅, the admission gate,
                     and the Safe/Frontier audit surface.
    Spec.Theorems  — the proven content: the Spera non-compositionality result
                     (a general existential, proven in-model), gate soundness,
                     multi-step closure, the audit surface, incremental
                     admission, and a universally quantified monotonicity law.
-/
import Spec.Model
import Spec.Theorems

namespace ARIA
open Capability

/-- A mechanical projection of the verified state (no drift: if the build is
    green, every value below was kernel-checked). -/
def summary : String :=
  s!"PCC spec (kernel-checked, Lean v4.29.1):\n" ++
  s!"  coalition safety — A alone safe: {coalitionSafe pccRules forbidden [agentA]}; " ++
  s!"B alone safe: {coalitionSafe pccRules forbidden [agentB]}; " ++
  s!"A+B safe: {coalitionSafe pccRules forbidden [agentA, agentB]} (Spera non-compositionality)\n" ++
  s!"  chain A+B+D reaches wireFunds: {memC wireFunds (closure pccRules (coalitionCaps [agentA, agentB, agentD]))}"

#eval summary

end ARIA

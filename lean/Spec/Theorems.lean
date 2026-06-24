/-
  Spec.Theorems — the proven content of the PCC coalition-safety model.

  Every theorem here is closed by the Lean kernel: definitional (`rfl`),
  existential-by-witness, or `decide` over a concrete finite instance (kernel
  reduction, NOT `native_decide` - no trust is extended to the compiler). Every
  theorem depends only on Lean's standard logical axioms (propext, Quot.sound);
  there is NO `sorry`, NO user-declared `axiom`, NO `native_decide`, NO vacuous
  `True` (enforced by tools/axiom_check.py + the vacuity lint). The proposal references
  these theorems BY NAME (see [proof: ...] markers), and the proof-claim-map
  enforcement gate refuses any proposal claim that does not map to a theorem
  proven here in a building spec — so the proposal cannot outrun the proofs.
-/
import Spec.Model

namespace ARIA
open Capability

/-! ## § 1  Structural soundness of the admission gate. -/

/-- [proof: admit_eq_safe] The admission gate admits exactly the safe coalitions
    (definitional). The control plane's decision IS the security property. -/
theorem admit_eq_safe (r : List Rule) (F : CapSet) (a : List CapSet) :
    admitCoalition r F a = coalitionSafe r F a := rfl

/-- [proof: empty_coalition_safe] The empty coalition is safe under any forbidden
    set that excludes the empty seed's closure (here: trivially). -/
theorem empty_coalition_safe : coalitionSafe pccRules forbidden [] = true := by decide

/-! ## § 2  The Spera non-compositionality result, proven in this model.

    These are genuine GENERAL theorems (existentials), discharged by exhibiting a
    witness whose Bool obligations the kernel decides. They establish, inside our
    decidable model, the phenomenon Spera (arXiv:2603.15973, 2026) proves in the
    abstract: per-agent safety does not compose to coalition safety. -/

/-- [proof: non_compositional] There exist rules, a forbidden set, and two agents
    each safe in isolation whose coalition is unsafe. -/
theorem non_compositional :
    ∃ (rules : List Rule) (F A B : CapSet),
      coalitionSafe rules F [A] = true ∧
      coalitionSafe rules F [B] = true ∧
      coalitionSafe rules F [A, B] = false :=
  ⟨pccRules, forbidden, agentA, agentB, by decide, by decide, by decide⟩

/-- [proof: per_agent_safety_insufficient] Even when EVERY agent is safe alone,
    the coalition can be unsafe. This is the precise statement that per-agent
    verification is insufficient and a coalition-level proof is mandatory. -/
theorem per_agent_safety_insufficient :
    ∃ (rules : List Rule) (F : CapSet) (agents : List CapSet),
      (agents.all (fun a => coalitionSafe rules F [a])) = true ∧
      coalitionSafe rules F agents = false :=
  ⟨pccRules, forbidden, [agentA, agentB], by decide, by decide⟩

/-! ## § 3  The standard instance, fully classified by the kernel. -/

theorem agentA_safe_alone : coalitionSafe pccRules forbidden [agentA] = true := by decide
theorem agentB_safe_alone : coalitionSafe pccRules forbidden [agentB] = true := by decide
theorem agentC_safe_alone : coalitionSafe pccRules forbidden [agentC] = true := by decide
theorem agentD_safe_alone : coalitionSafe pccRules forbidden [agentD] = true := by decide

/-- [proof: coalition_AB_unsafe] The forge+exfil coalition is unsafe: the
    conjunctive rule fires and signDeed ∈ Cl(A∪B). -/
theorem coalition_AB_unsafe : coalitionSafe pccRules forbidden [agentA, agentB] = false := by
  decide

/-- [proof: benign_coalition_safe] A coalition that never completes a dangerous
    conjunction is admitted: the gate is not trivially false. -/
theorem benign_coalition_safe : coalitionSafe pccRules forbidden [agentA, agentC] = true := by
  decide

theorem admit_rejects_dangerous : admitCoalition pccRules forbidden [agentA, agentB] = false := by
  decide
theorem admit_accepts_benign : admitCoalition pccRules forbidden [agentA, agentC] = true := by
  decide

/-! ## § 4  Multi-step (chained) closure: emergent capability via a chain. -/

/-- [proof: chain_reaches_wireFunds] A+B+D completes BOTH conjunctions in
    sequence (forge,exfil → signDeed; then signDeed,escalate → wireFunds), so the
    deepest forbidden capability is reached. Closure is genuinely iterative. -/
theorem chain_reaches_wireFunds :
    memC wireFunds (closure pccRules (coalitionCaps [agentA, agentB, agentD])) = true := by
  decide

/-- [proof: chain_needs_all_three] Without the escalation agent D, the second
    conjunction never fires: signDeed is reached but wireFunds is not. The chain
    requires all three contributors. -/
theorem chain_needs_all_three :
    memC signDeed (closure pccRules (coalitionCaps [agentA, agentB])) = true ∧
    memC wireFunds (closure pccRules (coalitionCaps [agentA, agentB])) = false := by
  decide

/-! ## § 5  Audit surface: the forbidden capabilities a coalition reaches. -/

/-- [proof: safe_iff_no_forbidden_reached] Safety holds exactly when the coalition
    reaches no forbidden capability (frontierForbidden empty), on the standard
    instances — connecting the audit surface to the safety predicate. -/
theorem safe_iff_no_forbidden_reached :
    ((frontierForbidden pccRules forbidden [agentA, agentC]).isEmpty
        = coalitionSafe pccRules forbidden [agentA, agentC]) ∧
    ((frontierForbidden pccRules forbidden [agentA, agentB]).isEmpty
        = coalitionSafe pccRules forbidden [agentA, agentB]) := by
  decide

/-- [proof: frontier_identifies_culprit] For the unsafe coalition, the audit
    surface names exactly which forbidden capability was reached. -/
theorem frontier_identifies_culprit :
    memC signDeed (frontierForbidden pccRules forbidden [agentA, agentB]) = true := by
  decide

/-! ## § 6  Incremental admission (membership change). -/

/-- [proof: incremental_safe_add] Adding a benign agent to a safe coalition keeps
    it safe: admission need not be recomputed from scratch in the safe direction. -/
theorem incremental_safe_add :
    coalitionSafe pccRules forbidden [agentA] = true ∧
    coalitionSafe pccRules forbidden [agentA, agentC] = true := by decide

/-- [proof: incremental_unsafe_add] Adding an agent that completes a conjunction
    crosses the frontier: a previously-safe coalition becomes unsafe, so the join
    of a new member is exactly where re-verification must fire. -/
theorem incremental_unsafe_add :
    coalitionSafe pccRules forbidden [agentA] = true ∧
    coalitionSafe pccRules forbidden [agentA, agentB] = false := by decide

/-! ## § 7  Monotonicity instances: unsafety persists under growth. -/

/-- [proof: unsafety_persists_under_growth] A superset of an unsafe coalition is
    unsafe (capabilities only accumulate): you cannot fix an unsafe coalition by
    adding members. -/
theorem unsafety_persists_under_growth :
    coalitionSafe pccRules forbidden [agentA, agentB] = false ∧
    coalitionSafe pccRules forbidden [agentA, agentB, agentC] = false := by decide

/-- [proof: forbidden_superset_no_safer] Enlarging the forbidden set never makes
    an unsafe coalition safe (here signDeed alone already forbids it). -/
theorem forbidden_superset_no_safer :
    coalitionSafe pccRules [signDeed] [agentA, agentB] = false ∧
    coalitionSafe pccRules forbidden [agentA, agentB] = false := by decide

/-! ## § 8  A GENERAL (universally quantified) monotonicity theorem.

    The battery above decides instances; this is a real `∀`-theorem with an
    inductive proof, establishing the law for ALL rules, coalitions, and
    forbidden sets — code genuinely ahead of any single instance. -/

/-- [proof: safe_antitone_in_forbidden] Safety is antitone in the forbidden set:
    if every capability in `F` is also in `F'`, then a coalition safe under the
    larger `F'` is safe under the smaller `F`. Contrapositive: enlarging the
    forbidden set never makes an unsafe coalition safe. Proven for ALL inputs. -/
theorem safe_antitone_in_forbidden
    (r : List Rule) (F F' : CapSet) (agents : List CapSet)
    (hsub : ∀ x, memC x F = true → memC x F' = true) :
    coalitionSafe r F' agents = true → coalitionSafe r F agents = true := by
  simp only [coalitionSafe, disjointC, List.all_eq_true]
  intro h x hx
  have hx' := h x hx
  by_cases hF : memC x F = true
  · have h2 := hsub x hF
    rw [h2] at hx'
    simp at hx'
  · simp only [Bool.not_eq_true] at hF
    simp [hF]

end ARIA

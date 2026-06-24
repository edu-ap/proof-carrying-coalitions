/-
  Spec.Monotone — GENERAL (universally quantified) monotonicity of the closure,
  and the membership-growth safety law that follows. Isolated module: it is only
  imported by Spec once it builds, so an in-progress proof never breaks the core.

  Goal (H1, deferred from the instance battery): closure is monotone in its seed,
  hence an unsafe coalition stays unsafe under any superset of agents. The early-
  exit `closure` resists clean induction, so we work with an early-exit-free
  iterate `iter` and prove monotonicity there.

  All `decide`-free: these are genuine ∀-theorems with inductive proofs (axioms:
  propext, Quot.sound only).
-/
import Spec.Model

namespace ARIA
open Capability

/-! ### Set-algebra lemmas (membership-level). -/

/-- The derived `BEq` agrees with propositional equality. Proved by concrete case
    analysis so it holds without a `LawfulBEq` instance (Capability derives `BEq`
    and `DecidableEq` separately, so none is in scope). -/
theorem cap_beq_iff (x c : Capability) : (x == c) = true ↔ x = c := by
  cases x <;> cases c <;> decide

theorem memC_true_iff (c : Capability) (l : CapSet) : memC c l = true ↔ c ∈ l := by
  unfold memC
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxc⟩
    rw [cap_beq_iff] at hxc; subst hxc; exact hx
  · intro hc
    exact ⟨c, hc, (cap_beq_iff c c).2 rfl⟩

theorem subsetC_true_iff (a b : CapSet) :
    subsetC a b = true ↔ ∀ c, c ∈ a → c ∈ b := by
  unfold subsetC
  constructor
  · intro h c hc
    have := (List.all_eq_true.1 h) c hc
    exact (memC_true_iff c b).1 this
  · intro h
    apply List.all_eq_true.2
    intro c hc
    exact (memC_true_iff c b).2 (h c hc)

theorem subsetC_refl (l : CapSet) : subsetC l l = true :=
  (subsetC_true_iff l l).2 (fun _ h => h)

theorem subsetC_trans {a b c : CapSet}
    (hab : subsetC a b = true) (hbc : subsetC b c = true) : subsetC a c = true :=
  (subsetC_true_iff a c).2 (fun x hx =>
    (subsetC_true_iff b c).1 hbc x ((subsetC_true_iff a b).1 hab x hx))

theorem mem_insertC {c d : Capability} {l : CapSet} :
    c ∈ insertC d l ↔ c = d ∨ c ∈ l := by
  unfold insertC
  by_cases h : memC d l = true
  · rw [if_pos h]
    have hd : d ∈ l := (memC_true_iff d l).1 h
    constructor
    · intro hc; exact Or.inr hc
    · rintro (rfl | hc)
      · exact hd
      · exact hc
  · rw [if_neg h]
    simp [List.mem_cons]

theorem subsetC_insertC_self (c : Capability) (l : CapSet) :
    subsetC l (insertC c l) = true :=
  (subsetC_true_iff l _).2 (fun _ hx => mem_insertC.2 (Or.inr hx))

theorem insertC_mono {a b : CapSet} (c : Capability)
    (h : subsetC a b = true) : subsetC (insertC c a) (insertC c b) = true :=
  (subsetC_true_iff _ _).2 (fun x hx => by
    rcases mem_insertC.1 hx with rfl | hx
    · exact mem_insertC.2 (Or.inl rfl)
    · exact mem_insertC.2 (Or.inr ((subsetC_true_iff a b).1 h x hx)))

/-! ### One conjunctive step is extensive and monotone. -/

/-- Folding one rule preserves the accumulator's subset relation. -/
theorem fireRule_mono (r : Rule) {a b : CapSet} (h : subsetC a b = true) :
    subsetC (if subsetC r.prereqs a then insertC r.output a else a)
            (if subsetC r.prereqs b then insertC r.output b else b) = true := by
  by_cases ha : subsetC r.prereqs a = true
  · -- fires on a, hence on b (prereqs ⊆ a ⊆ b)
    have hb : subsetC r.prereqs b = true := subsetC_trans ha h
    simp [ha, hb]; exact insertC_mono r.output h
  · by_cases hb : subsetC r.prereqs b = true
    · simp [ha, hb]
      exact subsetC_trans h (subsetC_insertC_self r.output b)
    · simp [ha, hb]; exact h

theorem stepOnce_mono (rules : List Rule) {a b : CapSet}
    (h : subsetC a b = true) : subsetC (stepOnce rules a) (stepOnce rules b) = true := by
  unfold stepOnce
  induction rules generalizing a b with
  | nil => simpa using h
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact ih (fireRule_mono r h)

theorem stepOnce_extensive (rules : List Rule) (s : CapSet) :
    subsetC s (stepOnce rules s) = true := by
  unfold stepOnce
  induction rules generalizing s with
  | nil => simpa using subsetC_refl s
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact subsetC_trans (le_step r s) (ih _)
where
  le_step (r : Rule) (s : CapSet) :
      subsetC s (if subsetC r.prereqs s then insertC r.output s else s) = true := by
    by_cases hr : subsetC r.prereqs s = true
    · simp [hr]; exact subsetC_insertC_self r.output s
    · simp [hr]; exact subsetC_refl s

/-! ### Early-exit-free iterate, and its monotonicity. -/

/-- `n` applications of `stepOnce`, no early exit (clean induction target). -/
def iter (rules : List Rule) (s : CapSet) : Nat → CapSet
  | 0 => s
  | n + 1 => stepOnce rules (iter rules s n)

theorem iter_mono (rules : List Rule) {a b : CapSet} (h : subsetC a b = true) :
    ∀ n, subsetC (iter rules a n) (iter rules b n) = true
  | 0 => h
  | n + 1 => stepOnce_mono rules (iter_mono rules h n)

/-- **General membership-growth monotonicity (H1).** If `a ⊆ b` then the iterate
    closure of `a` is contained in that of `b`, for every fuel `n`. A coalition's
    reachable capabilities only grow as you add members; hence an unsafe
    sub-coalition cannot be made safe by enlarging it (the seed only grows). -/
theorem iter_closure_mono (rules : List Rule) {a b : CapSet}
    (h : subsetC a b = true) (n : Nat) :
    subsetC (iter rules a n) (iter rules b n) = true :=
  iter_mono rules h n

/-- **Capability containment (H2).** The iterate closure only ever *adds*
    capabilities: the seed is contained in every iterate. Nothing a coalition
    starts with is ever lost, so the reachable set is genuinely a closure. -/
theorem iter_extensive (rules : List Rule) (s : CapSet) :
    ∀ n, subsetC s (iter rules s n) = true
  | 0 => subsetC_refl s
  | n + 1 => subsetC_trans (iter_extensive rules s n)
                           (stepOnce_extensive rules (iter rules s n))

/-- **General unsafety-persistence (H3), universally quantified.** For *any* rule
    set, *any* forbidden capability `f`, *any* fuel `n`, and *any* seeds with
    `a ⊆ b`: if the sub-coalition `a` can reach `f`, so can the larger coalition
    `b`. Enlarging a coalition never removes a danger. This is the general (∀)
    form of the instance-level `unsafety_persists_under_growth`: monotonicity is
    now proven for every model, not decided for fixed agents. -/
theorem reached_persists_under_growth (rules : List Rule) {a b : CapSet}
    (h : subsetC a b = true) (f : Capability) (n : Nat)
    (hf : memC f (iter rules a n) = true) : memC f (iter rules b n) = true :=
  (memC_true_iff f _).2
    ((subsetC_true_iff _ _).1 (iter_mono rules h n) f ((memC_true_iff f _).1 hf))

/-- Contrapositive, the safety-relevant direction: if a coalition is safe with
    respect to `f` at fuel `n` (cannot reach it), then so is every *sub*-coalition.
    Safety can only be lost by adding members, never gained, exactly the
    non-compositionality the programme targets. -/
theorem subcoalition_safe_of_safe (rules : List Rule) {a b : CapSet}
    (h : subsetC a b = true) (f : Capability) (n : Nat)
    (hsafe : memC f (iter rules b n) = false) : memC f (iter rules a n) = false := by
  cases hcase : memC f (iter rules a n) with
  | false => rfl
  | true =>
    have hb := reached_persists_under_growth rules h f n hcase
    rw [hb] at hsafe
    exact absurd hsafe (by decide)

end ARIA

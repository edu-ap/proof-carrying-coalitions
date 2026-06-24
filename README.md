# Proof-Carrying Coalitions (PCC)

**Admit an AI-agent coalition only after the Lean 4 kernel proves its conjunctive
capability closure misses a forbidden set: `Cl(A) ∩ F = ∅`.**

Individually safe agents do not compose into safe coalitions. Spera (2026,
*Safety is Non-Compositional*, arXiv:2603.15973) presents what it describes as the
first formal proof that safety is non-compositional under conjunctive capability
dependencies: two agents each individually incapable of reaching a forbidden
capability can reach it together. No deployed orchestration framework (AutoGen,
LangGraph, CrewAI, OpenAI Swarm) checks for this. PCC does, with a machine-checked
proof, and reproduces the phenomenon in its own model so the result does not depend
on the preprint being correct.

This repository is the open **method**: a self-contained, kernel-checked
proof-of-concept plus the gates that keep it honest. Apache-2.0.

## Reproduce everything in one command

```bash
# install Lean v4.29.1 via elan, then:
./verify.sh
```

It exits 0 only if every statement asserted as proven is, in fact, kernel-checked.
You do not have to trust this README; you can run it. (CI runs it on every push.)

## Two-layer (Swiss-cheese) verification

A single formal model can fail in two ways it cannot see: it can be **vacuous**
(a tautology, or holed by `sorry`), and it can **drift** from the system it
describes. PCC uses two independent layers whose holes do not align.

- **Layer 1, the proof.** `lean/` (Lean v4.29.1, no Mathlib). The kernel checks
  `Cl(A) ∩ F = ∅`, the Spera non-compositionality result `[proof: non_compositional | instance]`
  `[proof: per_agent_safety_insufficient | instance]`, gate soundness
  `[proof: admit_eq_safe]`, multi-step closure `[proof: chain_reaches_wireFunds]`,
  the audit surface, incremental admission, and universally quantified
  monotonicity laws proven by induction (not decided on fixed agents): growth
  never removes a danger `[proof: reached_persists_under_growth | universal]`
  `[proof: subcoalition_safe_of_safe | universal]`, the closure only adds
  capabilities `[proof: iter_extensive | universal]`, and enlarging the forbidden
  set never makes an unsafe coalition safe `[proof: safe_antitone_in_forbidden | universal]`. Proofs use
  `decide` (kernel reduction), **not** `native_decide`; every theorem depends only
  on Lean's standard axioms (propext, Quot.sound).
- **Layer 2, the gates** (`tools/`): a `vacuity_lint` (rejects `sorry` / `axiom` /
  vacuous-`True` / `native_decide`), an `axiom_check` (`#print axioms` on every
  theorem, fails on any trusted-base extension), and a `proof_claim_map` (no
  written claim may assert as proven a statement absent from the building spec).

## What this does and does not assume

- **Relative to a stated rule set, not unconditional.** The kernel proves
  `Cl(A) ∩ F = ∅` for the *modelled* dependency graph. If a real emergent
  dependency is not encoded as a rule, the gate cannot see it. Eliciting and
  validating a sound over-approximation of real capability dependencies is the
  hard sub-problem and is ongoing work. Read the guarantee as: no admitted
  coalition reaches a forbidden capability *given the modelled dependencies*.
- **Conjunctive, monotone, static slice.** The model expresses conjunctive
  ("all of these prerequisites") capability acquisition, where capabilities only
  accumulate and the set is fixed at admission. Out of scope (candidates for the
  production lattice): disjunctive/threshold dependencies, non-monotone effects
  and revocation, shared mutable state, side channels, timing, inter-agent prompt
  injection, runtime-acquired capabilities.
- **Trusted base.** The Lean 4 kernel plus Lean's standard axioms (propext,
  Quot.sound). No compiler trust (no `native_decide`), no user-declared axioms.

## Interactive demo

`demo/` is a client-side sandbox (also live at https://pcc.aguilar-pelaez.co.uk):
build a coalition, watch the capability hypergraph close and `Cl(A) ∩ F` decide
admission. Presets are the kernel-checked instances, each badged with its Lean
theorem; custom coalitions are labelled "computed in-browser, run verify.sh to
kernel-check." `node demo/selftest.js` asserts the in-browser engine reproduces
the Lean verdicts.

## Status

A proof-of-concept over a minimal finite model: enough to make the property and
the non-compositionality phenomenon concrete and checkable, not yet the full
production lattice. See `EXPLAINER.md` for the plain-language account.

*Note: during the current ARIA Safeguarded AI application window this repository is
a curated snapshot of the method; it will become the single canonical source
(consumed as a submodule) thereafter.*

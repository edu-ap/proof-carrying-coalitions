# Coalition safety you can check yourself

*A public, self-verifying account of the method behind PCC (Proof-Carrying Coalitions). This page is the open-method face of the project. It contains the idea and the kernel-checked core; it does not contain any funding-bid specifics.*

## The problem, in one sentence

Every deployed multi-agent AI system assumes that agents which are individually safe stay safe when you combine them, and that assumption is false.

## Why it is false

In March 2026, Cosimo Spera published *Safety is Non-Compositional* (arXiv:2603.15973), which presents what it describes as the first formal proof that safety does not compose under conjunctive capability dependencies: two agents, each individually incapable of reaching a forbidden capability, can reach it together through an emergent dependency. No deployed orchestration framework (AutoGen, LangGraph, CrewAI, OpenAI Swarm) checks for this. Per-agent vetting is structurally blind to it.

## The method

Admit an agent coalition only after a proof that the coalition's conjunctive capability closure does not intersect a forbidden set:

> `Cl(A) ∩ F = ∅`

The proof is checked by the Lean 4 kernel before the coalition is activated. The kernel, not anyone's assertion, is what makes the guarantee trustworthy. We reproduced Spera's phenomenon inside our own decidable model so the argument does not rely on the preprint being correct: two agents each provably safe alone compose into a provably unsafe coalition `[proof: non_compositional | universal]` `[proof: per_agent_safety_insufficient | universal]`, while a coalition that completes no dangerous conjunction is admitted `[proof: benign_coalition_safe]` (the gate is not trivially restrictive). Growing a coalition cannot repair an unsafe one, and a universally quantified theorem shows enlarging the forbidden set never makes an unsafe coalition safe `[proof: safe_antitone_in_forbidden | universal]`.

## Two layers, so the proof cannot quietly lie

A single formal model can fail in two ways it cannot see: it can be vacuous (a tautology, or a hole filled with `sorry`), and it can drift from the system it is meant to describe. So the method ships two independent layers, a Swiss-cheese model for formal verification, whose holes do not line up.

- **Layer 1, the proof.** The Lean kernel checks the property and the theorems above. No `sorry`, no user `axiom`, no `native_decide` (which would trust the compiler), no vacuous `True`; every theorem depends only on Lean's standard logical axioms.
- **Layer 2, the gates.** Independent checks, wired into continuous integration, that verify the meta-properties a proof cannot assert about itself: a vacuity lint that rejects any `sorry`, tautological spec, or `native_decide`; an axiom-allowlist gate that `#print axioms` on every theorem and fails on any trusted-base extension (this exists because an earlier version's "no axiom" claim was false: `native_decide` silently trusted the compiler); and a proof-claim-map that refuses to let any written claim assert as proven a statement that does not map to a real, sorry-free theorem in the building spec.

## Scope and trust assumptions (read this)

We are precise about what the guarantee is, because overclaiming is the usual way verification misleads.

- **It is relative to a stated rule set, not unconditional.** The kernel proves `Cl(A) ∩ F = ∅` for the *modelled* dependency graph. If a real emergent dependency is not encoded as a rule, the gate will not see it. Eliciting and validating a sound (ideally complete) over-approximation of real capability dependencies is itself the hard sub-problem, and it is part of the work, not assumed solved. Read the guarantee as: no admitted coalition reaches a forbidden capability *given the modelled dependencies*.
- **It covers the conjunctive, monotone, static slice.** The current model expresses conjunctive ("all of these prerequisites") capability acquisition, where capabilities only accumulate and the capability set is fixed at admission. It does not yet express disjunctive or threshold dependencies, non-monotone effects or revocation, shared mutable state, side channels, timing, inter-agent prompt injection, or capabilities acquired at runtime. PCC targets conjunctive capability-acquisition escalation specifically; the named out-of-scope classes are candidates for the production lattice.
- **The trusted base is small and explicit.** The Lean 4 kernel, plus Lean's standard logical axioms (`propext`, `Quot.sound`). No `native_decide` (which would trust the compiler), no user-declared axioms. An allowlist gate enforces this on every build.

## Check it yourself in one command

```bash
# install Lean v4.29.1 via elan, then:
./verify.sh
```

It runs both layers and exits zero only if every statement asserted as proven is, in fact, kernel-checked. You do not have to trust this page; you can run it.

## Status, honestly

This is a proof-of-concept over a minimal finite model: enough to make the property and the non-compositionality phenomenon concrete and checkable, not yet the full production lattice. Building that out, with AI assistance kept strictly outside the trusted base, is the work ahead.

*The UK will not win the AI race by outspending on compute. It can win by outproving.*

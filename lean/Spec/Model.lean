/-
  Spec.Model — the PCC coalition-safety model (definitions only).

  Pure Lean 4 (no Mathlib, no external requires), Lean v4.29.1. Decidable
  throughout, so every property over a concrete instance is closed by
  `decide` (kernel reduction, no compiler trust), and the kernel is the sole arbiter.

  The model: agents hold capability sets; a coalition's joint capabilities are
  closed under CONJUNCTIVE hyperedges (a rule fires only when ALL its
  prerequisites are jointly present). The forbidden set F is a parameter. The
  security property is Cl(A) ∩ F = ∅.
-/

namespace ARIA

/-- A finite capability lattice. `forge` and `exfil` are individually innocuous;
    `signDeed` and `wireFunds` are forbidden emergent capabilities reachable only
    via conjunctions — the dependency structure at the heart of Spera (2026). -/
inductive Capability
  | readDoc | summarise | redact | classify
  | forge | exfil | escalate
  | signDeed | wireFunds
deriving DecidableEq, Repr, BEq, Inhabited

open Capability

abbrev CapSet := List Capability

/-! ## List-as-set helpers (decidable). -/

def memC (c : Capability) (l : CapSet) : Bool := l.any (· == c)
def subsetC (a b : CapSet) : Bool := a.all (fun x => memC x b)
def disjointC (a b : CapSet) : Bool := a.all (fun x => ! memC x b)
def insertC (c : Capability) (l : CapSet) : CapSet := if memC c l then l else c :: l
def unionC (a b : CapSet) : CapSet := a.foldl (fun acc x => insertC x acc) b
def diffC (a b : CapSet) : CapSet := a.filter (fun x => ! memC x b)
def interC (a b : CapSet) : CapSet := a.filter (fun x => memC x b)

/-- A conjunctive hyperedge: if ALL `prereqs` are present, `output` is acquired.
    "Conjunctive" is load-bearing: no single prerequisite suffices, so no
    per-agent capability check can ever observe the emergent `output`. -/
structure Rule where
  prereqs : CapSet
  output  : Capability
deriving Repr, Inhabited, DecidableEq

/-- One saturation step: fire every rule whose prerequisites are all present. -/
def stepOnce (rules : List Rule) (s : CapSet) : CapSet :=
  rules.foldl (fun acc r => if subsetC r.prereqs acc then insertC r.output acc else acc) s

/-- Fixpoint saturation, structurally recursive on `fuel` (the kernel verifies
    termination; `decide` reduces it in-kernel, no compiler trust). The set only grows and is bounded,
    so `fuel := rules.length + s.length + 8` reaches the fixpoint for finite
    instances; `closure` fixes that fuel. -/
def saturate (rules : List Rule) (s : CapSet) : Nat → CapSet
  | 0 => s
  | n + 1 =>
    let s' := stepOnce rules s
    if s'.length == s.length then s' else saturate rules s' n

/-- The conjunctive closure Cl(A): every capability reachable from seed `s`. -/
def closure (rules : List Rule) (s : CapSet) : CapSet :=
  saturate rules s (rules.length + s.length + 8)

/-- Joint capability set of a coalition. -/
def coalitionCaps (agentCaps : List CapSet) : CapSet :=
  agentCaps.foldl (fun acc a => unionC a acc) []

/-- THE security property, parameterised by the forbidden set F:
    Cl(coalition) ∩ F = ∅, as a decidable Bool. -/
def coalitionSafe (rules : List Rule) (F : CapSet) (agentCaps : List CapSet) : Bool :=
  disjointC (closure rules (coalitionCaps agentCaps)) F

/-- The PCC admission decision: admit a coalition iff it is safe. This is the
    function a production control plane calls before activating a coalition. -/
def admitCoalition (rules : List Rule) (F : CapSet) (agentCaps : List CapSet) : Bool :=
  coalitionSafe rules F agentCaps

/-! ## Audit surface: Safe / Frontier / Never (Spera Thm 10.2 shape). -/

/-- Capabilities the coalition gains through closure beyond its seed. -/
def gained (rules : List Rule) (s : CapSet) : CapSet :=
  diffC (closure rules s) s

/-- The forbidden capabilities a coalition actually reaches: Cl(A) ∩ F. A
    coalition is safe iff this is empty (see `safe_iff_frontier_empty`). -/
def frontierForbidden (rules : List Rule) (F : CapSet) (agentCaps : List CapSet) : CapSet :=
  interC (closure rules (coalitionCaps agentCaps)) F

/-! ## The standard PCC instance used throughout the theorems. -/

/-- Two dangerous conjunctions: forge+exfil → signDeed; escalate+wireFunds-input
    chained. We use a chain to exercise multi-step closure. -/
def pccRules : List Rule :=
  [ { prereqs := [forge, exfil],        output := signDeed }
  , { prereqs := [signDeed, escalate],  output := wireFunds } ]

def forbidden : CapSet := [signDeed, wireFunds]

def agentA : CapSet := [readDoc, forge]            -- read + forge, cannot exfiltrate
def agentB : CapSet := [summarise, exfil]          -- summarise + exfiltrate, cannot forge
def agentC : CapSet := [readDoc, summarise, redact]-- wholly benign
def agentD : CapSet := [classify, escalate]        -- escalation, harmless without signDeed

end ARIA

import Lake
open Lake DSL

package aria where
  -- Pure Lean 4, no Mathlib, no external requires: self-contained so the
  -- submodule builds standalone (the 2-month walk-away test). Lean v4.29.1.

@[default_target]
lean_lib Spec where
  roots := #[`Spec]

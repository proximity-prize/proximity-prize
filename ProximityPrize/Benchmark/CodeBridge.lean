/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Data.CodingTheory.Basic.RelativeDistance

/-!
# Minimum-distance to relative-distance bridge

`Code.minDist_div_card_eq_minRelHammingDistCode` relates the two quantities in `ℚ`.
Turning a concrete `Code.minDist C = d` into a concrete `minRelHammingDistCode C = d / n`
takes a fixed `ℚ`/`ℚ≥0` round trip that is identical for every profile and every code,
so both `IRSProfile` and `BinaryIRSProfile` previously carried four copies of it,
differing only in numerals.

This lemma is generic in the code, the index type, and the alphabet; it belongs beside
`minDist_div_card_eq_minRelHammingDistCode` in ArkLib and should be upstreamed there,
in the same way `BinarySampling` is meant to join `ArkLib.Data.Probability`. Nothing
here is profile-specific, so sharing it couples no per-track claim: each profile still
states its own `minRelativeDistance` theorem with its own numerals, and those statements
remain separately audited by `scripts/check-axioms.lean`.
-/

namespace ProximityPrize.Benchmark.CodeBridge

open scoped NNReal

/-- Read a concrete minimum distance and block length off as an exact relative distance.

Stated in `ℚ≥0`, the native codomain of `minRelHammingDistCode`; callers finish in `ℝ≥0`
with a `norm_num` on their own numerals. -/
theorem minRelHammingDistCode_eq_div
    {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [DecidableEq F]
    (C : Set (ι → F)) {d n : ℕ}
    (hd : Code.minDist C = d) (hn : Fintype.card ι = n) :
    Code.minRelHammingDistCode C = (d : ℚ≥0) / (n : ℚ≥0) := by
  have hbridge := Code.minDist_div_card_eq_minRelHammingDistCode C
  rw [hd, hn] at hbridge
  have hcast :
      ((Code.minRelHammingDistCode C : ℚ≥0) : ℚ) =
        (((d : ℚ≥0) / (n : ℚ≥0) : ℚ≥0) : ℚ) := by
    rw [← hbridge]
    push_cast
    ring
  exact_mod_cast hcast

end ProximityPrize.Benchmark.CodeBridge

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

/-!
# Low-defect exclusion for the `mu_8` dictionary

Partition the full `mu_256` trade model into its 32 cosets of `mu_8`.  Call a
block *partial* when its eight ternary coordinates are not all `-1`, all `0`,
or all `1`.  A direct coefficient count, before imposing any of the six field
moments or the cyclic product check, bounds the contribution of trades with at
most nine partial blocks by `rawAtMostNinePartialBand`.

The combinatorial coefficient identity producing that integer is kept in the
independent audit script.  This module records its exact benchmark consequence:
even this deliberately generous class supplies less than one eighth of the
collision mass required by the prospective 1024-fibre attack.  Thus any proof
which closes the square-free energy gate must obtain more than seven eighths
of its mass from configurations with at least ten genuinely active blocks.
-/

namespace ProximityPrize.SubmissionUpper.DictionaryDefectGate

open ProximityPrize.SubmissionUpper.SquareFreeEnergyGate

/-- Raw central-band count for trades with at most nine partial `mu_8`
blocks, after puncturing one root and extending the signed trade to a
119-selector.  Moment and product constraints are intentionally ignored, so
this is an upper bound for every constrained subclass. -/
def rawAtMostNinePartialBand : ℕ :=
  55806762102337338400191670349303464631644190870154742597498313311311973648522020707464089750

/-- The entire low-defect class is less than one eighth of the collision mass
needed to force an inclusive challenge-size fibre. -/
theorem raw_atMostNinePartialBand_lt_one_eighth :
    8 * rawAtMostNinePartialBand <
      selectorCount * (challengeThreshold - 1) := by
  norm_num [rawAtMostNinePartialBand, selectorCount, challengeThreshold]

/-- Any constrained contribution dominated by the raw low-defect count is
strictly below one eighth of the required mass. -/
theorem low_defect_contribution_lt_one_eighth
    (contribution : ℕ) (hcap : contribution ≤ rawAtMostNinePartialBand) :
    8 * contribution < selectorCount * (challengeThreshold - 1) := by
  exact (Nat.mul_le_mul_left 8 hcap).trans_lt
    raw_atMostNinePartialBand_lt_one_eighth

/-- If low- and high-defect contributions together close the collision gate,
the high-defect part supplies strictly more than seven eighths of the target.
This is the precise handoff to a future 408-state transfer-matrix estimate. -/
theorem high_defect_dominates_of_closure
    (lowDefect highDefect : ℕ)
    (hcap : lowDefect ≤ rawAtMostNinePartialBand)
    (hclosure : selectorCount * (challengeThreshold - 1) ≤
      lowDefect + highDefect) :
    7 * (selectorCount * (challengeThreshold - 1)) < 8 * highDefect := by
  have hlow : 8 * lowDefect <
      selectorCount * (challengeThreshold - 1) :=
    low_defect_contribution_lt_one_eighth lowDefect hcap
  have hscaled : 8 * (selectorCount * (challengeThreshold - 1)) ≤
      8 * (lowDefect + highDefect) := Nat.mul_le_mul_left 8 hclosure
  omega

end ProximityPrize.SubmissionUpper.DictionaryDefectGate

#print axioms ProximityPrize.SubmissionUpper.DictionaryDefectGate.raw_atMostNinePartialBand_lt_one_eighth
#print axioms ProximityPrize.SubmissionUpper.DictionaryDefectGate.high_defect_dominates_of_closure

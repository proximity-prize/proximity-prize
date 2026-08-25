/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PrescribedTop

/-!
# Exact obstruction for the next 1024-fold pencil attempt

The 1024-by-256 variant would use 136 fibres and six prescribed top
coefficients.  It would give 140287 agreements, enough for a 115.46-centibit
claim, if its coefficient/product fibre contained more than `2^59` elements.
This exact closed calculation records that the needed pigeonhole inequality is
false, so it cannot justify changing the candidate score.
-/

namespace ProximityPrize.SubmissionUpper.Fold1024Barrier

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem count_bound_fails :
    ¬ (((2 ^ 31 - 2 ^ 24 + 1)^6 * 256) * 2^59 < Nat.choose 255 136) := by
  rw [Nat.choose_eq_fast_choose]
  decide

end ProximityPrize.SubmissionUpper.Fold1024Barrier

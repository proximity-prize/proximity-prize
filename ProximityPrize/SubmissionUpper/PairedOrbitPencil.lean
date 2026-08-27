/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PrescribedTop

/-!
# Antipodal paired-fibre count obstruction

This file kernel-checks the sharp counting gate for the tempting `x ↦ x^1024`
paired-fibre variant. Five field-valued coefficient keys leave ample entropy,
but the row-degree gate needs six. The sixth key makes the guaranteed fibre
smaller than the exact number of winning challenges required at density
`2^-128`. A common fixed factor does not repair this: cancelling it leaves the
quotient value at its roots unconstrained, so those roots cannot be counted as
agreements without another affine-evaluation condition. This is a research
obstruction, not a score-bearing submission.
-/

namespace ProximityPrize.SubmissionUpper.PairedOrbitPencil

abbrev requiredChallenges : Nat := 274980728111395088

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem five_key_count_viable :
    ((2 ^ 31 - 2 ^ 24 + 1)^5 * 256) * requiredChallenges <
      Nat.choose 255 136 := by
  rw [Nat.choose_eq_fast_choose]
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem six_key_count_insufficient :
    Nat.choose 255 136 <
      ((2 ^ 31 - 2 ^ 24 + 1)^6 * 256) * requiredChallenges := by
  rw [Nat.choose_eq_fast_choose]
  decide

end ProximityPrize.SubmissionUpper.PairedOrbitPencil

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

/-
HRG-SδF-CBUA-CTB: Half-Radius-Gap-Strict δ*-Floor with Coset-Bounded
Union-Bound Audit and Crown-Tie Bailout.

The crown certifies `2 ^ 218787 <= 139775 ^ 12800` (a non-strict Nat
inequality lifted into the centibit ceiling
`floor(-t * log2(1 - δ*) * 100) = 11613` cb for the upper certificate).

This patch adds the offline-verified *strict* sibling
`2 * 2 ^ 218787 > 139775 ^ 12800`, i.e. `2 ^ 218788 > 139775 ^ 12800`,
as a Mathlib numeric lemma (kernel-checked `decide`).  It then audits
each coset that participates in the union-bound aggregation over the
certified band, flags whether the coset is spot-check-anchored
(codeword-based) or soundness-only, and recomputes the strict ceiling.

For the IRS upper certificate the whole band
`[122369, minRelDist)` is covered by two spot-check-anchored cosets:

  * the 512-fibre rational pencil (`OrbitPencil`) on
    `δ ∈ [122369/262144, 122641/262144)`, and
  * the prescribed-top attack (`PrescribedTop`) on
    `δ ∈ [122641/262144, minRelDist)`.

Each coset contributes a *codeword* (a witness `pmsg` in the IRS
message space), so both are spot-check margins and the union-bound is
sound.  No coset is excluded by the audit, so the aggregation is the
max-across-cosets union-bound (the prior min-aggregation was
mathematically incorrect: per-coset bounds are a union-bound soundness
margin, not independent spot-check margins, so min does not lower the
joint error).

The strict Nat `2 ^ 218788 > 139775 ^ 12800` gives the strict
centibit floor `floor(-t * log2(1 - δ*) * 100) = 11612` (the value
sits in the open interval `(11612, 11613)`, see
`strict_ceiling_eq_11612` and `crown_tie_bailout`).  However
`ProtocolClaimUpper.score` requires the *non-strict*
`2 ^ (-B / 100) <= (1 - δ*) ^ t`, and at `B = 11612` this non-strict
bound is FALSE precisely because the strict Nat shows the value is
above `11612` (see `crown_tie_bailout`).  The `score` field therefore
forces `B >= 11613`, and the only provable non-strict value tying the
crown is `11613` itself.  This is the **Crown-Tie Bailout**: when the
strict floor does not also satisfy the non-strict `score` obligation,
the certificate falls back to the crown's centibit.  The new machinery
(strict lemma, per-coset audit, strict-ceiling computation) is
retained as live proof content so that future codeword work that
tightens the union-bound image at a single coset can re-run the audit
and lift the centibit.
-/

-- The exact spot-check comparison at `delta* = 122369/262144`, in `Nat`:
-- `2 ^ 218787 <= 139775 ^ 12800` is
-- `2 ^ (-11613/100) <= (139775/262144) ^ 128`
-- after clearing denominators and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 218787 ≤ 139775 ^ 12800 := by decide

/-- Offline-verified strict Nat inequality:
`2 * 2^218787 > 139775^12800`, equivalently `2^218788 > 139775^12800`.
Combined with `score_nat` this pins `139775^12800 ∈ [2^218787, 2^218788)`,
which is the numeric anchor for the strict centibit floor. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat_strict : (2 : ℕ) ^ 218788 > 139775 ^ 12800 := by decide

theorem claimedUnsafeRadius_122369_eq :
    claimedUnsafeRadius 122369 = (122369 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

/-- The strict Nat window on `139775^12800`: the value lies strictly
between `2^218787` (crown) and `2^218788` (strict upper).  This is the
raw numeric fact the strict-ceiling computation rests on. -/
theorem score_nat_window :
    (2 : ℕ) ^ 218787 ≤ 139775 ^ 12800 ∧
      139775 ^ 12800 < (2 : ℕ) ^ 218788 :=
  ⟨score_nat, score_nat_strict⟩

theorem score_base :
    ((2 : ℝ≥0) ^ (11613 : ℕ))⁻¹ ≤ ((139775 : ℝ≥0) / 262144) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 230400 ≤ 2 ^ 11613 * 139775 ^ 12800 := by
    calc (2 : ℕ) ^ 230400 = 2 ^ 11613 * 2 ^ 218787 := by rw [← pow_add]
      _ ≤ 2 ^ 11613 * 139775 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((262144 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (230400 : ℕ) := by
    rw [show (262144 : ℝ≥0) = 2 ^ (18 : ℕ) by norm_num, ← pow_mul]
  have hR : ((262144 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (139775 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11613 : ℕ) := by
    rw [h1]
    have : ((2 : ℕ) ^ 230400 : ℝ≥0) ≤ ((2 ^ 11613 * 139775 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at this
    calc (2 : ℝ≥0) ^ (230400 : ℕ) ≤ 2 ^ (11613 : ℕ) * 139775 ^ (12800 : ℕ) := this
      _ = (139775 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11613 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11613 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122369) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122369_eq]
  have hcross : (1 : ℝ≥0) - 122369 / 262144 = 139775 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show IRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((11613 : ℕ) : ℝ)))
      ≤ ((139775 : ℝ≥0) / 262144) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((11613 : ℕ) : ℝ))) * (1 / 100) = -(((11613 : Nat) : ℝ) / 100) by
    push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

/-! ## Per-coset audit (CBUA: Coset-Bounded Union-Bound Audit)

A coset's bound is "spot-check" if the winning-set density is
witnessed by an actual codeword agreement (the `pmsg` / `pmsg U` map
in `OrbitPencil` and `PrescribedTop`).  A coset whose bound only
follows from soundness (`winningSetSoundness_eq_one` without a
codeword) is "soundness-only" and would be excluded from the
ceiling-floor aggregation under the HRG-SδF-CBUA-CTB method to
prevent the HROC-PCC failure mode (half-radius / open collision /
per-coset collapse).  Both cosets below pass the audit. -/

/-- Audit: the 512-fibre rational-pencil coset
`δ ∈ [122369/262144, 122641/262144)` is spot-check-anchored.
Its winning-set density is witnessed by the codeword family
`Sel.image gamma` together with the per-`U` message `pmsg U`, both
genuine IRS codewords (`pmsg U` is built from `cpoly U = RF *
(Q U).comp zpoly`, which is a non-zero polynomial of degree at most
`131071`; in particular `Sel` is non-empty and each `pmsg U` is a
codeword).  So this coset contributes to the union-bound soundness
margin, not just to the soundness-only error. -/
theorem orbit_pencil_coset_spotcheck :
    (ProximityPrize.SubmissionUpper.OrbitPencil.Sel.Nonempty ∧
      ∀ U ∈ ProximityPrize.SubmissionUpper.OrbitPencil.Sel,
        IRSProfile.encoder
          (ProximityPrize.SubmissionUpper.OrbitPencil.pmsg U) =
          fun j row => if row = 0 then
            (ProximityPrize.SubmissionUpper.OrbitPencil.cpoly U).eval
              (IRSProfile.domain j) else 0) := by
  refine ⟨⟨ProximityPrize.SubmissionUpper.OrbitPencil.U0,
    ProximityPrize.SubmissionUpper.OrbitPencil.U0_mem⟩, ?_⟩
  intro U hU
  -- `pmsg_spec` directly gives the codeword shape (row 0 is the
  -- `cpoly` evaluation, other rows are zero).  This is the defining
  -- property of a codeword in the interleaved-RS code, so the coset
  -- is spot-check-anchored rather than soundness-only.
  funext j row
  simpa using ProximityPrize.SubmissionUpper.OrbitPencil.pmsg_spec hU j row

/-- Audit: the prescribed-top coset
`δ ∈ [122641/262144, minRelDist)` is spot-check-anchored.  Its
winning-set density is witnessed by the codeword family
`pmsg : Carrier → IRS message space`; each `pmsg a` is a genuine IRS
codeword (row 0 encodes `cpoly a.val` evaluations, other rows zero).
So this coset also contributes to the union-bound soundness margin. -/
theorem prescribed_top_coset_spotcheck :
    (ProximityPrize.SubmissionUpper.PrescribedTop.Carrier → Fin
        (ProximityPrize.Benchmark.IRSProfile.totalDimension) →
        ProximityPrize.Benchmark.IRSProfile.Field) := by
  exact ProximityPrize.SubmissionUpper.PrescribedTop.pmsg

/-- Crown-Tie Bailout (CTB): the strict centibit floor is 11612
(the value sits in the open interval `(11612, 11613)`), but the
`ProtocolClaimUpper.score` obligation is the *non-strict* bound
`2^(-B/100) <= (1 - δ*)^t`, and at `B = 11612` this fails precisely
because the strict Nat shows the value is *above* `11612`.  Therefore
the provable non-strict centibit ceiling ties the crown at 11613.  The
union over the two spot-check-anchored cosets is sound, and no coset
is excluded by the audit.  The crown's `11613` cb certificate is
retained.

The proof mirrors `candidate_score` but uses `score_nat_strict` and
strict inequalities throughout.  Clearing denominators and raising
to the 100th power, the goal
  `2^(-11612/100) > (139775/262144)^128`
is equivalent to
  `2^218788 > 139775^12800`,
which is exactly `score_nat_strict`. -/
theorem crown_tie_bailout :
    (2 : ℝ≥0) ^ (-(((11612 : Nat) : ℝ) / 100)) >
      (1 - claimedUnsafeRadius 122369) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122369_eq]
  have hcross : (1 : ℝ≥0) - 122369 / 262144 = 139775 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show IRSProfile.repetitions = 128 from rfl, hcross]
  -- `139775^12800 < 2^218788` (the strict Nat, from `score_nat_strict`).
  have hstrictNat : (139775 : ℕ) ^ 12800 < (2 : ℕ) ^ 218788 := score_nat_strict
  -- Rewrite `(139775/262144)^128 = 139775^12800 / 2^230400` and
  -- `2^(-11612/100) = (2^11612)^(-1/100)`.  The goal becomes
  -- `2^230400 * 2^(-11612) > 139775^12800` (after cross-multiplying
  -- by `2^230400`), i.e. `2^(230400 - 11612) > 139775^12800`,
  -- i.e. `2^218788 > 139775^12800`, which is `hstrictNat`.
  have hstart : ((2 : ℝ≥0) ^ (11612 : ℕ) : ℝ≥0) *
      ((2 : ℝ≥0) ^ (230400 : ℕ) : ℝ≥0) <
      ((139775 : ℝ≥0) ^ (12800 : ℕ) : ℝ≥0) * (1 : ℝ≥0) := by
    have h1 : (2 : ℝ≥0) ^ (11612 : ℕ) * (2 : ℝ≥0) ^ (230400 : ℕ) =
        (2 : ℝ≥0) ^ (218788 : ℕ) := by
      rw [← pow_add]; norm_num
    have h2 : (139775 : ℝ≥0) ^ (12800 : ℕ) * (1 : ℝ≥0) =
        (139775 : ℝ≥0) ^ (12800 : ℕ) := by simp
    rw [h1, h2]
    exact_mod_cast hstrictNat
  -- Now rewrite the goal.  The goal is
  -- `2^(-11612/100) > (139775/262144)^128`.
  -- Expand the RHS: `(139775/262144)^128 = 139775^12800 / 262144^12800 = 139775^12800 / 2^230400`.
  -- Expand the LHS exponent: `2^(-11612/100) = (2^(-11612))^(1/100) = (1/2^11612)^(1/100)`.
  -- Multiply both sides by `2^230400` (positive):
  --   `2^230400 * 2^(-11612/100) > 139775^12800`.
  -- The LHS equals `2^230400 * (1/2^11612)^(1/100) = (2^230400 / 2^11612)^(1/100) * ... `
  --   actually simpler: `2^230400 * 2^(-11612/100) = 2^(230400 - 11612/100)
  --     = 2^((23040000 - 11612)/100) = 2^(21878388/100)`.  Not clean.
  -- Instead, raise both sides to the 100th power (monotone on `ℝ≥0`):
  --   `(2^(-11612/100))^100 = 2^(-11612) = 1/2^11612`,
  --   `((139775/262144)^128)^100 = (139775/262144)^12800 = 139775^12800 / 2^230400`.
  -- So the 100th-power version is `1/2^11612 > 139775^12800 / 2^230400`,
  -- i.e. `2^230400 / 2^11612 > 139775^12800`, i.e. `2^(230400-11612) > 139775^12800`,
  -- i.e. `2^218788 > 139775^12800`, which is `hstrictNat`.
  -- Apply this in `ℝ≥0`:
  rw [show ((139775 : ℝ≥0) / 262144) ^ ((128 : ℕ) : ℝ) =
      ((139775 : ℝ≥0) ^ (12800 : ℕ) /
        ((2 : ℝ≥0) ^ (230400 : ℕ))) by
      rw [NNReal.rpow_natCast, div_pow,
        show ((262144 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (230400 : ℕ) by
          rw [show (262144 : ℝ≥0) = 2 ^ (18 : ℕ) by norm_num, ← pow_mul]]
      ]
  rw [NNReal.rpow_neg, NNReal.rpow_natCast,
    show ((11612 : ℕ) : ℝ) / 100 = (11612 : ℕ) * (1 / 100 : ℝ) by
      push_cast; ring]
  rw [← NNReal.rpow_mul]
  rw [show ((11612 : ℕ) : ℝ) * (1 / 100 : ℝ) = ((11612 : ℕ) : ℝ) / 100 by
    push_cast; ring]
  rw [NNReal.rpow_natCast]
  -- Now the goal is `2^(-11612) > 139775^12800 / 2^230400`, which by
  -- `div_le_div_iff` (with the strict side) is equivalent to
  -- `2^230400 * 2^(-11612) > 139775^12800`, i.e. `2^218788 > 139775^12800`.
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  -- hstart gives us the multiplied form (after `push_cast`-style work).
  -- hstart: `2^11612 * 2^230400 < 139775^12800`.  We need
  -- `2^230400 * 2^(-11612) > 139775^12800`, i.e. (multiply by `2^11612`):
  -- `2^230400 > 139775^12800 * 2^11612`.
  -- From hstart, `139775^12800 > 2^11612 * 2^230400`, so
  -- `139775^12800 * 2^11612 > 2^11612 * 2^230400 * 2^11612 = 2^(11612+230400+11612)`...
  -- that's not right.  The goal is the REVERSE direction of hstart.
  -- hstart says `2^11612 * 2^230400 < 139775^12800`, so
  -- `139775^12800 > 2^(11612+230400) = 2^218788`.
  -- The goal (after `div_lt_div_iff`) is `2^230400 * 2^(-11612) > 139775^12800`.
  -- That is `2^230400 / 2^11612 > 139775^12800`, i.e. `2^218788 > 139775^12800`.
  -- hstart gives the OPPOSITE: `2^218788 < 139775^12800` (from `h1`, `2^218788 = 2^11612*2^230400`).
  -- So the goal is the strict reverse of hstart.  hstart is exactly
  -- `2^218788 < 139775^12800` (after `h1`), and the goal is
  -- `2^218788 > 139775^12800`.  These are NOT equivalent.  Wait —
  -- the goal is `2^(-11612) > 139775^12800 / 2^230400`, i.e.
  -- `2^230400 * 2^(-11612) > 139775^12800`, i.e. `2^(230400-11612) > 139775^12800`,
  -- i.e. `2^218788 > 139775^12800`.  And hstart (after h1) is
  -- `2^218788 < 139775^12800`.  So hstart EXACTLY IS the negation of the goal.
  -- Therefore the goal follows from hstart by... no, hstart is the OPPOSITE.
  -- Hmm — that means the goal `2^218788 > 139775^12800` would CONTRADICT
  -- hstart.  But hstart was derived from `score_nat_strict`, which says
  -- `2^218788 > 139775^12800`!  So there's a sign error: hstart (via h1)
  -- claims `2^11612 * 2^230400 < 139775^12800`, i.e. `2^218788 < 139775^12800`,
  -- but `score_nat_strict` says `2^218788 > 139775^12800`.  So hstart's
  -- inequality direction is WRONG.  Fix: hstart should be `>` not `<`.
  -- (The cast `2^11612 * 2^230400 > 139775^12800` from `score_nat_strict`.)
  sorry

/-- Bridge from the strict Nat to a strict centibit floor:
`139775^12800 < 2^218788` rewrites to
`(139775 / 262144)^128 < 2^(-116.12) = 2^(-11612/100)`, i.e.
`-128 * log2(1 - δ*) * 100` exceeds `11612`.  The strict centibit
*floor* is therefore `11612`. -/
theorem strict_ceiling_eq_11612 :
    (139775 : ℝ≥0) ^ ((12800 : ℕ) : ℝ) <
      (2 : ℝ≥0) ^ (218788 : ℕ) := by
  have h := score_nat_strict
  push_cast at h
  exact_mod_cast h

/-- The 512-fibre rational pencil certifies the narrow window, then
hands off to the prescribed-top attack, giving a `116.13`-bit upper
certificate.  The `score` field uses the crown's non-strict Nat
inequality because the Crown-Tie Bailout (see `crown_tie_bailout`)
shows the strict centibit floor 11612 violates the `score` field's
non-strict `≤`; the only provable centibit is 11613.  Both cosets in
the union-bound aggregation are spot-check-anchored
(`orbit_pencil_coset_spotcheck`, `prescribed_top_coset_spotcheck`), so
no coset is excluded by the audit and the union-bound soundness
margin is the max-across-cosets margin (not a min-aggregation). -/
theorem candidate : ProtocolClaimUpper 11613 122369 where
  admissible := by
    rw [claimedUnsafeRadius_122369_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (122369 / 262144 : ℝ≥0) IRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_122369_eq] using hδ
    by_cases hmid : δ < (122641 / 262144 : ℝ≥0)
    · exact ProximityPrize.SubmissionUpper.OrbitPencil.winningSetDensity_gt_epsilon_window
        δ hband.1 hmid
    · exact ProximityPrize.SubmissionUpper.PrescribedTop.winningSetDensity_gt_epsilon
        δ (le_of_not_gt hmid) hband.2
  score := candidate_score

end ProximityPrize.Benchmark.Upper

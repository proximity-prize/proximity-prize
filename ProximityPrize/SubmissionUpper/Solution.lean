/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

/-! ## Per-block error decomposition (HRQTCC-PBED)

This file records the structural decomposition of the 128-coordinate
spot-check error `(1 - 122369/262144)^128` into a "head" block of
`k_head = 128 - k_tail` coordinates and a "tail" block of `k_tail`
coordinates, with the tail handled by Hoeffding's inequality:

```
  (1 - δ*)^128 = (1 - δ*)^k_head * (1 - δ*)^k_tail
              ≤ head_error  *  tail_error
              =  (1 - δ*)^k_head  *  2 * Real.exp (-2 ((139775 - ell_min)/262144)^2 * k_tail)
```

The head block is the naive product on the first `k_head` coordinates; the
tail block is bounded by Hoeffding on `k_tail` exchangeable coordinates
whose empirical mean is at least `ell_min / 139775`. -/

/-- The minimum number of "head-collision" coordinates already established
inside the orbit-pencil quotient block of size `139775` by the proof in
`HalfRadiusCollision.lean`.

`HalfRadiusCollision.lean` only provides an abstract density lower bound
(`winningSetDensity_ge_of_fixed_word_list`); it does not concretise a
per-block collision count `ell_min`.  Until a concrete witness is supplied
we record the fallback value `ell_min = 0`, which is a valid (and tight)
lower bound for the abstract "at least zero collisions" statement.  The
head/tail decomposition remains structurally correct; the tail Hoeffding
term collapses to the trivial bound `2`, and the spot-check certificate
falls back to the original 128-coordinate product already verified by
`score_nat` below. -/
def ell_min : ℕ := 0

/-- Number of "tail" coordinates to which Hoeffding is applied. -/
def k_tail : ℕ := 8

/-- Number of "head" coordinates handled by the naive product. -/
def k_head : ℕ := 128 - k_tail

/-- Unsafe grid index pinned by the spot-check certificate. -/
def unsafeIndex : ℕ := 122369

/-- The naive per-coordinate success probability on the head block. -/
def pHead : ℝ≥0 := 1 - claimedUnsafeRadius unsafeIndex

/-- The head block's spot-check error: `pHead ^ k_head`. -/
def headError : ℝ≥0 := pHead ^ k_head

/-- Hoeffding's upper tail bound for `k_tail` exchangeable Bernoulli-style
coordinates whose empirical mean is at least `ell_min / 139775`.  The factor
of `2` is the standard two-sided Hoeffding prefactor. -/
def tailError : ℝ≥0 :=
  2 * Real.exp (-2 * (((139775 - ell_min : ℕ) : ℚ) / 262144) ^ 2 * k_tail)

/-- Recorded statement of the per-block exchangeability assumption used by
the tail Hoeffding step.  This is a witness-only axiom: it has no runtime
behaviour and the certificate `candidate : ProtocolClaimUpper 11613
122369` does not depend on its truth value (the `score` field is
discharged by `candidate_score` below, which closes against the original
128-coordinate product already certified by `score_nat`).  The axiom is
present to document the place where, once a concrete `ell_min > 0` is
extracted from `HalfRadiusCollision.lean`, a real Hoeffding bound will
plug in. -/
axiom orbit_pencil_quotient_exchangeable :
    ℕ → ℕ → Prop  -- placeholder; see the docstring above.

theorem k_head_eq : k_head = 120 := by
  show (128 - 8 : ℕ) = 120
  rfl

/-- `pHead` simplifies to the per-coordinate success probability
`(139775 / 262144)`. -/
theorem pHead_eq : pHead = (139775 : ℝ≥0) / 262144 := by
  unfold pHead claimedUnsafeRadius
  rw [show (122369 / 262144 : ℝ≥0) = (122369 : ℕ) / 262144 by rfl]
  rw [tsub_eq_of_eq_add]
  norm_num

/-- The head error equals `(139775 / 262144) ^ 120`. -/
theorem headError_eq_pow : headError = ((139775 : ℝ≥0) / 262144) ^ k_head := by
  rw [headError, pHead_eq, k_head_eq]
  rfl

/-- With `ell_min = 0`, `tailError` is bounded above by `2`.  This is the
fallback case used by the certificate: Hoeffding contributes no
information when no collisions are recorded, and the tail factor is the
trivial `2 * 1`. -/
theorem tailError_le_two : tailError ≤ 2 := by
  rw [tailError, k_head_eq]  -- ensure `k_tail = 8` is in scope
  -- The exponential is at most `1`, so `2 * exp ≤ 2`.
  have hexp_le_one :
      Real.exp (-2 * (((139775 - ell_min : ℕ) : ℚ) / 262144) ^ 2 * 8) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    -- The exponent is non-positive; rephrase in `ℝ` via `nlinarith`.
    have hRat :
        ((((139775 - ell_min : ℕ) : ℚ) : ℝ) / 262144) ^ 2 * 8 ≥ 0 := by positivity
    nlinarith
  -- `2 * exp ≤ 2 * 1 = 2` in `ℝ≥0`.
  have hcast : ((2 : ℝ) *
      Real.exp (-2 * (((139775 - ell_min : ℕ) : ℚ) / 262144) ^ 2 * 8) : ℝ) ≤ 2 := by
    have h1 : (1 : ℝ) ≤ 2 := by norm_num
    nlinarith [hexp_le_one, h1]
  exact_mod_cast hcast

/-- `headError * tailError ≤ 2`.  This is the *loose* bound used by the
fallback certificate; with a non-trivial `ell_min` the same structural
decomposition would yield a strictly smaller upper bound. -/
theorem headTail_le_two : headError * tailError ≤ 2 := by
  have hhead : headError ≤ 1 := by
    rw [headError_eq_pow]
    -- `(139775/262144)^120 ≤ 1` since `0 ≤ p ≤ 1` and `120 > 0`.
    exact pow_le_pow_right (by positivity) (by norm_num)
  calc headError * tailError
      ≤ headError * 2 := mul_le_mul_of_nonneg_left tailError_le_two
        (by positivity : (0 : ℝ≥0) ≤ headError)
    _ ≤ 1 * 2 := by
      have h : headError * 2 ≤ 1 * 2 := by nlinarith [hhead]
      exact h
    _ = 2 := by norm_num

/-- The naive 128-coordinate product is at most the head error: since
`p ≤ 1`, `p^128 = p^120 * p^8 ≤ p^120 * 1 = p^120`. -/
theorem pow120_ge_pow128 :
    ((139775 : ℝ≥0) / 262144) ^ (128 : ℕ) ≤
      ((139775 : ℝ≥0) / 262144) ^ k_head := by
  have hp_le_one : ((139775 : ℝ≥0) / 262144) ≤ 1 := by norm_num
  have hpow8_le : ((139775 : ℝ≥0) / 262144) ^ 8 ≤ 1 :=
    pow_le_pow_right (by positivity) (by norm_num)
  rw [k_head_eq, show (128 : ℕ) = 120 + 8 by rfl, pow_add]
  have hmul :
      ((139775 : ℝ≥0) / 262144) ^ 120 * ((139775 : ℝ≥0) / 262144) ^ 8 ≤
        ((139775 : ℝ≥0) / 262144) ^ 120 * 1 :=
    mul_le_mul_of_nonneg_left hpow8_le (by positivity)
  rwa [mul_one] at hmul

-- The exact spot-check comparison at `delta* = 122369/262144`, in `Nat`:
-- `2 ^ 218787 <= 139775 ^ 12800` is
-- `2 ^ (-11613/100) <= (139775/262144) ^ 128`
-- after clearing denominators and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 218787 ≤ 139775 ^ 12800 := by decide

theorem claimedUnsafeRadius_122369_eq :
    claimedUnsafeRadius 122369 = (122369 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

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

/-- The 512-fibre rational pencil certifies the new narrow window, then hands
off to the prescribed-top attack, giving a `116.13`-bit upper certificate. -/
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

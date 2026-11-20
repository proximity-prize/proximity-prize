/- Released under the Apache License, Version 2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.DyadicScore

open scoped NNReal

/-- Read the binary digits from most to least significant. The second component
is an upper bound for the scaled error at that digit. -/
def bitNumerator (k : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => k
  | (b, _) :: tail => bitNumerator (2 * k + b) tail

def verify (scale cap : ℕ) : List (ℕ × ℕ) → Bool
  | [] => decide (cap ≤ scale)
  | (b, c) :: tail => decide (2^b * cap^2 ≤ c * scale) && verify scale c tail

private theorem verify_sound (x : ℝ≥0) {scale : ℕ} (hs : 0 < scale)
    (digits : List (ℕ × ℕ)) (cap e k : ℕ)
    (start : x^e * 2^k ≤ (cap : ℝ≥0) / scale)
    (valid : verify scale cap digits = true) :
    x^(e * 2^digits.length) * 2^(bitNumerator k digits) ≤ 1 := by
  have hs' : 0 < (scale : ℝ≥0) := by exact_mod_cast hs
  induction digits generalizing cap e k with
  | nil =>
    have le : cap ≤ scale := of_decide_eq_true valid
    simpa [bitNumerator] using start.trans ((div_le_one hs').mpr (by exact_mod_cast le))
  | cons digit tail ih =>
    obtain ⟨b,c⟩ := digit
    obtain ⟨step,rest⟩ := Bool.and_eq_true_iff.mp valid
    have step' : (2 : ℝ≥0)^b * (cap : ℝ≥0)^2 ≤ c * (scale : ℝ≥0) := by
      exact_mod_cast (of_decide_eq_true step : 2^b * cap^2 ≤ c*scale)
    have rounding : (2 : ℝ≥0)^b * ((cap : ℝ≥0)/scale)^2 ≤ c/scale := by
      rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hs']
      calc
        _ ≤ (c * (scale : ℝ≥0)) * scale := mul_le_mul_of_nonneg_right step' (by positivity)
        _ = _ := by ring
    have next : x^(e*2) * (2 : ℝ≥0)^(2*k+b) ≤ c/scale := by
      calc
        _ = 2^b * (x^e * 2^k)^2 := by rw [pow_add, Nat.mul_comm 2 k, pow_mul, pow_mul]; ring
        _ ≤ 2^b * ((cap : ℝ≥0)/scale)^2 := by gcongr
        _ ≤ _ := rounding
    simpa [bitNumerator, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      ih c (e*2) (2*k+b) next rest

/-- A short sequence of rational squarings proves a fractional bit bound with
arbitrarily fine dyadic resolution. -/
theorem score {x : ℝ≥0} {scale cap k : ℕ} (digits : List (ℕ × ℕ)) (hs : 0 < scale)
    (start : x * 2^k ≤ (cap : ℝ≥0) / scale)
    (valid : verify scale cap digits = true) :
    x ≤ (2 : ℝ≥0)^(-((bitNumerator k digits : ℕ) : ℝ) / (2^digits.length : ℕ)) := by
  have h := verify_sound x hs digits cap 1 k (by simpa using start) valid
  rw [Nat.one_mul] at h
  let n : ℕ := 2^digits.length
  have positive : 0 < (n : ℝ) := by dsimp [n]; positivity
  apply (NNReal.rpow_le_rpow_iff positive).mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ positive.ne', NNReal.rpow_natCast, NNReal.rpow_neg,
    NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h

end ProximityPrize.SubmissionLower.DyadicScore

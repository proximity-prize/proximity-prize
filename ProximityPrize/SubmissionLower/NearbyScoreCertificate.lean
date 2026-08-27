import ProximityPrize.Benchmark.TargetLower

/-!
# Generic compact score certificate near 64 bits

Model: gpt-5.
Research source base: cb4383c9414a5aff86809df81cbb33a02a193824.

This is a new, uncompiled proof draft for remote verification. It parameterizes
the accepted hundredth-root / 128th-power score argument. The natural-number
certificates are explicit hypotheses; no new numerical instance is evaluated.

Only the score component of the protected ProtocolClaim is proved. Neither
the reduction-error bound nor the full admissible-radius interval is supplied.
The final interface assumes a positive numerator and denominator and explicitly
requires numerator <= denominator, so natural subtraction denotes the intended
nonnegative radius complement.
-/

namespace ProximityPrize.SubmissionLower.NearbyScoreCertificate

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section ScoreProofs

/-- The rational approximation must be an upper bound on the root. -/
theorem rpow_fraction_le_of_nat_power
    (d u v : ℕ) (hv : 0 < v)
    (hroot : 2 ^ d * v ^ (100 : ℕ) ≤ u ^ (100 : ℕ)) :
    (2 : ℝ≥0) ^ ((d : ℝ) / 100) ≤ (u : ℝ≥0) / (v : ℝ≥0) := by
  have hv' : (0 : ℝ≥0) < (v : ℝ≥0) := by exact_mod_cast hv
  have hcast :
      (2 : ℝ≥0) ^ d * (v : ℝ≥0) ^ (100 : ℕ) ≤
        (u : ℝ≥0) ^ (100 : ℕ) := by
    exact_mod_cast hroot
  have hquot :
      (2 : ℝ≥0) ^ d ≤
        (u : ℝ≥0) ^ (100 : ℕ) / (v : ℝ≥0) ^ (100 : ℕ) :=
    (le_div_iff₀ (pow_pos hv' 100)).2 hcast
  have hpow :
      ((2 : ℝ≥0) ^ d) ^ ((100 : ℝ)⁻¹) ≤ (u : ℝ≥0) / (v : ℝ≥0) := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    change (2 : ℝ≥0) ^ d ≤
      ((u : ℝ≥0) / (v : ℝ≥0)) ^ (((100 : ℕ) : ℝ))
    rw [NNReal.rpow_natCast, div_pow]
    exact hquot
  simpa only [← NNReal.rpow_natCast_mul, div_eq_mul_inv] using hpow

theorem claimedRadius_pos_of_nat_pos
    (num den : ℕ) (hnum : 0 < num) (hden : 0 < den) :
    0 < claimedRadius num den := by
  unfold claimedRadius
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hden)

theorem claimedRadius_le_one_of_nat_le
    (num den : ℕ) (hden : 0 < den) (hnumden : num ≤ den) :
    claimedRadius num den ≤ 1 := by
  have hden' : (0 : ℝ≥0) < (den : ℝ≥0) := by exact_mod_cast hden
  have hle : (num : ℝ≥0) ≤ (den : ℝ≥0) := by exact_mod_cast hnumden
  unfold claimedRadius
  apply (div_le_iff₀ hden').2
  simpa only [one_mul] using hle

/-- No unproved replacement of truncated subtraction by ring subtraction. -/
theorem one_sub_claimedRadius_eq_nat_gap
    (num den : ℕ) (hden : 0 < den) (hnumden : num ≤ den) :
    1 - claimedRadius num den = ((den - num : ℕ) : ℝ≥0) / (den : ℝ≥0) := by
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hle := claimedRadius_le_one_of_nat_le num den hden hnumden
  apply NNReal.coe_injective
  rw [NNReal.coe_sub hle]
  simp only [claimedRadius, NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast,
    Nat.cast_sub hnumden]
  field_simp [ne_of_gt hdenR] <;> ring

/-- Clear only positive denominators to obtain the actual 128th-power bound. -/
theorem spot_power_le_rational_of_nat_certificate
    (num den u v : ℕ) (hden : 0 < den) (hnumden : num ≤ den) (hu : 0 < u)
    (hspot : 2 ^ (64 : ℕ) * u * (den - num) ^ (128 : ℕ) ≤
      v * den ^ (128 : ℕ)) :
    (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * ((v : ℝ≥0) / (u : ℝ≥0)) := by
  have hden' : (0 : ℝ≥0) < (den : ℝ≥0) := by exact_mod_cast hden
  have hu' : (0 : ℝ≥0) < (u : ℝ≥0) := by exact_mod_cast hu
  have hcast :
      (2 : ℝ≥0) ^ (64 : ℕ) * (u : ℝ≥0) *
          ((den - num : ℕ) : ℝ≥0) ^ (128 : ℕ) ≤
        (v : ℝ≥0) * (den : ℝ≥0) ^ (128 : ℕ) := by
    exact_mod_cast hspot
  calc
    (1 - claimedRadius num den) ^ IRSProfile.repetitions =
        ((den - num : ℕ) : ℝ≥0) ^ (128 : ℕ) /
          (den : ℝ≥0) ^ (128 : ℕ) := by
      rw [one_sub_claimedRadius_eq_nat_gap num den hden hnumden,
        IRSProfile.repetitions, div_pow]
    _ ≤ (v : ℝ≥0) / ((2 : ℝ≥0) ^ (64 : ℕ) * (u : ℝ≥0)) := by
      apply (div_le_div_iff₀ (pow_pos hden' 128)
        (mul_pos (pow_pos (by norm_num : (0 : ℝ≥0) < 2) 64) hu')).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast
    _ = ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * ((v : ℝ≥0) / (u : ℝ≥0)) := by
      rw [div_mul_div_comm, one_mul]

/-- Generic score component. The algebra also permits a zero radius; the
positive-radius public interface is stated separately below. -/
theorem score_le_claimedError_of_certificates
    (d num den u v : ℕ)
    (hden : 0 < den) (hnumden : num ≤ den) (hu : 0 < u) (hv : 0 < v)
    (hroot : 2 ^ d * v ^ (100 : ℕ) ≤ u ^ (100 : ℕ))
    (hspot : 2 ^ (64 : ℕ) * u * (den - num) ^ (128 : ℕ) ≤
      v * den ^ (128 : ℕ)) :
    (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤
      claimedError (6400 + d) := by
  have hscale :
      (v : ℝ≥0) / (u : ℝ≥0) ≤ (2 : ℝ≥0) ^ (-((d : ℝ) / 100)) := by
    calc
      (v : ℝ≥0) / (u : ℝ≥0) =
          1 / ((u : ℝ≥0) / (v : ℝ≥0)) := by
        rw [one_div, inv_div]
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((d : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity)
          (rpow_fraction_le_of_nat_power d u v hv hroot)
      _ = (2 : ℝ≥0) ^ (-((d : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  have hexponent :
      -(((6400 + d : ℕ) : ℝ) / 100) =
        -((64 : ℕ) : ℝ) + -((d : ℝ) / 100) := by
    push_cast
    ring
  calc
    (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * ((v : ℝ≥0) / (u : ℝ≥0)) :=
      spot_power_le_rational_of_nat_certificate num den u v hden hnumden hu hspot
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
        (2 : ℝ≥0) ^ (-((d : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError (6400 + d) := by
      unfold claimedError
      rw [hexponent, NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

/-- Radius positivity is proved from the explicit natural hypotheses, rather
than being folded silently into the score certificate. -/
theorem radius_positive_and_score
    (d num den u v : ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hnumden : num ≤ den)
    (hu : 0 < u) (hv : 0 < v)
    (hroot : 2 ^ d * v ^ (100 : ℕ) ≤ u ^ (100 : ℕ))
    (hspot : 2 ^ (64 : ℕ) * u * (den - num) ^ (128 : ℕ) ≤
      v * den ^ (128 : ℕ)) :
    0 < claimedRadius num den ∧
      (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤
        claimedError (6400 + d) :=
  ⟨claimedRadius_pos_of_nat_pos num den hnum hden,
    score_le_claimedError_of_certificates d num den u v hden hnumden hu hv hroot hspot⟩

/-- Exactly the protected `ProtocolClaim.score` inequality at `6400+d`.
Full target admissibility and the reduction-error bound remain separate. -/
theorem protected_score_of_certificates
    (d num den u v : ℕ)
    (hnum : 0 < num) (hden : 0 < den) (hnumden : num ≤ den)
    (hu : 0 < u) (hv : 0 < v)
    (hroot : 2 ^ d * v ^ (100 : ℕ) ≤ u ^ (100 : ℕ))
    (hspot : 2 ^ (64 : ℕ) * u * (den - num) ^ (128 : ℕ) ≤
      v * den ^ (128 : ℕ)) :
    (1 - claimedRadius num den) ^ IRSProfile.repetitions ≤
      claimedError (6400 + d) :=
  (radius_positive_and_score d num den u v hnum hden hnumden hu hv hroot hspot).2

end ScoreProofs

#print axioms rpow_fraction_le_of_nat_power
#print axioms claimedRadius_pos_of_nat_pos
#print axioms claimedRadius_le_one_of_nat_le
#print axioms one_sub_claimedRadius_eq_nat_gap
#print axioms spot_power_le_rational_of_nat_certificate
#print axioms score_le_claimedError_of_certificates
#print axioms radius_positive_and_score
#print axioms protected_score_of_certificates

end ProximityPrize.SubmissionLower.NearbyScoreCertificate

import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.BCHKSUniversalGlobalCapacity

namespace ProximityPrize.SubmissionLower

/-! Numeric ledger for applying the universal-numerator construction to one
already-selected score-64 factor.

The global score-64 coefficient `1265711` was tuned for the enormous global
support cap.  The local coefficient below is two larger so that it also
absorbs the affine `+d` term uniformly from `D ≥ 1`. -/

def bchksFixedFactorIncidenceCoefficient6400 : ℕ := 1265713

def bchksFixedFactorResultCap6400 (d D : ℕ) : ℕ :=
  2 * bchksUniversalExponent6399 * d * D + d

def bchksFixedFactorFusedCap6400 (d D : ℕ) : ℕ :=
  bchksFixedFactorIncidenceCoefficient6400 * d * D

/-- The local fused capacity absorbs the exact floor conversion used by the
pair selector, including the affine numerator's additional `+d` degree. -/
theorem bchks_fixed_factor_fused_incidence_6400
    (d D : ℕ) (hD : 1 ≤ D) :
    (262144 - 131071) * bchksFixedFactorResultCap6400 d D ≤
      (262144 - bchksErrors6400 - 131071) *
        bchksFixedFactorFusedCap6400 d D := by
  have hsmall : 131073 ≤ 141323 * D := by omega
  have hmul := Nat.mul_le_mul_left d hsmall
  calc
    (262144 - 131071) * bchksFixedFactorResultCap6400 d D =
        68719214586 * d * D + 131073 * d := by
          norm_num [bchksFixedFactorResultCap6400,
            bchksUniversalExponent6399]
          ring
    _ ≤ 68719214586 * d * D + 141323 * d * D := by
          apply Nat.add_le_add_left
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    _ = (262144 - bchksErrors6400 - 131071) *
        bchksFixedFactorFusedCap6400 d D := by
          norm_num [bchksErrors6400, bchksFixedFactorFusedCap6400,
            bchksFixedFactorIncidenceCoefficient6400]
          ring

/-- One whole-polynomial bad set, one selected-factor leading/separability
bad set, the fused resultant ledger, and one `(errors+1)` charge per inner
factor all fit in the selected-factor budget through degree 114. -/
theorem bchks_fixed_factor_total_ledger_le_6400
    (d D : ℕ) (hd : d ≤ 114) (hdD : d ≤ D) :
    D + 2 * d * D + bchksFixedFactorFusedCap6400 d D +
        (bchksErrors6400 + 1) * d ≤
      144802557 * D := by
  have hmainCoeff : 1 + 2 * d +
      bchksFixedFactorIncidenceCoefficient6400 * d ≤ 144291511 := by
    norm_num [bchksFixedFactorIncidenceCoefficient6400] at ⊢
    omega
  have hmain := Nat.mul_le_mul_right D hmainCoeff
  have hpair := Nat.mul_le_mul_left (bchksErrors6400 + 1) hdD
  calc
    D + 2 * d * D + bchksFixedFactorFusedCap6400 d D +
        (bchksErrors6400 + 1) * d =
      (1 + 2 * d + bchksFixedFactorIncidenceCoefficient6400 * d) * D +
        (bchksErrors6400 + 1) * d := by
          simp only [bchksFixedFactorFusedCap6400]
          ring
    _ ≤ 144291511 * D + (bchksErrors6400 + 1) * D :=
      Nat.add_le_add hmain hpair
    _ = 144368292 * D := by
      norm_num [bchksErrors6400]
      ring
    _ ≤ 144802557 * D := Nat.mul_le_mul_right D (by norm_num)

/-- The strict seed-cardinality hypothesis produced by fixed-factor selection
therefore implies the exact strict ledger needed by global pigeonholing. -/
theorem bchks_fixed_factor_total_ledger_lt_6400
    (t d D : ℕ) (hd : d ≤ 114) (hdD : d ≤ D)
    (hT : 144802557 * D < t) :
    D + 2 * d * D + bchksFixedFactorFusedCap6400 d D +
        (bchksErrors6400 + 1) * d < t :=
  (bchks_fixed_factor_total_ledger_le_6400 d D hd hdD).trans_lt hT

/-- Degree 115 is beyond this particular conservative ledger: its dominant
coefficient alone already exceeds the selected-factor allowance. -/
theorem bchks_fixed_factor_degree_115_dominant_exceeds :
    144802557 < 1 + 2 * 115 +
      bchksFixedFactorIncidenceCoefficient6400 * 115 := by
  norm_num [bchksFixedFactorIncidenceCoefficient6400]

end ProximityPrize.SubmissionLower

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.BinaryTargetLower

/-!
# Lower reduction-threshold certificate at radius `1/4`

At radius `1/4`, the certified IRS combination-round error is below `2^-160`.
The separate spot-check term `(3/4)^128 = 2^-53.1248...` is below `2^-53.12`,
which is certified through the rational bracket `1837/1000 ≤ 2^(88/100)`.
-/

namespace ProximityPrize.SubmissionBinaryLower

open Code CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark
open scoped ENNReal NNReal

set_option maxRecDepth 100000

noncomputable abbrev SquaredCode : Set (BinaryIRSProfile.Index →
    Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
      Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))

set_option maxRecDepth 20000 in
theorem squaredCode_minDistance :
    Code.minDist (SquaredCode : Set (BinaryIRSProfile.Index →
      Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) = 1048577 := by
  calc
    Code.minDist (SquaredCode : Set (BinaryIRSProfile.Index →
        Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) =
      Code.minDist (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
        Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) := by
          exact Code.minDist_interleavedCodeSet (κ := Fin 2)
            (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
              Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))
    _ = 1048577 := BinaryIRSProfile.minDistance

theorem squaredCode_relativeUniqueDecodingRadius :
    Code.relativeUniqueDecodingRadius
      (SquaredCode : Set (BinaryIRSProfile.Index →
        Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) =
      (1 : ℝ≥0) / 4 := by
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, squaredCode_minDistance]
  apply NNReal.eq
  norm_num

theorem squaredCode_lambda_quarter_le_one :
    Code.Lambda
      (SquaredCode : Set (BinaryIRSProfile.Index →
        Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))
      (1 / 4 : ℝ) ≤ 1 := by
  have h := Code.isUniquelyDecodable_relativeUniqueDecodingRadius
    (SquaredCode : Set (BinaryIRSProfile.Index →
      Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))
  rw [squaredCode_relativeUniqueDecodingRadius] at h
  exact Code.isUniquelyDecodable_iff_Lambda_le.mp h

theorem baseCode_relativeUniqueDecodingRadius :
    Code.relativeUniqueDecodingRadius
      (BinaryIRSProfile.baseCode : Set (BinaryIRSProfile.Index → BinaryIRSProfile.Field)) =
      (1 : ℝ≥0) / 4 := by
  unfold Code.relativeUniqueDecodingRadius
  rw [Code.dist_eq_minDist, BinaryIRSProfile.baseMinDistance]
  apply NNReal.eq
  norm_num

theorem base_mca_quarter_le :
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.baseCode
        (1 / 4 : ℝ) ≤
      (Fintype.card BinaryIRSProfile.Index : ENNReal) /
        (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
  have hudr : (1 / 4 : ℝ≥0) ≤
      Code.relativeUniqueDecodingRadius
        (BinaryIRSProfile.baseCode : Set (BinaryIRSProfile.Index → BinaryIRSProfile.Field)) := by
    rw [baseCode_relativeUniqueDecodingRadius]
  have hca :=
    RS_correlatedAgreement_affineLines_uniqueDecodingRegime
      (deg := BinaryIRSProfile.baseDimension) (domain := BinaryIRSProfile.domain)
      (δ := (1 / 4 : ℝ≥0)) hudr
  have heps :=
    (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le
      (F := BinaryIRSProfile.Field)
      (BinaryIRSProfile.baseCode : Set (BinaryIRSProfile.Index → BinaryIRSProfile.Field))
      (1 / 4 : ℝ≥0)
      (ProximityGap.errorBound (1 / 4 : ℝ≥0)
        BinaryIRSProfile.baseDimension BinaryIRSProfile.domain)).mp hca
  calc
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.baseCode
          (1 / 4 : ℝ) ≤
        epsCa (F := BinaryIRSProfile.Field)
          (BinaryIRSProfile.baseCode : Set (BinaryIRSProfile.Index → BinaryIRSProfile.Field))
          (1 / 4 : ℝ≥0) (1 / 4 : ℝ≥0) := by
      refine ProximityGap.mcaError_le_epsCa_of_pos_of_two_mul_lt_dist
        (ι := BinaryIRSProfile.Index) (F := BinaryIRSProfile.Field)
        BinaryIRSProfile.baseCode (1 / 4 : ℝ≥0) ?_ ?_
      · norm_num
      · rw [Code.dist_eq_minDist, BinaryIRSProfile.baseMinDistance]
        norm_num
    _ ≤ (Fintype.card BinaryIRSProfile.Index : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
      rw [ProximityGap.errorBound_eq_n_div_q_of_le_relUDR hudr] at heps
      rw [ENNReal.coe_div (by simp)] at heps
      exact heps

theorem mca_quarter_le :
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.code
        (1 / 4 : ℝ) ≤
      (Fintype.card BinaryIRSProfile.Index : ENNReal) /
        (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
  calc
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.code
        (1 / 4 : ℝ) ≤
      mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.baseCode
        (1 / 4 : ℝ) := by
          simpa [BinaryIRSProfile.code, BinaryIRSProfile.baseCode,
            ReedSolomon.Interleaved.irsCode,
            BinaryIRSProfile.totalDimension_div_interleaving] using
            (ProximityGap.mcaError_interleaved_le BinaryIRSProfile.baseCode
              BinaryIRSProfile.interleaving (1 / 4 : ℝ≥0)
              (by norm_num [BinaryIRSProfile.interleaving]) (by norm_num) (by norm_num))
    _ ≤ _ := base_mca_quarter_le

theorem certifiedGammaError_quarter_le_two_pow_neg_160 :
    certifiedGammaError BinaryIRSProfile.code (1 / 4 : ℝ≥0) ≤
      (1 : ℝ≥0) / 2 ^ (160 : ℕ) := by
  have hLambdaNat :
      (Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat ≤ 1 :=
    ENat.toNat_le_of_le_natCast squaredCode_lambda_quarter_le_one
  have hList :
      ((Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) ≤
        (1 : ENNReal) / (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
    exact ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.code (1 / 4 : ℝ) +
          ((Code.Lambda SquaredCode (1 / 4 : ℝ)).toNat : ENNReal) /
            (Fintype.card BinaryIRSProfile.Field : ENNReal) ≤
        (Fintype.card BinaryIRSProfile.Index : ENNReal) /
            (Fintype.card BinaryIRSProfile.Field : ENNReal) +
          (1 : ENNReal) /
            (Fintype.card BinaryIRSProfile.Field : ENNReal) :=
      add_le_add mca_quarter_le hList
    _ ≤ (((1 : ℝ≥0) / 2 ^ (160 : ℕ) : ℝ≥0) : ENNReal) := by
      have hne :
          (Fintype.card BinaryIRSProfile.Index : ENNReal) /
                (Fintype.card BinaryIRSProfile.Field : ENNReal) +
              1 / (Fintype.card BinaryIRSProfile.Field : ENNReal) ≠ ⊤ := by
        rw [ENNReal.add_ne_top]
        constructor <;> apply ENNReal.div_ne_top <;> simp
      apply (ENNReal.toReal_le_toReal hne (by simp)).mp
      have hparts := ENNReal.add_ne_top.mp hne
      rw [ENNReal.toReal_add hparts.1 hparts.2,
        ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num [BinaryIRSProfile.Index, BinaryIRSProfile.Field, BF64.card_ext3]

/-- Exact rational lower bound used for the 53.12-bit score certificate. -/
theorem two_rpow_eighty_eight_hundred_ge :
    (1837 : ℝ≥0) / 1000 ≤ (2 : ℝ≥0) ^ ((88 : ℝ) / 100) := by
  have hroot :
      (1837 : ℝ≥0) / 1000 ≤
        ((2 : ℝ≥0) ^ (88 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (1837 : ℝ≥0) / 1000 ≤
        ((2 : ℝ≥0) ^ (88 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((88 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

end ProximityPrize.SubmissionBinaryLower

namespace ProximityPrize.Benchmark.Binary

open scoped NNReal

set_option maxRecDepth 100000

/-- The 53.12-bit lower certificate at radius `1/4`. -/
theorem candidate : ProtocolClaim 5312 1 4 where
  admissible := by
    constructor <;> norm_num [claimedRadius, BinaryIRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError BinaryIRSProfile.code (1 / 4 : ℝ≥0) ≤
        reductionTarget :=
      ProximityPrize.SubmissionBinaryLower.certifiedGammaError_quarter_le_two_pow_neg_160.trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 1 4 = (1 / 4 : ℝ≥0) := by
      norm_num [claimedRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode BinaryIRSProfile.domain
            BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving =
          BinaryIRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    calc
      (1 - claimedRadius 1 4) ^ BinaryIRSProfile.repetitions ≤
          ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) * (1837 / 1000) := by
        rw [← NNReal.coe_le_coe]
        norm_num [claimedRadius, BinaryIRSProfile.repetitions, div_le_iff₀]
      _ ≤ ((1 : ℝ≥0) / 2 ^ (54 : ℕ)) *
            (2 : ℝ≥0) ^ ((88 : ℝ) / 100) := by
        exact mul_le_mul_of_nonneg_left
          ProximityPrize.SubmissionBinaryLower.two_rpow_eighty_eight_hundred_ge
          (by positivity)
      _ = claimedError 5312 := by
        unfold claimedError
        rw [show -((((5312 : ℕ) : ℝ) / 100)) =
            -((54 : ℕ) : ℝ) + (88 : ℝ) / 100 by norm_num,
          NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
          NNReal.rpow_neg, NNReal.rpow_natCast]
        norm_num

end ProximityPrize.Benchmark.Binary

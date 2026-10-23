import ProximityPrize.SubmissionBinaryLower.BCHKSParameters
import ProximityPrize.SubmissionBinaryLower.JohnsonFamily

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped NNReal

noncomputable abbrev BCHKSSquaredCode :
    Set (BinaryIRSProfile.Index → Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
      Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))

set_option maxRecDepth 20000 in
theorem bchksSquaredCode_minDistance :
    Code.minDist BCHKSSquaredCode = 1048577 := by
  calc
    Code.minDist BCHKSSquaredCode =
        Code.minDist (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
          Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (BinaryIRSProfile.code : Set (BinaryIRSProfile.Index →
          Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))
    _ = 1048577 := BinaryIRSProfile.minDistance

/-- Grid representative of the claimed radius's integer-agreement cell. -/
noncomputable def bchksGrid : ℝ≥0 := (614242 : ℝ≥0) / 2097152

lemma bchksGrid_floor :
    ⌊bchksGrid * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors := by
  norm_num [bchksGrid, bchksErrors, BinaryIRSProfile.Index]

/-- The cell representative lies below the list-`10⁹` Johnson radius of the
squared code: `(1 − 1/q)·(1 − √(1 − q/(q−1)·(ℓ−1)/ℓ·δ_min))` with
`q = |F|^{128} ≥ 2^192`, `(ℓ−1)/ℓ = 999999999/10⁹` and `δ_min = 1048577/2097152`.
The `q/(q−1) ≥ 1` factor only enlarges the radicand, so the bound is proved by
`√(1 − 999999999/10⁹·1048577/2097152) < 7071065/10⁷` and
`(1 − 2⁻¹⁹²)·(1 − 7071065/10⁷) ≥ 614242/2097152`. -/
set_option maxRecDepth 100000 in
lemma bchks_lambda_le_jqEll :
    (bchksGrid : ℝ) ≤
      JohnsonBound.Jqℓ ((Fintype.card
          (Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field) : ℚ))
        (bchksListBound : ℚ)
        ((Code.minDist BCHKSSquaredCode : ℚ) /
          (Fintype.card BinaryIRSProfile.Index : ℚ)) := by
  set N : ℕ := Fintype.card
      (Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)
      with hN_def
  have hq2e : (2 : ℚ) ^ 192 ≤ (N : ℚ) := by
    rw [hN_def]
    calc (2 : ℚ) ^ 192 = Fintype.card BinaryIRSProfile.Field := by
          rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ) from
            BF64.card_ext3]; norm_num
      _ ≤ Fintype.card
          (Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field) := by
        exact_mod_cast Fintype.card_le_of_injective
          (fun a => fun (_ : Fin 2)
            (_ : Fin BinaryIRSProfile.interleaving) => a) (by
            intro a b h
            exact congrFun (congrFun h ⟨0, by norm_num⟩)
              ⟨0, by norm_num [BinaryIRSProfile.interleaving]⟩)
  have hq0 : (N : ℚ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2 ^ 192) hq2e)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (by norm_num : (1 : ℚ) ≤ 2 ^ 192) hq2e
  have hN2R : (2 : ℝ) ^ 192 ≤ (N : ℝ) := by exact_mod_cast hq2e
  rw [bchksSquaredCode_minDistance, BinaryIRSProfile.card_index,
    JohnsonBound.Jqℓ_eq_mul_one_sub_sqrt hq0]
  push_cast
  have hcast :
      (N : ℝ) / ((N : ℝ) - 1) *
          (((bchksListBound : ℝ) - 1) / bchksListBound) * (1048577 / 2097152) =
        (N : ℝ) / ((N : ℝ) - 1) *
          ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152)) := by
    rw [show (((bchksListBound : ℝ) - 1) / (bchksListBound : ℝ)) =
        999999999 / 1000000000 by norm_num [bchksListBound]]
    ring
  rw [hcast]
  have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hfrac : (1 : ℝ) ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    rw [le_div_iff₀ hNm1]; linarith
  have hge : (999999999 / 1000000000 : ℝ) * (1048577 / 2097152) ≤
      (N : ℝ) / ((N : ℝ) - 1) *
        ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152)) := by
    rw [← mul_one ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152))]
    exact mul_le_mul_of_nonneg_right hfrac (by norm_num)
  have hs : √(1 - (N : ℝ) / ((N : ℝ) - 1) *
        ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152))) ≤
      (7071065 / 10000000 : ℝ) := by
    calc √(1 - (N : ℝ) / ((N : ℝ) - 1) *
            ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152)))
        ≤ √(1 - (999999999 / 1000000000 : ℝ) * (1048577 / 2097152)) :=
          Real.sqrt_le_sqrt (by linarith)
      _ ≤ (7071065 / 10000000 : ℝ) := by
          rw [show (7071065 / 10000000 : ℝ) =
              √((7071065 / 10000000 : ℝ) ^ 2) from
            (Real.sqrt_sq (by norm_num)).symm]
          apply Real.sqrt_le_sqrt
          norm_num
  have hNinv : (1 - 1 / (2 : ℝ) ^ 192) ≤ 1 - 1 / (N : ℝ) := by
    have h2 : (1 : ℝ) / (N : ℝ) ≤ 1 / (2 : ℝ) ^ 192 :=
      one_div_le_one_div_of_le (by norm_num) hN2R
    linarith
  have hN1inv : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith : (0 : ℝ) < (N : ℝ))]
    exact hN1R
  calc (bchksGrid : ℝ) = 614242 / 2097152 := by norm_num [bchksGrid]
    _ ≤ (1 - 1 / (2 : ℝ) ^ 192) * (1 - 7071065 / 10000000) := by norm_num
    _ ≤ (1 - 1 / (N : ℝ)) * (1 - √(1 - (N : ℝ) / ((N : ℝ) - 1) *
          ((999999999 / 1000000000 : ℝ) * (1048577 / 2097152)))) := by
      refine mul_le_mul hNinv ?_ (by norm_num) hN1inv
      exact sub_le_sub_left hs 1

set_option maxRecDepth 100000 in
lemma bchks_lambda_le :
    Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) ≤
      (bchksListBound : ℕ∞) := by
  have hfloor : ⌊bchksRadius * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ =
      ⌊bchksGrid * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ := by
    rw [bchksRadius_floor_nnreal, bchksGrid_floor]
  rw [ProximityGap.GrandChallenges.lambda_eq_of_floor_eq hfloor]
  haveI : Nonempty BinaryIRSProfile.Index := ⟨⟨0, by norm_num⟩⟩
  have hJ := CodingTheory.johnson_bound_lambda_le_ell BCHKSSquaredCode
    bchksListBound (by norm_num [bchksListBound])
  exact (Code.Lambda_mono bchks_lambda_le_jqEll).trans hJ

end ProximityPrize.SubmissionBinaryLower

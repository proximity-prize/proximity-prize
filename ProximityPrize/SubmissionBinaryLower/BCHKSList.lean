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

noncomputable def bchksGrid : ℝ≥0 := (614241 : ℝ≥0) / 2097152

private lemma bchks_eta_pos :
    0 < (1 - Real.sqrt (1 / 2 : ℝ) - (bchksGrid : ℝ)) := by
  have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
    norm_num
  norm_num [bchksGrid] at hs ⊢
  linarith

lemma bchksGrid_floor :
    ⌊bchksRadius * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ =
      ⌊bchksGrid * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ := by
  rw [bchksRadius_floor_nnreal]
  norm_num [bchksErrors, bchksGrid, BinaryIRSProfile.Index]

set_option maxRecDepth 100000 in
lemma bchks_lambda_le :
    Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) ≤
      (bchksListBound : ℕ∞) := by
  have hcell : Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) =
      Code.Lambda BCHKSSquaredCode (bchksGrid : ℝ) :=
    ProximityGap.GrandChallenges.lambda_eq_of_floor_eq (C := BCHKSSquaredCode)
      (δ := bchksRadius) (δ' := bchksGrid) bchksGrid_floor
  rw [hcell]
  let η : ℝ := 1 - Real.sqrt (1 / 2 : ℝ) - (bchksGrid : ℝ)
  have hη : 0 < η := by simpa [η] using bchks_eta_pos
  have hJ := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    BCHKSSquaredCode (1 / 2 : ℝ) η (by norm_num) (by norm_num) hη (by
      rw [bchksSquaredCode_minDistance]
      norm_num [BinaryIRSProfile.Index])
  have hr : 1 - Real.sqrt (1 / 2 : ℝ) - η = (bchksGrid : ℝ) := by
    simp [η]
  rw [hr] at hJ
  have hreal : (1 / (2 * η * (1 / 2 : ℝ))) ≤ bchksListBound := by
    dsimp [η, bchksListBound]
    have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
      norm_num
    have heta : (1 : ℝ) / 4000000 < η := by
      dsimp [η]
      norm_num [bchksGrid] at hs ⊢
      linarith
    rw [show 2 * η * (1 / 2 : ℝ) = η by ring]
    rw [div_le_iff₀ hη]
    nlinarith
  have hE : (Code.Lambda BCHKSSquaredCode (bchksGrid : ℝ) : ENNReal) ≤
      (bchksListBound : ENNReal) := hJ.trans (by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

end ProximityPrize.SubmissionBinaryLower

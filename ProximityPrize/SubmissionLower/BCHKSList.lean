import ProximityPrize.SubmissionLower.BCHKSParameters
import ProximityPrize.SubmissionLower.JohnsonFamily

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable abbrev BCHKSSquaredCode :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem bchksSquaredCode_minDistance :
    Code.minDist BCHKSSquaredCode = 131073 := by
  calc
    Code.minDist BCHKSSquaredCode =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

private lemma bchks_eta_pos :
    0 < (1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius : ℝ)) := by
  have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
    norm_num
  norm_num [bchksRadius] at hs ⊢
  linarith

set_option maxRecDepth 100000 in
lemma bchks_lambda_le :
    Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) ≤
      (bchksListBound : ℕ∞) := by
  let η : ℝ := 1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius : ℝ)
  have hη : 0 < η := by simpa [η] using bchks_eta_pos
  have hJ := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    BCHKSSquaredCode (1 / 2 : ℝ) η (by norm_num) (by norm_num) hη (by
      rw [bchksSquaredCode_minDistance]
      norm_num [IRSProfile.Index])
  have hr : 1 - Real.sqrt (1 / 2 : ℝ) - η = (bchksRadius : ℝ) := by
    simp [η]
  rw [hr] at hJ
  have hreal : (1 / (2 * η * (1 / 2 : ℝ))) ≤ bchksListBound := by
    dsimp [η, bchksListBound]
    have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
      norm_num
    have heta : (1 : ℝ) / 5000 < η := by
      dsimp [η]
      norm_num [bchksRadius] at hs ⊢
      linarith
    rw [show 2 * η * (1 / 2 : ℝ) = η by ring]
    rw [div_le_iff₀ hη]
    nlinarith
  have hE : (Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) : ENNReal) ≤
      (bchksListBound : ENNReal) := hJ.trans (by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

end ProximityPrize.SubmissionLower

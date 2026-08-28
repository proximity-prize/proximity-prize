import ProximityPrize.SubmissionLower.BCHKSParameters6399
import ProximityPrize.SubmissionLower.JohnsonFamily

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable abbrev BCHKS6399SquaredCode :
    Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
      IRSProfile.Field) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (IRSProfile.code : Set (IRSProfile.Index →
      Fin IRSProfile.interleaving → IRSProfile.Field))

set_option maxRecDepth 20000 in
theorem bchks6399_squaredCode_minDistance :
    Code.minDist BCHKS6399SquaredCode = 131073 := by
  calc
    Code.minDist BCHKS6399SquaredCode =
        Code.minDist (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field)) := by
      exact Code.minDist_interleavedCodeSet (κ := Fin 2)
        (IRSProfile.code : Set (IRSProfile.Index →
          Fin IRSProfile.interleaving → IRSProfile.Field))
    _ = 131073 := IRSProfile.minDistance

private lemma bchks6399_eta_pos :
    0 < (1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius6399 : ℝ)) := by
  have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
    norm_num
  norm_num [bchksRadius6399] at hs ⊢
  linarith

set_option maxRecDepth 100000 in
theorem bchks6399_lambda_le :
    Code.Lambda BCHKS6399SquaredCode (bchksRadius6399 : ℝ) ≤
      (bchksListBound6399 : ℕ∞) := by
  let η : ℝ := 1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius6399 : ℝ)
  have hη : 0 < η := by simpa [η] using bchks6399_eta_pos
  have hJ := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    BCHKS6399SquaredCode (1 / 2 : ℝ) η (by norm_num) (by norm_num) hη (by
      rw [bchks6399_squaredCode_minDistance]
      norm_num [IRSProfile.Index])
  have hr : 1 - Real.sqrt (1 / 2 : ℝ) - η = (bchksRadius6399 : ℝ) := by
    simp [η]
  rw [hr] at hJ
  have hreal :
      (1 / (2 * η * (1 / 2 : ℝ))) ≤ bchksListBound6399 := by
    dsimp [η, bchksListBound6399]
    have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
      norm_num
    have heta : (1 : ℝ) / 30000 <
        1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius6399 : ℝ) := by
      norm_num [bchksRadius6399] at hs ⊢
      linarith
    rw [show 2 * (1 - Real.sqrt (1 / 2 : ℝ) -
        (bchksRadius6399 : ℝ)) * (1 / 2 : ℝ) =
          1 - Real.sqrt (1 / 2 : ℝ) - (bchksRadius6399 : ℝ) by ring]
    rw [div_le_iff₀ (by simpa using bchks6399_eta_pos)]
    nlinarith
  have hE : (Code.Lambda BCHKS6399SquaredCode
      (bchksRadius6399 : ℝ) : ENNReal) ≤
      (bchksListBound6399 : ENNReal) := hJ.trans (by
        simpa only [ENNReal.ofReal_natCast] using
          ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

end ProximityPrize.SubmissionLower

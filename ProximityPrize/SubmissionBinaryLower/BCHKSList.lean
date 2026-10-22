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

private lemma lambda_eq_floor_div_card {ι F : Type*} [Fintype ι] [Nonempty ι]
    (C : Set (ι → F)) {δ : ℝ} (hδ : 0 ≤ δ) :
    Code.Lambda C δ
      = Code.Lambda C ((⌊δ * Fintype.card ι⌋₊ : ℝ) / Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hset : ∀ y : ι → F,
      Code.closeCodewordsRel C y δ
        = Code.closeCodewordsRel C y ((⌊δ * Fintype.card ι⌋₊ : ℝ) / Fintype.card ι) := by
    intro y
    ext c
    simp only [Code.closeCodewordsRel, Code.relHammingBall, Set.mem_ofPred_eq,
      and_congr_right_iff, Code.relHammingDist]
    intro _
    push_cast
    rw [div_le_iff₀ hn, div_le_iff₀ hn, div_mul_cancel₀ _ hn.ne', Nat.cast_le,
      ← Nat.le_floor_iff (by positivity)]
  unfold Code.Lambda
  exact iSup_congr fun y => by rw [hset y]

private lemma bchks_eta_pos :
    0 < (1 - Real.sqrt (1 / 2 : ℝ) -
      (bchksErrors : ℝ) / Fintype.card BinaryIRSProfile.Index) := by
  have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
    norm_num
  norm_num [bchksErrors, BinaryIRSProfile.Index] at hs ⊢
  linarith

set_option maxRecDepth 100000 in
lemma bchks_lambda_le :
    Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) ≤
      (bchksListBound : ℕ∞) := by
  rw [lambda_eq_floor_div_card BCHKSSquaredCode
    (hδ := by positivity : (0 : ℝ) ≤ (bchksRadius : ℝ)), bchksRadius_floor]
  let η : ℝ := 1 - Real.sqrt (1 / 2 : ℝ) -
    (bchksErrors : ℝ) / Fintype.card BinaryIRSProfile.Index
  have hη : 0 < η := by simpa [η] using bchks_eta_pos
  have hJ := CodingTheory.mds_johnson_lambda_le_of_rate_distance
    BCHKSSquaredCode (1 / 2 : ℝ) η (by norm_num) (by norm_num) hη (by
      rw [bchksSquaredCode_minDistance]
      norm_num [BinaryIRSProfile.Index])
  have hr : 1 - Real.sqrt (1 / 2 : ℝ) - η =
      (bchksErrors : ℝ) / Fintype.card BinaryIRSProfile.Index := by
    simp [η]
  rw [hr] at hJ
  have hreal : (1 / (2 * η * (1 / 2 : ℝ))) ≤ bchksListBound := by
    dsimp [η, bchksListBound]
    have hs : Real.sqrt (1 / 2 : ℝ) < 70710679 / 100000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 70710679 / 100000000)]
      norm_num
    have heta : (1 : ℝ) / 4000000 < η := by
      dsimp [η]
      norm_num [bchksErrors, BinaryIRSProfile.Index] at hs ⊢
      linarith
    rw [show 2 * η * (1 / 2 : ℝ) = η by ring]
    rw [div_le_iff₀ hη]
    nlinarith
  have hE : (Code.Lambda BCHKSSquaredCode
      ((bchksErrors : ℝ) / Fintype.card BinaryIRSProfile.Index) : ENNReal) ≤
      (bchksListBound : ENNReal) := hJ.trans (by
        simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

end ProximityPrize.SubmissionBinaryLower

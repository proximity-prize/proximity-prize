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
  have hs : Real.sqrt (1 / 2 : ℝ) < 707106782 / 1000000000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 707106782 / 1000000000)]
    norm_num
  norm_num [bchksGrid] at hs ⊢
  linarith

private lemma lambda_eq_of_floor
    {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hf : ⌊δ * (Fintype.card BinaryIRSProfile.Index : ℝ)⌋₊ =
      ⌊δ' * (Fintype.card BinaryIRSProfile.Index : ℝ)⌋₊) :
    Code.Lambda BCHKSSquaredCode δ = Code.Lambda BCHKSSquaredCode δ' := by
  classical
  have hn : (0 : ℝ) < Fintype.card BinaryIRSProfile.Index := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card BinaryIRSProfile.Index)
  have hδn : 0 ≤ δ * (Fintype.card BinaryIRSProfile.Index : ℝ) :=
    mul_nonneg hδ hn.le
  have hδ'n : 0 ≤ δ' * (Fintype.card BinaryIRSProfile.Index : ℝ) :=
    mul_nonneg hδ' hn.le
  have hball : ∀ (y c : BinaryIRSProfile.Index → Fin 2 →
      Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field),
      (Code.relHammingDist y c : ℝ) ≤ δ ↔ (Code.relHammingDist y c : ℝ) ≤ δ' := by
    intro y c
    have hdist : (Code.relHammingDist y c : ℝ) =
        (hammingDist y c : ℝ) / Fintype.card BinaryIRSProfile.Index := by
      simp [Code.relHammingDist]
    rw [hdist, div_le_iff₀ hn, div_le_iff₀ hn]
    constructor
    · intro hle
      have hk : hammingDist y c ≤ ⌊δ * Fintype.card BinaryIRSProfile.Index⌋₊ :=
        (Nat.le_floor_iff hδn).1 hle
      exact (Nat.le_floor_iff hδ'n).2 (hf ▸ hk)
    · intro hle
      have hk : hammingDist y c ≤ ⌊δ' * Fintype.card BinaryIRSProfile.Index⌋₊ :=
        (Nat.le_floor_iff hδ'n).1 hle
      exact (Nat.le_floor_iff hδn).2 (hf.symm ▸ hk)
  have hset : ∀ y, Code.closeCodewordsRel BCHKSSquaredCode y δ =
      Code.closeCodewordsRel BCHKSSquaredCode y δ' := by
    intro y
    ext c
    rw [Code.mem_closeCodewordsRel_iff, Code.mem_closeCodewordsRel_iff]
    exact and_congr_right fun _ => hball y c
  unfold Code.Lambda
  exact iSup_congr fun y => by rw [hset y]

set_option maxRecDepth 100000 in
lemma bchks_lambda_le :
    Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) ≤
      (bchksListBound : ℕ∞) := by
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
    have hs : Real.sqrt (1 / 2 : ℝ) < 707106782 / 1000000000 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 707106782 / 1000000000)]
      norm_num
    have heta : (1 : ℝ) / 4000000 < η := by
      dsimp [η]
      norm_num [bchksGrid] at hs ⊢
      linarith
    rw [show 2 * η * (1 / 2 : ℝ) = η by ring]
    rw [div_le_iff₀ hη]
    nlinarith
  have hfloor :
      ⌊(bchksRadius : ℝ) * (Fintype.card BinaryIRSProfile.Index : ℝ)⌋₊ =
        ⌊(bchksGrid : ℝ) * (Fintype.card BinaryIRSProfile.Index : ℝ)⌋₊ := by
    norm_num [bchksRadius, bchksGrid, BinaryIRSProfile.Index]
  have hLam : Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) =
      Code.Lambda BCHKSSquaredCode (bchksGrid : ℝ) :=
    lambda_eq_of_floor (by positivity) (by positivity) hfloor
  have hE : (Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ) : ENNReal) ≤
      (bchksListBound : ENNReal) := by
    rw [hLam]
    exact hJ.trans (by
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hreal)
  exact_mod_cast hE

end ProximityPrize.SubmissionBinaryLower

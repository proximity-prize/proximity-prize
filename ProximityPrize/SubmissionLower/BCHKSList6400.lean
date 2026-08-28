import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.BCHKSList6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark CodingTheory JohnsonBound
open scoped NNReal

set_option maxRecDepth 100000

/-- The squared-code alphabet at the score-64 endpoint. -/
noncomputable abbrev BCHKS6400Alphabet : Type :=
  Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field

lemma bchks6400_alphabet_card_ge :
    (1048576 : ℕ) ≤ Fintype.card BCHKS6400Alphabet := by
  have hfield : (1048576 : ℕ) ≤ Fintype.card IRSProfile.Field := by
    have hext := KoalaBear.card_ext6
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize] at hext ⊢
  have hinner :
      Fintype.card IRSProfile.Field ≤
        Fintype.card (Fin IRSProfile.interleaving → IRSProfile.Field) := by
    refine Fintype.card_le_of_injective (fun a _ => a) ?_
    intro a b hab
    exact congrFun hab ⟨0, by norm_num [IRSProfile.interleaving]⟩
  have houter :
      Fintype.card (Fin IRSProfile.interleaving → IRSProfile.Field) ≤
        Fintype.card BCHKS6400Alphabet := by
    refine Fintype.card_le_of_injective (fun f _ => f) ?_
    intro f g hab
    exact congrFun hab ⟨0, by norm_num⟩
  calc (1048576 : ℕ) ≤ Fintype.card IRSProfile.Field := hfield
    _ ≤ Fintype.card (Fin IRSProfile.interleaving → IRSProfile.Field) :=
      hinner
    _ ≤ Fintype.card BCHKS6400Alphabet := houter

/-- The score-64 radius lies below the exact finite-alphabet Johnson radius at
list size `300000`. -/
lemma bchks6400_radius_le_Jql :
    (bchksRadius6400 : ℝ) ≤
      Jqℓ (Fintype.card BCHKS6400Alphabet : ℚ) bchksListBound6400
        ((Code.minDist BCHKS6399SquaredCode : ℚ) /
          (Fintype.card IRSProfile.Index : ℚ)) := by
  have hd : (Code.minDist BCHKS6399SquaredCode : ℚ) = 131073 := by
    exact_mod_cast congrArg Nat.cast bchks6399_squaredCode_minDistance
  have hn : (Fintype.card IRSProfile.Index : ℚ) = 262144 := by
    norm_num [IRSProfile.Index]
  set q : ℚ := ((Fintype.card BCHKS6400Alphabet : ℕ) : ℚ) with hq_def
  have hq20 : (1048576 : ℚ) ≤ q := by
    rw [hq_def]
    exact_mod_cast bchks6400_alphabet_card_ge
  have hq1 : (1 : ℚ) < q := lt_of_lt_of_le (by norm_num) hq20
  have hq0 : q ≠ 0 := by positivity
  rw [hd, hn, Jqℓ_eq_mul_one_sub_sqrt hq0]
  set x : ℚ :=
    q / (q - 1) * ((bchksListBound6400 - 1) / bchksListBound6400) *
      (131073 / 262144) with hx_def
  set y : ℚ :=
    ((bchksListBound6400 - 1) / bchksListBound6400) *
      (131073 / 262144) with hy_def
  have hb1 : (1 : ℚ) ≤ bchksListBound6400 := by
    norm_num [bchksListBound6400]
  have hy_nonneg : (0 : ℚ) ≤ y := by
    rw [hy_def]
    norm_num [bchksListBound6400]
  have hfrac1 : (1 : ℚ) ≤ q / (q - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hxy : y ≤ x := by
    rw [hx_def, hy_def]
    nlinarith [hfrac1, hy_nonneg]
  have hsqrt_mono :
      √((1 - x : ℚ) : ℝ) ≤ √((1 - y : ℚ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    have h := sub_le_sub_left hxy (1 : ℚ)
    exact_mod_cast h
  have hsqrt_y :
      √((1 - y : ℚ) : ℝ) ≤ (741454 : ℝ) / 1048576 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    ·
      norm_num [bchksListBound6400]
    · rw [hy_def]
      norm_num [bchksListBound6400]
  have hs_le :
      √((1 - x : ℚ) : ℝ) ≤ (741454 : ℝ) / 1048576 :=
    hsqrt_mono.trans hsqrt_y
  have hone_sub :
      (307122 : ℝ) / 1048576 ≤ 1 - √((1 - x : ℚ) : ℝ) := by
    have hsplit :
        (741454 : ℝ) / 1048576 + 307122 / 1048576 = 1 := by
      norm_num
    linarith [hs_le]
  have hfactor :
      ((1048575 : ℝ)) / 1048576 ≤ ((1 - 1 / q : ℚ) : ℝ) := by
    have h1q : (1 / q : ℚ) ≤ 1 / 1048576 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith [hq20]
    have hcast :
        ((1 - 1 / 1048576 : ℚ) : ℝ) ≤ ((1 - 1 / q : ℚ) : ℝ) := by
      exact_mod_cast sub_le_sub_left h1q 1
    calc ((1048575 : ℝ)) / 1048576 =
        ((1 - 1 / 1048576 : ℚ) : ℝ) := by
          push_cast
          norm_num
      _ ≤ ((1 - 1 / q : ℚ) : ℝ) := hcast
  have hfactor_nonneg : (0 : ℝ) ≤ ((1 - 1 / q : ℚ) : ℝ) :=
    le_trans (by norm_num) hfactor
  calc (bchksRadius6400 : ℝ) = (307121 : ℝ) / 1048576 := by
        norm_num [bchksRadius6400]
    _ ≤ ((1048575 : ℝ)) / 1048576 * ((307122 : ℝ) / 1048576) := by
        norm_num
    _ ≤ ((1 - 1 / q : ℚ) : ℝ) * (1 - √((1 - x : ℚ) : ℝ)) :=
        mul_le_mul hfactor hone_sub (by norm_num) hfactor_nonneg

/-- Finite-Johnson list bound for the squared code at the score-64 radius. -/
theorem bchks6400_lambda_le :
    Code.Lambda BCHKS6399SquaredCode (bchksRadius6400 : ℝ) ≤
      (bchksListBound6400 : ℕ∞) := by
  have hwrap := johnson_bound_lambda_le_ell BCHKS6399SquaredCode
    bchksListBound6400 (by norm_num [bchksListBound6400])
  have hmono := Code.Lambda_mono
    (C := BCHKS6399SquaredCode)
    bchks6400_radius_le_Jql
  have hchain : Code.Lambda BCHKS6399SquaredCode (bchksRadius6400 : ℝ) ≤
      (bchksListBound6400 : ℕ∞) := le_trans hmono hwrap
  exact hchain

end ProximityPrize.SubmissionLower

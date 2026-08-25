/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionLower.BCHKSList6399

/-!
# Exact integer-ball list bound at the 64.00-bit radius

The relative radius `307123 / 1048576` has absolute Hamming radius `76780` at
block length `262144`.  Keeping this floor, and keeping the diagonal term in
the agreement-incidence second moment, gives the exact bound `Lambda <= 42324`
for the two-row interleaving used by the BCHKS reduction.

This is a list-side theorem only.  It does not supply the MCA numerator needed
for a `ProtocolClaim 6400` certificate.
-/

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open scoped NNReal BigOperators

set_option maxRecDepth 100000

noncomputable def bchksRadius6400 : ℝ≥0 :=
  (307123 : ℝ≥0) / 1048576

def bchksErrors6400 : ℕ := 76780

def bchksListBound6400 : ℕ := 42324

lemma bchksRadius6400_floor :
    ⌊(bchksRadius6400 : ℝ) *
        (Fintype.card IRSProfile.Index : ℝ)⌋₊ = bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

private def centerCommon {n A : Type*} [Fintype n] [DecidableEq A]
    (u v y : n → A) : ℕ :=
  (Finset.univ.filter fun i => u i = y i ∧ v i = y i).card

private def centerMultiplicity {n A : Type*} [Fintype n] [DecidableEq A]
    (T : Finset (n → A)) (y : n → A) (i : n) : ℕ :=
  (T.filter fun c => c i = y i).card

private lemma sum_centerMultiplicity_eq_sum_agree
    {n A : Type*} [Fintype n] [DecidableEq A]
    (T : Finset (n → A)) (y : n → A) :
    ∑ i, centerMultiplicity T y i =
      ∑ c ∈ T, Code.agree c y := by
  classical
  simp only [centerMultiplicity, Code.agree, Finset.card_filter]
  rw [Finset.sum_comm]

private lemma sum_sq_centerMultiplicity_eq_sum_centerCommon
    {n A : Type*} [Fintype n] [DecidableEq A]
    (T : Finset (n → A)) (y : n → A) :
    ∑ i, (centerMultiplicity T y i : ℚ) ^ 2 =
      ∑ c ∈ T, ∑ c' ∈ T, (centerCommon c c' y : ℚ) := by
  classical
  simp only [centerMultiplicity, centerCommon, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [sq, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext c
  rw [Finset.sum_comm]
  congr 1
  funext c'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp_all

private lemma sq_sum_agree_le_centerCommon
    {n A : Type*} [Fintype n] [DecidableEq A]
    (T : Finset (n → A)) (y : n → A) :
    (∑ c ∈ T, (Code.agree c y : ℚ)) ^ 2 ≤
      (Fintype.card n : ℚ) *
        (∑ c ∈ T, ∑ c' ∈ T, (centerCommon c c' y : ℚ)) := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset n))
    (f := fun i => (centerMultiplicity T y i : ℚ))
  rw [Finset.card_univ, sum_sq_centerMultiplicity_eq_sum_centerCommon] at hcs
  have hsum :
      ∑ i, (centerMultiplicity T y i : ℚ) =
        ∑ c ∈ T, (Code.agree c y : ℚ) := by
    exact_mod_cast sum_centerMultiplicity_eq_sum_agree T y
  rw [← hsum]
  exact hcs

private lemma centerCommon_self
    {n A : Type*} [Fintype n] [DecidableEq A]
    (c y : n → A) : centerCommon c c y = Code.agree c y := by
  classical
  simp [centerCommon, Code.agree]

private lemma centerCommon_le_agree
    {n A : Type*} [Fintype n] [DecidableEq A]
    (c c' y : n → A) : centerCommon c c' y ≤ Code.agree c c' := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi.1.trans hi.2.symm

private lemma integer_ball_card_le
    (y : IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
      IRSProfile.Field)
    (T : Finset (IRSProfile.Index → Fin 2 →
      Fin IRSProfile.interleaving → IRSProfile.Field))
    (hT : ∀ c ∈ T,
      c ∈ Code.closeCodewordsRel BCHKS6399SquaredCode y
        (bchksRadius6400 : ℝ)) :
    T.card ≤ bchksListBound6400 := by
  classical
  let L : ℚ := T.card
  have hclose : ∀ c ∈ T, (185364 : ℚ) ≤ Code.agree c y := by
    intro c hc
    have hball := (Code.mem_closeCodewordsRel_iff.mp (hT c hc)).2
    simp only [Code.relHammingDist_coe] at hball
    have hn : (Fintype.card IRSProfile.Index : ℝ) = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn] at hball
    have hradius : (bchksRadius6400 : ℝ) = (307123 : ℝ) / 1048576 := by
      norm_num [bchksRadius6400]
    rw [hradius] at hball
    have hdistR : (hammingDist y c : ℝ) < 76781 := by
      let d : ℕ := hammingDist y c
      change (d : ℝ) / 262144 ≤ (307123 : ℝ) / 1048576 at hball
      change (d : ℝ) < 76781
      have hball' : (d : ℝ) ≤ (307123 : ℝ) / 4 := by
        calc
          (d : ℝ) = ((d : ℝ) / 262144) * 262144 := by ring
          _ ≤ ((307123 : ℝ) / 1048576) * 262144 := by
            exact mul_le_mul_of_nonneg_right hball (by norm_num)
          _ = (307123 : ℝ) / 4 := by norm_num
      linarith
    have hdist : hammingDist y c ≤ 76780 := by
      have : hammingDist y c < 76781 := by exact_mod_cast hdistR
      omega
    have hagree : Code.agree c y + hammingDist y c = 262144 := by
      rw [hammingDist_comm]
      simpa [IRSProfile.Index] using
        (Code.agree_add_hammingDist (u := c) (v := y))
    exact_mod_cast (show 185364 ≤ Code.agree c y by omega)
  have hpair : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' →
      (Code.agree c c' : ℚ) ≤ 131071 := by
    intro c hc c' hc' hne
    have hdist := Code.minDist_le_dist
      (C := BCHKS6399SquaredCode)
      (Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
      (Code.mem_closeCodewordsRel_iff.mp (hT c' hc')).1 hne
    rw [bchks6399_squaredCode_minDistance] at hdist
    have hagree : Code.agree c c' + hammingDist c c' = 262144 := by
      simpa [IRSProfile.Index] using
        (Code.agree_add_hammingDist (u := c) (v := c'))
    exact_mod_cast (show Code.agree c c' ≤ 131071 by omega)
  have hB : L * 185364 ≤ ∑ c ∈ T, (Code.agree c y : ℚ) := by
    calc
      L * 185364 = ∑ _c ∈ T, (185364 : ℚ) := by
        simp [L]
      _ ≤ ∑ c ∈ T, (Code.agree c y : ℚ) :=
        Finset.sum_le_sum hclose
  have hcommon :
      ∑ c ∈ T, ∑ c' ∈ T, (centerCommon c c' y : ℚ) ≤
        ∑ c ∈ T,
          ((Code.agree c y : ℚ) + (L - 1) * 131071) := by
    apply Finset.sum_le_sum
    intro c hc
    have hsplit :
        ∑ c' ∈ T, (centerCommon c c' y : ℚ) =
          (centerCommon c c y : ℚ) +
            ∑ c' ∈ T.erase c, (centerCommon c c' y : ℚ) :=
      (Finset.add_sum_erase T
        (fun c' => (centerCommon c c' y : ℚ)) hc).symm
    have herase :
        ∑ c' ∈ T.erase c, (centerCommon c c' y : ℚ) ≤
          (L - 1) * 131071 := by
      have hb : ∀ c' ∈ T.erase c,
          (centerCommon c c' y : ℚ) ≤ 131071 := by
        intro c' hc'
        have hca : (centerCommon c c' y : ℚ) ≤
            (Code.agree c c' : ℚ) := by
          exact_mod_cast centerCommon_le_agree c c' y
        exact hca.trans (hpair c hc c' (Finset.mem_of_mem_erase hc')
          (Ne.symm (Finset.ne_of_mem_erase hc')))
      have hsum := Finset.sum_le_card_nsmul (T.erase c)
        (fun c' => (centerCommon c c' y : ℚ)) 131071 hb
      rw [nsmul_eq_mul] at hsum
      have hcarderase : ((T.erase c).card : ℚ) = L - 1 := by
        rw [Finset.card_erase_of_mem hc]
        have hcard : 1 ≤ T.card := Finset.card_pos.mpr ⟨c, hc⟩
        rw [Nat.cast_sub hcard]
        rfl
      rwa [hcarderase] at hsum
    rw [hsplit, centerCommon_self]
    linarith
  have hsum_nonneg :
      0 ≤ ∑ c ∈ T, (Code.agree c y : ℚ) := by positivity
  have hLB_nonneg : 0 ≤ L * 185364 := by positivity
  have hsq : (L * 185364) ^ 2 ≤
      (∑ c ∈ T, (Code.agree c y : ℚ)) ^ 2 :=
    pow_le_pow_left₀ hLB_nonneg hB 2
  have hcs := sq_sum_agree_le_centerCommon T y
  have hkey : (∑ c ∈ T, (Code.agree c y : ℚ)) ^ 2 ≤
      (262144 : ℚ) *
        (∑ c ∈ T,
          ((Code.agree c y : ℚ) + (L - 1) * 131071)) := by
    refine hcs.trans ?_
    have hn : (Fintype.card IRSProfile.Index : ℚ) = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    exact mul_le_mul_of_nonneg_left hcommon (by norm_num)
  have hsum_lower : L * 185364 ≤
      ∑ c ∈ T, (Code.agree c y : ℚ) := hB
  have hsum_upper :
      ∑ c ∈ T, (Code.agree c y : ℚ) ≤ L * 262144 := by
    calc
      ∑ c ∈ T, (Code.agree c y : ℚ)
          ≤ ∑ _c ∈ T, (262144 : ℚ) := by
              apply Finset.sum_le_sum
              intro c hc
              have ha : Code.agree c y ≤ 262144 := by
                simpa [IRSProfile.Index] using
                  (Code.agree_le_card (u := c) (v := y))
              exact_mod_cast ha
      _ = L * 262144 := by simp [L]
  by_contra hnot
  have hLnat : 42325 ≤ T.card := by
    simp only [bchksListBound6400] at hnot ⊢
    omega
  have hL : (42325 : ℚ) ≤ L := by
    change (42325 : ℚ) ≤ (T.card : ℚ)
    exact_mod_cast hLnat
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hsum_diag :
      ∑ c ∈ T,
          ((Code.agree c y : ℚ) + (L - 1) * 131071) =
        (∑ c ∈ T, (Code.agree c y : ℚ)) +
          L * (L - 1) * 131071 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    change (∑ c ∈ T, (Code.agree c y : ℚ)) +
        (T.card : ℚ) * ((L - 1) * 131071) = _
    change (∑ c ∈ T, (Code.agree c y : ℚ)) +
        L * ((L - 1) * 131071) = _
    ring
  rw [hsum_diag] at hkey
  have hmono :
      (L * 185364) ^ 2 - 262144 * (L * 185364) ≤
        (∑ c ∈ T, (Code.agree c y : ℚ)) ^ 2 -
          262144 * (∑ c ∈ T, (Code.agree c y : ℚ)) := by
    nlinarith
  nlinarith

theorem bchks6400_integer_ball_lambda_le :
    Code.Lambda BCHKS6399SquaredCode (bchksRadius6400 : ℝ) ≤
      (bchksListBound6400 : ℕ∞) := by
  apply Code.Lambda_le_of_forall_finset_card_le
  intro y T hT
  exact integer_ball_card_le y T hT

/-- Exact remaining field-sized numerator allowance after the proved list term. -/
lemma bchks6400_remaining_mca_budget :
    274980728111395087 - bchksListBound6400 = 274980728111352763 := by
  norm_num [bchksListBound6400]

end ProximityPrize.SubmissionLower

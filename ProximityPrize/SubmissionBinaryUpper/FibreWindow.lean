/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.FibrePencil

/-!
# The coset-pencil window certificate

Words, codewords, the violating instance and the density bound for the coset
pencil of `FibrePencil`.
-/

namespace ProximityPrize.SubmissionBinaryUpper.FibrePencil

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open scoped NNReal

/-! ## Words, codewords and the violating instance -/

abbrev kk := BinaryIRSProfile.totalDimension
abbrev ss := BinaryIRSProfile.interleaving

local instance : NeZero ss := ⟨by norm_num [ss, BinaryIRSProfile.interleaving]⟩

/-- The pencil denominator `Y - α`, which has no root on the domain. -/
noncomputable def Den : Polynomial FF := YF - Polynomial.C alpha

theorem Den_eval_ne (j : Idx) : Den.eval (BinaryIRSProfile.domain j) ≠ 0 := by
  rw [Den, eval_sub, eval_C, sub_ne_zero, YF, map_eval_domain, Y_domain]
  apply alpha_ne_label
  have := j.isLt
  change j.val < 2 ^ 21 at this
  omega

theorem Den_isUnit (j : Idx) : IsUnit (Den.eval (BinaryIRSProfile.domain j)) :=
  isUnit_iff_ne_zero.mpr (Den_eval_ne j)

/-- Division by the denominator is written with `Ring.inverse`, so that every
algebraic step stays inside the commutative-ring structure of `Ext3`. -/
noncomputable def word1 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then
    RF.eval (BinaryIRSProfile.domain j) * (VF U0).eval (YF.eval (BinaryIRSProfile.domain j)) *
      Ring.inverse (Den.eval (BinaryIRSProfile.domain j))
  else 0

noncomputable def word2 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then
    RF.eval (BinaryIRSProfile.domain j) * Ring.inverse (Den.eval (BinaryIRSProfile.domain j))
  else 0

noncomputable def cpoly (U : Finset ℕ) : Polynomial FF := RF * (Q U).comp YF

theorem cpoly_natDegree_le {U : Finset ℕ} (hU : U ∈ Sel) : (cpoly U).natDegree ≤ 1048575 := by
  calc (cpoly U).natDegree ≤ RF.natDegree + ((Q U).comp YF).natDegree := natDegree_mul_le
    _ ≤ 16383 + (Q U).natDegree * YF.natDegree := by
        rw [RF_natDegree]; exact Nat.add_le_add_left natDegree_comp_le _
    _ ≤ 16383 + 63 * 16384 := by
        rw [YF_natDegree]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Q_natDegree_le hU)) _
    _ = 1048575 := by norm_num

theorem cpoly_degree_lt {U : Finset ℕ} (hU : U ∈ Sel) : (cpoly U).degree < (kk / ss : ℕ) := by
  rw [PrescribedTop.rowDimension_eq]
  by_cases hz : cpoly U = 0
  · rw [hz]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hz]
    exact_mod_cast lt_of_le_of_lt (cpoly_natDegree_le hU) (by norm_num)

abbrev Carrier := {U : Finset ℕ // U ∈ Sel}

noncomputable def pmsg (a : Carrier) : Fin kk → FF :=
  Classical.choose (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.prop))

theorem pmsg_spec (a : Carrier) (j : Idx) (row : Fin ss) :
    BinaryIRSProfile.encoder (pmsg a) j row =
      if row = 0 then (cpoly a.val).eval (BinaryIRSProfile.domain j) else 0 :=
  Classical.choose_spec (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.prop)) j row

theorem word_agree (a : Carrier) {j : Idx} (hj : j ∈ J a.val) :
    word1 j + gamma a.val • word2 j = BinaryIRSProfile.encoder (pmsg a) j := by
  funext row
  rw [pmsg_spec, Pi.add_apply, Pi.smul_apply]
  by_cases hrow : row = 0
  · subst hrow
    simp only [word1, word2, if_pos, smul_eq_mul]
    rw [cpoly, eval_mul, eval_comp, gamma, deltaV, eval_sub]
    set x := BinaryIRSProfile.domain j
    set z := YF.eval x
    have hDi : Ring.inverse (Den.eval x) * Den.eval x = 1 :=
      Ring.inverse_mul_cancel _ (Den_isUnit j)
    have hD : Den.eval x = z - alpha := by rw [Den, eval_sub, eval_C]
    have hQ := congrArg (fun P => P.eval z) (Q_spec a.val)
    simp only [eval_mul, eval_sub, eval_X, eval_C, pencil, deltaV] at hQ
    rw [← hD] at hQ
    have hvan : RF.eval x * (VF a.val).eval z = 0 := by
      rcases Finset.mem_union.mp hj with hc | hf
      · rw [RF_eval_core hc, zero_mul]
      · rw [VF_eval_fib (Sel_cand a.prop) hf, mul_zero]
    linear_combination (RF.eval x * (Q a.val).eval z) * hDi +
      Ring.inverse (Den.eval x) * hvan - (RF.eval x * Ring.inverse (Den.eval x)) * hQ
  · simp only [word1, word2, if_neg hrow, smul_zero, add_zero]

theorem YFC_monic : Den.Monic := by
  rw [Den]
  have hm : YF.Monic := Y_monic.map _
  refine hm.sub_of_left ?_
  rw [degree_eq_natDegree hm.ne_zero, YF_natDegree]
  exact degree_C_le.trans_lt (by exact_mod_cast (by norm_num : 0 < 16384))

theorem YFC_natDegree : Den.natDegree = 16384 := by
  rw [Den, natDegree_sub_C, YF_natDegree]

noncomputable def rowPoly (u : Fin kk → FF) : Polynomial FF :=
  ToyProblem.Spec.rsPolynomial (kk / ss)
    (unflatten kk ss BinaryIRSProfile.interleaving_dvd_totalDimension u 0)

theorem rowPoly_degree_lt (u : Fin kk → FF) : (rowPoly u).degree < (1048576 : ℕ) := by
  have h := ToyProblem.Spec.rsPolynomial_degree_lt (kk / ss)
    (unflatten kk ss BinaryIRSProfile.interleaving_dvd_totalDimension u 0)
  have hcast : ((kk / ss : ℕ) : WithBot ℕ) = ((1048576 : ℕ) : WithBot ℕ) := by
    rw [PrescribedTop.rowDimension_eq]
  rw [hcast] at h
  exact h

theorem enc_row0 (u : Fin kk → FF) (j : Idx) :
    BinaryIRSProfile.encoder u j 0 = (rowPoly u).eval (BinaryIRSProfile.domain j) := by
  have h0 : BinaryIRSProfile.encoder u j 0 = BinaryIRSProfile.encoder u j 0 := rfl
  conv_rhs at h0 => rw [BinaryIRSProfile.encoder, encoder_apply, ToyProblem.Spec.rsEncoder_apply]
  exact h0

theorem word2_zero (j : Idx) :
    word2 j 0 = RF.eval (BinaryIRSProfile.domain j) *
      Ring.inverse (Den.eval (BinaryIRSProfile.domain j)) := by
  simp only [word2, if_pos]

theorem alg_cancel (r i c d : FF) (h0 : r * i = c) (hDi : i * d = 1) : r = c * d := by
  linear_combination d * h0 - r * hDi

/-- The polynomial core of the violation argument, stated for an arbitrary
row polynomial so that only one polynomial ring structure is in play. -/
theorem far_generic (c : Polynomial FF) (hc : c.degree < (1048576 : ℕ)) (S : Finset Idx)
    (hcard : 1064960 ≤ S.card)
    (h : ∀ j ∈ S, RF.eval (BinaryIRSProfile.domain j) =
      c.eval (BinaryIRSProfile.domain j) * Den.eval (BinaryIRSProfile.domain j)) : False := by
  have hRdeg : RF.degree < (S.card : ℕ) := by
    rw [degree_eq_natDegree RF_monic.ne_zero, RF_natDegree]
    exact_mod_cast (by omega : 16383 < S.card)
  have heval : ∀ j ∈ S, RF.eval (BinaryIRSProfile.domain j) =
      (c * Den).eval (BinaryIRSProfile.domain j) := by
    intro j hj
    rw [eval_mul]
    exact h j hj
  by_cases hc0 : c = 0
  · have heq := Polynomial.eq_of_degrees_lt_of_eval_index_eq S
      BinaryIRSProfile.domain.injective.injOn hRdeg
      (by rw [hc0, zero_mul]; exact WithBot.bot_lt_coe _) heval
    rw [hc0, zero_mul] at heq
    exact RF_monic.ne_zero heq
  · have hn : c.natDegree < 1048576 := (natDegree_lt_iff_degree_lt hc0).mpr hc
    have hPdeg : (c * Den).degree < (S.card : ℕ) := by
      rw [degree_eq_natDegree (mul_ne_zero hc0 YFC_monic.ne_zero),
        natDegree_mul hc0 YFC_monic.ne_zero, YFC_natDegree]
      exact_mod_cast (by omega : c.natDegree + 16384 < S.card)
    have heq := Polynomial.eq_of_degrees_lt_of_eval_index_eq S
      BinaryIRSProfile.domain.injective.injOn hRdeg hPdeg heval
    have h := congrArg Polynomial.natDegree heq
    rw [RF_natDegree, natDegree_mul hc0 YFC_monic.ne_zero, YFC_natDegree] at h
    omega

theorem word2_far (u : Fin kk → FF) (S : Finset Idx) (hcard : 1064960 ≤ S.card)
    (hagree : ∀ j ∈ S, word2 j = BinaryIRSProfile.encoder u j) : False := by
  refine far_generic (rowPoly u) (rowPoly_degree_lt u) S hcard ?_
  intro j hj
  have h0 := congrFun (hagree j hj) (0 : Fin ss)
  rw [word2_zero, enc_row0] at h0
  exact alg_cancel _ _ _ _ h0 (Ring.inverse_mul_cancel _ (Den_isUnit j))

theorem gammaImage_card : (Sel.image gamma).card = NN := by
  rw [Finset.card_image_of_injOn gamma_injOn, Sel_card]

/-! ## The certified window -/

theorem epsilon_lt_fraction :
    ProximityPrize.Benchmark.Binary.Upper.epsilonStar <
      ((NN : ℕ) : ℝ≥0) / (Fintype.card FF : ℝ≥0) := by
  unfold ProximityPrize.Benchmark.Binary.Upper.epsilonStar ProximityGap.prizeThreshold
  rw [BF64.card_ext3]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num [NN]

theorem winningSetDensity_gt_epsilon_window (δ : ℝ≥0)
    (hlo : (966657 / 2097152 : ℝ≥0) ≤ δ) (hhi : δ < (1015833 / 2097152 : ℝ≥0)) :
    ProximityPrize.Benchmark.Binary.Upper.epsilonStar <
      winningSetDensity BinaryIRSProfile.encoder δ := by
  classical
  have hcardI : Fintype.card Idx = 2097152 := PrescribedTop.card_Idx
  have hd_lo : (966657 / 2097152 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hlo
  have hd_hi : (δ : ℝ) < 1015833 / 2097152 := by exact_mod_cast hhi
  have hx_lo : (1081319 : ℝ) < (1 - (δ : ℝ)) * 2097152 := by nlinarith
  have hx_hi : (1 - (δ : ℝ)) * 2097152 ≤ 1130495 := by nlinarith
  have ht_hi : Nat.ceil ((1 - (δ : ℝ)) * 2097152) ≤ 1130495 :=
    Nat.ceil_le.mpr (by exact_mod_cast hx_hi)
  have hsub : ∀ a : Carrier, ∃ T ⊆ J a.val, T.card = Nat.ceil ((1 - (δ : ℝ)) * 2097152) := by
    intro a
    exact Finset.exists_subset_card_eq (by rw [J_card (Sel_cand a.prop)]; exact ht_hi)
  choose T hTsub hTcard using hsub
  let x : ViolatingInstance BinaryIRSProfile.encoder δ :=
    { v := 0
      μ₁ := 0
      μ₂ := 0
      f₁ := word1
      f₂ := word2
      violates := by
        rintro ⟨W, ⟨M, hW, -⟩, S, hS, hA⟩
        have hSreal : (1081319 : ℝ) < S.card := by
          rw [hcardI] at hS
          push_cast at hS
          linarith
        have hSnat : 1064960 ≤ S.card := by
          have : (1081319 : ℕ) < S.card := by exact_mod_cast hSreal
          omega
        refine word2_far (M 1) S hSnat ?_
        intro j hj
        have h := hA 1 j hj
        rw [hW 1] at h
        simpa using h }
  have hsubset : ((Sel.image gamma : Finset FF) : Set FF) ⊆
      winningSetFor BinaryIRSProfile.encoder δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ := by
    intro γ hγ
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hγ
    let a : Carrier := ⟨U, hU⟩
    simp only [winningSetFor, Set.mem_setOf_eq]
    refine ⟨![BinaryIRSProfile.encoder (pmsg a)], ⟨![pmsg a], ?_, ?_⟩, T a, ?_, ?_⟩
    · intro i
      fin_cases i
      rfl
    · intro i
      fin_cases i
      simp [x]
    · rw [hTcard, hcardI]
      exact_mod_cast Nat.le_ceil _
    · intro i j hj
      fin_cases i
      have h := word_agree a (hTsub a hj)
      simpa [x] using h
  have hncard : NN ≤ (winningSetFor BinaryIRSProfile.encoder δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard := by
    rw [← gammaImage_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsubset (Set.toFinite _)
  refine lt_of_lt_of_le epsilon_lt_fraction (le_trans ?_ (winningSetRatio_le_winningSetDensity x))
  rw [winningSetRatio]
  gcongr

end ProximityPrize.SubmissionBinaryUpper.FibrePencil

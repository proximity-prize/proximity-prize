/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.PoleFamily

/-!
# The pole pair of TR26-237, Lemma 6.1, below half radius

Every member `A` of `PoleFamily` has `L_W L_A = R + C_A` with the common top
`R = L_W X^(2^20)` and `deg C_A ≤ 2^20`.  For a pole `β` outside the domain take

* `f₂ = 1 / (x - β)`, which agrees with no row codeword on more than `2^20`
  points, since `1 - c(x) (x - β)` is nonzero at `β`;
* `f₁ = R(x) / (x - β)`.

On `W ∪ A`, of size `9 N / 16`, `R = -C_A`, so `f₁ + C_A(β) f₂` is the codeword
`-(C_A - C_A(β)) / (x - β)` of degree below `2^20`.  A generic `β ∈ Ext3` makes
`A ↦ C_A(β)` injective on `2^64 + 1` members, so the radius window
`[7/16, 1/2)` is unsafe.
-/

namespace ProximityPrize.SubmissionBinaryUpper.PolePencil

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open ProximityPrize.SubmissionBinaryUpper.FlatPoly
open ProximityPrize.SubmissionBinaryUpper.PoleFamily
open scoped NNReal

set_option linter.constructorNameAsVariable false

abbrev FF := BinaryIRSProfile.Field

theorem algebraMap_injective : Function.Injective (algebraMap K FF) :=
  (algebraMap K FF).injective

theorem domain_eq (j : Idx) : BinaryIRSProfile.domain j = algebraMap K FF (nodeN j.val) := rfl

/-! ## The selected members -/

abbrev NN : ℕ := 2 ^ 64 + 1

theorem card_Param : Fintype.card Param = 2 ^ 71 := by
  simp only [Param, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem exists_selected : ∃ S : Finset Param, S.card = NN := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Param)) (n := NN)
    (by rw [Finset.card_univ, card_Param]; norm_num)
  exact ⟨S, hS⟩

noncomputable def Sel : Finset Param := Classical.choose exists_selected

theorem Sel_card : Sel.card = NN := Classical.choose_spec exists_selected

noncomputable def CF (p : Param) : Polynomial FF := (Cp p).map (algebraMap K FF)

theorem CF_sub_ne_zero {p q : Param} (hne : p ≠ q) : CF p - CF q ≠ 0 := by
  rw [CF, CF, ← Polynomial.map_sub]
  refine (Polynomial.map_ne_zero_iff algebraMap_injective).mpr ?_
  exact sub_ne_zero.mpr fun h => hne (Cp_injective h)

theorem CF_natDegree_le (p : Param) : (CF p).natDegree ≤ 2 ^ 20 :=
  natDegree_map_le.trans (Cp_natDegree_le p)

theorem CF_sub_natDegree_le (p q : Param) : (CF p - CF q).natDegree ≤ 2 ^ 20 :=
  (natDegree_sub_le _ _).trans (max_le (CF_natDegree_le p) (CF_natDegree_le q))

/-! ## The generic pole -/

noncomputable irreducible_def domainF : Finset FF :=
  (Finset.univ : Finset Idx).image BinaryIRSProfile.domain

theorem domainF_card : domainF.card ≤ 2 ^ 21 := by
  rw [domainF_def]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, PrescribedTop.card_Idx]
  norm_num

theorem mem_domainF (j : Idx) : BinaryIRSProfile.domain j ∈ domainF := by
  rw [domainF_def]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

noncomputable def collisionRoots (z : Param × Param) : Finset FF :=
  (CF z.1 - CF z.2).roots.toFinset

noncomputable def bad : Finset FF := domainF ∪ Sel.offDiag.biUnion collisionRoots

theorem bad_card_lt : bad.card < (Finset.univ : Finset FF).card := by
  have hcoll : (Sel.offDiag.biUnion collisionRoots).card ≤ Sel.offDiag.card * 2 ^ 20 := by
    refine Finset.card_biUnion_le_card_mul _ _ _ ?_
    intro z _
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (CF_sub_natDegree_le _ _))
  have hoff : Sel.offDiag.card = NN * (NN - 1) := by
    rw [Finset.offDiag_card, Sel_card, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hD := domainF_card
  rw [Finset.card_univ, BF64.card_ext3]
  calc bad.card ≤ domainF.card + (Sel.offDiag.biUnion collisionRoots).card :=
        Finset.card_union_le _ _
    _ ≤ 2 ^ 21 + NN * (NN - 1) * 2 ^ 20 := by rw [← hoff]; omega
    _ < 2 ^ 192 := by norm_num [NN]

theorem exists_beta : ∃ a : FF, a ∉ bad := by
  by_contra h
  push_neg at h
  have : bad = Finset.univ := Finset.eq_univ_of_forall h
  have hlt := bad_card_lt
  rw [this] at hlt
  exact lt_irrefl _ hlt

noncomputable def beta : FF := Classical.choose exists_beta

theorem beta_not_bad : beta ∉ bad := Classical.choose_spec exists_beta

theorem beta_ne_domain (j : Idx) : BinaryIRSProfile.domain j ≠ beta := by
  intro e
  apply beta_not_bad
  exact Finset.mem_union_left _ (e ▸ mem_domainF j)

/-- The winning challenge of a member. -/
noncomputable def gamma (p : Param) : FF := (CF p).eval beta

theorem gamma_injOn : Set.InjOn gamma (Sel : Set Param) := by
  intro p hp q hq heq
  by_contra hne
  apply beta_not_bad
  have hroot : beta ∈ collisionRoots (p, q) := by
    rw [collisionRoots, Multiset.mem_toFinset, mem_roots (CF_sub_ne_zero hne)]
    rw [IsRoot, eval_sub]
    exact sub_eq_zero.mpr heq
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hne⟩, hroot⟩)

theorem gammaImage_card : (Sel.image gamma).card = NN := by
  rw [Finset.card_image_of_injOn gamma_injOn, Sel_card]

/-! ## Codewords -/

noncomputable def Q (p : Param) : Polynomial FF :=
  (CF p - Polynomial.C (gamma p)) /ₘ (Polynomial.X - Polynomial.C beta)

theorem Q_spec (p : Param) :
    (Polynomial.X - Polynomial.C beta) * Q p = CF p - Polynomial.C (gamma p) := by
  rw [Q, mul_divByMonic_eq_iff_isRoot]
  simp [IsRoot, gamma]

theorem Q_natDegree_le (p : Param) : (Q p).natDegree ≤ 2 ^ 20 - 1 := by
  rw [Q, natDegree_divByMonic _ (monic_X_sub_C beta), natDegree_X_sub_C]
  have h : (CF p - Polynomial.C (gamma p)).natDegree ≤ 2 ^ 20 := by
    rw [natDegree_sub_C]
    exact CF_natDegree_le p
  omega

/-- The row codeword of a member. -/
noncomputable def cpoly (p : Param) : Polynomial FF := -Q p

abbrev kk := PrescribedTop.kk
abbrev ss := PrescribedTop.ss

local instance : NeZero ss := ⟨by norm_num [ss, PrescribedTop.ss, BinaryIRSProfile.interleaving]⟩

theorem cpoly_degree_lt (p : Param) : (cpoly p).degree < (kk / ss : ℕ) := by
  rw [PrescribedTop.rowDimension_eq]
  by_cases hz : cpoly p = 0
  · rw [hz]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hz, cpoly, natDegree_neg]
    have := Q_natDegree_le p
    exact_mod_cast (show (Q p).natDegree < PrescribedTop.mm by
      simp only [PrescribedTop.mm]; omega)

/-- The common top of every member, mapped to the challenge field. -/
noncomputable def RF : Polynomial FF := (LamW * Xp (2 ^ 20)).map (algebraMap K FF)

theorem RF_add_CF_eval (p : Param) {j : Idx} (hj : j ∈ Sset p) :
    RF.eval (BinaryIRSProfile.domain j) + (CF p).eval (BinaryIRSProfile.domain j) = 0 := by
  rw [RF, CF, ← eval_add, ← Polynomial.map_add, ← Cp_split, domain_eq, eval_map,
    eval₂_at_apply, vanish_Sset p hj, map_zero]

/-! ## Words and the violating instance -/

noncomputable def word1 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then
    RF.eval (BinaryIRSProfile.domain j) * Ring.inverse (BinaryIRSProfile.domain j - beta)
  else 0

noncomputable def word2 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then Ring.inverse (BinaryIRSProfile.domain j - beta) else 0

theorem Den_isUnit (j : Idx) : IsUnit (BinaryIRSProfile.domain j - beta) :=
  isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (beta_ne_domain j))

abbrev Carrier := {p : Param // p ∈ Sel}

noncomputable def pmsg (a : Carrier) : Fin kk → FF :=
  Classical.choose (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.val))

theorem pmsg_spec (a : Carrier) (j : Idx) (row : Fin ss) :
    BinaryIRSProfile.encoder (pmsg a) j row =
      if row = 0 then (cpoly a.val).eval (BinaryIRSProfile.domain j) else 0 :=
  Classical.choose_spec (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.val)) j row

theorem word_agree (a : Carrier) {j : Idx} (hj : j ∈ Sset a.val) :
    word1 j + gamma a.val • word2 j = BinaryIRSProfile.encoder (pmsg a) j := by
  funext row
  rw [pmsg_spec, Pi.add_apply, Pi.smul_apply]
  by_cases hrow : row = 0
  · subst hrow
    simp only [word1, word2, if_pos, smul_eq_mul]
    rw [cpoly, eval_neg]
    set x := BinaryIRSProfile.domain j
    have hDi : Ring.inverse (x - beta) * (x - beta) = 1 :=
      Ring.inverse_mul_cancel _ (Den_isUnit j)
    have hQ := congrArg (fun P => P.eval x) (Q_spec a.val)
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hQ
    have hv := RF_add_CF_eval a.val hj
    linear_combination Ring.inverse (x - beta) * hv + Ring.inverse (x - beta) * hQ -
      (Q a.val).eval x * hDi
  · simp only [word1, word2, if_neg hrow, smul_zero, add_zero]

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

/-- `1/(x - β)` agrees with no row codeword on more than `2^20` points. -/
theorem far_generic (c : Polynomial FF) (hc : c.degree < (1048576 : ℕ)) (S : Finset Idx)
    (hcard : 1048576 < S.card)
    (h : ∀ j ∈ S, c.eval (BinaryIRSProfile.domain j) * (BinaryIRSProfile.domain j - beta) = 1) :
    False := by
  by_cases hc0 : c = 0
  · obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have := h j hj
    rw [hc0, eval_zero, zero_mul] at this
    exact zero_ne_one this
  · have hn : c.natDegree < 1048576 := (natDegree_lt_iff_degree_lt hc0).mpr hc
    have hne : c * (Polynomial.X - Polynomial.C beta) ≠ 0 := mul_ne_zero hc0 (X_sub_C_ne_zero beta)
    have hPdeg : (c * (Polynomial.X - Polynomial.C beta)).degree < ((S.card : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree hne, natDegree_mul hc0 (X_sub_C_ne_zero beta), natDegree_X_sub_C]
      exact_mod_cast (by omega : c.natDegree + 1 < S.card)
    have h1deg : (1 : Polynomial FF).degree < ((S.card : ℕ) : WithBot ℕ) := by
      rw [degree_one]
      exact_mod_cast (by omega : 0 < S.card)
    have heq := Polynomial.eq_of_degrees_lt_of_eval_index_eq S
      BinaryIRSProfile.domain.injective.injOn hPdeg h1deg (by
        intro j hj
        rw [eval_mul, eval_sub, eval_X, eval_C, eval_one]
        exact h j hj)
    have := congrArg (fun P => P.eval beta) heq
    simp at this

theorem word2_far (u : Fin kk → FF) (S : Finset Idx) (hcard : 1048576 < S.card)
    (hagree : ∀ j ∈ S, word2 j = BinaryIRSProfile.encoder u j) : False := by
  refine far_generic (rowPoly u) (rowPoly_degree_lt u) S hcard ?_
  intro j hj
  have h0 := congrFun (hagree j hj) (0 : Fin ss)
  rw [enc_row0] at h0
  simp only [word2, if_pos] at h0
  have hDi := Ring.inverse_mul_cancel _ (Den_isUnit j)
  rwa [h0] at hDi

/-! ## The certified window -/

theorem epsilon_lt_fraction :
    ProximityPrize.Benchmark.Binary.Upper.epsilonStar <
      ((NN : ℕ) : ℝ≥0) / (Fintype.card FF : ℝ≥0) := by
  unfold ProximityPrize.Benchmark.Binary.Upper.epsilonStar ProximityGap.prizeThreshold
  rw [BF64.card_ext3]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num [NN]

theorem winningSetDensity_gt_epsilon (δ : ℝ≥0)
    (hlo : (917504 / 2097152 : ℝ≥0) ≤ δ) (hhi : δ < (1048576 / 2097152 : ℝ≥0)) :
    ProximityPrize.Benchmark.Binary.Upper.epsilonStar <
      winningSetDensity BinaryIRSProfile.encoder δ := by
  classical
  have hcardI : Fintype.card Idx = 2097152 := PrescribedTop.card_Idx
  have hd_lo : (917504 / 2097152 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hlo
  have hd_hi : (δ : ℝ) < 1048576 / 2097152 := by exact_mod_cast hhi
  have hx_lo : (1048576 : ℝ) < (1 - (δ : ℝ)) * 2097152 := by linarith
  have hx_hi : (1 - (δ : ℝ)) * 2097152 ≤ 1179648 := by linarith
  have ht_hi : Nat.ceil ((1 - (δ : ℝ)) * 2097152) ≤ 1179648 :=
    Nat.ceil_le.mpr (by exact_mod_cast hx_hi)
  have hsub : ∀ a : Carrier, ∃ T ⊆ Sset a.val,
      T.card = Nat.ceil ((1 - (δ : ℝ)) * 2097152) := by
    intro a
    refine Finset.exists_subset_card_eq ?_
    rw [Sset_card]
    exact ht_hi.trans (by norm_num)
  choose T hTsub hTcard using hsub
  let x : ViolatingInstance BinaryIRSProfile.encoder δ :=
    { v := 0
      μ₁ := 0
      μ₂ := 0
      f₁ := word1
      f₂ := word2
      violates := by
        rintro ⟨W, ⟨M, hW, -⟩, S, hS, hA⟩
        have hSreal : (1048576 : ℝ) < S.card := by
          rw [hcardI] at hS
          push_cast at hS
          linarith
        have hSnat : 1048576 < S.card := by exact_mod_cast hSreal
        refine word2_far (M 1) S hSnat ?_
        intro j hj
        have h := hA 1 j hj
        rw [hW 1] at h
        simpa using h }
  have hsubset : ((Sel.image gamma : Finset FF) : Set FF) ⊆
      winningSetFor BinaryIRSProfile.encoder δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ := by
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
    let a : Carrier := ⟨p, hp⟩
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

end ProximityPrize.SubmissionBinaryUpper.PolePencil

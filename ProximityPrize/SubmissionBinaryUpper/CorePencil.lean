/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.LabelDecode

/-!
# The pole pair one level down, with a core

Write `Y = Ys(x)` for the label of a domain point and `R` for the locator of the 63 words
`1, …, 63` (the coset of label `0` without `0`).  Every member `S` of `LabelFamily` has
`V_S(Y) = R'(Y) + C_S(Y)` with the common top `R' = L_W^3 Y^12288` and `deg C_S ≤ 2^14`.
For a generic `α ∈ Ext3` take

* `f₂ = R(x) / (Y(x) - α)`,
* `f₁ = R(x) R'(Y(x)) / (Y(x) - α)`.

On the core both words vanish, and so does every codeword `R(x) Q(Y(x))`.  On the 64-point
fibres over `S`, `R'(Y) = -C_S(Y)`, so `f₁ + C_S(α) f₂ = -R(x) Q_S(Y(x))` with
`Q_S = (C_S - C_S(α)) / (Y - α)`, of degree at most `63 + 64 (2^14 - 1) = 2^20 - 1`.
The agreement set has `63 + 64 · 18432 = 9N/16 + 63` points, and `f₂` agrees with no row
codeword on more than `2^20 + 63` points.  A generic `α` separates `2^64 + 1` members.
-/

namespace ProximityPrize.SubmissionBinaryUpper.CorePencil

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open ProximityPrize.SubmissionBinaryUpper.FlatPoly
open ProximityPrize.SubmissionBinaryUpper.LabelSpace
open ProximityPrize.SubmissionBinaryUpper.LabelFamily
open scoped NNReal

set_option linter.constructorNameAsVariable false

attribute [local irreducible] FlatPoly.P SubspacePoly.L

abbrev FF := BinaryIRSProfile.Field
abbrev Idx := BinaryIRSProfile.Index

theorem algebraMap_injective : Function.Injective (algebraMap K FF) :=
  (algebraMap K FF).injective

theorem domain_eq (j : Idx) : BinaryIRSProfile.domain j = algebraMap K FF (nodeN j.val) := rfl

theorem map_eval_domain (P : Polynomial K) (j : Idx) :
    (P.map (algebraMap K FF)).eval (BinaryIRSProfile.domain j) =
      algebraMap K FF (P.eval (nodeN j.val)) := by
  rw [domain_eq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-! ## The number of members -/

theorem card_NZ11 : Fintype.card NZ11 = 2047 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [Yv, ZMod.card]

theorem card_NZ10 : Fintype.card NZ10 = 1023 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [ZMod.card]

theorem card_emb : Fintype.card (Fin 3 ↪ NZ10) = 1023 * 1022 * 1021 := by
  rw [Fintype.card_embedding_eq, card_NZ10, Fintype.card_fin]
  rfl

theorem card_Param : Fintype.card Param = 455 * 32 * 2047 * (1023 * 1022 * 1021) * 512 * 4 := by
  simp only [Param, Fintype.card_prod, Fintype.card_fin, ZMod.card, card_NZ11, card_emb,
    Fintype.card_fun]
  norm_num

abbrev NN : ℕ := 2 ^ 64 + 1

theorem exists_selected : ∃ S : Finset Param, S.card = NN := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Param)) (n := NN)
    (by rw [Finset.card_univ, card_Param]; norm_num)
  exact ⟨S, hS⟩

noncomputable def Sel : Finset Param := Classical.choose exists_selected

theorem Sel_card : Sel.card = NN := Classical.choose_spec exists_selected

/-! ## Corrections in the challenge field -/

noncomputable def CF (p : Param) : Polynomial FF := (Cp p).map (algebraMap K FF)

theorem CF_sub_ne_zero {p q : Param} (hne : p ≠ q) : CF p - CF q ≠ 0 := by
  rw [CF, CF, ← Polynomial.map_sub]
  refine (Polynomial.map_ne_zero_iff algebraMap_injective).mpr ?_
  exact sub_ne_zero.mpr fun h => hne (LabelDecode.Cp_injective h)

theorem CF_natDegree_le (p : Param) : (CF p).natDegree ≤ 16384 :=
  natDegree_map_le.trans (Cp_natDegree_le p)

theorem CF_sub_natDegree_le (p q : Param) : (CF p - CF q).natDegree ≤ 16384 :=
  (natDegree_sub_le _ _).trans (max_le (CF_natDegree_le p) (CF_natDegree_le q))

/-! ## The generic pencil point -/

/-- The labels of the domain points. -/
noncomputable irreducible_def labelsF : Finset FF :=
  (Finset.univ : Finset Idx).image fun j => algebraMap K FF (Ys.eval (nodeN j.val))

theorem labelsF_card : labelsF.card ≤ 2 ^ 21 := by
  rw [labelsF_def]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, PrescribedTop.card_Idx]
  norm_num

noncomputable def collisionRoots (z : Param × Param) : Finset FF :=
  (CF z.1 - CF z.2).roots.toFinset

noncomputable def bad : Finset FF := labelsF ∪ Sel.offDiag.biUnion collisionRoots

theorem bad_card_lt : bad.card < (Finset.univ : Finset FF).card := by
  have hcoll : (Sel.offDiag.biUnion collisionRoots).card ≤ Sel.offDiag.card * 16384 := by
    refine Finset.card_biUnion_le_card_mul _ _ _ ?_
    intro z _
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (CF_sub_natDegree_le _ _))
  have hoff : Sel.offDiag.card = NN * (NN - 1) := by
    rw [Finset.offDiag_card, Sel_card, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hL := labelsF_card
  rw [Finset.card_univ, BF64.card_ext3]
  calc bad.card ≤ labelsF.card + (Sel.offDiag.biUnion collisionRoots).card :=
        Finset.card_union_le _ _
    _ ≤ 2 ^ 21 + NN * (NN - 1) * 16384 := by rw [← hoff]; omega
    _ < 2 ^ 192 := by norm_num [NN]

theorem exists_alpha : ∃ a : FF, a ∉ bad := by
  by_contra h
  push_neg at h
  have : bad = Finset.univ := Finset.eq_univ_of_forall h
  have hlt := bad_card_lt
  rw [this] at hlt
  exact lt_irrefl _ hlt

noncomputable def alpha : FF := Classical.choose exists_alpha

theorem alpha_not_bad : alpha ∉ bad := Classical.choose_spec exists_alpha

theorem alpha_ne_label (j : Idx) : algebraMap K FF (Ys.eval (nodeN j.val)) ≠ alpha := by
  intro e
  apply alpha_not_bad
  refine Finset.mem_union_left _ ?_
  rw [labelsF_def]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, e⟩

/-- The winning challenge of a member. -/
noncomputable def gamma (p : Param) : FF := (CF p).eval alpha

theorem gamma_injOn : Set.InjOn gamma (Sel : Set Param) := by
  intro p hp q hq heq
  by_contra hne
  apply alpha_not_bad
  have hroot : alpha ∈ collisionRoots (p, q) := by
    rw [collisionRoots, Multiset.mem_toFinset, mem_roots (CF_sub_ne_zero hne)]
    rw [IsRoot, eval_sub]
    exact sub_eq_zero.mpr heq
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hne⟩, hroot⟩)

theorem gammaImage_card : (Sel.image gamma).card = NN := by
  rw [Finset.card_image_of_injOn gamma_injOn, Sel_card]

noncomputable def Q (p : Param) : Polynomial FF :=
  (CF p - Polynomial.C (gamma p)) /ₘ (Polynomial.X - Polynomial.C alpha)

theorem Q_spec (p : Param) :
    (Polynomial.X - Polynomial.C alpha) * Q p = CF p - Polynomial.C (gamma p) := by
  rw [Q, mul_divByMonic_eq_iff_isRoot]
  simp [IsRoot, gamma]

theorem Q_natDegree_le (p : Param) : (Q p).natDegree ≤ 16383 := by
  rw [Q, natDegree_divByMonic _ (monic_X_sub_C alpha), natDegree_X_sub_C]
  have h : (CF p - Polynomial.C (gamma p)).natDegree ≤ 16384 := by
    rw [natDegree_sub_C]
    exact CF_natDegree_le p
  omega

/-! ## The label polynomial and the core -/

noncomputable def YF : Polynomial FF := Ys.map (algebraMap K FF)

theorem YF_monic : YF.Monic := Ys_monic.map _

theorem YF_natDegree : YF.natDegree = 64 := by
  rw [YF, natDegree_map_eq_of_injective algebraMap_injective, Ys_natDegree]

noncomputable def Den : Polynomial FF := YF - Polynomial.C alpha

theorem Den_monic : Den.Monic := by
  rw [Den]
  refine YF_monic.sub_of_left ?_
  rw [degree_eq_natDegree YF_monic.ne_zero, YF_natDegree]
  exact degree_C_le.trans_lt (by exact_mod_cast (by norm_num : 0 < 64))

theorem Den_natDegree : Den.natDegree = 64 := by
  rw [Den, natDegree_sub_C, YF_natDegree]

theorem Den_eval_ne (j : Idx) : Den.eval (BinaryIRSProfile.domain j) ≠ 0 := by
  rw [Den, eval_sub, eval_C, sub_ne_zero, YF, map_eval_domain]
  exact alpha_ne_label j

theorem Den_isUnit (j : Idx) : IsUnit (Den.eval (BinaryIRSProfile.domain j)) :=
  isUnit_iff_ne_zero.mpr (Den_eval_ne j)

noncomputable def Rc : Polynomial K := ∏ l ∈ Finset.Ico 1 64, (Polynomial.X - Polynomial.C (nodeN l))

theorem Rc_monic : Rc.Monic := monic_prod_of_monic _ _ (fun l _ => monic_X_sub_C (nodeN l))

theorem Rc_natDegree : Rc.natDegree = 63 := by
  rw [Rc, natDegree_prod_of_monic _ _ (fun l _ => monic_X_sub_C (nodeN l))]
  simp

noncomputable def RF : Polynomial FF := Rc.map (algebraMap K FF)

theorem RF_monic : RF.Monic := Rc_monic.map _

theorem RF_natDegree : RF.natDegree = 63 := by
  rw [RF, natDegree_map_eq_of_injective algebraMap_injective, Rc_natDegree]

noncomputable def RtF : Polynomial FF := Rtop.map (algebraMap K FF)

/-! ## Agreement sets -/

def toIdx (i : ℕ) : Idx := ⟨i % 2097152, Nat.mod_lt _ (by norm_num)⟩

theorem toIdx_val {i : ℕ} (hi : i < 2097152) : (toIdx i).val = i := Nat.mod_eq_of_lt hi

noncomputable irreducible_def coreSet : Finset Idx := (Finset.Ico 1 64).image toIdx

theorem coreSet_card : coreSet.card = 63 := by
  rw [coreSet_def, Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha c hc hac
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hc
  have := congrArg Fin.val hac
  rwa [toIdx_val (by omega), toIdx_val (by omega)] at this

theorem coreSet_val {j : Idx} (hj : j ∈ coreSet) : 1 ≤ j.val ∧ j.val < 64 := by
  rw [coreSet_def] at hj
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
  have hl' := Finset.mem_Ico.mp hl
  rw [toIdx_val (by omega)]
  exact hl'

theorem lab_idx_lt (v : V) {l : ℕ} (hl : l < 64) : 64 * hidx v + l < 2097152 := by
  have := hidx_lt v
  omega

noncomputable irreducible_def labSet (p : Param) : Finset Idx :=
  (Sset p ×ˢ Finset.range 64).image fun q => toIdx (64 * hidx q.1 + q.2)

theorem labSet_card (p : Param) : (labSet p).card = 1179648 := by
  rw [labSet_def, Finset.card_image_of_injOn, Finset.card_product, Sset_card, Finset.card_range]
  rintro ⟨v, l⟩ hq ⟨v', l'⟩ hq' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hq hq'
  have h' := congrArg Fin.val h
  simp only at h'
  rw [toIdx_val (lab_idx_lt v hq.2), toIdx_val (lab_idx_lt v' hq'.2)] at h'
  have hl : l = l' := by omega
  have hv : hidx v = hidx v' := by omega
  rw [hidx_injective hv, hl]

theorem labSet_mem {p : Param} {j : Idx} (hj : j ∈ labSet p) :
    ∃ v ∈ Sset p, Ys.eval (nodeN j.val) = lab v ∧ 64 ≤ j.val := by
  rw [labSet_def] at hj
  obtain ⟨⟨v, l⟩, hq, rfl⟩ := Finset.mem_image.mp hj
  simp only [Finset.mem_product, Finset.mem_range] at hq
  refine ⟨v, hq.1, ?_, ?_⟩
  · rw [toIdx_val (lab_idx_lt v hq.2), Ys_label v l hq.2]
  · rw [toIdx_val (lab_idx_lt v hq.2)]
    have hv : v ≠ 0 := fun h0 => zero_not_mem p (h0 ▸ hq.1)
    have := hidx_pos hv
    omega

/-- The agreement set of a member: the core and the 64-point fibres over the member. -/
noncomputable def Jset (p : Param) : Finset Idx := coreSet ∪ labSet p

theorem Jset_card (p : Param) : (Jset p).card = 1179711 := by
  rw [Jset, Finset.card_union_of_disjoint, coreSet_card, labSet_card]
  rw [Finset.disjoint_left]
  intro j hc hl
  obtain ⟨-, -, -, h64⟩ := labSet_mem hl
  have := coreSet_val hc
  omega

theorem RF_eval_core {j : Idx} (hj : j ∈ coreSet) : RF.eval (BinaryIRSProfile.domain j) = 0 := by
  have hv := coreSet_val hj
  rw [RF, map_eval_domain, map_eq_zero_iff _ algebraMap_injective, Rc, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_Ico.mpr hv) (by simp)

theorem vanish (p : Param) {j : Idx} (hj : j ∈ Jset p) :
    RF.eval (BinaryIRSProfile.domain j) *
      (RtF.eval (YF.eval (BinaryIRSProfile.domain j)) +
        (CF p).eval (YF.eval (BinaryIRSProfile.domain j))) = 0 := by
  rcases Finset.mem_union.mp hj with hc | hl
  · rw [RF_eval_core hc, zero_mul]
  · obtain ⟨v, hv, hy, -⟩ := labSet_mem hl
    have hz : YF.eval (BinaryIRSProfile.domain j) = algebraMap K FF (lab v) := by
      rw [YF, map_eval_domain, hy]
    rw [hz, RtF, CF, eval_map, eval_map, eval₂_at_apply, eval₂_at_apply, ← map_add,
      ← eval_add, ← Vp_split, Vp_eval p hv, map_zero, mul_zero]

/-! ## Words, codewords and the violating instance -/

abbrev kk := BinaryIRSProfile.totalDimension
abbrev ss := BinaryIRSProfile.interleaving

local instance : NeZero ss := ⟨by norm_num [ss, BinaryIRSProfile.interleaving]⟩

noncomputable def word1 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then
    RF.eval (BinaryIRSProfile.domain j) * RtF.eval (YF.eval (BinaryIRSProfile.domain j)) *
      Ring.inverse (Den.eval (BinaryIRSProfile.domain j))
  else 0

noncomputable def word2 : Idx → Fin ss → FF := fun j row =>
  if row = 0 then
    RF.eval (BinaryIRSProfile.domain j) * Ring.inverse (Den.eval (BinaryIRSProfile.domain j))
  else 0

noncomputable def cpoly (p : Param) : Polynomial FF := -(RF * (Q p).comp YF)

theorem cpoly_natDegree_le (p : Param) : (cpoly p).natDegree ≤ 1048575 := by
  rw [cpoly, natDegree_neg]
  calc (RF * (Q p).comp YF).natDegree ≤ RF.natDegree + ((Q p).comp YF).natDegree :=
        natDegree_mul_le
    _ ≤ 63 + (Q p).natDegree * YF.natDegree := by
        rw [RF_natDegree]; exact Nat.add_le_add_left natDegree_comp_le _
    _ ≤ 63 + 16383 * 64 := by
        rw [YF_natDegree]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Q_natDegree_le p)) _
    _ = 1048575 := by norm_num

theorem cpoly_degree_lt (p : Param) : (cpoly p).degree < (kk / ss : ℕ) := by
  rw [PrescribedTop.rowDimension_eq]
  by_cases hz : cpoly p = 0
  · rw [hz]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hz]
    exact_mod_cast lt_of_le_of_lt (cpoly_natDegree_le p) (by norm_num)

abbrev Carrier := {p : Param // p ∈ Sel}

noncomputable def pmsg (a : Carrier) : Fin kk → FF :=
  Classical.choose (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.val))

theorem pmsg_spec (a : Carrier) (j : Idx) (row : Fin ss) :
    BinaryIRSProfile.encoder (pmsg a) j row =
      if row = 0 then (cpoly a.val).eval (BinaryIRSProfile.domain j) else 0 :=
  Classical.choose_spec (PrescribedTop.exists_message (cpoly a.val) (cpoly_degree_lt a.val)) j row

theorem word_agree (a : Carrier) {j : Idx} (hj : j ∈ Jset a.val) :
    word1 j + gamma a.val • word2 j = BinaryIRSProfile.encoder (pmsg a) j := by
  funext row
  rw [pmsg_spec, Pi.add_apply, Pi.smul_apply]
  by_cases hrow : row = 0
  · subst hrow
    simp only [word1, word2, if_pos, smul_eq_mul]
    rw [cpoly, eval_neg, eval_mul, eval_comp]
    set x := BinaryIRSProfile.domain j
    set z := YF.eval x
    have hD : Den.eval x = z - alpha := by rw [Den, eval_sub, eval_C]
    have hDi : Ring.inverse (Den.eval x) * (z - alpha) = 1 := by
      rw [← hD]
      exact Ring.inverse_mul_cancel _ (Den_isUnit j)
    have hQ := congrArg (fun P => P.eval z) (Q_spec a.val)
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hQ
    have hv := vanish a.val hj
    linear_combination Ring.inverse (Den.eval x) * hv +
      (RF.eval x * Ring.inverse (Den.eval x)) * hQ - (RF.eval x * (Q a.val).eval z) * hDi
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

theorem word2_zero (j : Idx) :
    word2 j 0 = RF.eval (BinaryIRSProfile.domain j) *
      Ring.inverse (Den.eval (BinaryIRSProfile.domain j)) := by
  simp only [word2, if_pos]

theorem alg_cancel (r i c d : FF) (h0 : r * i = c) (hDi : i * d = 1) : r = c * d := by
  linear_combination d * h0 - r * hDi

/-- `R(x) / (Y(x) - α)` agrees with no row codeword on more than `2^20 + 63` points. -/
theorem far_generic (c : Polynomial FF) (hc : c.degree < (1048576 : ℕ)) (S : Finset Idx)
    (hcard : 1048640 ≤ S.card)
    (h : ∀ j ∈ S, RF.eval (BinaryIRSProfile.domain j) =
      c.eval (BinaryIRSProfile.domain j) * Den.eval (BinaryIRSProfile.domain j)) : False := by
  have hRdeg : RF.degree < (S.card : ℕ) := by
    rw [degree_eq_natDegree RF_monic.ne_zero, RF_natDegree]
    exact_mod_cast (by omega : 63 < S.card)
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
      rw [degree_eq_natDegree (mul_ne_zero hc0 Den_monic.ne_zero),
        natDegree_mul hc0 Den_monic.ne_zero, Den_natDegree]
      exact_mod_cast (by omega : c.natDegree + 64 < S.card)
    have heq := Polynomial.eq_of_degrees_lt_of_eval_index_eq S
      BinaryIRSProfile.domain.injective.injOn hRdeg hPdeg heval
    have h := congrArg Polynomial.natDegree heq
    rw [RF_natDegree, natDegree_mul hc0 Den_monic.ne_zero, Den_natDegree] at h
    omega

theorem word2_far (u : Fin kk → FF) (S : Finset Idx) (hcard : 1048640 ≤ S.card)
    (hagree : ∀ j ∈ S, word2 j = BinaryIRSProfile.encoder u j) : False := by
  refine far_generic (rowPoly u) (rowPoly_degree_lt u) S hcard ?_
  intro j hj
  have h0 := congrFun (hagree j hj) (0 : Fin ss)
  rw [word2_zero, enc_row0] at h0
  exact alg_cancel _ _ _ _ h0 (Ring.inverse_mul_cancel _ (Den_isUnit j))

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
    (hlo : (917441 / 2097152 : ℝ≥0) ≤ δ) (hhi : δ < (1015833 / 2097152 : ℝ≥0)) :
    ProximityPrize.Benchmark.Binary.Upper.epsilonStar <
      winningSetDensity BinaryIRSProfile.encoder δ := by
  classical
  have hcardI : Fintype.card Idx = 2097152 := PrescribedTop.card_Idx
  have hd_lo : (917441 / 2097152 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hlo
  have hd_hi : (δ : ℝ) < 1015833 / 2097152 := by exact_mod_cast hhi
  have hx_lo : (1081319 : ℝ) < (1 - (δ : ℝ)) * 2097152 := by linarith
  have hx_hi : (1 - (δ : ℝ)) * 2097152 ≤ 1179711 := by linarith
  have ht_hi : Nat.ceil ((1 - (δ : ℝ)) * 2097152) ≤ 1179711 :=
    Nat.ceil_le.mpr (by exact_mod_cast hx_hi)
  have hsub : ∀ a : Carrier, ∃ T ⊆ Jset a.val,
      T.card = Nat.ceil ((1 - (δ : ℝ)) * 2097152) := by
    intro a
    exact Finset.exists_subset_card_eq (by rw [Jset_card]; exact ht_hi)
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
        have hSnat : 1048640 ≤ S.card := by
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

end ProximityPrize.SubmissionBinaryUpper.CorePencil

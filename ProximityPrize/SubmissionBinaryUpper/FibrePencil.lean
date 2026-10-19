/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.SubspacePoly
import Mathlib.Combinatorics.Pigeonhole

/-!
# A coset pencil on the additive domain

The subspace polynomial `Y` of the first `2^14` words is constant on the 128
cosets `16384 h + W` of the domain, with value `y h`.  An agreement set is a
fixed 16383-point core inside `W` together with 67 whole cosets with labels
`U ⊆ [1, 128)`, so it has `16383 + 67 * 16384 = 1114111` points.

Its vanishing polynomial is `R(x) V_U(Y(x))`.  Only the two top coefficients
of `V_U` below its leading one are prescribed.  Because the labels span a
seven-dimensional `𝔽₂`-space, these lie in sets of size `2^7` and `2^49`.
A rational pencil with a generic extension-field point `α` absorbs one more
coefficient, so every member of a key class gives a codeword
`R(x) Q_U(Y(x))` with `deg Q_U ≤ 63`, i.e. of degree at most `2^20 - 1`, and a
distinct winning challenge.
-/

namespace ProximityPrize.SubmissionBinaryUpper.FibrePencil

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open scoped NNReal

abbrev FF := BinaryIRSProfile.Field
abbrev Idx := BinaryIRSProfile.Index

theorem algebraMap_injective : Function.Injective (algebraMap K FF) :=
  (algebraMap K FF).injective

theorem domain_eq (j : Idx) : BinaryIRSProfile.domain j = algebraMap K FF (nodeN j.val) := rfl

/-! ## Label polynomials -/

noncomputable def V (U : Finset ℕ) : Polynomial K :=
  ∏ h ∈ U, (Polynomial.X - Polynomial.C (y h))

theorem V_eq_multiset (U : Finset ℕ) :
    V U = ((U.val.map y).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
  rw [V, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

theorem V_monic (U : Finset ℕ) : (V U).Monic :=
  monic_prod_of_monic _ _ (fun h _ => monic_X_sub_C (y h))

theorem V_natDegree (U : Finset ℕ) : (V U).natDegree = U.card := by
  rw [V, natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C (y h))]
  simp

theorem V_coeff_66 {U : Finset ℕ} (hU : U.card = 67) :
    (V U).coeff 66 = (-1) ^ 1 * (U.val.map y).esymm 1 := by
  rw [V_eq_multiset, Multiset.prod_X_sub_C_coeff _ (by simp [hU])]
  simp [hU]

theorem V_coeff_65 {U : Finset ℕ} (hU : U.card = 67) :
    (V U).coeff 65 = (-1) ^ 2 * (U.val.map y).esymm 2 := by
  rw [V_eq_multiset, Multiset.prod_X_sub_C_coeff _ (by simp [hU])]
  simp [hU]

theorem V_eval_zero_iff {U : Finset ℕ} (hU : U ⊆ Finset.range 128) {h : ℕ} (hh : h < 128) :
    (V U).eval (y h) = 0 ↔ h ∈ U := by
  constructor
  · intro hz
    rw [V, eval_prod, Finset.prod_eq_zero_iff] at hz
    obtain ⟨c, hc, hzero⟩ := hz
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hzero
    have hc' : c < 128 := by simpa using hU hc
    rwa [y_injective hh hc' hzero]
  · intro hm
    rw [V, eval_prod]
    exact Finset.prod_eq_zero hm (by simp)

theorem V_injective {U W : Finset ℕ} (hU : U ⊆ Finset.range 128) (hW : W ⊆ Finset.range 128)
    (h : V U = V W) : U = W := by
  ext c
  constructor
  · intro hc
    have hc' : c < 128 := by simpa using hU hc
    rw [← V_eval_zero_iff hW hc', ← h, V_eval_zero_iff hU hc']
    exact hc
  · intro hc
    have hc' : c < 128 := by simpa using hW hc
    rw [← V_eval_zero_iff hU hc', h, V_eval_zero_iff hW hc']
    exact hc

/-! ## The cheap key and its fibre -/

noncomputable def Candidates : Finset (Finset ℕ) := (Finset.Ico 1 128).powersetCard 67

theorem candidates_card : Candidates.card = Nat.choose 127 67 := by
  rw [Candidates, Finset.card_powersetCard, Nat.card_Ico]

theorem mem_candidates {U : Finset ℕ} (hU : U ∈ Candidates) :
    U ⊆ Finset.Ico 1 128 ∧ U.card = 67 :=
  Finset.mem_powersetCard.mp hU

theorem candidates_sub_range {U : Finset ℕ} (hU : U ∈ Candidates) : U ⊆ Finset.range 128 := by
  intro h hh
  have := (mem_candidates hU).1 hh
  simp only [Finset.mem_Ico] at this
  simp only [Finset.mem_range]
  omega

noncomputable def key (U : Finset ℕ) : K × K := ((V U).coeff 66, (V U).coeff 65)

noncomputable def keySet : Finset (K × K) :=
  (S1.image (fun z => (-1) ^ 1 * z)) ×ˢ (S2.image (fun z => (-1) ^ 2 * z))

theorem keySet_card : keySet.card ≤ 2 ^ 56 := by
  rw [keySet, Finset.card_product]
  calc (S1.image (fun z => (-1) ^ 1 * z)).card * (S2.image (fun z => (-1) ^ 2 * z)).card
      ≤ S1.card * S2.card := Nat.mul_le_mul Finset.card_image_le Finset.card_image_le
    _ ≤ 2 ^ 7 * 2 ^ 49 := Nat.mul_le_mul S1_card S2_card
    _ = 2 ^ 56 := by norm_num

theorem key_mem {U : Finset ℕ} (hU : U ∈ Candidates) : key U ∈ keySet := by
  have hlab : ∀ a ∈ U.val.map y, a ∈ S1 := by
    intro a ha
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp ha
    have : h < 128 := by simpa using candidates_sub_range hU hh
    exact y_mem_S1 this
  rw [key, keySet, Finset.mem_product, V_coeff_66 (mem_candidates hU).2,
    V_coeff_65 (mem_candidates hU).2]
  exact ⟨Finset.mem_image_of_mem _ (esymm_one_mem _ hlab),
    Finset.mem_image_of_mem _ (esymm_two_mem _ hlab)⟩

set_option maxRecDepth 100000 in
theorem fibre_count : 2 ^ 56 * 2 ^ 64 < Nat.choose 127 67 := by
  rw [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 100000 in
theorem exists_big_fiber :
    ∃ σ ∈ keySet, 2 ^ 64 < (Candidates.filter fun U => key U = σ).card := by
  refine Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (fun U hU => key_mem hU) ?_
  rw [candidates_card]
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ keySet_card) fibre_count

noncomputable def sigma0 : K × K := Classical.choose exists_big_fiber

noncomputable def Fam : Finset (Finset ℕ) := Candidates.filter fun U => key U = sigma0

theorem Fam_card_gt : 2 ^ 64 < Fam.card := (Classical.choose_spec exists_big_fiber).2

theorem Fam_mem {U : Finset ℕ} (hU : U ∈ Fam) : U ∈ Candidates := (Finset.mem_filter.mp hU).1

theorem Fam_key {U : Finset ℕ} (hU : U ∈ Fam) : key U = sigma0 := (Finset.mem_filter.mp hU).2

abbrev NN : ℕ := 2 ^ 64 + 1

theorem exists_selected : ∃ S : Finset (Finset ℕ), S ⊆ Fam ∧ S.card = NN :=
  Finset.exists_subset_card_eq (Nat.succ_le_of_lt Fam_card_gt)

noncomputable def Sel : Finset (Finset ℕ) := Classical.choose exists_selected

theorem Sel_sub : Sel ⊆ Fam := (Classical.choose_spec exists_selected).1

theorem Sel_card : Sel.card = NN := (Classical.choose_spec exists_selected).2

theorem Sel_cand {U : Finset ℕ} (hU : U ∈ Sel) : U ∈ Candidates := Fam_mem (Sel_sub hU)

theorem V_sub_natDegree_le {U W : Finset ℕ} (hU : U ∈ Fam) (hW : W ∈ Fam) :
    (V U - V W).natDegree ≤ 64 := by
  have hkey := (Fam_key hU).trans (Fam_key hW).symm
  have h66 : (V U).coeff 66 = (V W).coeff 66 := congrArg Prod.fst hkey
  have h65 : (V U).coeff 65 = (V W).coeff 65 := congrArg Prod.snd hkey
  have hcU := (mem_candidates (Fam_mem hU)).2
  have hcW := (mem_candidates (Fam_mem hW)).2
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro d hd
  have hd' : 64 < d := by exact_mod_cast hd
  rw [coeff_sub]
  rcases Nat.lt_or_ge d 67 with hlt | hge
  · interval_cases d
    · rw [h65, sub_self]
    · rw [h66, sub_self]
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      have h1 := V_monic U
      have h2 := V_monic W
      rw [Monic, leadingCoeff, V_natDegree, hcU] at h1
      rw [Monic, leadingCoeff, V_natDegree, hcW] at h2
      rw [h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [V_natDegree, hcU]; exact hgt),
        coeff_eq_zero_of_natDegree_lt (by rw [V_natDegree, hcW]; exact hgt), sub_self]

/-! ## The generic pencil point -/

noncomputable def VF (U : Finset ℕ) : Polynomial FF := (V U).map (algebraMap K FF)

theorem VF_sub_ne_zero {U W : Finset ℕ} (hU : U ∈ Sel) (hW : W ∈ Sel) (hne : U ≠ W) :
    VF U - VF W ≠ 0 := by
  rw [VF, VF, ← Polynomial.map_sub]
  refine (Polynomial.map_ne_zero_iff algebraMap_injective).mpr ?_
  exact sub_ne_zero.mpr fun h =>
    hne (V_injective (candidates_sub_range (Sel_cand hU)) (candidates_sub_range (Sel_cand hW)) h)

theorem VF_sub_natDegree_le {U W : Finset ℕ} (hU : U ∈ Sel) (hW : W ∈ Sel) :
    (VF U - VF W).natDegree ≤ 64 := by
  rw [VF, VF, ← Polynomial.map_sub]
  exact (natDegree_map_le).trans (V_sub_natDegree_le (Sel_sub hU) (Sel_sub hW))

noncomputable def labelsF : Finset FF := (Finset.range 128).image fun h => algebraMap K FF (y h)

noncomputable def collisionRoots (z : Finset ℕ × Finset ℕ) : Finset FF :=
  (VF z.1 - VF z.2).roots.toFinset

noncomputable def bad : Finset FF := labelsF ∪ Sel.offDiag.biUnion collisionRoots

theorem bad_card_lt : bad.card < (Finset.univ : Finset FF).card := by
  have hlab : labelsF.card ≤ 128 := Finset.card_image_le.trans (by simp)
  have hcoll : (Sel.offDiag.biUnion collisionRoots).card ≤ Sel.offDiag.card * 64 := by
    refine Finset.card_biUnion_le_card_mul _ _ _ ?_
    intro z hz
    have hmem := Finset.mem_offDiag.mp hz
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (VF_sub_natDegree_le hmem.1 hmem.2.1))
  have hoff : Sel.offDiag.card = NN * (NN - 1) := by
    rw [Finset.offDiag_card, Sel_card, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [Finset.card_univ, BF64.card_ext3]
  calc bad.card ≤ labelsF.card + (Sel.offDiag.biUnion collisionRoots).card :=
        Finset.card_union_le _ _
    _ ≤ 128 + NN * (NN - 1) * 64 := by rw [← hoff]; omega
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

theorem alpha_ne_label {h : ℕ} (hh : h < 128) : algebraMap K FF (y h) ≠ alpha := by
  intro e
  apply alpha_not_bad
  refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, by simpa using hh, e⟩)

theorem VF_eval_alpha_injOn : Set.InjOn (fun U => (VF U).eval alpha) (Sel : Set (Finset ℕ)) := by
  intro U hU W hW heq
  by_contra hne
  apply alpha_not_bad
  have hroot : alpha ∈ collisionRoots (U, W) := by
    rw [collisionRoots, Multiset.mem_toFinset, mem_roots (VF_sub_ne_zero hU hW hne)]
    simpa [eval_sub] using sub_eq_zero.mpr heq
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨(U, W), Finset.mem_offDiag.mpr ⟨hU, hW, hne⟩, hroot⟩)

theorem Sel_nonempty : Sel.Nonempty := by
  rw [← Finset.card_pos, Sel_card]
  positivity

noncomputable def U0 : Finset ℕ := Sel_nonempty.choose

theorem U0_mem : U0 ∈ Sel := Sel_nonempty.choose_spec

noncomputable def deltaV (U : Finset ℕ) : Polynomial FF := VF U0 - VF U

noncomputable def pencil (U : Finset ℕ) : Polynomial FF :=
  deltaV U - Polynomial.C ((deltaV U).eval alpha)

noncomputable def Q (U : Finset ℕ) : Polynomial FF :=
  pencil U /ₘ (Polynomial.X - Polynomial.C alpha)

theorem Q_spec (U : Finset ℕ) :
    (Polynomial.X - Polynomial.C alpha) * Q U = pencil U := by
  rw [Q, mul_divByMonic_eq_iff_isRoot]
  simp [pencil, IsRoot]

theorem Q_natDegree_le {U : Finset ℕ} (hU : U ∈ Sel) : (Q U).natDegree ≤ 63 := by
  rw [Q, natDegree_divByMonic _ (monic_X_sub_C alpha), natDegree_X_sub_C]
  have h : (pencil U).natDegree ≤ 64 := by
    rw [pencil, natDegree_sub_C]
    exact VF_sub_natDegree_le U0_mem hU
  omega

/-- The winning challenge of a selected label set. -/
noncomputable def gamma (U : Finset ℕ) : FF := -((deltaV U).eval alpha)

theorem gamma_injOn : Set.InjOn gamma (Sel : Set (Finset ℕ)) := by
  intro U hU W hW h
  apply VF_eval_alpha_injOn hU hW
  have h' : (deltaV U).eval alpha = (deltaV W).eval alpha := neg_injective h
  simp only [deltaV, eval_sub] at h'
  simpa using h'

/-! ## The core, the coset fibres and the agreement sets -/

def toIdx (i : ℕ) : Idx := ⟨i % 2097152, Nat.mod_lt _ (by norm_num)⟩

theorem toIdx_val {i : ℕ} (hi : i < 2097152) : (toIdx i).val = i := Nat.mod_eq_of_lt hi

noncomputable def R : Polynomial K := ∏ l ∈ Finset.Ico 1 16384, (Polynomial.X - Polynomial.C (nodeN l))

theorem R_monic : R.Monic := monic_prod_of_monic _ _ (fun l _ => monic_X_sub_C (nodeN l))

theorem R_natDegree : R.natDegree = 16383 := by
  rw [R, natDegree_prod_of_monic _ _ (fun l _ => monic_X_sub_C (nodeN l))]
  simp

noncomputable def RF : Polynomial FF := R.map (algebraMap K FF)

theorem RF_natDegree : RF.natDegree = 16383 := by
  rw [RF, natDegree_map_eq_of_injective algebraMap_injective, R_natDegree]

theorem RF_monic : RF.Monic := R_monic.map _

noncomputable def YF : Polynomial FF := Ysub.map (algebraMap K FF)

theorem YF_natDegree : YF.natDegree = 16384 := by
  rw [YF, natDegree_map_eq_of_injective algebraMap_injective, Y_natDegree]

theorem map_eval_domain (P : Polynomial K) (j : Idx) :
    (P.map (algebraMap K FF)).eval (BinaryIRSProfile.domain j) =
      algebraMap K FF (P.eval (nodeN j.val)) := by
  rw [domain_eq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem Y_domain (j : Idx) : Ysub.eval (nodeN j.val) = y (j.val / 16384) := by
  have h := Y_fibre (j.val / 16384) (j.val % 16384) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem YF_domain_ne (j : Idx) : YF.eval (BinaryIRSProfile.domain j) - alpha ≠ 0 := by
  rw [YF, map_eval_domain, Y_domain, sub_ne_zero]
  apply alpha_ne_label
  have := j.isLt
  change j.val < 2 ^ 21 at this
  omega

noncomputable def core : Finset Idx := (Finset.Ico 1 16384).image toIdx

noncomputable def fib (U : Finset ℕ) : Finset Idx :=
  (U ×ˢ Finset.range 16384).image fun p => toIdx (16384 * p.1 + p.2)

noncomputable def J (U : Finset ℕ) : Finset Idx := core ∪ fib U

theorem core_card : core.card = 16383 := by
  rw [core, Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha c hc hac
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hc
  have := congrArg Fin.val hac
  rwa [toIdx_val (by omega), toIdx_val (by omega)] at this

theorem fib_card {U : Finset ℕ} (hU : U ∈ Candidates) : (fib U).card = 67 * 16384 := by
  have hsub := candidates_sub_range hU
  rw [fib, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range,
    (mem_candidates hU).2]
  rintro ⟨a, l⟩ ha ⟨c, l'⟩ hc hac
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at ha hc
  have ha' : a < 128 := by simpa using hsub ha.1
  have hc' : c < 128 := by simpa using hsub hc.1
  have := congrArg Fin.val hac
  simp only at this
  rw [toIdx_val (by omega), toIdx_val (by omega)] at this
  simp only [Prod.mk.injEq]
  omega

theorem core_fib_disjoint {U : Finset ℕ} (hU : U ∈ Candidates) : Disjoint core (fib U) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨⟨a, l'⟩, hp, he⟩ := Finset.mem_image.mp hj'
  simp only [Finset.mem_product, Finset.mem_range] at hp
  have ha := (mem_candidates hU).1 hp.1
  simp only [Finset.mem_Ico] at hl ha
  have := congrArg Fin.val he
  rw [toIdx_val (by omega), toIdx_val (by omega)] at this
  omega

theorem J_card {U : Finset ℕ} (hU : U ∈ Candidates) : (J U).card = 1114111 := by
  rw [J, Finset.card_union_of_disjoint (core_fib_disjoint hU), core_card, fib_card hU]

theorem RF_eval_core {j : Idx} (hj : j ∈ core) : RF.eval (BinaryIRSProfile.domain j) = 0 := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
  rw [RF, map_eval_domain, map_eq_zero_iff _ algebraMap_injective]
  have hl' := Finset.mem_Ico.mp hl
  rw [toIdx_val (by omega), R, eval_prod]
  exact Finset.prod_eq_zero hl (by simp)

theorem VF_eval_fib {U : Finset ℕ} (hU : U ∈ Candidates) {j : Idx} (hj : j ∈ fib U) :
    (VF U).eval (YF.eval (BinaryIRSProfile.domain j)) = 0 := by
  obtain ⟨⟨a, l⟩, hp, rfl⟩ := Finset.mem_image.mp hj
  simp only [Finset.mem_product, Finset.mem_range] at hp
  have ha : a < 128 := by simpa using candidates_sub_range hU hp.1
  rw [YF, map_eval_domain, VF, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    map_eq_zero_iff _ algebraMap_injective, toIdx_val (by omega), Y_fibre a l hp.2]
  exact (V_eval_zero_iff (candidates_sub_range hU) ha).mpr hp.1

end ProximityPrize.SubmissionBinaryUpper.FibrePencil

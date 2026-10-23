/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.PrescribedTop

/-!
# A rational pencil on the 512-by-512 NTT grid

The size-`2^18` NTT domain is partitioned into 512 fibres by `x ↦ x^512`.
We use 272 whole fibres together with a fixed 511-point core.  Prescribing 14
top coefficients and the product of the selected fibre labels leaves more than
`2^59` choices while forcing pairwise differences to have the two roots needed
to fit under the row-degree budget.
-/

namespace ProximityPrize.SubmissionUpper.OrbitPencil

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open ProximityPrize.Benchmark
open scoped NNReal BigOperators

abbrev K := _root_.KoalaBear.Field
abbrev FF := IRSProfile.Field
abbrev Idx := IRSProfile.Index
abbrev Small := Fin 512

def idx (a b : Small) : Idx :=
  ⟨a.val * 512 + b.val, by omega⟩

theorem idx_injective : Function.Injective (fun ab : Small × Small => idx ab.1 ab.2) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [idx] at hv
    omega
  · apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [idx] at hv
    omega

noncomputable def omega : K := IRSProfile.baseNttDomain.omega

theorem omega_pow : omega ^ 262144 = 1 :=
  IRSProfile.baseNttDomain.primitive.pow_eq_one

noncomputable def node (i : Idx) : K := omega ^ i.val

theorem node_eq (i : Idx) : node i = PrescribedTop.nodes i := rfl

noncomputable def y (b : Small) : K := node (idx 0 b) ^ 512

theorem pow_block (w : K) (hw : w ^ 262144 = 1) (a b : Small) :
    (w ^ (a.val * 512 + b.val)) ^ 512 = (w ^ b.val) ^ 512 := by
  rw [pow_add, mul_pow, ← pow_mul, ← pow_mul]
  rw [show (a.val * 512) * 512 = a.val * 262144 by ring]
  rw [show b.val * 512 = 512 * b.val by omega]
  rw [show a.val * 262144 = 262144 * a.val by omega, pow_mul]
  rw [hw, one_pow, one_mul]

theorem node_pow (a b : Small) : node (idx a b) ^ 512 = y b := by
  simpa only [node, y, idx, Fin.val_zero, zero_mul, zero_add] using
    pow_block omega omega_pow a b

theorem y_injective : Function.Injective y := by
  intro b c h
  apply Fin.ext
  refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 512) ?_
  apply IRSProfile.baseNttDomain.primitive.pow_inj
  · change b.val * 512 < 262144
    omega
  · change c.val * 512 < 262144
    omega
  simpa only [y, node, idx, omega, Fin.val_zero, zero_mul, zero_add, pow_mul] using h

noncomputable def outer : Finset Small := Finset.univ.erase 0

theorem outer_card : outer.card = 511 := by simp [outer]

noncomputable def Candidates : Finset (Finset Small) :=
  Finset.powersetCard 272 outer

theorem candidates_card : Candidates.card = Nat.choose 511 272 := by
  rw [Candidates, Finset.card_powersetCard, outer_card]

noncomputable def V (U : Finset Small) : Polynomial K :=
  ∏ b ∈ U, ((Polynomial.X : Polynomial K) - Polynomial.C (OrbitPencil.y b))

theorem V_monic (U : Finset Small) : (V U).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C (y b)

theorem V_natDegree (U : Finset Small) : (V U).natDegree = U.card := by
  classical
  rw [V, Polynomial.natDegree_prod_of_monic _ _
    (fun b (_ : b ∈ U) => Polynomial.monic_X_sub_C (y b))]
  simp

theorem V_eval_zero_iff (U : Finset Small) (b : Small) :
    (V U).eval (y b) = 0 ↔ b ∈ U := by
  classical
  constructor
  · intro h
    rw [V, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨c, hc, hzero⟩ := h
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hzero
    rwa [y_injective hzero]
  · intro h
    rw [V, Polynomial.eval_prod]
    refine Finset.prod_eq_zero h ?_
    simp

theorem V_injective : Function.Injective V := by
  intro U W h
  ext b
  rw [← V_eval_zero_iff U b, ← V_eval_zero_iff W b, h]

noncomputable def topKey (U : Finset Small) : Fin 14 → K :=
  fun i => (V U).coeff (271 - i.val)

noncomputable def productKey (U : Finset Small) : Small :=
  ⟨(∑ b ∈ U, b.val) % 512, Nat.mod_lt _ (by norm_num)⟩

noncomputable def key (U : Finset Small) : (Fin 14 → K) × Small :=
  (topKey U, productKey U)

theorem card_keys : Fintype.card ((Fin 14 → K) × Small) =
    (2 ^ 31 - 2 ^ 24 + 1) ^ 14 * 512 := by
  rw [Fintype.card_prod, Fintype.card_fun, PrescribedTop.card_K]
  norm_num

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem orbit_count :
    ((2 ^ 31 - 2 ^ 24 + 1)^14 * 512) * 2^59 < Nat.choose 511 272 := by
  rw [Nat.choose_eq_fast_choose]
  decide

theorem exists_big_fiber :
    ∃ σ : (Fin 14 → K) × Small,
      2^59 < (Candidates.filter fun U => key U = σ).card := by
  refine PrescribedTop.pigeonhole Candidates key _ ?_
  rw [card_keys, candidates_card]
  exact orbit_count

noncomputable def sigma0 := Classical.choose exists_big_fiber
noncomputable def Fam : Finset (Finset Small) := Candidates.filter fun U => key U = sigma0

theorem Fam_card_gt : 2^59 < Fam.card := Classical.choose_spec exists_big_fiber

theorem Fam_mem {U : Finset Small} (hU : U ∈ Fam) : U ⊆ outer ∧ U.card = 272 := by
  exact Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1

theorem Fam_key {U : Finset Small} (hU : U ∈ Fam) : key U = sigma0 :=
  (Finset.mem_filter.mp hU).2

theorem omega_pow_sum_eq_of_mod_eq {a b : ℕ} (h : a % 512 = b % 512) :
    omega ^ (512 * a) = omega ^ (512 * b) := by
  apply pow_eq_pow_of_modEq (n := 262144) _ omega_pow
  change (512 * a) % 262144 = (512 * b) % 262144
  omega

theorem V_eval_zero {U : Finset Small} (hcard : U.card = 272) :
    (V U).eval 0 = omega ^ (512 * ∑ b ∈ U, b.val) := by
  rw [V, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rw [Finset.prod_neg, hcard]
  norm_num
  simp_rw [y, node, idx, Fin.val_zero, zero_mul, zero_add, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.mul_sum]
  simp [mul_comm]

theorem V_eval_zero_eq_of_key {U W : Finset Small}
    (hU : U ∈ Fam) (hW : W ∈ Fam) : (V U).eval 0 = (V W).eval 0 := by
  rw [V_eval_zero (Fam_mem hU).2, V_eval_zero (Fam_mem hW).2]
  apply omega_pow_sum_eq_of_mod_eq
  have hk := congrArg Prod.snd ((Fam_key hU).trans (Fam_key hW).symm)
  exact congrArg Fin.val hk

theorem V_coeff_top {U : Finset Small} (hU : U ∈ Fam) : (V U).coeff 272 = 1 := by
  have hm := V_monic U
  rw [Polynomial.Monic, Polynomial.leadingCoeff, V_natDegree, (Fam_mem hU).2] at hm
  exact hm

theorem V_coeff_gt {U : Finset Small} (hU : U ∈ Fam) {d : ℕ} (hd : 272 < d) :
    (V U).coeff d = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [V_natDegree, (Fam_mem hU).2]
  exact hd

theorem top_coeff_eq {U W : Finset Small} (hU : U ∈ Fam) (hW : W ∈ Fam)
    {d : ℕ} (hlo : 258 ≤ d) (hhi : d ≤ 271) : (V U).coeff d = (V W).coeff d := by
  have hk := congrArg Prod.fst ((Fam_key hU).trans (Fam_key hW).symm)
  have hi : 271 - d < 14 := by omega
  have hc := congrFun hk ⟨271 - d, hi⟩
  simpa only [key, topKey, show 271 - (271 - d) = d by omega] using hc

theorem V_sub_degree_lt {U W : Finset Small} (hU : U ∈ Fam) (hW : W ∈ Fam) :
    (V U - V W).degree < (258 : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro d hd
  have hd258 : 258 ≤ d := by exact_mod_cast hd
  rw [Polynomial.coeff_sub]
  rcases lt_trichotomy d 272 with hlt | heq | hgt
  · have hle : d ≤ 271 := by omega
    rw [top_coeff_eq hU hW hd258 hle, sub_self]
  · subst d
    rw [V_coeff_top hU, V_coeff_top hW, sub_self]
  · rw [V_coeff_gt hU hgt, V_coeff_gt hW hgt, sub_self]

abbrev NN : ℕ := 2^59 + 1

theorem exists_selected : ∃ S : Finset (Finset Small), S ⊆ Fam ∧ S.card = NN := by
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq (s := Fam)
    (n := NN) (by simpa [NN] using Nat.succ_le_iff.mpr Fam_card_gt : NN ≤ Fam.card)
  exact ⟨S, hsub, hcard⟩

noncomputable def Sel : Finset (Finset Small) := Classical.choose exists_selected
theorem Sel_sub : Sel ⊆ Fam := (Classical.choose_spec exists_selected).1
theorem Sel_card : Sel.card = NN := (Classical.choose_spec exists_selected).2

theorem Sel_mem {U : Finset Small} (hU : U ∈ Sel) : U ∈ Fam := Sel_sub hU

noncomputable def VF (U : Finset Small) : Polynomial FF :=
  (V U).map (algebraMap K FF)

theorem VF_sub_ne_zero {U W : Finset Small} (hne : U ≠ W) : VF U - VF W ≠ 0 := by
  rw [VF, VF, ← Polynomial.map_sub]
  exact (Polynomial.map_ne_zero_iff PrescribedTop.algebraMap_injective).mpr
    (sub_ne_zero.mpr (fun h => hne (V_injective h)))

theorem VF_sub_natDegree_lt {U W : Finset Small} (hU : U ∈ Sel) (hW : W ∈ Sel) :
    (VF U - VF W).natDegree < 258 := by
  have hd := V_sub_degree_lt (Sel_mem hU) (Sel_mem hW)
  have hn : (V U - V W).natDegree < 258 := by
    by_cases hz : V U - V W = 0
    · simp [hz]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hd
  calc
    (VF U - VF W).natDegree = ((V U - V W).map (algebraMap K FF)).natDegree := by
      rw [Polynomial.map_sub, VF, VF]
    _ ≤ (V U - V W).natDegree := Polynomial.natDegree_map_le
    _ < 258 := hn

noncomputable def projected : Finset FF :=
  Finset.univ.image (fun b : Small => algebraMap K FF (y b))

theorem projected_card : projected.card = 512 := by
  rw [projected, Finset.card_image_of_injective]
  simp
  intro b c h
  exact y_injective (PrescribedTop.algebraMap_injective h)

noncomputable def collisionRoots (z : (Finset Small) × (Finset Small)) : Finset FF :=
  (VF z.1 - VF z.2).roots.toFinset

theorem collisionRoots_card_le (z : (Finset Small) × (Finset Small))
    (hz : z ∈ Sel.offDiag) : (collisionRoots z).card ≤ 257 := by
  have hmem := Finset.mem_offDiag.mp hz
  have hd := VF_sub_natDegree_lt hmem.1 hmem.2.1
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' (VF z.1 - VF z.2)).trans (by omega))

noncomputable def bad : Finset FF :=
  (projected ∪ {0}) ∪ Sel.offDiag.biUnion collisionRoots

theorem collision_union_card_le :
    (Sel.offDiag.biUnion collisionRoots).card ≤ Sel.offDiag.card * 257 :=
  Finset.card_biUnion_le_card_mul Sel.offDiag collisionRoots 257 collisionRoots_card_le

theorem offdiag_card : Sel.offDiag.card = NN * (NN - 1) := by
  rw [Finset.offDiag_card, Sel_card, Nat.mul_sub_left_distrib]
  simp

theorem projected_union_card_le : (projected ∪ {0}).card ≤ 513 := by
  calc (projected ∪ {0}).card ≤ projected.card + ({0} : Finset FF).card := Finset.card_union_le _ _
    _ = 513 := by rw [projected_card]; simp

theorem collision_arith : 513 + Sel.offDiag.card * 257 ≤ NN^2 * 272 + 513 := by
  rw [offdiag_card]
  have h1 : NN * (NN - 1) ≤ NN * NN :=
    Nat.mul_le_mul_left NN (Nat.sub_le NN 1)
  have h2 : NN * (NN - 1) * 257 ≤ NN^2 * 257 := by
    simpa [pow_two] using Nat.mul_le_mul_right 257 h1
  have h3 : NN^2 * 257 ≤ NN^2 * 272 := Nat.mul_le_mul_left _ (by norm_num)
  calc
    513 + NN * (NN - 1) * 257 ≤ 513 + NN^2 * 257 := Nat.add_le_add_left h2 513
    _ ≤ 513 + NN^2 * 272 := Nat.add_le_add_left h3 513
    _ = NN^2 * 272 + 513 := Nat.add_comm _ _

set_option maxRecDepth 10000 in
theorem bad_card_le : bad.card ≤ NN^2 * 272 + 513 := by
  have hcoll := collision_union_card_le
  have hp := projected_union_card_le
  rw [bad]
  calc
    ((projected ∪ {0}) ∪ Sel.offDiag.biUnion collisionRoots).card ≤
        (projected ∪ {0}).card + (Sel.offDiag.biUnion collisionRoots).card :=
      Finset.card_union_le _ _
    _ ≤ 513 + Sel.offDiag.card * 257 := Nat.add_le_add hp hcoll
    _ ≤ NN^2 * 272 + 513 := collision_arith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
theorem alpha_count : NN^2 * 272 + 513 < (2 ^ 31 - 2 ^ 24 + 1)^6 := by
  dsimp [NN]
  decide

theorem bad_lt_univ : bad.card < (Finset.univ : Finset FF).card := by
  rw [Finset.card_univ, PrescribedTop.card_FF]
  exact bad_card_le.trans_lt alpha_count

theorem exists_alpha : ∃ a : FF, a ∉ bad := by
  by_contra h
  push_neg at h
  have : bad = Finset.univ := by ext a; simp [h a]
  have hlt := bad_lt_univ
  rw [this] at hlt
  exact (lt_irrefl _) hlt

noncomputable def alpha : FF := Classical.choose exists_alpha
theorem alpha_not_bad : alpha ∉ bad := Classical.choose_spec exists_alpha

theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  apply alpha_not_bad
  simp [bad, h]

theorem alpha_ne_projected (b : Small) : alpha ≠ algebraMap K FF (y b) := by
  intro h
  apply alpha_not_bad
  simp [bad, projected, h]

theorem VF_eval_alpha_injective_on : Set.InjOn (fun U => (VF U).eval alpha) (Sel : Set _) := by
  intro U hU W hW heq
  by_contra hne
  apply alpha_not_bad
  have hroot : alpha ∈ collisionRoots (U, W) := by
    rw [collisionRoots, Multiset.mem_toFinset, Polynomial.mem_roots (VF_sub_ne_zero hne)]
    simpa [Polynomial.eval_sub] using sub_eq_zero.mpr heq
  simp only [bad, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨(U, W), Finset.mem_offDiag.mpr ⟨hU, hW, hne⟩, hroot⟩)

theorem Sel_nonempty : Sel.Nonempty := by
  rw [← Finset.card_pos, Sel_card]
  positivity

noncomputable def U0 : Finset Small := Sel_nonempty.choose
theorem U0_mem : U0 ∈ Sel := Sel_nonempty.choose_spec

noncomputable def deltaV (U : Finset Small) : Polynomial FF := VF U0 - VF U
noncomputable def gamma (U : Finset Small) : FF := (deltaV U).eval alpha / alpha
noncomputable def pencil (U : Finset Small) : Polynomial FF :=
  deltaV U - Polynomial.C (gamma U) * (Polynomial.X : Polynomial FF)

theorem deltaV_eval_zero {U : Finset Small} (hU : U ∈ Sel) : (deltaV U).eval 0 = 0 := by
  have hmap (P : Polynomial K) :
      (P.map (algebraMap K FF)).eval 0 = algebraMap K FF (P.eval 0) := by
    rw [← map_zero (algebraMap K FF), Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [deltaV, Polynomial.eval_sub, VF, VF, hmap, hmap,
    V_eval_zero_eq_of_key (Sel_mem U0_mem) (Sel_mem hU), sub_self]

theorem pencil_eval_zero {U : Finset Small} (hU : U ∈ Sel) : (pencil U).eval 0 = 0 := by
  simp [pencil, deltaV_eval_zero hU]

theorem pencil_eval_alpha (U : Finset Small) : (pencil U).eval alpha = 0 := by
  rw [pencil, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    gamma, div_mul_cancel₀ _ alpha_ne_zero, sub_self]

theorem pencil_degree_lt {U : Finset Small} (hU : U ∈ Sel) :
    (pencil U).degree < (258 : ℕ) := by
  have hd : (deltaV U).degree < (258 : ℕ) := by
    have hn := VF_sub_natDegree_lt U0_mem hU
    by_cases hz : deltaV U = 0
    · rw [hz]
      exact WithBot.bot_lt_coe 258
    · rw [Polynomial.degree_eq_natDegree hz]
      exact_mod_cast hn
  have hlin : (Polynomial.C (gamma U) * (Polynomial.X : Polynomial FF)).degree < (258 : ℕ) := by
    calc
      (Polynomial.C (gamma U) * (Polynomial.X : Polynomial FF)).degree ≤ (1 : ℕ) := by
        simpa using Polynomial.degree_C_mul_X_le (gamma U)
      _ < (258 : ℕ) := by norm_num
  exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hd hlin)

theorem exists_Q (U : Finset Small) (hU : U ∈ Sel) :
    ∃ Q : Polynomial FF,
      pencil U = (Polynomial.X : Polynomial FF) * (Polynomial.X - Polynomial.C alpha) * Q ∧
        Q.natDegree ≤ 255 := by
  have hx : (Polynomial.X : Polynomial FF) ∣ pencil U := by
    rw [show (Polynomial.X : Polynomial FF) = Polynomial.X - Polynomial.C 0 by simp,
      Polynomial.dvd_iff_isRoot]
    exact pencil_eval_zero hU
  obtain ⟨Q1, hQ1⟩ := hx
  have hq1eval : Q1.eval alpha = 0 := by
    have hp := pencil_eval_alpha U
    rw [hQ1, Polynomial.eval_mul, Polynomial.eval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left alpha_ne_zero
  have ha : (Polynomial.X : Polynomial FF) - Polynomial.C alpha ∣ Q1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hq1eval
  obtain ⟨Q, hQ⟩ := ha
  refine ⟨Q, ?_, ?_⟩
  · rw [hQ1, hQ, mul_assoc]
  · by_cases hQz : Q = 0
    · simp [hQz]
    · have hfac1 : (Polynomial.X : Polynomial FF) ≠ 0 := Polynomial.X_ne_zero
      have hfac2 : ((Polynomial.X : Polynomial FF) - Polynomial.C alpha) ≠ 0 :=
        Polynomial.X_sub_C_ne_zero alpha
      have hpne : (Polynomial.X : Polynomial FF) * (Polynomial.X - Polynomial.C alpha) * Q ≠ 0 :=
        mul_ne_zero (mul_ne_zero hfac1 hfac2) hQz
      have hnat : ((Polynomial.X : Polynomial FF) *
          (Polynomial.X - Polynomial.C alpha) * Q).natDegree < 258 := by
        have hd := pencil_degree_lt hU
        rw [show pencil U = (Polynomial.X : Polynomial FF) *
            (Polynomial.X - Polynomial.C alpha) * Q by rw [hQ1, hQ, mul_assoc]] at hd
        exact (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr hd
      rw [Polynomial.natDegree_mul (mul_ne_zero hfac1 hfac2) hQz,
        Polynomial.natDegree_mul hfac1 hfac2, Polynomial.natDegree_X,
        Polynomial.natDegree_X_sub_C] at hnat
      omega

noncomputable def Q (U : Finset Small) : Polynomial FF :=
  if hU : U ∈ Sel then Classical.choose (exists_Q U hU) else 0

theorem Q_spec {U : Finset Small} (hU : U ∈ Sel) :
    pencil U = (Polynomial.X : Polynomial FF) *
      (Polynomial.X - Polynomial.C alpha) * Q U ∧ (Q U).natDegree ≤ 255 := by
  simp only [Q, dif_pos hU]
  exact Classical.choose_spec (exists_Q U hU)

theorem gamma_injective {U W : Finset Small} (hU : U ∈ Sel) (hW : W ∈ Sel)
    (hgamma : gamma U = gamma W) : U = W := by
  apply VF_eval_alpha_injective_on hU hW
  have hdelta : (deltaV U).eval alpha = (deltaV W).eval alpha := by
    have := congrArg (fun z : FF => z * alpha) hgamma
    simpa only [gamma, div_mul_cancel₀ _ alpha_ne_zero] using this
  rw [deltaV, deltaV, Polynomial.eval_sub, Polynomial.eval_sub] at hdelta
  exact sub_right_inj.mp hdelta

noncomputable def coreA : Finset Small := Finset.univ.erase 0

noncomputable def R : Polynomial K :=
  ∏ a ∈ coreA, ((Polynomial.X : Polynomial K) - Polynomial.C (node (idx a 0)))

theorem R_monic : R.Monic :=
  Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C (node (idx a 0))

theorem coreA_card : coreA.card = 511 := by simp [coreA]

theorem R_natDegree : R.natDegree = 511 := by
  rw [R, Polynomial.natDegree_prod_of_monic _ _
    (fun a (_ : a ∈ coreA) => Polynomial.monic_X_sub_C (node (idx a 0)))]
  simp [coreA_card]

noncomputable def RF : Polynomial FF := R.map (algebraMap K FF)

theorem RF_natDegree : RF.natDegree = 511 := by
  rw [RF, Polynomial.natDegree_map_eq_of_injective PrescribedTop.algebraMap_injective,
    R_natDegree]

theorem RF_ne_zero : RF ≠ 0 := by
  intro h
  have := RF_natDegree
  rw [h] at this
  simp at this

theorem RF_eval_core (a : Small) (ha : a ∈ coreA) :
    RF.eval (IRSProfile.domain (idx a 0)) = 0 := by
  rw [RF, Polynomial.eval_map, PrescribedTop.domain_eq, ← node_eq,
    Polynomial.eval₂_at_apply, map_eq_zero_iff _ PrescribedTop.algebraMap_injective]
  rw [R, Polynomial.eval_prod]
  refine Finset.prod_eq_zero ha ?_
  simp

noncomputable def zpoly : Polynomial FF := (Polynomial.X : Polynomial FF)^512

noncomputable def cpoly (U : Finset Small) : Polynomial FF := RF * (Q U).comp zpoly

theorem cpoly_natDegree_le {U : Finset Small} (hU : U ∈ Sel) :
    (cpoly U).natDegree ≤ 131071 := by
  calc
    (cpoly U).natDegree ≤ RF.natDegree + ((Q U).comp zpoly).natDegree := by
      rw [cpoly]
      exact Polynomial.natDegree_mul_le
    _ ≤ 511 + (Q U).natDegree * zpoly.natDegree := by
      rw [RF_natDegree]
      exact Nat.add_le_add_left Polynomial.natDegree_comp_le 511
    _ ≤ 511 + 255 * 512 := by
      have hq := (Q_spec hU).2
      have hz : zpoly.natDegree = 512 := by simp [zpoly]
      rw [hz]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right 512 hq) 511
    _ = 131071 := by norm_num

theorem cpoly_degree_lt {U : Finset Small} (hU : U ∈ Sel) :
    (cpoly U).degree < (131072 : ℕ) := by
  by_cases hz : cpoly U = 0
  · rw [hz]
    exact WithBot.bot_lt_coe 131072
  · rw [Polynomial.degree_eq_natDegree hz]
    exact_mod_cast (lt_of_le_of_lt (cpoly_natDegree_le hU) (by norm_num : 131071 < 131072))

abbrev kk := IRSProfile.totalDimension
abbrev ss := IRSProfile.interleaving
local instance : NeZero ss := ⟨by norm_num [ss, IRSProfile.interleaving]⟩

noncomputable def pmsg (U : Finset Small) : Fin kk → FF :=
  if hU : U ∈ Sel then Classical.choose
    (PrescribedTop.exists_message (cpoly U) (by
      rw [PrescribedTop.rowDimension_eq]
      exact cpoly_degree_lt hU)) else 0

set_option maxRecDepth 10000 in
theorem pmsg_spec {U : Finset Small} (hU : U ∈ Sel) (j : Idx) (row : Fin ss) :
    IRSProfile.encoder (pmsg U) j row =
      if row = 0 then (cpoly U).eval (IRSProfile.domain j) else 0 := by
  simp only [pmsg, dif_pos hU]
  exact Classical.choose_spec
    (PrescribedTop.exists_message (cpoly U) (by
      rw [PrescribedTop.rowDimension_eq]
      exact cpoly_degree_lt hU)) j row

noncomputable def corePairs : Finset (Small × Small) := coreA.product {0}
noncomputable def blockPairs (U : Finset Small) : Finset (Small × Small) := Finset.univ.product U
noncomputable def pairSet (U : Finset Small) := corePairs ∪ blockPairs U
noncomputable def T (U : Finset Small) : Finset Idx :=
  (pairSet U).image (fun ab => idx ab.1 ab.2)

set_option maxRecDepth 10000 in
theorem pair_disjoint {U : Finset Small} (hU : U ∈ Sel) :
    Disjoint corePairs (blockPairs U) := by
  rw [corePairs, blockPairs]
  rw [Finset.disjoint_left]
  intro ab habc habb
  have hc := Finset.mem_product.mp habc
  have hb := Finset.mem_product.mp habb
  have hb0 : (0 : Small) ∉ U := by
    intro h0
    have hout := (Fam_mem (Sel_mem hU)).1 h0
    simp [outer] at hout
  have heq : ab.2 = 0 := Finset.mem_singleton.mp hc.2
  rw [heq] at hb
  exact hb0 hb.2

theorem T_card {U : Finset Small} (hU : U ∈ Sel) : (T U).card = 139775 := by
  rw [T, Finset.card_image_of_injective _ idx_injective, pairSet,
    Finset.card_union_of_disjoint (pair_disjoint hU)]
  simp [corePairs, blockPairs, coreA_card, (Fam_mem (Sel_mem hU)).2]

noncomputable def zval (j : Idx) : FF := IRSProfile.domain j ^ 512

theorem zval_idx (a b : Small) : zval (idx a b) = algebraMap K FF (y b) := by
  rw [zval, PrescribedTop.domain_eq, ← node_eq, ← map_pow, node_pow]

theorem y_ne_zero (b : Small) : y b ≠ 0 := by
  rw [y, node]
  exact pow_ne_zero _ (pow_ne_zero _
    (IRSProfile.baseNttDomain.primitive.ne_zero (by norm_num)))

theorem zval_idx_ne_zero (a b : Small) : zval (idx a b) ≠ 0 := by
  rw [zval_idx]
  intro h
  apply y_ne_zero b
  apply PrescribedTop.algebraMap_injective
  simpa using h

theorem zval_idx_sub_alpha_ne_zero (a b : Small) : zval (idx a b) - alpha ≠ 0 := by
  rw [sub_ne_zero, zval_idx]
  exact (alpha_ne_projected b).symm

theorem VF_eval_block (U : Finset Small) (a b : Small) (hb : b ∈ U) :
    (VF U).eval (zval (idx a b)) = 0 := by
  rw [zval_idx, VF, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    map_eq_zero_iff _ PrescribedTop.algebraMap_injective]
  exact (V_eval_zero_iff U b).mpr hb

noncomputable def f1scalar (j : Idx) : FF :=
  RF.eval (IRSProfile.domain j) * (VF U0).eval (zval j) /
    (zval j * (zval j - alpha))

noncomputable def f2scalar (j : Idx) : FF :=
  - RF.eval (IRSProfile.domain j) / (zval j - alpha)

noncomputable def f1 (j : Idx) (row : Fin ss) : FF := if row = 0 then f1scalar j else 0
noncomputable def f2 (j : Idx) (row : Fin ss) : FF := if row = 0 then f2scalar j else 0

theorem cpoly_eval (U : Finset Small) (j : Idx) :
    (cpoly U).eval (IRSProfile.domain j) =
      RF.eval (IRSProfile.domain j) * (Q U).eval (zval j) := by
  rw [cpoly, Polynomial.eval_mul, Polynomial.eval_comp, zpoly, Polynomial.eval_pow,
    Polynomial.eval_X, zval]

theorem scalar_agree_core {U : Finset Small} (hU : U ∈ Sel) (a : Small) (ha : a ∈ coreA) :
    f1scalar (idx a 0) + gamma U * f2scalar (idx a 0) =
      (cpoly U).eval (IRSProfile.domain (idx a 0)) := by
  rw [f1scalar, f2scalar, cpoly_eval, RF_eval_core a ha]
  simp

theorem scalar_agree_block {U : Finset Small} (hU : U ∈ Sel)
    (a b : Small) (hb : b ∈ U) :
    f1scalar (idx a b) + gamma U * f2scalar (idx a b) =
      (cpoly U).eval (IRSProfile.domain (idx a b)) := by
  have hp := congrArg (Polynomial.eval (zval (idx a b))) (Q_spec hU).1
  simp only [pencil, deltaV, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C] at hp
  rw [VF_eval_block U a b hb, sub_zero] at hp
  rw [cpoly_eval, f1scalar, f2scalar]
  have hz := zval_idx_ne_zero a b
  have hza := zval_idx_sub_alpha_ne_zero a b
  field_simp [hz, hza]
  linear_combination (RF.eval (IRSProfile.domain (idx a b))) * hp

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem word_agree {U : Finset Small} (hU : U ∈ Sel) (j : Idx) (hj : j ∈ T U) :
    f1 j + gamma U • f2 j = IRSProfile.encoder (pmsg U) j := by
  rw [T, Finset.mem_image] at hj
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hj
  have hpairs : (a, b) ∈ corePairs ∨ (a, b) ∈ blockPairs U := by
    exact Finset.mem_union.mp (by simpa [pairSet] using hab)
  funext row
  rw [pmsg_spec hU]
  by_cases hr : row = 0
  · subst row
    simp only [f1, f2, if_pos, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hpairs with hcore | hblock
    · have hc := Finset.mem_product.mp
        (show (a, b) ∈ coreA.product {0} by simpa [corePairs] using hcore)
      have hb0 : b = 0 := Finset.mem_singleton.mp hc.2
      subst b
      exact scalar_agree_core hU a hc.1
    · have hb := Finset.mem_product.mp
        (show (a, b) ∈ Finset.univ.product U by simpa [blockPairs] using hblock)
      exact scalar_agree_block hU a b hb.2
  · simp [f1, f2, hr]

def aOf (j : Idx) : Small := ⟨j.val / 512, by omega⟩
def bOf (j : Idx) : Small := ⟨j.val % 512, Nat.mod_lt _ (by norm_num)⟩

theorem idx_aOf_bOf (j : Idx) : idx (aOf j) (bOf j) = j := by
  apply Fin.ext
  simp only [idx, aOf, bOf]
  omega

theorem zval_ne_zero (j : Idx) : zval j ≠ 0 := by
  rw [← idx_aOf_bOf j]
  exact zval_idx_ne_zero (aOf j) (bOf j)

theorem zval_sub_alpha_ne_zero (j : Idx) : zval j - alpha ≠ 0 := by
  rw [← idx_aOf_bOf j]
  exact zval_idx_sub_alpha_ne_zero (aOf j) (bOf j)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem f2_far (δ : ℝ≥0) (hδ : δ < (122641 / 262144 : ℝ≥0)) :
    ¬ RelaxedRelationFor (ℓ := 2) IRSProfile.encoder δ (0 : Fin kk → FF)
      ![0, 0] ![f1, f2] := by
  intro hrel
  rcases hrel with ⟨W, ⟨M, hW, _hc⟩, S, hS, hA⟩
  have hd : (δ : ℝ) < 122641 / 262144 := by exact_mod_cast hδ
  have hScard : 131583 < S.card := by
    have hreal : (139503 : ℝ) < (1 - (δ : ℝ)) * 262144 := by nlinarith
    have hcardR : (139503 : ℝ) < (S.card : ℝ) := by
      calc (139503 : ℝ) < (1 - (δ : ℝ)) * 262144 := hreal
        _ ≤ (S.card : ℝ) := by simpa using hS
    have hnat : 139503 < S.card := by exact_mod_cast hcardR
    omega
  let q : Polynomial FF := ToyProblem.Spec.rsPolynomial (kk / ss)
    (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension (M 1) 0)
  have hqdeg : q.degree < (131072 : ℕ) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (kk / ss)
      (unflatten kk ss IRSProfile.interleaving_dvd_totalDimension (M 1) 0)
    simpa only [PrescribedTop.rowDimension_eq] using h
  have hqnat : q.natDegree ≤ 131071 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hqdeg
      exact Nat.le_pred_of_lt this
  let A : Polynomial FF := (Polynomial.X : Polynomial FF)^512 - Polynomial.C alpha
  let P : Polynomial FF := A * q + RF
  have hAnd : A.natDegree = 512 := by
    simp [A, Polynomial.natDegree_X_pow_sub_C]
  have hPdeg : P.natDegree ≤ 131583 := by
    have hmul : (A * q).natDegree ≤ 131583 := by
      calc
        (A * q).natDegree ≤ A.natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 512 + 131071 := by rw [hAnd]; exact Nat.add_le_add_left hqnat 512
        _ = 131583 := by norm_num
    calc
      P.natDegree ≤ max (A * q).natDegree RF.natDegree := by
        change (A * q + RF).natDegree ≤ _
        exact Polynomial.natDegree_add_le (A * q) RF
      _ ≤ max 131583 511 := max_le_max hmul (by rw [RF_natDegree])
      _ = 131583 := by norm_num
  have heval : ∀ j ∈ S, P.eval (IRSProfile.domain j) = 0 := by
    intro j hj
    have ha := congrFun (hA 1 j hj) (0 : Fin ss)
    rw [hW 1, IRSProfile.encoder, encoder_apply, ToyProblem.Spec.rsEncoder_apply] at ha
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, f2, if_pos] at ha
    change f2scalar j = q.eval (IRSProfile.domain j) at ha
    rw [f2scalar] at ha
    have hza := zval_sub_alpha_ne_zero j
    have hmul : -RF.eval (IRSProfile.domain j) =
        q.eval (IRSProfile.domain j) * (zval j - alpha) := by
      calc
        -RF.eval (IRSProfile.domain j) =
            (-RF.eval (IRSProfile.domain j) / (zval j - alpha)) * (zval j - alpha) := by
              rw [div_mul_cancel₀ _ hza]
        _ = q.eval (IRSProfile.domain j) * (zval j - alpha) := by rw [ha]
    dsimp only [P, A]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    change (zval j - alpha) * q.eval (IRSProfile.domain j) +
      RF.eval (IRSProfile.domain j) = 0
    linear_combination -hmul
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P
      (S.image IRSProfile.domain)
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact heval j hj
    · rw [Finset.card_image_of_injective _ IRSProfile.domain.injective]
      exact lt_of_le_of_lt hPdeg hScard
  have hEq : A * q = -RF := by
    have := congrArg (fun p : Polynomial FF => p - RF) hPzero
    simpa [P] using this
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero] at hEq
    have : RF = 0 := by simpa using hEq.symm
    exact RF_ne_zero this
  · have hA0 : A ≠ 0 := by
      intro h
      have := hAnd
      rw [h] at this
      simp at this
    have hdegEq := congrArg Polynomial.natDegree hEq
    rw [Polynomial.natDegree_mul hA0 hq0, hAnd, Polynomial.natDegree_neg, RF_natDegree] at hdegEq
    omega

theorem gamma_image_card : (Sel.image gamma).card = NN := by
  rw [Finset.card_image_iff.mpr]
  · exact Sel_card
  · intro U hU W hW h
    exact gamma_injective hU hW h

theorem density_nat : Fintype.card FF < NN * 2^128 := by
  rw [PrescribedTop.card_FF]
  dsimp [NN]
  norm_num

theorem epsilon_lt_fraction :
    ProximityPrize.Benchmark.Upper.epsilonStar <
      (NN : ℝ≥0) / (Fintype.card FF : ℝ≥0) := by
  unfold ProximityPrize.Benchmark.Upper.epsilonStar ProximityGap.prizeThreshold
  push_cast
  have hk : (0 : ℝ≥0) < 2^(128 : ℕ) := by positivity
  have hq : (0 : ℝ≥0) < (Fintype.card FF : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  rw [div_lt_div_iff₀ hk hq]
  norm_num

noncomputable def attack (δ : ℝ≥0) (hhi : δ < (122641 / 262144 : ℝ≥0)) :
    ViolatingInstance IRSProfile.encoder δ :=
  { v := 0
    μ₁ := 0
    μ₂ := 0
    f₁ := f1
    f₂ := f2
    violates := f2_far δ hhi }

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem winningSetDensity_gt_epsilon_window (δ : ℝ≥0)
    (hlo : (122369 / 262144 : ℝ≥0) ≤ δ)
    (hhi : δ < (122641 / 262144 : ℝ≥0)) :
    ProximityPrize.Benchmark.Upper.epsilonStar < winningSetDensity IRSProfile.encoder δ := by
  classical
  have hdlo : (122369 / 262144 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hlo
  have hagree : (1 - (δ : ℝ)) * 262144 ≤ (139775 : ℝ) := by nlinarith
  let x := attack δ hhi
  have himg : (Sel.image gamma : Set FF) ⊆
      winningSetFor IRSProfile.encoder δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂ := by
    intro g hg
    have hg' : g ∈ Sel.image gamma := hg
    rw [Finset.mem_image] at hg'
    obtain ⟨U, hU, rfl⟩ := hg'
    simp only [winningSetFor, Set.mem_setOf_eq]
    refine ⟨![IRSProfile.encoder (pmsg U)], ?_, T U, ?_, ?_⟩
    · refine ⟨![pmsg U], ?_, ?_⟩
      · intro i
        fin_cases i
        rfl
      · intro i
        fin_cases i
        simp [x, attack]
    · rw [T_card hU]
      simpa [PrescribedTop.card_Idx] using hagree
    · intro i j hj
      fin_cases i
      simpa [x, attack] using word_agree hU j hj
  have hcard : NN ≤
      (winningSetFor IRSProfile.encoder δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard := by
    rw [← gamma_image_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg (Set.toFinite _)
  refine lt_of_lt_of_le epsilon_lt_fraction ?_
  calc
    (NN : ℝ≥0) / (Fintype.card FF : ℝ≥0) ≤ winningSetRatio x := by
      rw [winningSetRatio]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ winningSetDensity IRSProfile.encoder δ := winningSetRatio_le_winningSetDensity x

end ProximityPrize.SubmissionUpper.OrbitPencil

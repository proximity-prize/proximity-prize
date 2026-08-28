import ProximityPrize.SubmissionLower.ContactTranslation

namespace ProximityPrize.SubmissionLower.ContactBoundaryRank

open scoped BigOperators Pointwise
open ContactRankKernel
open ContactInterpolation
open ContactTranslation
open ProximityPrize.Benchmark

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K]

def boundaryExponents (M L : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {d | d 0 ≤ M ∧ d 0 + d 2 = L + 1 ∧ d 1 = 0}

def augmentedBoxExponents (M L s : ℕ) : Set (Fin 3 →₀ ℕ) :=
  boxExponents M L s ∪ boundaryExponents M L

def boundaryCoefficientBox (M L : ℕ) : Submodule K (Poly K) :=
  MvPolynomial.restrictSupport K (boundaryExponents M L)

def augmentedCoefficientBox (M L s : ℕ) : Submodule K (Poly K) :=
  MvPolynomial.restrictSupport K (augmentedBoxExponents M L s)

theorem restrictSupport_union (S T : Set (Fin 3 →₀ ℕ)) :
    MvPolynomial.restrictSupport K (S ∪ T) =
      MvPolynomial.restrictSupport K S ⊔ MvPolynomial.restrictSupport K T := by
  simp only [MvPolynomial.restrictSupport_eq_span, Set.image_union,
    Submodule.span_union]

theorem augmentedCoefficientBox_eq_sup (M L s : ℕ) :
    augmentedCoefficientBox K M L s =
      coefficientBox K M L s ⊔ boundaryCoefficientBox K M L := by
  exact restrictSupport_union K (boxExponents M L s) (boundaryExponents M L)

private def exponentTriple (i j z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 z

@[simp] private theorem exponentTriple_zero (i j z : ℕ) :
    exponentTriple i j z 0 = i := by simp [exponentTriple]

@[simp] private theorem exponentTriple_one (i j z : ℕ) :
    exponentTriple i j z 1 = j := by simp [exponentTriple]

@[simp] private theorem exponentTriple_two (i j z : ℕ) :
    exponentTriple i j z 2 = z := by simp [exponentTriple]

private theorem exponentTriple_eta (d : Fin 3 →₀ ℕ) :
    exponentTriple (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp

def boundaryExponentsEquiv (M L : ℕ) (hML : M ≤ L + 1) :
    boundaryExponents M L ≃ Fin (M + 1) where
  toFun d := ⟨d.val 0, by rcases d.property with ⟨hM, hsum, hR⟩; omega⟩
  invFun i := ⟨exponentTriple i.val 0 (L + 1 - i.val), by
    have hi := i.isLt
    have hiM : i.val ≤ M := by omega
    have hiL : i.val ≤ L + 1 := hiM.trans hML
    simp only [boundaryExponents, Set.mem_setOf_eq, exponentTriple_zero,
      exponentTriple_two, exponentTriple_one]
    constructor
    · omega
    constructor
    · exact Nat.add_sub_of_le hiL
    · trivial⟩
  left_inv d := by
    apply Subtype.ext
    rw [Subtype.coe_mk]
    rcases d.property with ⟨hM, hsum, hR⟩
    rw [← exponentTriple_eta d.val]
    congr 1
    · exact hR.symm
    · have hs : d.val 2 + d.val 0 = L + 1 := by omega
      exact (Nat.eq_sub_of_add_eq hs).symm
  right_inv i := by
    apply Fin.ext
    simp [exponentTriple]

instance boundaryExponentsFintype (M L : ℕ) : Fintype (boundaryExponents M L) := by
  classical
  let f : boundaryExponents M L → BoxIndex M (L + 1) 0 := fun d =>
    boxExponentsEquivIndex M (L + 1) 0 ⟨d.val, by
      rcases d.property with ⟨hM, hsum, hR⟩
      exact ⟨hM, hsum.le, by omega⟩⟩
  exact Fintype.ofInjective f (by
    intro a b hab
    dsimp [f] at hab
    have hh := (boxExponentsEquivIndex M (L + 1) 0).injective hab
    apply Subtype.ext
    exact congrArg (fun x : boxExponents M (L + 1) 0 => x.val) hh)

instance boundaryCoefficientBoxFinite (M L : ℕ) :
    Module.Finite K (boundaryCoefficientBox K M L) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boundaryExponents M L))

theorem boundaryCoefficientBox_finrank (M L : ℕ) (hML : M ≤ L + 1) :
    Module.finrank K (boundaryCoefficientBox K M L) = M + 1 := by
  change Module.finrank K (MvPolynomial.restrictSupport K (boundaryExponents M L)) = _
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K (boundaryExponents M L))]
  rw [Fintype.card_congr (boundaryExponentsEquiv M L hML)]
  simp

instance augmentedCoefficientBoxFinite (M L s : ℕ) :
    Module.Finite K (augmentedCoefficientBox K M L s) := by
  rw [augmentedCoefficientBox_eq_sup]
  infer_instance

theorem augmentedCoefficientBox_finrank_le (M L s : ℕ) (hML : M ≤ L) :
    Module.finrank K (augmentedCoefficientBox K M L s) ≤
      blockInputCount M L s + (M + 1) := by
  rw [augmentedCoefficientBox_eq_sup]
  have hsup := Submodule.finrank_add_le_finrank_add_finrank
    (coefficientBox K M L s) (boundaryCoefficientBox K M L)
  rw [coefficientBox_finrank_range K M L s hML,
    boundaryCoefficientBox_finrank K M L (hML.trans (Nat.le_succ L))] at hsup
  exact hsup

def differenceExponents (h : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {d | d 0 + d 1 = h ∧ d 2 = 0}

theorem slopeDifference_mem_differenceBox :
    slopeDifference K ∈ MvPolynomial.restrictSupport K (differenceExponents 1) := by
  apply (MvPolynomial.restrictSupport K (differenceExponents 1)).sub_mem
  · change MvPolynomial.monomial (Finsupp.single 0 1) (1 : K) ∈ _
    apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
    left
    simp [differenceExponents]
  · change MvPolynomial.monomial (Finsupp.single 1 1) (1 : K) ∈ _
    apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
    left
    simp [differenceExponents]

theorem slopeDifference_pow_mem_differenceBox (h : ℕ) :
    slopeDifference K ^ h ∈
      MvPolynomial.restrictSupport K (differenceExponents h) := by
  induction h with
  | zero =>
      simp only [pow_zero]
      change MvPolynomial.monomial 0 (1 : K) ∈ _
      apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
      left
      simp [differenceExponents]
  | succ h ih =>
      have hset : differenceExponents h + differenceExponents 1 ⊆
          differenceExponents (h + 1) := by
        rintro d ⟨a, ha, b, hb, rfl⟩
        rcases ha with ⟨ha, ha2⟩
        rcases hb with ⟨hb, hb2⟩
        simp only [differenceExponents, Set.mem_setOf_eq, Finsupp.add_apply] at ha hb ⊢
        omega
      apply MvPolynomial.restrictSupport_mono (R := K) hset
      rw [MvPolynomial.restrictSupport_add]
      simpa only [pow_succ] using Submodule.mul_mem_mul ih
        (slopeDifference_mem_differenceBox K)

theorem difference_add_boundary_subset_augmented
    {M L s h : ℕ} (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s) :
    differenceExponents h + boundaryExponents (M - h) (L - h) ⊆
      augmentedBoxExponents M L s := by
  rintro d ⟨a, ha, b, hb, rfl⟩
  rcases ha with ⟨ha, ha2⟩
  rcases hb with ⟨hbM, hbSum, hbR⟩
  simp only [augmentedBoxExponents, Set.mem_union, boxExponents,
    boundaryExponents, Set.mem_setOf_eq, Finsupp.add_apply]
  by_cases haR : a 1 = 0
  · right
    constructor
    · omega
    constructor <;> omega
  · left
    constructor
    · omega
    constructor <;> omega

theorem slopeDifference_mul_boundary_mem_augmented
    {M L s h : ℕ} (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s)
    {q : Poly K} (hq : q ∈ boundaryCoefficientBox K (M - h) (L - h)) :
    slopeDifference K ^ h * q ∈ augmentedCoefficientBox K M L s := by
  have hmul : slopeDifference K ^ h * q ∈
      MvPolynomial.restrictSupport K
        (differenceExponents h + boundaryExponents (M - h) (L - h)) := by
    rw [MvPolynomial.restrictSupport_add]
    exact Submodule.mul_mem_mul (slopeDifference_pow_mem_differenceBox K h) hq
  exact MvPolynomial.restrictSupport_mono (R := K)
    (difference_add_boundary_subset_augmented hM hL hs) hmul

theorem old_boundary_disjoint (M L s : ℕ) :
    Disjoint (coefficientBox K M L s) (boundaryCoefficientBox K M L) := by
  apply Submodule.disjoint_def.mpr
  intro p hp hbp
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_zero]
  by_contra hd
  have hmem : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
  rcases hp hmem with ⟨hM, hsum, hs⟩
  rcases hbp hmem with ⟨hbM, hbSum, hbR⟩
  omega

def augmentedBlockJet (M L s h : ℕ) :
    augmentedCoefficientBox K M L s →ₗ[K] Poly K :=
  (contactJet K h).comp (augmentedCoefficientBox K M L s).subtype

def combinedMultiplyIntoAugmented {M L s h : ℕ}
    (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s) :
    (coefficientBox K (M - h) (L - h) (s - h) ×
      boundaryCoefficientBox K (M - h) (L - h)) →ₗ[K]
        augmentedCoefficientBox K M L s where
  toFun q := ⟨slopeDifference K ^ h * (q.1.val + q.2.val), by
    rw [mul_add]
    apply (augmentedCoefficientBox K M L s).add_mem
    · apply MvPolynomial.restrictSupport_mono (R := K)
          (show boxExponents M L s ⊆ augmentedBoxExponents M L s by
            intro d hd
            exact Or.inl hd)
        (slopeDifference_mul_mem_coefficientBox K hM (hM.trans hL) hs q.1.property)
    · exact slopeDifference_mul_boundary_mem_augmented K hM hL hs q.2.property⟩
  map_add' q r := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    ring
  map_smul' c q := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring

theorem combinedMultiplyIntoAugmented_injective {M L s h : ℕ}
    (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s) :
    Function.Injective (combinedMultiplyIntoAugmented K hM hL hs) := by
  intro q r heq
  have hmul : slopeDifference K ^ h * (q.1.val + q.2.val) =
      slopeDifference K ^ h * (r.1.val + r.2.val) := congrArg Subtype.val heq
  have hsum : q.1.val + q.2.val = r.1.val + r.2.val :=
    mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hmul
  have hcross : q.1.val - r.1.val = r.2.val - q.2.val := by
    linear_combination hsum
  have hold : q.1.val - r.1.val ∈ coefficientBox K (M - h) (L - h) (s - h) :=
    (coefficientBox K (M - h) (L - h) (s - h)).sub_mem q.1.property r.1.property
  have hboundary : r.2.val - q.2.val ∈ boundaryCoefficientBox K (M - h) (L - h) :=
    (boundaryCoefficientBox K (M - h) (L - h)).sub_mem r.2.property q.2.property
  have hzero : q.1.val - r.1.val = 0 :=
    Submodule.disjoint_def.mp (old_boundary_disjoint K (M - h) (L - h) (s - h))
      (q.1.val - r.1.val) hold (hcross ▸ hboundary)
  apply Prod.ext
  · apply Subtype.ext
    exact sub_eq_zero.mp hzero
  · apply Subtype.ext
    have : r.2.val - q.2.val = 0 := by rw [← hcross, hzero]
    exact (sub_eq_zero.mp this).symm

def combinedKernelEmbedding {M L s h : ℕ}
    (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s) :
    (coefficientBox K (M - h) (L - h) (s - h) ×
      boundaryCoefficientBox K (M - h) (L - h)) →ₗ[K]
        LinearMap.ker (augmentedBlockJet K M L s h) :=
  LinearMap.codRestrict (LinearMap.ker (augmentedBlockJet K M L s h))
    (combinedMultiplyIntoAugmented K hM hL hs) (fun q => by
      change contactJet K h (slopeDifference K ^ h * (q.1.val + q.2.val)) = 0
      exact contactJet_mul_slopeDifference K h (q.1.val + q.2.val))

theorem combinedKernelEmbedding_injective {M L s h : ℕ}
    (hM : h ≤ M) (hL : M ≤ L) (hs : h ≤ s) :
    Function.Injective (combinedKernelEmbedding K hM hL hs) := by
  intro q r heq
  apply combinedMultiplyIntoAugmented_injective K hM hL hs
  exact congrArg Subtype.val heq

def boundaryKernelLowerBound (M s h : ℕ) : ℕ :=
  min 1 (s + 1 - h) * (M + 1 - h)

def boundaryRankBound (M s h : ℕ) : ℕ :=
  (M + 1) - boundaryKernelLowerBound M s h

theorem augmentedBlockJet_rank_le {M L s h : ℕ} (hML : M ≤ L) :
    Module.finrank K (LinearMap.range (augmentedBlockJet K M L s h)) ≤
      contactRankBound M L s h + boundaryRankBound M s h := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hinj := LinearMap.finrank_le_finrank_of_injective
          (combinedKernelEmbedding_injective K hM hML hs)
      have hsum := (augmentedBlockJet K M L s h).finrank_range_add_finrank_ker
      have hdim := augmentedCoefficientBox_finrank_le K M L s hML
      rw [Module.finrank_prod,
        coefficientBox_finrank_range K (M - h) (L - h) (s - h)
          (Nat.sub_le_sub_right hML h),
        boundaryCoefficientBox_finrank K (M - h) (L - h)
          (by omega : M - h ≤ L - h + 1)] at hinj
      have hMeq : M - h + 1 = M + 1 - h := by omega
      have hLeq : L - h + 1 = L + 1 - h := by omega
      have hseq : s - h + 1 = s + 1 - h := by omega
      rw [hMeq, hLeq, hseq] at hinj
      have hbase := blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
      rw [coefficientBox_finrank_range K M L s hML,
        coefficientBox_finrank_range K (M - h) (L - h) (s - h)
          (Nat.sub_le_sub_right hML h), hMeq, hLeq, hseq] at hbase
      have hKI : blockKernelLowerBound M L s h ≤ blockInputCount M L s := by
        simp only [blockKernelLowerBound, blockInputCount]
        omega
      have hBI : M + 1 - h ≤ M + 1 := Nat.sub_le _ _
      have hinj' : blockKernelLowerBound M L s h + (M + 1 - h) ≤
          Module.finrank K (LinearMap.ker (augmentedBlockJet K M L s h)) := by
        simpa only [blockKernelLowerBound] using hinj
      have hcontact : contactRankBound M L s h + blockKernelLowerBound M L s h =
          blockInputCount M L s := Nat.sub_add_cancel hKI
      have hboundary : boundaryRankBound M s h + (M + 1 - h) = M + 1 := by
        simp only [boundaryRankBound, boundaryKernelLowerBound,
          Nat.min_eq_left (by omega : 1 ≤ s + 1 - h), one_mul]
        exact Nat.sub_add_cancel hBI
      omega
    · have hrange := LinearMap.finrank_range_le (augmentedBlockJet K M L s h)
      have hdim := augmentedCoefficientBox_finrank_le K M L s hML
      have hz : s + 1 - h = 0 := by omega
      simpa only [contactRankBound, blockKernelLowerBound, blockInputCount,
        boundaryRankBound, boundaryKernelLowerBound, hz, min_zero, zero_mul, Nat.sub_zero]
        using hrange.trans hdim
  · have hrange := LinearMap.finrank_range_le (augmentedBlockJet K M L s h)
    have hdim := augmentedCoefficientBox_finrank_le K M L s hML
    have hz : M + 1 - h = 0 := by omega
    simpa only [contactRankBound, blockKernelLowerBound, blockInputCount,
      boundaryRankBound, boundaryKernelLowerBound, hz, mul_zero, Nat.sub_zero,
      Finset.range_zero, Finset.sum_empty] using hrange.trans hdim

def boundaryLocalRankBound (m L s : ℕ) : ℕ :=
  ∑ r ∈ Finset.range m,
    boundaryRankBound (min r L) s (min (r + 1) (m - r))

def augmentedLocalRankBound (m L s : ℕ) : ℕ :=
  localRankBound m L s + boundaryLocalRankBound m L s

theorem boundary_local_rank_frozen : boundaryLocalRankBound 16 184 4 = 88 := by
  norm_num [boundaryLocalRankBound, boundaryRankBound, boundaryKernelLowerBound,
    Finset.sum_range_succ]

theorem augmented_local_rank_frozen : augmentedLocalRankBound 16 184 4 = 99478 := by
  rw [augmentedLocalRankBound, boundary_local_rank_frozen]
  norm_num [localRankBound, contactRankBound, blockInputCount, blockKernelLowerBound,
    Finset.sum_range_succ]

abbrev BoundaryCoefficientIndex (D w L : ℕ) :=
  (k : Fin L) × Fin (D - w * (k.val + 1))

abbrev AugmentedCoefficientIndex (D w L s : ℕ) :=
  CoefficientIndex D w L s ⊕ BoundaryCoefficientIndex D w L

def boundaryColumnExponent {D w L : ℕ}
  (c : BoundaryCoefficientIndex D w L) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 c.2.val + Finsupp.single 1 (c.1.val + 1) +
    Finsupp.single 3 (L - c.1.val)

@[simp] theorem boundaryColumnExponent_x {D w L : ℕ}
    (c : BoundaryCoefficientIndex D w L) : boundaryColumnExponent c 0 = c.2.val := by
  simp [boundaryColumnExponent]

@[simp] theorem boundaryColumnExponent_y {D w L : ℕ}
    (c : BoundaryCoefficientIndex D w L) : boundaryColumnExponent c 1 = c.1.val + 1 := by
  simp [boundaryColumnExponent]

@[simp] theorem boundaryColumnExponent_r {D w L : ℕ}
    (c : BoundaryCoefficientIndex D w L) : boundaryColumnExponent c 2 = 0 := by
  simp [boundaryColumnExponent]

@[simp] theorem boundaryColumnExponent_z {D w L : ℕ}
    (c : BoundaryCoefficientIndex D w L) :
    boundaryColumnExponent c 3 = L - c.1.val := by
  simp [boundaryColumnExponent]

def augmentedColumnExponent {D w L s : ℕ}
    (c : AugmentedCoefficientIndex D w L s) : Fin 4 →₀ ℕ :=
  Sum.elim columnExponent boundaryColumnExponent c

theorem boundaryColumnExponent_injective (D w L : ℕ) :
    Function.Injective
      (boundaryColumnExponent : BoundaryCoefficientIndex D w L → Fin 4 →₀ ℕ) := by
  intro c d h
  have hx := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
  have hy := congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
  simp only [boundaryColumnExponent_x] at hx
  simp only [boundaryColumnExponent_y] at hy
  rcases c with ⟨⟨ci, hci⟩, ⟨ce, hce⟩⟩
  rcases d with ⟨⟨di, hdi⟩, ⟨de, hde⟩⟩
  simp only at hx hy
  have hid : ci = di := by omega
  subst di
  subst de
  rfl

theorem baseColumn_seed_le {D w L s : ℕ} (c : CoefficientIndex D w L s) :
    columnExponent c 1 + columnExponent c 3 ≤ L := by
  simp only [columnExponent_y, columnExponent_z]
  have hi := c.1.isLt
  have hz := c.2.2.1.isLt
  omega

theorem boundaryColumn_seed_eq {D w L : ℕ} (c : BoundaryCoefficientIndex D w L) :
    boundaryColumnExponent c 1 + boundaryColumnExponent c 3 = L + 1 := by
  simp only [boundaryColumnExponent_y, boundaryColumnExponent_z]
  have hi := c.1.isLt
  omega

theorem augmentedColumnExponent_injective (D w L s : ℕ) :
    Function.Injective
      (augmentedColumnExponent : AugmentedCoefficientIndex D w L s → Fin 4 →₀ ℕ) := by
  intro c d h
  rcases c with c | c <;> rcases d with d | d
  · exact congrArg Sum.inl ((columnExponent_injective D w L s) h)
  · exfalso
    have hh := congrArg (fun e : Fin 4 →₀ ℕ => e 1 + e 3) h
    simp only [augmentedColumnExponent, Sum.elim_inl, Sum.elim_inr] at hh
    have hc := baseColumn_seed_le c
    have hd := boundaryColumn_seed_eq d
    omega
  · exfalso
    have hh := congrArg (fun e : Fin 4 →₀ ℕ => e 1 + e 3) h
    simp only [augmentedColumnExponent, Sum.elim_inl, Sum.elim_inr] at hh
    have hc := boundaryColumn_seed_eq c
    have hd := baseColumn_seed_le d
    omega
  · exact congrArg Sum.inr ((boundaryColumnExponent_injective D w L) h)

def augmentedReconstruct (D w L s : ℕ)
    (θ : AugmentedCoefficientIndex D w L s → K) : MvPolynomial (Fin 4) K :=
  ∑ c : AugmentedCoefficientIndex D w L s,
    MvPolynomial.monomial (augmentedColumnExponent c) (θ c)

theorem augmentedReconstruct_coeff (D w L s : ℕ)
    (θ : AugmentedCoefficientIndex D w L s → K)
    (c : AugmentedCoefficientIndex D w L s) :
    MvPolynomial.coeff (augmentedColumnExponent c)
      (augmentedReconstruct K D w L s θ) = θ c := by
  classical
  rcases c with c | c <;>
    simp [augmentedReconstruct, MvPolynomial.coeff_sum,
      (augmentedColumnExponent_injective D w L s).eq_iff]

@[simp] theorem augmentedReconstruct_zero (D w L s : ℕ) :
    augmentedReconstruct K D w L s
      (0 : AugmentedCoefficientIndex D w L s → K) = 0 := by
  simp [augmentedReconstruct]

theorem augmentedReconstruct_injective (D w L s : ℕ) :
    Function.Injective (augmentedReconstruct K D w L s) := by
  intro θ η h
  funext c
  have hh := congrArg (MvPolynomial.coeff (augmentedColumnExponent c)) h
  simpa only [augmentedReconstruct_coeff] using hh

def boundaryCoefficientCount (D w L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, (D - w * (k + 1))

def augmentedCoefficientCount (D w L s : ℕ) : ℕ :=
  coefficientCount D w L s + boundaryCoefficientCount D w L

theorem boundary_coefficient_index_card (D w L : ℕ) :
    Fintype.card (BoundaryCoefficientIndex D w L) = boundaryCoefficientCount D w L := by
  simp [BoundaryCoefficientIndex, boundaryCoefficientCount, Fintype.card_sigma,
    Finset.sum_range]

theorem augmented_coefficient_index_card (D w L s : ℕ) :
    Fintype.card (AugmentedCoefficientIndex D w L s) =
      augmentedCoefficientCount D w L s := by
  rw [Fintype.card_sum, coefficient_index_card, boundary_coefficient_index_card]
  rfl

theorem boundary_coefficient_count_frozen :
    boundaryCoefficientCount 2957328 131071 184 = 31900253 := by
  norm_num [boundaryCoefficientCount, Finset.sum_range_succ]

theorem augmented_coefficient_count_frozen :
    augmentedCoefficientCount 2957328 131071 184 4 = 26084069943 := by
  rw [augmentedCoefficientCount, boundary_coefficient_count_frozen]
  norm_num [coefficientCount, Finset.sum_range_succ]

theorem frozen_augmented_interpolation_gate :
    262144 * augmentedLocalRankBound 16 184 4 <
      augmentedCoefficientCount 2957328 131071 184 4 := by
  rw [augmented_local_rank_frozen, augmented_coefficient_count_frozen]
  norm_num

def boundaryGlobalExponents (D w L : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 3 = L + 1 ∧ 0 < d 1 ∧ d 2 = 0 ∧
    d 0 + w * d 1 < D}

def augmentedGlobalExponents (D w L s : ℕ) : Set (Fin 4 →₀ ℕ) :=
  globalExponents D w L s ∪ boundaryGlobalExponents D w L

def augmentedGlobalCoefficientBox (D w L s : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (augmentedGlobalExponents D w L s)

theorem augmentedColumnMonomial_mem (D w L s : ℕ)
    (c : AugmentedCoefficientIndex D w L s) (a : K) :
    MvPolynomial.monomial (augmentedColumnExponent c) a ∈
      augmentedGlobalCoefficientBox K D w L s := by
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  left
  rcases c with c | c
  · left
    have hi := c.1.isLt
    have hj := c.2.1.isLt
    have hz := c.2.2.1.isLt
    have he := c.2.2.2.isLt
    simp only [augmentedColumnExponent, Sum.elim_inl, globalExponents,
      Set.mem_setOf_eq, columnExponent_x, columnExponent_y,
      columnExponent_r, columnExponent_z]
    omega
  · right
    have hi := c.1.isLt
    have he := c.2.isLt
    simp only [augmentedColumnExponent, Sum.elim_inr, boundaryGlobalExponents,
      Set.mem_setOf_eq, boundaryColumnExponent_x, boundaryColumnExponent_y,
      boundaryColumnExponent_r, boundaryColumnExponent_z]
    constructor
    · omega
    constructor
    · omega
    constructor
    · trivial
    · omega

theorem augmentedReconstruct_mem_globalBox (D w L s : ℕ)
    (θ : AugmentedCoefficientIndex D w L s → K) :
    augmentedReconstruct K D w L s θ ∈
      augmentedGlobalCoefficientBox K D w L s := by
  classical
  unfold augmentedReconstruct
  apply Submodule.sum_mem
  intro c hc
  exact augmentedColumnMonomial_mem K D w L s c (θ c)

theorem augmentedGlobal_support_caps (D w L s : ℕ)
    (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ∈ augmentedGlobalCoefficientBox K D w L s) :
    ∀ d ∈ Q.support,
      d 1 + d 3 ≤ L + 1 ∧ d 2 ≤ s ∧
      d 0 + w * d 1 + (w - 1) * d 2 < D ∧ d 3 ≤ L := by
  intro d hd
  rcases hQ hd with hold | hboundary
  · rcases hold with ⟨hseed, hr, hweight⟩
    exact ⟨hseed.trans (Nat.le_succ L), hr, hweight,
      (Nat.le_add_left (d 3) (d 1)).trans hseed⟩
  · rcases hboundary with ⟨hseed, hypos, hr, hweight⟩
    refine ⟨hseed.le, by omega, ?_, ?_⟩
    · simpa only [hr, Nat.mul_zero, Nat.add_zero] using hweight
    · omega

def boundaryAsColumn {D w L s : ℕ} (c : BoundaryCoefficientIndex D w L) :
    CoefficientIndex D w (L + 1) s :=
  ⟨⟨c.1.val + 1, by have hi := c.1.isLt; omega⟩,
    ⟨⟨0, Nat.succ_pos s⟩,
      ⟨⟨L - c.1.val, by
          have hi := c.1.isLt
          have hsub : L + 1 + 1 - (c.1.val + 1) = (L - c.1.val) + 1 := by omega
          rw [hsub]
          exact Nat.lt_succ_self _⟩,
        ⟨c.2.val, by exact c.2.isLt⟩⟩⟩⟩

theorem boundaryAsColumn_exponent {D w L s : ℕ}
    (c : BoundaryCoefficientIndex D w L) :
    columnExponent (boundaryAsColumn (s := s) c) = boundaryColumnExponent c := by
  ext i
  fin_cases i <;> simp [boundaryAsColumn]

def boundaryBlockEntry (D w L s : ℕ) (x u₀ u₁ : K)
    (c : BoundaryCoefficientIndex D w L) (r : ℕ) : Poly K :=
  blockEntry K D w (L + 1) s x u₀ u₁ (boundaryAsColumn (s := s) c) r

theorem coefficientBox_rzero_succ_mem_augmented
    {f M L s : ℕ} (hf : f ≤ M) {q : Poly K}
    (hq : q ∈ coefficientBox K f (L + 1) 0) :
    q ∈ augmentedCoefficientBox K M L s := by
  intro d hd
  rcases hq hd with ⟨hY, hseed, hR⟩
  simp only [augmentedBoxExponents, Set.mem_union, boxExponents,
    boundaryExponents, Set.mem_setOf_eq]
  by_cases heq : d 0 + d 2 = L + 1
  · right
    exact ⟨hY.trans hf, heq, Nat.eq_zero_of_le_zero hR⟩
  · left
    exact ⟨hY.trans hf, by omega, hR.trans (Nat.zero_le s)⟩

theorem boundaryBlockEntry_mem (D w L s : ℕ) (x u₀ u₁ : K)
    (c : BoundaryCoefficientIndex D w L) (r : ℕ) :
    boundaryBlockEntry K D w L s x u₀ u₁ c r ∈
      augmentedCoefficientBox K (min r L) L s := by
  classical
  unfold boundaryBlockEntry blockEntry
  apply Submodule.sum_mem
  intro f hf
  split_ifs with hfr
  · apply (augmentedCoefficientBox K (min r L) L s).smul_mem
    have hi := c.1.isLt
    have hfi := f.isLt
    change f.val < c.1.val + 1 + 1 at hfi
    have hfc : f.val ≤ c.1.val + 1 := by omega
    have hcL : c.1.val ≤ L := by omega
    have hmul := coefficientBox_mul K
      (seedAffine_pow_mem K u₀ u₁ (c.1.val + 1 - f.val))
      (localMonomial_mem K f.val 0 (L - c.1.val))
    have hshape :
        c.1.val + 1 - f.val + (f.val + (L - c.1.val)) = L + 1 := by
      have h1 := Nat.sub_add_cancel hfc
      have h2 := Nat.sub_add_cancel hcL
      omega
    rw [Nat.zero_add, Nat.zero_add, hshape] at hmul
    exact coefficientBox_rzero_succ_mem_augmented K
      (show f.val ≤ min r L by omega) hmul
  · exact (augmentedCoefficientBox K (min r L) L s).zero_mem

def boundedBoundaryBlockEntry (D w L s : ℕ) (x u₀ u₁ : K)
    (c : BoundaryCoefficientIndex D w L) (r : ℕ) :
    augmentedCoefficientBox K (min r L) L s :=
  ⟨boundaryBlockEntry K D w L s x u₀ u₁ c r,
    boundaryBlockEntry_mem K D w L s x u₀ u₁ c r⟩

def boundedAugmentedBlockEntry (D w L s : ℕ) (x u₀ u₁ : K)
    (c : AugmentedCoefficientIndex D w L s) (r : ℕ) :
    augmentedCoefficientBox K (min r L) L s := by
  rcases c with c | c
  · exact ⟨blockEntry K D w L s x u₀ u₁ c r, by
      apply MvPolynomial.restrictSupport_mono (R := K)
        (show boxExponents (min r L) L s ⊆
            augmentedBoxExponents (min r L) L s by
          intro d hd
          exact Or.inl hd)
      exact blockEntry_mem K D w L s x u₀ u₁ c r⟩
  · exact boundedBoundaryBlockEntry K D w L s x u₀ u₁ c r

def augmentedExtractBlock (D w L s : ℕ) (x u₀ u₁ : K) (r : ℕ) :
    (AugmentedCoefficientIndex D w L s → K) →ₗ[K]
      augmentedCoefficientBox K (min r L) L s where
  toFun θ := ∑ c : AugmentedCoefficientIndex D w L s,
    θ c • boundedAugmentedBlockEntry K D w L s x u₀ u₁ c r
  map_add' θ η := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a θ := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

theorem full_boundaryRankBound_eq (r m L s : ℕ) :
    boundaryRankBound (min r L) s (m - r) =
      boundaryRankBound (min r L) s (min (r + 1) (m - r)) := by
  by_cases h : r + 1 ≤ m - r
  · have hM : min r L ≤ r := min_le_left r L
    have hzero : min r L + 1 - (m - r) = 0 := by omega
    have hzero' : min r L + 1 - (r + 1) = 0 := by omega
    simp only [Nat.min_eq_left h, boundaryRankBound, boundaryKernelLowerBound,
      hzero, hzero', mul_zero, Nat.sub_zero]
  · have h' : m - r ≤ r + 1 := by omega
    rw [Nat.min_eq_right h']

abbrev AugmentedLocalTarget (m L s : ℕ) :=
  (r : Fin m) → LinearMap.range
    (augmentedBlockJet K (min r.val L) L s (m - r.val))

theorem augmentedLocalTarget_finrank_le (m L s : ℕ) :
    Module.finrank K (AugmentedLocalTarget K m L s) ≤
      augmentedLocalRankBound m L s := by
  change Module.finrank K ((r : Fin m) → LinearMap.range
    (augmentedBlockJet K (min r.val L) L s (m - r.val))) ≤ _
  rw [Module.finrank_pi_fintype]
  unfold augmentedLocalRankBound localRankBound boundaryLocalRankBound
  rw [← Finset.sum_add_distrib, Finset.sum_range]
  apply Finset.sum_le_sum
  intro r hr
  have hh := augmentedBlockJet_rank_le K
    (M := min r.val L) (L := L) (s := s) (h := m - r.val) (min_le_right r.val L)
  rw [full_contactRankBound_eq, full_boundaryRankBound_eq] at hh
  exact hh

abbrev AugmentedGlobalTarget (I : Type*) (m L s : ℕ) :=
  I → AugmentedLocalTarget K m L s

theorem augmentedGlobalTarget_finrank_le {I : Type*} [Fintype I]
    (m L s : ℕ) :
    Module.finrank K (AugmentedGlobalTarget K I m L s) ≤
      Fintype.card I * augmentedLocalRankBound m L s := by
  change Module.finrank K (I → AugmentedLocalTarget K m L s) ≤ _
  rw [Module.finrank_pi_fintype]
  calc
    (∑ _i : I, Module.finrank K (AugmentedLocalTarget K m L s)) ≤
        ∑ _i : I, augmentedLocalRankBound m L s := by
      apply Finset.sum_le_sum
      intro i hi
      exact augmentedLocalTarget_finrank_le K m L s
    _ = Fintype.card I * augmentedLocalRankBound m L s := by simp

def augmentedConstraintMap {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u₀ u₁ : I → K) :
    (AugmentedCoefficientIndex D w L s → K) →ₗ[K]
      AugmentedGlobalTarget K I m L s :=
  LinearMap.pi fun i => LinearMap.pi fun r =>
    (augmentedBlockJet K (min r.val L) L s (m - r.val)).rangeRestrict.comp
      (augmentedExtractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)

theorem exists_nonzero_augmented_kernel_array {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u₀ u₁ : I → K)
    (hgate : Fintype.card I * augmentedLocalRankBound m L s <
      augmentedCoefficientCount D w L s) :
    ∃ θ : AugmentedCoefficientIndex D w L s → K,
      θ ≠ 0 ∧ augmentedConstraintMap K D w L s m nodes u₀ u₁ θ = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective (augmentedConstraintMap K D w L s m nodes u₀ u₁) := by
    intro θ η heq
    by_contra hne
    apply hnone
    refine ⟨θ - η, sub_ne_zero.mpr hne, ?_⟩
    rw [map_sub, heq, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, augmented_coefficient_index_card] at hdim
  have hupper := augmentedGlobalTarget_finrank_le K (I := I) m L s
  exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)

theorem augmentedTranslationColumn_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (c : AugmentedCoefficientIndex D w L s) (a : K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁
      (MvPolynomial.monomial (augmentedColumnExponent c) a)).coeff r =
        a • ((boundedAugmentedBlockEntry K D w L s x u₀ u₁ c r) : Poly K) := by
  rcases c with c | c
  · simpa [augmentedColumnExponent, boundedAugmentedBlockEntry] using
      translation_column_coeff K D w L s x u₀ u₁ c a r
  · have hh := translation_column_coeff K D w (L + 1) s x u₀ u₁
      (boundaryAsColumn (s := s) c) a r
    rw [boundaryAsColumn_exponent] at hh
    simpa [augmentedColumnExponent, boundedAugmentedBlockEntry, boundedBoundaryBlockEntry,
      boundaryBlockEntry] using hh

theorem translation_augmentedReconstruct_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (θ : AugmentedCoefficientIndex D w L s → K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁
      (augmentedReconstruct K D w L s θ)).coeff r =
      ((augmentedExtractBlock K D w L s x u₀ u₁ r θ) : Poly K) := by
  rw [augmentedReconstruct, map_sum, Polynomial.finsetSum_coeff]
  simp only [augmentedTranslationColumn_coeff]
  change (∑ c : AugmentedCoefficientIndex D w L s,
    θ c • ((boundedAugmentedBlockEntry K D w L s x u₀ u₁ c r) : Poly K)) =
      (((∑ c : AugmentedCoefficientIndex D w L s,
        θ c • boundedAugmentedBlockEntry K D w L s x u₀ u₁ c r) :
          augmentedCoefficientBox K (min r L) L s) : Poly K)
  simp

theorem augmentedConstraintMap_apply {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u₀ u₁ : I → K)
    (θ : AugmentedCoefficientIndex D w L s → K) (i : I) (r : Fin m) :
    ((augmentedConstraintMap K D w L s m nodes u₀ u₁ θ i r) : Poly K) =
      contactJet K (m - r.val)
        ((augmentedExtractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ) : Poly K) := rfl

theorem exists_nonzero_augmented_block_equations {I : Type*} [Fintype I]
    (D w L s m : ℕ) (nodes u₀ u₁ : I → K)
    (hgate : Fintype.card I * augmentedLocalRankBound m L s <
      augmentedCoefficientCount D w L s) :
    ∃ θ : AugmentedCoefficientIndex D w L s → K, θ ≠ 0 ∧
      ∀ (i : I) (r : Fin m),
        contactJet K (m - r.val)
          ((augmentedExtractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ) : Poly K) = 0 := by
  obtain ⟨θ, hθ, hzero⟩ :=
    exists_nonzero_augmented_kernel_array K D w L s m nodes u₀ u₁ hgate
  refine ⟨θ, hθ, ?_⟩
  intro i r
  have hh := congrArg
    (fun t : AugmentedGlobalTarget K I m L s => ((t i r) : Poly K)) hzero
  change contactJet K (m - r.val)
    ((augmentedExtractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ) : Poly K) = 0 at hh
  exact hh

theorem all_augmented_blocks_divisible_of_equations
    (D w L s m : ℕ) (x u₀ u₁ : K)
    (θ : AugmentedCoefficientIndex D w L s → K)
    (h : ∀ r : Fin m, contactJet K (m - r.val)
      ((augmentedExtractBlock K D w L s x u₀ u₁ r.val θ) : Poly K) = 0) :
    ∀ r : ℕ, slopeDifference K ^ (m - r) ∣
      ((augmentedExtractBlock K D w L s x u₀ u₁ r θ) : Poly K) := by
  intro r
  by_cases hr : r < m
  · exact (contactJet_eq_zero_iff K (m - r) _).mp (h ⟨r, hr⟩)
  · have hm : m - r = 0 := by omega
    simp only [hm, pow_zero, one_dvd]

abbrev FrozenAugmentedCoefficientIndex :=
  AugmentedCoefficientIndex 2957328 131071 184 4

theorem exists_frozen_augmented_nonzero_array
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ θ : FrozenAugmentedCoefficientIndex → IRSProfile.Field, θ ≠ 0 ∧
      ∀ (i : IRSProfile.Index) (r : Fin 16),
        contactJet IRSProfile.Field (16 - r.val)
          ((augmentedExtractBlock IRSProfile.Field 2957328 131071 184 4
            (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ) : Poly IRSProfile.Field) = 0 := by
  apply exists_nonzero_augmented_block_equations IRSProfile.Field
    2957328 131071 184 4 16 (fun i : IRSProfile.Index => IRSProfile.domain i) u₀ u₁
  rw [show Fintype.card IRSProfile.Index = 262144 by norm_num [IRSProfile.Index]]
  exact frozen_augmented_interpolation_gate

theorem exists_frozen_augmented_translated_contact_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ augmentedGlobalCoefficientBox IRSProfile.Field 2957328 131071 184 4 ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (16 - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u₀ i) (u₁ i) Q).coeff r := by
  obtain ⟨θ, hθ, heq⟩ := exists_frozen_augmented_nonzero_array u₀ u₁
  refine ⟨augmentedReconstruct IRSProfile.Field 2957328 131071 184 4 θ,
    ?_, augmentedReconstruct_mem_globalBox IRSProfile.Field 2957328 131071 184 4 θ, ?_⟩
  · intro hzero
    apply hθ
    apply augmentedReconstruct_injective IRSProfile.Field 2957328 131071 184 4
    simpa only [augmentedReconstruct_zero] using hzero
  · intro i r
    rw [translation_augmentedReconstruct_coeff]
    exact all_augmented_blocks_divisible_of_equations IRSProfile.Field
      2957328 131071 184 4 16 (IRSProfile.domain i) (u₀ i) (u₁ i) θ
      (heq i) r

theorem augmented_specialization_natDegree_lt
    (D w L s : ℕ) (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hD : 0 < D) (hcaps : Q ∈ augmentedGlobalCoefficientBox K D w L s)
    (hP : P.natDegree ≤ w) :
    (specialization K P γ Q).natDegree < D := by
  classical
  have hsupport := augmentedGlobal_support_caps K D w L s Q hcaps
  have hterms : ∀ d ∈ Q.support,
      (specialization K P γ
        (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤ D - 1 := by
    intro d hd
    have hweight := (hsupport d hd).2.2.1
    have hh := specialization_monomial_natDegree_le K P γ w hP d
      (MvPolynomial.coeff d Q)
    omega
  rw [MvPolynomial.as_sum Q, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le Q.support
    (fun d => specialization K P γ
      (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
  exact lt_of_le_of_lt hh (by omega)

theorem exists_frozen_augmented_universal_vanishing_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ augmentedGlobalCoefficientBox IRSProfile.Field 2957328 131071 184 4 ∧
      ∀ (γ : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ 131071 → 184833 ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u₀ i + γ * u₁ i) →
        specialization IRSProfile.Field P γ Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hcontact⟩ :=
    exists_frozen_augmented_translated_contact_interpolant u₀ u₁
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro γ P support hP hcard hvalues
  apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P γ
    IRSProfile.domain u₀ u₁ support 16
  · intro i hi r
    exact hcontact i r
  · exact hvalues
  · have hdegree := augmented_specialization_natDegree_lt IRSProfile.Field
      2957328 131071 184 4 Q P γ (by decide) hcaps hP
    have hbound : 2957328 ≤ 16 * support.card := by omega
    exact hdegree.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactBoundaryRank

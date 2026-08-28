import ProximityPrize.SubmissionLower.ContactBoundaryInterpolation

namespace ProximityPrize.SubmissionLower.ContactStaircaseInterpolation

open scoped BigOperators Pointwise
open ContactRankKernel ContactInterpolation ContactTranslation
open ProximityPrize.Benchmark

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

variable (K : Type*) [Field K]

abbrev BoundaryChannel := (q : Fin 3) × Fin (3 - q.val)

def stairBoundaryExponents (M : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {d | d 0 ≤ M ∧ 162 < d 0 + d 2 ∧ d 0 + d 2 + d 1 ≤ 165}

def stairAugmentedExponents (M : ℕ) : Set (Fin 3 →₀ ℕ) :=
  boxExponents M 162 5 ∪ stairBoundaryExponents M

def stairBoundaryBox (M : ℕ) : Submodule K (Poly K) :=
  MvPolynomial.restrictSupport K (stairBoundaryExponents M)

def stairAugmentedBox (M : ℕ) : Submodule K (Poly K) :=
  MvPolynomial.restrictSupport K (stairAugmentedExponents M)

theorem stairAugmentedBox_eq_sup (M : ℕ) :
    stairAugmentedBox K M = coefficientBox K M 162 5 ⊔ stairBoundaryBox K M := by
  exact ContactBoundaryRank.restrictSupport_union K
    (boxExponents M 162 5) (stairBoundaryExponents M)

def stairBoundaryCode (M : ℕ) (d : stairBoundaryExponents M) :
    BoundaryChannel × Fin (M + 1) :=
  let q := d.val 0 + d.val 2 - 162
  ⟨⟨⟨q - 1, by rcases d.property with ⟨hM, hlo, hhi⟩; omega⟩,
      ⟨d.val 1, by
        rcases d.property with ⟨hM, hlo, hhi⟩
        have hqdef : q = d.val 0 + d.val 2 - 162 := rfl
        have hqlo : 1 ≤ q := by dsimp [q]; omega
        have hqhi : q ≤ 3 := by dsimp [q]; omega
        change d.val 1 < 3 - (q - 1)
        interval_cases q <;> omega⟩⟩,
    ⟨d.val 0, by rcases d.property with ⟨hM, hlo, hhi⟩; omega⟩⟩

theorem stairBoundaryCode_injective (M : ℕ) :
    Function.Injective (stairBoundaryCode M) := by
  intro d e h
  rcases d.property with ⟨hdM, hdlo, hdhi⟩
  rcases e.property with ⟨heM, helo, hehi⟩
  have hq := congrArg (fun x : BoundaryChannel × Fin (M + 1) => x.1.1.val) h
  have hr := congrArg (fun x : BoundaryChannel × Fin (M + 1) => x.1.2.val) h
  have hf := congrArg (fun x : BoundaryChannel × Fin (M + 1) => x.2.val) h
  simp only [stairBoundaryCode] at hq hr hf
  have hdle : 162 ≤ d.val 0 + d.val 2 := by omega
  have hele : 162 ≤ e.val 0 + e.val 2 := by omega
  have hdrec := Nat.sub_add_cancel hdle
  have herec := Nat.sub_add_cancel hele
  have hdqlo : 1 ≤ d.val 0 + d.val 2 - 162 := by omega
  have heqlo : 1 ≤ e.val 0 + e.val 2 - 162 := by omega
  have hq' : d.val 0 + d.val 2 - 162 = e.val 0 + e.val 2 - 162 := by omega
  have hsum : d.val 0 + d.val 2 = e.val 0 + e.val 2 := by omega
  have hz : d.val 2 = e.val 2 := by omega
  apply Subtype.ext
  ext i
  fin_cases i
  · exact hf
  · exact hr
  · exact hz

instance stairBoundaryExponentsFintype (M : ℕ) :
    Fintype (stairBoundaryExponents M) := by
  classical
  exact Fintype.ofInjective (stairBoundaryCode M)
    (stairBoundaryCode_injective M)

instance stairBoundaryBoxFinite (M : ℕ) : Module.Finite K (stairBoundaryBox K M) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (stairBoundaryExponents M))

theorem stairBoundaryBox_finrank_le (M : ℕ) :
    Module.finrank K (stairBoundaryBox K M) ≤ 6 * (M + 1) := by
  change Module.finrank K (MvPolynomial.restrictSupport K (stairBoundaryExponents M)) ≤ _
  rw [Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport K (stairBoundaryExponents M))]
  have hc := Fintype.card_le_of_injective (stairBoundaryCode M)
    (stairBoundaryCode_injective M)
  norm_num [BoundaryChannel, Fintype.card_sigma, Finset.sum_range] at hc ⊢
  exact hc

instance stairAugmentedBoxFinite (M : ℕ) : Module.Finite K (stairAugmentedBox K M) := by
  rw [stairAugmentedBox_eq_sup]
  infer_instance

theorem stairAugmentedBox_finrank_le (M : ℕ) (hM : M ≤ 162) :
    Module.finrank K (stairAugmentedBox K M) ≤
      blockInputCount M 162 5 + 6 * (M + 1) := by
  rw [stairAugmentedBox_eq_sup]
  have hsup := Submodule.finrank_add_le_finrank_add_finrank
    (coefficientBox K M 162 5) (stairBoundaryBox K M)
  rw [coefficientBox_finrank_range K M 162 5 hM] at hsup
  exact hsup.trans (Nat.add_le_add_left (stairBoundaryBox_finrank_le K M) _)

abbrev kernelChannels (h : ℕ) := {c : BoundaryChannel // c.2.val + h ≤ 5}

def kernelBoundaryExponent {M h : ℕ} (c : kernelChannels h × Fin (M + 1 - h)) :
    Fin 3 →₀ ℕ :=
  let q := c.1.val.1.val + 1
  let j := c.1.val.2.val
  let g := c.2.val
  Finsupp.single 0 g + Finsupp.single 1 j +
    Finsupp.single 2 (162 - h + q - g)

@[simp] theorem kernelBoundaryExponent_zero {M h : ℕ}
    (c : kernelChannels h × Fin (M + 1 - h)) :
    kernelBoundaryExponent c 0 = c.2.val := by
  simp [kernelBoundaryExponent]

@[simp] theorem kernelBoundaryExponent_one {M h : ℕ}
    (c : kernelChannels h × Fin (M + 1 - h)) :
    kernelBoundaryExponent c 1 = c.1.val.2.val := by
  simp [kernelBoundaryExponent]

@[simp] theorem kernelBoundaryExponent_two {M h : ℕ}
    (c : kernelChannels h × Fin (M + 1 - h)) :
    kernelBoundaryExponent c 2 =
      162 - h + (c.1.val.1.val + 1) - c.2.val := by
  simp [kernelBoundaryExponent]

def kernelBoundaryReconstruct (M h : ℕ) :
    (kernelChannels h × Fin (M + 1 - h) → K) →ₗ[K] Poly K where
  toFun θ := ∑ c, MvPolynomial.monomial (kernelBoundaryExponent c) (θ c)
  map_add' θ η := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a θ := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Pi.smul_apply, RingHom.id_apply]
    ext d
    by_cases hd : kernelBoundaryExponent c = d
    · subst d
      simp [MvPolynomial.smul_eq_C_mul]
    · simp [MvPolynomial.coeff_monomial, hd, MvPolynomial.smul_eq_C_mul]

theorem kernelBoundaryExponent_injective {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162) :
    Function.Injective
      (kernelBoundaryExponent : kernelChannels h × Fin (M + 1 - h) → Fin 3 →₀ ℕ) := by
  intro c d heq
  have h0 := congrArg (fun e : Fin 3 →₀ ℕ => e 0) heq
  have h1 := congrArg (fun e : Fin 3 →₀ ℕ => e 1) heq
  have h2 := congrArg (fun e : Fin 3 →₀ ℕ => e 2) heq
  simp only [kernelBoundaryExponent_zero] at h0
  simp only [kernelBoundaryExponent_one] at h1
  simp only [kernelBoundaryExponent_two] at h2
  have hc0 := c.2.isLt
  have hd0 := d.2.isLt
  have hcq := c.1.val.1.isLt
  have hdq := d.1.val.1.isLt
  rcases c with ⟨⟨⟨⟨cq, hcq'⟩, ⟨cj, hcj⟩⟩, hc⟩, ⟨cg, hcg⟩⟩
  rcases d with ⟨⟨⟨⟨dq, hdq'⟩, ⟨dj, hdj⟩⟩, hd⟩, ⟨dg, hdg⟩⟩
  simp only at h0 h1 h2
  subst dg
  subst dj
  have hqeq : cq = dq := by omega
  subst dq
  rfl

theorem kernelBoundaryReconstruct_injective {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162) :
    Function.Injective (kernelBoundaryReconstruct K M h) := by
  intro θ η heq
  funext c
  have hh := congrArg (MvPolynomial.coeff (kernelBoundaryExponent c)) heq
  classical
  simpa [kernelBoundaryReconstruct, MvPolynomial.coeff_sum,
    (kernelBoundaryExponent_injective hM hML).eq_iff] using hh

theorem kernelBoundaryExponent_seed_eq {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162)
    (c : kernelChannels h × Fin (M + 1 - h)) :
    kernelBoundaryExponent c 0 + kernelBoundaryExponent c 2 =
      162 - h + (c.1.val.1.val + 1) := by
  simp only [kernelBoundaryExponent_zero, kernelBoundaryExponent_two]
  have hg := c.2.isLt
  have hh : h ≤ 162 := hM.trans hML
  have hgh : c.2.val ≤ M - h := by omega
  have hg162 : c.2.val ≤ 162 - h := hgh.trans (Nat.sub_le_sub_right hML h)
  have hcancel := Nat.sub_add_cancel hg162
  omega

theorem difference_add_kernelBoundary_subset_stair
    {M h : ℕ} (hM : h ≤ M) (hML : M ≤ 162)
    (c : kernelChannels h × Fin (M + 1 - h)) :
    ContactBoundaryRank.differenceExponents h +
        {kernelBoundaryExponent c} ⊆ stairAugmentedExponents M := by
  rintro d ⟨a, ha, b, hb, rfl⟩
  rcases ha with ⟨ha, ha2⟩
  have hbEq : b = kernelBoundaryExponent c := by simpa using hb
  subst b
  have hseed := kernelBoundaryExponent_seed_eq hM hML c
  have hg := c.2.isLt
  have hq := c.1.val.1.isLt
  have hj := c.1.val.2.isLt
  have hjh := c.1.property
  simp only [stairAugmentedExponents, Set.mem_union, boxExponents,
    stairBoundaryExponents, Set.mem_setOf_eq, Finsupp.add_apply,
    kernelBoundaryExponent_zero, kernelBoundaryExponent_one,
    kernelBoundaryExponent_two]
  by_cases hold : a 0 + c.2.val +
      (162 - h + (c.1.val.1.val + 1) - c.2.val) ≤ 162
  · left
    constructor
    · omega
    constructor <;> omega
  · right
    constructor
    · omega
    constructor
    · omega
    · omega

theorem slopeDifference_mul_kernelBoundaryMonomial_mem
    {M h : ℕ} (hM : h ≤ M) (hML : M ≤ 162)
    (c : kernelChannels h × Fin (M + 1 - h)) (a : K) :
    slopeDifference K ^ h * MvPolynomial.monomial (kernelBoundaryExponent c) a ∈
      stairAugmentedBox K M := by
  have hm : MvPolynomial.monomial (kernelBoundaryExponent c) a ∈
      MvPolynomial.restrictSupport K ({kernelBoundaryExponent c} : Set (Fin 3 →₀ ℕ)) := by
    apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
    exact Or.inl (Set.mem_singleton _)
  have hprod : slopeDifference K ^ h * MvPolynomial.monomial
      (kernelBoundaryExponent c) a ∈
      MvPolynomial.restrictSupport K
        (ContactBoundaryRank.differenceExponents h + {kernelBoundaryExponent c}) := by
    rw [MvPolynomial.restrictSupport_add]
    exact Submodule.mul_mem_mul
      (ContactBoundaryRank.slopeDifference_pow_mem_differenceBox K h) hm
  exact MvPolynomial.restrictSupport_mono (R := K)
    (difference_add_kernelBoundary_subset_stair hM hML c) hprod

def boundaryKernelMultiply {M h : ℕ} (hM : h ≤ M) (hML : M ≤ 162) :
    (kernelChannels h × Fin (M + 1 - h) → K) →ₗ[K] stairAugmentedBox K M where
  toFun θ := ⟨slopeDifference K ^ h * kernelBoundaryReconstruct K M h θ, by
    change slopeDifference K ^ h *
      (∑ c, MvPolynomial.monomial (kernelBoundaryExponent c) (θ c)) ∈ _
    rw [Finset.mul_sum]
    apply Submodule.sum_mem
    intro c hc
    exact slopeDifference_mul_kernelBoundaryMonomial_mem K hM hML c (θ c)⟩
  map_add' θ η := by
    apply Subtype.ext
    simp only [map_add, mul_add, Submodule.coe_add]
  map_smul' a θ := by
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul,
      RingHom.id_apply]
    ring

theorem old_coeff_kernelBoundary_zero {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162)
    (q : coefficientBox K (M - h) (162 - h) (5 - h))
    (c : kernelChannels h × Fin (M + 1 - h)) :
    MvPolynomial.coeff (kernelBoundaryExponent c) q.val = 0 := by
  by_contra hne
  have hmem : kernelBoundaryExponent c ∈ q.val.support :=
    MvPolynomial.mem_support_iff.mpr hne
  rcases q.property hmem with ⟨hY, hbox, hR⟩
  have hseed := kernelBoundaryExponent_seed_eq hM hML c
  have hgt : 162 - h <
      kernelBoundaryExponent c 0 + kernelBoundaryExponent c 2 := by
    rw [hseed]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  exact (Nat.not_lt_of_ge hbox) hgt

theorem kernelBoundaryReconstruct_coeff {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162)
    (θ : kernelChannels h × Fin (M + 1 - h) → K)
    (c : kernelChannels h × Fin (M + 1 - h)) :
    MvPolynomial.coeff (kernelBoundaryExponent c)
      (kernelBoundaryReconstruct K M h θ) = θ c := by
  classical
  simp [kernelBoundaryReconstruct, MvPolynomial.coeff_sum,
    (kernelBoundaryExponent_injective hM hML).eq_iff]

def combinedStairMultiply {M h : ℕ} (hM : h ≤ M) (hML : M ≤ 162)
    (hs : h ≤ 5) :
    (coefficientBox K (M - h) (162 - h) (5 - h) ×
      (kernelChannels h × Fin (M + 1 - h) → K)) →ₗ[K]
        stairAugmentedBox K M where
  toFun q := ⟨slopeDifference K ^ h *
      (q.1.val + kernelBoundaryReconstruct K M h q.2), by
    rw [mul_add]
    apply (stairAugmentedBox K M).add_mem
    · apply MvPolynomial.restrictSupport_mono (R := K)
          (show boxExponents M 162 5 ⊆ stairAugmentedExponents M by
            intro d hd
            exact Or.inl hd)
        (slopeDifference_mul_mem_coefficientBox K hM (hM.trans hML) hs q.1.property)
    · exact (boundaryKernelMultiply K hM hML q.2).property⟩
  map_add' q r := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    ring
  map_smul' a q := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
      RingHom.id_apply, MvPolynomial.smul_eq_C_mul]
    ring

theorem combinedStairMultiply_injective {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162) (hs : h ≤ 5) :
    Function.Injective (combinedStairMultiply K hM hML hs) := by
  intro q r heq
  have hmul : slopeDifference K ^ h *
      (q.1.val + kernelBoundaryReconstruct K M h q.2) =
    slopeDifference K ^ h *
      (r.1.val + kernelBoundaryReconstruct K M h r.2) := congrArg Subtype.val heq
  have hsum := mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hmul
  have htheta : q.2 = r.2 := by
    funext c
    have hh := congrArg (MvPolynomial.coeff (kernelBoundaryExponent c)) hsum
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add,
      old_coeff_kernelBoundary_zero K hM hML q.1 c,
      old_coeff_kernelBoundary_zero K hM hML r.1 c,
      zero_add, zero_add, kernelBoundaryReconstruct_coeff K hM hML,
      kernelBoundaryReconstruct_coeff K hM hML] at hh
    exact hh
  apply Prod.ext
  · apply Subtype.ext
    rw [htheta] at hsum
    exact add_right_cancel hsum
  · exact htheta

def stairBlockJet (M h : ℕ) : stairAugmentedBox K M →ₗ[K] Poly K :=
  (contactJet K h).comp (stairAugmentedBox K M).subtype

def combinedStairKernelEmbedding {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162) (hs : h ≤ 5) :
    (coefficientBox K (M - h) (162 - h) (5 - h) ×
      (kernelChannels h × Fin (M + 1 - h) → K)) →ₗ[K]
      LinearMap.ker (stairBlockJet K M h) :=
  LinearMap.codRestrict (LinearMap.ker (stairBlockJet K M h))
    (combinedStairMultiply K hM hML hs) (fun q => by
      change contactJet K h (slopeDifference K ^ h *
        (q.1.val + kernelBoundaryReconstruct K M h q.2)) = 0
      exact contactJet_mul_slopeDifference K h _)

theorem combinedStairKernelEmbedding_injective {M h : ℕ}
    (hM : h ≤ M) (hML : M ≤ 162) (hs : h ≤ 5) :
    Function.Injective (combinedStairKernelEmbedding K hM hML hs) := by
  intro q r heq
  apply combinedStairMultiply_injective K hM hML hs
  exact congrArg Subtype.val heq

def stairBoundaryKernelCount (M h : ℕ) : ℕ :=
  Fintype.card (kernelChannels h) * (M + 1 - h)

def kernelChannelCount (h : ℕ) : ℕ :=
  min 3 (6 - h) + min 2 (6 - h) + min 1 (6 - h)

abbrev KernelChannelIndex (h : ℕ) :=
  (q : Fin 3) × Fin (min (3 - q.val) (6 - h))

def kernelChannelsEquiv (h : ℕ) : kernelChannels h ≃ KernelChannelIndex h where
  toFun c := ⟨c.val.1, ⟨c.val.2.val, by
    apply lt_min c.val.2.isLt
    have hc := c.property
    omega⟩⟩
  invFun c := ⟨⟨c.1, ⟨c.2.val, (c.2.isLt.trans_le (min_le_left _ _))⟩⟩, by
    change c.2.val + h ≤ 5
    have hc : c.2.val < 6 - h := c.2.isLt.trans_le (min_le_right _ _)
    omega⟩
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Sigma.ext
    · rfl
    · apply HEq.rfl

theorem kernelChannels_card (h : ℕ) :
    Fintype.card (kernelChannels h) = kernelChannelCount h := by
  rw [Fintype.card_congr (kernelChannelsEquiv h)]
  simp only [KernelChannelIndex, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [kernelChannelCount, Nat.add_assoc]

def stairBoundaryRankBound (M h : ℕ) : ℕ :=
  6 * (M + 1) - stairBoundaryKernelCount M h

theorem stairBlockJet_rank_le {M h : ℕ} (hML : M ≤ 162) :
    Module.finrank K (LinearMap.range (stairBlockJet K M h)) ≤
      contactRankBound M 162 5 h + stairBoundaryRankBound M h := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ 5
    · have hinj := LinearMap.finrank_le_finrank_of_injective
          (combinedStairKernelEmbedding_injective K hM hML hs)
      have hsum := (stairBlockJet K M h).finrank_range_add_finrank_ker
      have hdim := stairAugmentedBox_finrank_le K M hML
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Fintype.card_prod, Fintype.card_fin,
        coefficientBox_finrank_range K (M - h) (162 - h) (5 - h)
          (Nat.sub_le_sub_right hML h)] at hinj
      have hMeq : M - h + 1 = M + 1 - h := by omega
      have hLeq : 162 - h + 1 = 162 + 1 - h := by omega
      have hseq : 5 - h + 1 = 5 + 1 - h := by omega
      rw [hMeq, hLeq, hseq] at hinj
      have hbase := blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
      rw [coefficientBox_finrank_range K M 162 5 hML,
        coefficientBox_finrank_range K (M - h) (162 - h) (5 - h)
          (Nat.sub_le_sub_right hML h), hMeq, hLeq, hseq] at hbase
      have hKI : blockKernelLowerBound M 162 5 h ≤ blockInputCount M 162 5 := by
        simp only [blockKernelLowerBound, blockInputCount]
        omega
      have hBI : stairBoundaryKernelCount M h ≤ 6 * (M + 1) := by
        unfold stairBoundaryKernelCount
        have hc : Fintype.card (kernelChannels h) ≤ 6 := by
          calc
            _ ≤ Fintype.card BoundaryChannel :=
              Fintype.card_le_of_injective (fun c : kernelChannels h => c.val)
                Subtype.val_injective
            _ = 6 := by
              norm_num [BoundaryChannel, Fintype.card_sigma, Finset.sum_range,
                Fin.sum_univ_succ]
        exact (Nat.mul_le_mul hc (Nat.sub_le _ _))
      have hinj' : blockKernelLowerBound M 162 5 h + stairBoundaryKernelCount M h ≤
          Module.finrank K (LinearMap.ker (stairBlockJet K M h)) := by
        simpa only [blockKernelLowerBound, stairBoundaryKernelCount] using hinj
      have hcontact : contactRankBound M 162 5 h + blockKernelLowerBound M 162 5 h =
          blockInputCount M 162 5 := Nat.sub_add_cancel hKI
      have hboundary : stairBoundaryRankBound M h + stairBoundaryKernelCount M h =
          6 * (M + 1) := Nat.sub_add_cancel hBI
      omega
    · have hrange := LinearMap.finrank_range_le (stairBlockJet K M h)
      have hdim := stairAugmentedBox_finrank_le K M hML
      have hz : 5 + 1 - h = 0 := by omega
      have hkc : Fintype.card (kernelChannels h) = 0 := by
        letI : IsEmpty (kernelChannels h) := ⟨fun c => by
          have := c.property
          omega⟩
        exact Fintype.card_eq_zero
      simpa only [contactRankBound, blockKernelLowerBound, blockInputCount,
        stairBoundaryRankBound, stairBoundaryKernelCount, hz, zero_mul,
        Nat.sub_zero, hkc] using hrange.trans hdim
  · have hrange := LinearMap.finrank_range_le (stairBlockJet K M h)
    have hdim := stairAugmentedBox_finrank_le K M hML
    have hz : M + 1 - h = 0 := by omega
    simpa only [contactRankBound, blockKernelLowerBound, blockInputCount,
      stairBoundaryRankBound, stairBoundaryKernelCount, hz, mul_zero,
      Nat.sub_zero, Finset.range_zero, Finset.sum_empty] using hrange.trans hdim

theorem full_stairBoundaryRankBound_eq (r m : ℕ) :
    stairBoundaryRankBound (min r 162) (m - r) =
      stairBoundaryRankBound (min r 162) (min (r + 1) (m - r)) := by
  by_cases h : r + 1 ≤ m - r
  · have hM : min r 162 ≤ r := min_le_left r 162
    have hzero : min r 162 + 1 - (m - r) = 0 := by omega
    have hzero' : min r 162 + 1 - (r + 1) = 0 := by omega
    simp only [Nat.min_eq_left h, stairBoundaryRankBound,
      stairBoundaryKernelCount, hzero, hzero', mul_zero, Nat.sub_zero]
  · have h' : m - r ≤ r + 1 := by omega
    rw [Nat.min_eq_right h']

def stairBoundaryLocalRankBound (m : ℕ) : ℕ :=
  ∑ r ∈ Finset.range m,
    stairBoundaryRankBound (min r 162) (min (r + 1) (m - r))

def stairLocalRankBound (m : ℕ) : ℕ :=
  localRankBound m 162 5 + stairBoundaryLocalRankBound m

theorem stair_boundary_local_rank_frozen : stairBoundaryLocalRankBound 18 = 674 := by
  norm_num [stairBoundaryLocalRankBound, stairBoundaryRankBound,
    stairBoundaryKernelCount, kernelChannels_card, kernelChannelCount,
    Finset.sum_range_succ]

theorem stair_local_rank_frozen : stairLocalRankBound 18 = 128988 := by
  rw [stairLocalRankBound, stair_boundary_local_rank_frozen]
  norm_num [localRankBound, contactRankBound, blockInputCount,
    blockKernelLowerBound, Finset.sum_range_succ]

abbrev StairBoundaryCoefficientIndex (D w L : ℕ) :=
  (c : BoundaryChannel) ×
    (t : Fin (L - c.1.val)) ×
      Fin (D - w * (c.1.val + 1 + t.val) - (w - 1) * c.2.val)

abbrev StairCoefficientIndex (D w L s : ℕ) :=
  CoefficientIndex D w L s ⊕ StairBoundaryCoefficientIndex D w L

def stairBoundaryColumnExponent {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 c.2.2.val +
    Finsupp.single 1 (c.1.1.val + 1 + c.2.1.val) +
    Finsupp.single 2 c.1.2.val +
    Finsupp.single 3 (L - c.2.1.val)

@[simp] theorem stairBoundaryColumnExponent_x {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    stairBoundaryColumnExponent c 0 = c.2.2.val := by simp [stairBoundaryColumnExponent]

@[simp] theorem stairBoundaryColumnExponent_y {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    stairBoundaryColumnExponent c 1 = c.1.1.val + 1 + c.2.1.val := by
  simp [stairBoundaryColumnExponent]

@[simp] theorem stairBoundaryColumnExponent_r {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    stairBoundaryColumnExponent c 2 = c.1.2.val := by simp [stairBoundaryColumnExponent]

@[simp] theorem stairBoundaryColumnExponent_z {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    stairBoundaryColumnExponent c 3 = L - c.2.1.val := by simp [stairBoundaryColumnExponent]

def stairColumnExponent {D w L s : ℕ} (c : StairCoefficientIndex D w L s) :
    Fin 4 →₀ ℕ := Sum.elim columnExponent stairBoundaryColumnExponent c

theorem stairBoundaryColumn_seed_eq {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    stairBoundaryColumnExponent c 1 + stairBoundaryColumnExponent c 3 =
      L + (c.1.1.val + 1) := by
  simp only [stairBoundaryColumnExponent_y, stairBoundaryColumnExponent_z]
  have ht := c.2.1.isLt
  have hc := c.1.1.isLt
  omega

theorem stairBoundaryColumnExponent_injective (D w L : ℕ) :
    Function.Injective
      (stairBoundaryColumnExponent : StairBoundaryCoefficientIndex D w L → Fin 4 →₀ ℕ) := by
  intro c d h
  have hx := congrArg (fun e : Fin 4 →₀ ℕ => e 0) h
  have hy := congrArg (fun e : Fin 4 →₀ ℕ => e 1) h
  have hr := congrArg (fun e : Fin 4 →₀ ℕ => e 2) h
  have hz := congrArg (fun e : Fin 4 →₀ ℕ => e 3) h
  simp only [stairBoundaryColumnExponent_x] at hx
  simp only [stairBoundaryColumnExponent_y] at hy
  simp only [stairBoundaryColumnExponent_r] at hr
  simp only [stairBoundaryColumnExponent_z] at hz
  have hcseed := stairBoundaryColumn_seed_eq c
  have hdseed := stairBoundaryColumn_seed_eq d
  have hq : c.1.1.val = d.1.1.val := by omega
  have ht : c.2.1.val = d.2.1.val := by omega
  have hj : c.1.2.val = d.1.2.val := hr
  have he : c.2.2.val = d.2.2.val := hx
  rcases c with ⟨⟨⟨cq, hcq⟩, ⟨cj, hcj⟩⟩, ⟨⟨ct, hct⟩, ⟨ce, hce⟩⟩⟩
  rcases d with ⟨⟨⟨dq, hdq⟩, ⟨dj, hdj⟩⟩, ⟨⟨dt, hdt⟩, ⟨de, hde⟩⟩⟩
  simp only at hq ht hj he
  subst dq
  subst dj
  subst dt
  subst de
  rfl

theorem stairColumnExponent_injective (D w L s : ℕ) :
    Function.Injective
      (stairColumnExponent : StairCoefficientIndex D w L s → Fin 4 →₀ ℕ) := by
  intro c d h
  rcases c with c | c <;> rcases d with d | d
  · exact congrArg Sum.inl ((columnExponent_injective D w L s) h)
  · exfalso
    have hh := congrArg (fun e : Fin 4 →₀ ℕ => e 1 + e 3) h
    simp only [stairColumnExponent, Sum.elim_inl, Sum.elim_inr] at hh
    have hc := ContactBoundaryRank.baseColumn_seed_le c
    have hd := stairBoundaryColumn_seed_eq d
    have hq := d.1.1.isLt
    omega
  · exfalso
    have hh := congrArg (fun e : Fin 4 →₀ ℕ => e 1 + e 3) h
    simp only [stairColumnExponent, Sum.elim_inl, Sum.elim_inr] at hh
    have hc := stairBoundaryColumn_seed_eq c
    have hd := ContactBoundaryRank.baseColumn_seed_le d
    have hq := c.1.1.isLt
    omega
  · exact congrArg Sum.inr ((stairBoundaryColumnExponent_injective D w L) h)

def stairReconstruct (D w L s : ℕ) (θ : StairCoefficientIndex D w L s → K) :
    MvPolynomial (Fin 4) K :=
  ∑ c, MvPolynomial.monomial (stairColumnExponent c) (θ c)

theorem stairReconstruct_coeff (D w L s : ℕ)
    (θ : StairCoefficientIndex D w L s → K) (c : StairCoefficientIndex D w L s) :
    MvPolynomial.coeff (stairColumnExponent c) (stairReconstruct K D w L s θ) = θ c := by
  classical
  rcases c with c | c <;>
    simp [stairReconstruct, MvPolynomial.coeff_sum,
      (stairColumnExponent_injective D w L s).eq_iff]

@[simp] theorem stairReconstruct_zero (D w L s : ℕ) :
    stairReconstruct K D w L s (0 : StairCoefficientIndex D w L s → K) = 0 := by
  simp [stairReconstruct]

theorem stairReconstruct_injective (D w L s : ℕ) :
    Function.Injective (stairReconstruct K D w L s) := by
  intro θ η h
  funext c
  have hh := congrArg (MvPolynomial.coeff (stairColumnExponent c)) h
  simpa only [stairReconstruct_coeff] using hh

def stairBoundaryCoefficientCount (D w L : ℕ) : ℕ :=
  ∑ c : BoundaryChannel,
    ∑ t : Fin (L - c.1.val),
      (D - w * (c.1.val + 1 + t.val) - (w - 1) * c.2.val)

def stairCoefficientCount (D w L s : ℕ) : ℕ :=
  coefficientCount D w L s + stairBoundaryCoefficientCount D w L

theorem stair_boundary_index_card (D w L : ℕ) :
    Fintype.card (StairBoundaryCoefficientIndex D w L) =
      stairBoundaryCoefficientCount D w L := by
  simp [StairBoundaryCoefficientIndex, BoundaryChannel, stairBoundaryCoefficientCount,
    Fintype.card_sigma]

theorem stair_index_card (D w L s : ℕ) :
    Fintype.card (StairCoefficientIndex D w L s) = stairCoefficientCount D w L s := by
  rw [Fintype.card_sum, coefficient_index_card, stair_boundary_index_card]
  rfl

theorem stair_boundary_coefficient_count_frozen :
    stairBoundaryCoefficientCount 3325194 131071 162 = 218030972 := by
  decide

theorem stair_coefficient_count_frozen :
    stairCoefficientCount 3325194 131071 162 5 = 33814325384 := by
  rw [stairCoefficientCount, stair_boundary_coefficient_count_frozen]
  norm_num [coefficientCount, Finset.sum_range_succ]

theorem frozen_stair_interpolation_gate :
    262144 * stairLocalRankBound 18 < stairCoefficientCount 3325194 131071 162 5 := by
  rw [stair_local_rank_frozen, stair_coefficient_count_frozen]
  norm_num

def stairBoundaryGlobalExponents (D w L : ℕ) : Set (Fin 4 →₀ ℕ) :=
  {d | L < d 1 + d 3 ∧ d 1 + d 3 + d 2 ≤ L + 3 ∧
    d 3 ≤ L ∧ d 0 + w * d 1 + (w - 1) * d 2 < D}

def stairGlobalExponents (D w L : ℕ) : Set (Fin 4 →₀ ℕ) :=
  globalExponents D w L 5 ∪ stairBoundaryGlobalExponents D w L

def stairGlobalCoefficientBox (D w L : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (stairGlobalExponents D w L)

theorem stairColumnMonomial_mem (D w L : ℕ)
    (c : StairCoefficientIndex D w L 5) (a : K) :
    MvPolynomial.monomial (stairColumnExponent c) a ∈
      stairGlobalCoefficientBox K D w L := by
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  left
  rcases c with c | c
  · left
    have hi := c.1.isLt
    have hj := c.2.1.isLt
    have hz := c.2.2.1.isLt
    have he := c.2.2.2.isLt
    simp only [stairColumnExponent, Sum.elim_inl, globalExponents,
      Set.mem_setOf_eq, columnExponent_x, columnExponent_y,
      columnExponent_r, columnExponent_z]
    omega
  · right
    have hq := c.1.1.isLt
    have hj := c.1.2.isLt
    have ht := c.2.1.isLt
    have he := c.2.2.isLt
    have hseed := stairBoundaryColumn_seed_eq c
    simp only [stairColumnExponent, Sum.elim_inr, stairBoundaryGlobalExponents,
      Set.mem_setOf_eq, stairBoundaryColumnExponent_x,
      stairBoundaryColumnExponent_y, stairBoundaryColumnExponent_r,
      stairBoundaryColumnExponent_z]
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    · omega

theorem stairReconstruct_mem_globalBox (D w L : ℕ)
    (θ : StairCoefficientIndex D w L 5 → K) :
    stairReconstruct K D w L 5 θ ∈ stairGlobalCoefficientBox K D w L := by
  classical
  unfold stairReconstruct
  apply Submodule.sum_mem
  intro c hc
  exact stairColumnMonomial_mem K D w L c (θ c)

theorem stairGlobal_support_caps (D w L : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ∈ stairGlobalCoefficientBox K D w L) :
    ∀ d ∈ Q.support,
      d 1 + d 3 ≤ L + 3 ∧ d 2 ≤ 5 ∧
      d 0 + w * d 1 + (w - 1) * d 2 < D ∧ d 3 ≤ L := by
  intro d hd
  rcases hQ hd with hold | hstair
  · rcases hold with ⟨hseed, hr, hweight⟩
    exact ⟨hseed.trans (by omega), hr, hweight,
      (Nat.le_add_left (d 3) (d 1)).trans hseed⟩
  · rcases hstair with ⟨hlo, htotal, hz, hweight⟩
    exact ⟨by omega, by omega, hweight, hz⟩

theorem stairGlobal_mem_hull (D w L : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ∈ stairGlobalCoefficientBox K D w L) :
    Q ∈ globalCoefficientBox K D w (L + 3) 5 := by
  intro d hd
  have hc := stairGlobal_support_caps K D w L Q hQ d hd
  exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

theorem stairGlobal_degree_Z_le (D w L : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ∈ stairGlobalCoefficientBox K D w L) :
    Q.degreeOf (3 : Fin 4) ≤ L := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact (stairGlobal_support_caps K D w L Q hQ d hd).2.2.2

def stairBoundaryAsColumn {D w L : ℕ} (c : StairBoundaryCoefficientIndex D w L) :
    CoefficientIndex D w (L + 3) 5 :=
  ⟨⟨c.1.1.val + 1 + c.2.1.val, by
      have hq := c.1.1.isLt
      have ht := c.2.1.isLt
      omega⟩,
    ⟨⟨c.1.2.val, by have hj := c.1.2.isLt; omega⟩,
      ⟨⟨L - c.2.1.val, by
          have hq := c.1.1.isLt
          have ht := c.2.1.isLt
          have hsub : L + 3 + 1 - (c.1.1.val + 1 + c.2.1.val) =
              (L - c.2.1.val) + (3 - c.1.1.val) := by omega
          rw [hsub]
          have : 0 < 3 - c.1.1.val := by omega
          omega⟩,
        ⟨c.2.2.val, by exact c.2.2.isLt⟩⟩⟩⟩

theorem stairBoundaryAsColumn_exponent {D w L : ℕ}
    (c : StairBoundaryCoefficientIndex D w L) :
    columnExponent (stairBoundaryAsColumn c) = stairBoundaryColumnExponent c := by
  ext i
  fin_cases i <;> simp [stairBoundaryAsColumn]

def stairBoundaryBlockEntry (D w L : ℕ) (x u₀ u₁ : K)
    (c : StairBoundaryCoefficientIndex D w L) (r : ℕ) : Poly K :=
  blockEntry K D w (L + 3) 5 x u₀ u₁ (stairBoundaryAsColumn c) r

theorem coefficientBox_stair_mem
    {f M L q j : ℕ} (hf : f ≤ M) (hq : 1 ≤ q) (hqj : q + j ≤ 3)
    {P : Poly K} (hP : P ∈ coefficientBox K f (L + q) j) :
    P ∈ MvPolynomial.restrictSupport K
      (boxExponents M L 5 ∪ {d | d 0 ≤ M ∧ L < d 0 + d 2 ∧
        d 0 + d 2 + d 1 ≤ L + 3}) := by
  intro d hd
  rcases hP hd with ⟨hY, hseed, hR⟩
  simp only [Set.mem_union, boxExponents, Set.mem_setOf_eq]
  by_cases hold : d 0 + d 2 ≤ L
  · exact Or.inl ⟨hY.trans hf, hold, hR.trans (by omega)⟩
  · exact Or.inr ⟨hY.trans hf, by omega, by omega⟩

theorem stairBoundaryBlockEntry_mem (D w : ℕ) (x u₀ u₁ : K)
    (c : StairBoundaryCoefficientIndex D w 162) (r : ℕ) :
    stairBoundaryBlockEntry K D w 162 x u₀ u₁ c r ∈
      stairAugmentedBox K (min r 162) := by
  classical
  unfold stairBoundaryBlockEntry blockEntry
  apply Submodule.sum_mem
  intro f hf
  split_ifs with hfr
  · apply (stairAugmentedBox K (min r 162)).smul_mem
    have hq := c.1.1.isLt
    have hj := c.1.2.isLt
    have ht := c.2.1.isLt
    have hfi := f.isLt
    change f.val < c.1.1.val + 1 + c.2.1.val + 1 at hfi
    have hfc : f.val ≤ c.1.1.val + 1 + c.2.1.val := by omega
    have hiL : c.1.1.val + 1 + c.2.1.val ≤ 162 := by omega
    have hmul := coefficientBox_mul K
      (seedAffine_pow_mem K u₀ u₁
        (c.1.1.val + 1 + c.2.1.val - f.val))
      (localMonomial_mem K f.val c.1.2.val (162 - c.2.1.val))
    have hshape : c.1.1.val + 1 + c.2.1.val - f.val +
        (f.val + (162 - c.2.1.val)) = 162 + (c.1.1.val + 1) := by
      have h1 := Nat.sub_add_cancel hfc
      have h2 := Nat.sub_add_cancel (show c.2.1.val ≤ 162 by omega)
      omega
    simp only [Nat.zero_add] at hmul
    rw [hshape] at hmul
    have hmem := coefficientBox_stair_mem K
      (L := 162) (q := c.1.1.val + 1) (j := c.1.2.val)
      (show f.val ≤ min r 162 by omega)
      (show 1 ≤ c.1.1.val + 1 by omega)
      (show c.1.1.val + 1 + c.1.2.val ≤ 3 by
        have := c.1.2.isLt
        omega) hmul
    apply MvPolynomial.restrictSupport_mono (R := K) ?_ hmem
    intro d hd
    rcases hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr hd
  · exact (stairAugmentedBox K (min r 162)).zero_mem

def boundedStairBoundaryBlockEntry (D w : ℕ) (x u₀ u₁ : K)
    (c : StairBoundaryCoefficientIndex D w 162) (r : ℕ) :
    stairAugmentedBox K (min r 162) :=
  ⟨stairBoundaryBlockEntry K D w 162 x u₀ u₁ c r,
    stairBoundaryBlockEntry_mem K D w x u₀ u₁ c r⟩

def boundedStairBlockEntry (D w : ℕ) (x u₀ u₁ : K)
    (c : StairCoefficientIndex D w 162 5) (r : ℕ) :
    stairAugmentedBox K (min r 162) := by
  rcases c with c | c
  · exact ⟨blockEntry K D w 162 5 x u₀ u₁ c r, by
      apply MvPolynomial.restrictSupport_mono (R := K)
        (show boxExponents (min r 162) 162 5 ⊆
            stairAugmentedExponents (min r 162) by
          intro d hd
          exact Or.inl hd)
      exact blockEntry_mem K D w 162 5 x u₀ u₁ c r⟩
  · exact boundedStairBoundaryBlockEntry K D w x u₀ u₁ c r

def stairExtractBlock (D w : ℕ) (x u₀ u₁ : K) (r : ℕ) :
    (StairCoefficientIndex D w 162 5 → K) →ₗ[K]
      stairAugmentedBox K (min r 162) where
  toFun θ := ∑ c, θ c • boundedStairBlockEntry K D w x u₀ u₁ c r
  map_add' θ η := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a θ := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

abbrev StairLocalTarget (m : ℕ) :=
  (r : Fin m) → LinearMap.range
    (stairBlockJet K (min r.val 162) (m - r.val))

theorem stairLocalTarget_finrank_le (m : ℕ) :
    Module.finrank K (StairLocalTarget K m) ≤ stairLocalRankBound m := by
  change Module.finrank K ((r : Fin m) → LinearMap.range
    (stairBlockJet K (min r.val 162) (m - r.val))) ≤ _
  rw [Module.finrank_pi_fintype]
  unfold stairLocalRankBound localRankBound stairBoundaryLocalRankBound
  rw [← Finset.sum_add_distrib, Finset.sum_range]
  apply Finset.sum_le_sum
  intro r hr
  have hh := stairBlockJet_rank_le K
    (M := min r.val 162) (h := m - r.val) (min_le_right r.val 162)
  rw [ContactInterpolation.full_contactRankBound_eq,
    full_stairBoundaryRankBound_eq] at hh
  exact hh

abbrev StairGlobalTarget (I : Type*) (m : ℕ) := I → StairLocalTarget K m

theorem stairGlobalTarget_finrank_le {I : Type*} [Fintype I] (m : ℕ) :
    Module.finrank K (StairGlobalTarget K I m) ≤
      Fintype.card I * stairLocalRankBound m := by
  change Module.finrank K (I → StairLocalTarget K m) ≤ _
  rw [Module.finrank_pi_fintype]
  calc
    (∑ _i : I, Module.finrank K (StairLocalTarget K m)) ≤
        ∑ _i : I, stairLocalRankBound m := by
      apply Finset.sum_le_sum
      intro i hi
      exact stairLocalTarget_finrank_le K m
    _ = Fintype.card I * stairLocalRankBound m := by simp

def stairConstraintMap {I : Type*} [Fintype I]
    (D w m : ℕ) (nodes u₀ u₁ : I → K) :
    (StairCoefficientIndex D w 162 5 → K) →ₗ[K] StairGlobalTarget K I m :=
  LinearMap.pi fun i => LinearMap.pi fun r =>
    (stairBlockJet K (min r.val 162) (m - r.val)).rangeRestrict.comp
      (stairExtractBlock K D w (nodes i) (u₀ i) (u₁ i) r.val)

theorem exists_nonzero_stair_kernel_array {I : Type*} [Fintype I]
    (D w m : ℕ) (nodes u₀ u₁ : I → K)
    (hgate : Fintype.card I * stairLocalRankBound m <
      stairCoefficientCount D w 162 5) :
    ∃ θ : StairCoefficientIndex D w 162 5 → K,
      θ ≠ 0 ∧ stairConstraintMap K D w m nodes u₀ u₁ θ = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective (stairConstraintMap K D w m nodes u₀ u₁) := by
    intro θ η heq
    by_contra hne
    apply hnone
    refine ⟨θ - η, sub_ne_zero.mpr hne, ?_⟩
    rw [map_sub, heq, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, stair_index_card] at hdim
  have hupper := stairGlobalTarget_finrank_le K (I := I) m
  exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)

theorem stairTranslationColumn_coeff (D w : ℕ) (x u₀ u₁ : K)
    (c : StairCoefficientIndex D w 162 5) (a : K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁
      (MvPolynomial.monomial (stairColumnExponent c) a)).coeff r =
      a • ((boundedStairBlockEntry K D w x u₀ u₁ c r) : Poly K) := by
  rcases c with c | c
  · simpa [stairColumnExponent, boundedStairBlockEntry] using
      translation_column_coeff K D w 162 5 x u₀ u₁ c a r
  · have hh := translation_column_coeff K D w 165 5 x u₀ u₁
      (stairBoundaryAsColumn c) a r
    rw [stairBoundaryAsColumn_exponent] at hh
    simpa [stairColumnExponent, boundedStairBlockEntry,
      boundedStairBoundaryBlockEntry, stairBoundaryBlockEntry] using hh

theorem translation_stairReconstruct_coeff (D w : ℕ) (x u₀ u₁ : K)
    (θ : StairCoefficientIndex D w 162 5 → K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁ (stairReconstruct K D w 162 5 θ)).coeff r =
      ((stairExtractBlock K D w x u₀ u₁ r θ) : Poly K) := by
  rw [stairReconstruct, map_sum, Polynomial.finsetSum_coeff]
  simp only [stairTranslationColumn_coeff]
  change (∑ c : StairCoefficientIndex D w 162 5,
    θ c • ((boundedStairBlockEntry K D w x u₀ u₁ c r) : Poly K)) =
      (((∑ c : StairCoefficientIndex D w 162 5,
        θ c • boundedStairBlockEntry K D w x u₀ u₁ c r) :
          stairAugmentedBox K (min r 162)) : Poly K)
  simp

theorem exists_nonzero_stair_block_equations {I : Type*} [Fintype I]
    (D w m : ℕ) (nodes u₀ u₁ : I → K)
    (hgate : Fintype.card I * stairLocalRankBound m < stairCoefficientCount D w 162 5) :
    ∃ θ : StairCoefficientIndex D w 162 5 → K, θ ≠ 0 ∧
      ∀ (i : I) (r : Fin m), contactJet K (m - r.val)
        ((stairExtractBlock K D w (nodes i) (u₀ i) (u₁ i) r.val θ) : Poly K) = 0 := by
  obtain ⟨θ, hθ, hzero⟩ := exists_nonzero_stair_kernel_array K D w m nodes u₀ u₁ hgate
  refine ⟨θ, hθ, ?_⟩
  intro i r
  have hh := congrArg (fun t : StairGlobalTarget K I m => ((t i r) : Poly K)) hzero
  change contactJet K (m - r.val)
    ((stairExtractBlock K D w (nodes i) (u₀ i) (u₁ i) r.val θ) : Poly K) = 0 at hh
  exact hh

theorem all_stair_blocks_divisible_of_equations
    (D w m : ℕ) (x u₀ u₁ : K) (θ : StairCoefficientIndex D w 162 5 → K)
    (h : ∀ r : Fin m, contactJet K (m - r.val)
      ((stairExtractBlock K D w x u₀ u₁ r.val θ) : Poly K) = 0) :
    ∀ r : ℕ, slopeDifference K ^ (m - r) ∣
      ((stairExtractBlock K D w x u₀ u₁ r θ) : Poly K) := by
  intro r
  by_cases hr : r < m
  · exact (contactJet_eq_zero_iff K (m - r) _).mp (h ⟨r, hr⟩)
  · have hm : m - r = 0 := by omega
    simp only [hm, pow_zero, one_dvd]

abbrev FrozenStairCoefficientIndex := StairCoefficientIndex 3325194 131071 162 5

theorem exists_frozen_stair_nonzero_array
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ θ : FrozenStairCoefficientIndex → IRSProfile.Field, θ ≠ 0 ∧
      ∀ (i : IRSProfile.Index) (r : Fin 18),
        contactJet IRSProfile.Field (18 - r.val)
          ((stairExtractBlock IRSProfile.Field 3325194 131071
            (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ) : Poly IRSProfile.Field) = 0 := by
  apply exists_nonzero_stair_block_equations IRSProfile.Field
    3325194 131071 18 (fun i : IRSProfile.Index => IRSProfile.domain i) u₀ u₁
  rw [show Fintype.card IRSProfile.Index = 262144 by norm_num [IRSProfile.Index]]
  exact frozen_stair_interpolation_gate

theorem exists_frozen_stair_translated_contact_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ stairGlobalCoefficientBox IRSProfile.Field 3325194 131071 162 ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (18 - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u₀ i) (u₁ i) Q).coeff r := by
  obtain ⟨θ, hθ, heq⟩ := exists_frozen_stair_nonzero_array u₀ u₁
  refine ⟨stairReconstruct IRSProfile.Field 3325194 131071 162 5 θ,
    ?_, stairReconstruct_mem_globalBox IRSProfile.Field 3325194 131071 162 θ, ?_⟩
  · intro hzero
    apply hθ
    apply stairReconstruct_injective IRSProfile.Field 3325194 131071 162 5
    simpa only [stairReconstruct_zero] using hzero
  · intro i r
    rw [translation_stairReconstruct_coeff]
    exact all_stair_blocks_divisible_of_equations IRSProfile.Field
      3325194 131071 18 (IRSProfile.domain i) (u₀ i) (u₁ i) θ (heq i) r

theorem stair_specialization_natDegree_lt
    (D w L : ℕ) (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (γ : K)
    (hD : 0 < D) (hcaps : Q ∈ stairGlobalCoefficientBox K D w L)
    (hP : P.natDegree ≤ w) :
    (specialization K P γ Q).natDegree < D := by
  classical
  have hsupport := stairGlobal_support_caps K D w L Q hcaps
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

theorem exists_frozen_stair_universal_vanishing_interpolant
    (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧ Q ∈ stairGlobalCoefficientBox IRSProfile.Field 3325194 131071 162 ∧
      ∀ (γ : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ 131071 → 184733 ≤ support.card →
        (∀ i ∈ support, P.eval (IRSProfile.domain i) = u₀ i + γ * u₁ i) →
        specialization IRSProfile.Field P γ Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hcontact⟩ :=
    exists_frozen_stair_translated_contact_interpolant u₀ u₁
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro γ P support hP hcard hvalues
  apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P γ
    IRSProfile.domain u₀ u₁ support 18
  · intro i hi r
    exact hcontact i r
  · exact hvalues
  · have hdegree := stair_specialization_natDegree_lt IRSProfile.Field
      3325194 131071 162 Q P γ (by decide) hcaps hP
    have hbound : 3325194 ≤ 18 * support.card := by omega
    exact hdegree.trans_le hbound

theorem frozen_stair_support_caps
    (Q : MvPolynomial (Fin 4) IRSProfile.Field)
    (hQ : Q ∈ stairGlobalCoefficientBox IRSProfile.Field 3325194 131071 162) :
    ∀ d ∈ Q.support,
      d 1 + d 3 ≤ 165 ∧ d 2 ≤ 5 ∧
      d 0 + 131071 * d 1 + 131070 * d 2 < 3325194 ∧ d 3 ≤ 162 := by
  simpa using stairGlobal_support_caps IRSProfile.Field 3325194 131071 162 Q hQ

end

end ProximityPrize.SubmissionLower.ContactStaircaseInterpolation

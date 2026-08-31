import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactFiniteFieldKernelSectionAvoidance6660Research
import ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research
import ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research
import ProximityPrize.SubmissionLower.ContactSecondContactLegacyBridge6660Research

 
















namespace ProximityPrize.SubmissionLower
namespace ContactFullKernelCoprimePair6660Research

open scoped Classical BigOperators
open UniqueFactorizationMonoid
open ProximityPrize.Benchmark
open ContactFactorCaps
open ContactFiniteFieldKernelSectionAvoidance6660Research
open ContactFullKernelHeightTwoRouting6660Research
open ContactSecondContactSFreeInterpolation6660Research
open ContactSecondContactConstraintMap6660Research
open ContactSecondContactKernel6660Research
open ContactSecondContactKernelSections6660Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000

variable {K : Type*} [Field K]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 
def reconstructLinear (D w C rCap : Nat) :
    (CoefficientIndex D w C rCap -> K) →ₗ[K] MvPolynomial (Fin 4) K where
  toFun := reconstruct K D w C rCap
  map_add' theta eta := by
    classical
    simp [reconstruct, ← Finset.sum_add_distrib]
  map_smul' a theta := by
    classical
    simp only [reconstruct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    rw [MvPolynomial.smul_monomial]
    rfl

abbrev KernelSpace {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K) :=
  LinearMap.ker (globalConstraint K D w C rCap m nodes u0 u1)

def sectionPolynomial {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K)
    (v : KernelSpace D w C rCap m nodes u0 u1) :
    MvPolynomial (Fin 4) K :=
  reconstruct K D w C rCap v.1

 
def divisorSubmodule {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K)
    (G : MvPolynomial (Fin 4) K) :
    Submodule K (KernelSpace D w C rCap m nodes u0 u1) :=
  ((Ideal.span ({G} : Set (MvPolynomial (Fin 4) K))).restrictScalars K).comap
    ((reconstructLinear (K := K) D w C rCap).comp
      (LinearMap.ker (globalConstraint K D w C rCap m nodes u0 u1)).subtype)

theorem mem_divisorSubmodule_iff {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K)
    (G : MvPolynomial (Fin 4) K)
    (v : KernelSpace D w C rCap m nodes u0 u1) :
    v ∈ divisorSubmodule D w C rCap m nodes u0 u1 G <->
      G ∣ sectionPolynomial D w C rCap m nodes u0 u1 v := by
  simp only [divisorSubmodule, Submodule.mem_comap,
    LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  change G ∣ reconstruct K D w C rCap v.1 <->
    G ∣ reconstruct K D w C rCap v.1
  rfl

 

def NoUniversalNonunitDivisor {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K) : Prop :=
  ∀ G : MvPolynomial (Fin 4) K,
    (∀ v : KernelSpace D w C rCap m nodes u0 u1,
      G ∣ sectionPolynomial D w C rCap m nodes u0 u1 v) -> IsUnit G

 

theorem not_noUniversalNonunitDivisor_iff {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K) :
    ¬ NoUniversalNonunitDivisor D w C rCap m nodes u0 u1 <->
      ∃ G : MvPolynomial (Fin 4) K,
        (∀ v : KernelSpace D w C rCap m nodes u0 u1,
          G ∣ sectionPolynomial D w C rCap m nodes u0 u1 v) ∧ ¬ IsUnit G := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro G hdiv
    by_contra hunit
    apply hnone
    exact ⟨G, hdiv, hunit⟩
  · rintro ⟨G, hdiv, hunit⟩ hfull
    exact hunit (hfull G hdiv)

theorem divisorSubmodule_ne_top {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K)
    (hfull : NoUniversalNonunitDivisor D w C rCap m nodes u0 u1)
    (G : MvPolynomial (Fin 4) K) (hG : Irreducible G) :
    divisorSubmodule D w C rCap m nodes u0 u1 G ≠ ⊤ := by
  intro htop
  apply hG.not_isUnit
  apply hfull G
  intro v
  rw [← mem_divisorSubmodule_iff D w C rCap m nodes u0 u1 G v, htop]
  trivial

def allFactors (F : MvPolynomial (Fin 4) K) :
    Finset (MvPolynomial (Fin 4) K) :=
  (normalizedFactors F).toFinset

theorem allFactors_product_dvd
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∏ G ∈ allFactors F, G) ∣ F := by
  classical
  exact (normalizedFactors F).toFinset_prod_dvd_prod.trans
    (prod_normalizedFactors hF).dvd

private theorem eq_C_of_all_degreeOf_zero
    (F : MvPolynomial (Fin 4) K) (h : ∀ i, F.degreeOf i = 0) :
    F = MvPolynomial.C (F.coeff 0) := by
  classical
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro d hd
  have hd0 : d = 0 := by
    ext i
    have hi := MvPolynomial.monomial_le_degreeOf i hd
    rw [h i] at hi
    exact Nat.eq_zero_of_le_zero hi
  simp [hd0]

theorem normalizedFactor_coordinate_sum_pos
    (F G : MvPolynomial (Fin 4) K) (hG : G ∈ allFactors F) :
    0 < ∑ i : Fin 4, G.degreeOf i := by
  classical
  have hmem : G ∈ normalizedFactors F := Multiset.mem_toFinset.mp hG
  have hirr : Irreducible G := irreducible_of_normalized_factor G hmem
  by_contra hnot
  have hzero : ∀ i : Fin 4, G.degreeOf i = 0 := by
    intro i
    apply Nat.eq_zero_of_le_zero
    have hle : G.degreeOf i ≤ ∑ j : Fin 4, G.degreeOf j :=
      Finset.single_le_sum
        (fun j _ => Nat.zero_le (G.degreeOf j)) (Finset.mem_univ i)
    omega
  have hconst := eq_C_of_all_degreeOf_zero G hzero
  have hcoeff : G.coeff 0 ≠ 0 := by
    intro hz
    apply (ne_zero_of_mem_normalizedFactors hmem)
    rw [hconst, hz, map_zero]
  apply hirr.not_isUnit
  rw [hconst]
  exact hcoeff.isUnit.map MvPolynomial.C

 

theorem allFactors_card_le_coordinate_degree_sum
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (allFactors F).card ≤ ∑ i : Fin 4, F.degreeOf i := by
  classical
  have hdiv := allFactors_product_dvd F hF
  calc
    (allFactors F).card = ∑ _G ∈ allFactors F, (1 : Nat) := by simp
    _ ≤ ∑ G ∈ allFactors F, ∑ i : Fin 4, G.degreeOf i := by
      apply Finset.sum_le_sum
      intro G hG
      exact normalizedFactor_coordinate_sum_pos F G hG
    _ = ∑ i : Fin 4, ∑ G ∈ allFactors F, G.degreeOf i := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin 4, F.degreeOf i := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_degreeOf_le_of_prod_dvd (allFactors F) id F hF hdiv i

 

theorem exists_coprime_second_section {I : Type*} [Fintype I]
    (D w C rCap m : Nat) (nodes u0 u1 : I -> K)
    (v0 : KernelSpace D w C rCap m nodes u0 u1) (hv0 : v0 ≠ 0)
    (hfull : NoUniversalNonunitDivisor D w C rCap m nodes u0 u1)
    (hcard : (allFactors
      (sectionPolynomial D w C rCap m nodes u0 u1 v0)).card < ENat.card K) :
    ∃ v1 : KernelSpace D w C rCap m nodes u0 u1,
      NoCommonNonunitDivisor
        (sectionPolynomial D w C rCap m nodes u0 u1 v0)
        (sectionPolynomial D w C rCap m nodes u0 u1 v1) := by
  classical
  let F0 := sectionPolynomial D w C rCap m nodes u0 u1 v0
  have hF0 : F0 ≠ 0 := by
    apply reconstruct_ne_zero K D w C rCap v0.1
    intro hv
    apply hv0
    exact Subtype.ext hv
  let Factor := ↥(allFactors F0)
  let bad : Factor -> Submodule K (KernelSpace D w C rCap m nodes u0 u1) :=
    fun q => divisorSubmodule D w C rCap m nodes u0 u1 q.1
  have hproper : ∀ q : Factor, bad q ≠ ⊤ := by
    intro q
    apply divisorSubmodule_ne_top D w C rCap m nodes u0 u1 hfull
    exact irreducible_of_normalized_factor q.1
      (Multiset.mem_toFinset.mp q.2)
  have hfactorCard : Fintype.card Factor < ENat.card K := by
    simpa [Factor, F0] using hcard
  obtain ⟨v1, hv1⟩ :=
    exists_section_avoiding_bounded_proper_submodules bad hproper hfactorCard
  refine ⟨v1, ?_⟩
  intro G hGF0 hGF1
  by_contra hGunit
  have hG0 : G ≠ 0 := by
    intro hzero
    subst G
    simp only [zero_dvd_iff] at hGF0
    exact hF0 hGF0
  obtain ⟨p, hpG⟩ := exists_mem_normalizedFactors hG0 hGunit
  have hpirr : Irreducible p := irreducible_of_normalized_factor p hpG
  have hpF0 : p ∣ F0 := (dvd_of_mem_normalizedFactors hpG).trans hGF0
  obtain ⟨q, hqF0, hpq⟩ :=
    exists_mem_normalizedFactors_of_dvd hF0 hpirr hpF0
  have hqF1 : q ∣ sectionPolynomial D w C rCap m nodes u0 u1 v1 := by
    apply hpq.dvd_iff_dvd_left.mp
    exact (dvd_of_mem_normalizedFactors hpG).trans hGF1
  let qFactor : Factor := ⟨q, Multiset.mem_toFinset.mpr hqF0⟩
  apply hv1 qFactor
  dsimp [bad]
  change v1 ∈ divisorSubmodule D w C rCap m nodes u0 u1 qFactor.1
  simpa [qFactor] using
    ((mem_divisorSubmodule_iff D w C rCap m nodes u0 u1 q v1).mpr hqF1)

 

theorem customBox_degreeOf_X_le
    (Q : MvPolynomial (Fin 4) K) (D w C rCap : Nat)
    (hbox : Q ∈ globalCoefficientBox K D w C rCap) :
    Q.degreeOf (0 : Fin 4) ≤ D - 1 := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hw := (hbox hd).2.2
  omega

theorem customBox_degreeOf_Y_le
    (Q : MvPolynomial (Fin 4) K) (D w C rCap : Nat) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w C rCap) :
    Q.degreeOf (1 : Fin 4) ≤ (D - 1) / w := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  apply (Nat.le_div_iff_mul_le hw).mpr
  have hc := (hbox hd).2.2
  have hm : d 1 * w = w * d 1 := Nat.mul_comm _ _
  omega

theorem customBox_degreeOf_R_le
    (Q : MvPolynomial (Fin 4) K) (D w C rCap : Nat)
    (hbox : Q ∈ globalCoefficientBox K D w C rCap) :
    Q.degreeOf (2 : Fin 4) ≤ rCap := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  exact (hbox hd).2.1

theorem customBox_degreeOf_Z_le
    (Q : MvPolynomial (Fin 4) K) (D w C rCap : Nat)
    (hbox : Q ∈ globalCoefficientBox K D w C rCap) :
    Q.degreeOf (3 : Fin 4) ≤ C := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs := (hbox hd).1
  omega

abbrev RowKernel (u0 u1 : IRSProfile.Index -> IRSProfile.Field) :=
  KernelSpace 5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1

abbrev RowNoUniversalNonunitDivisor
    (u0 u1 : IRSProfile.Index -> IRSProfile.Field) :=
  NoUniversalNonunitDivisor 5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1

 

theorem row6660_allFactors_card_le
    (u0 u1 : IRSProfile.Index -> IRSProfile.Field) (v : RowKernel u0 u1)
    (hv : v ≠ 0) :
    (allFactors (sectionPolynomial 5848704 131071 717 9 32
      (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v)).card ≤
      5849473 := by
  let F := sectionPolynomial 5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v
  change (allFactors F).card ≤ 5849473
  have hF : F ≠ 0 := by
    apply reconstruct_ne_zero IRSProfile.Field 5848704 131071 717 9 v.1
    intro hz
    apply hv
    exact Subtype.ext hz
  have hcustom : F ∈ globalCoefficientBox IRSProfile.Field
      5848704 131071 717 9 :=
    reconstruct_mem_globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 v.1
  have hx := customBox_degreeOf_X_le F 5848704 131071 717 9 hcustom
  have hy := customBox_degreeOf_Y_le F 5848704 131071 717 9 (by norm_num) hcustom
  have hr := customBox_degreeOf_R_le F 5848704 131071 717 9 hcustom
  have hz := customBox_degreeOf_Z_le F 5848704 131071 717 9 hcustom
  norm_num at hx hy hr hz
  have hall := allFactors_card_le_coordinate_degree_sum F hF
  simp only [Fin.sum_univ_four] at hall
  omega

theorem row6660_factor_count_lt_field
    (u0 u1 : IRSProfile.Index -> IRSProfile.Field) (v : RowKernel u0 u1)
    (hv : v ≠ 0) :
    (allFactors (sectionPolynomial 5848704 131071 717 9 32
      (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v)).card <
      ENat.card IRSProfile.Field := by
  rw [ENat.card_eq_coe_fintype_card]
  have hfield : Fintype.card IRSProfile.Field = (2130706433 : Nat) ^ 6 :=
    AlignmentProtocol6401Conditional.field_cardinality
  rw [hfield]
  exact_mod_cast (row6660_allFactors_card_le u0 u1 v hv |>.trans_lt (by norm_num))

 

theorem exists_row6660_coprime_kernel_sections
    (u0 u1 : IRSProfile.Index -> IRSProfile.Field)
    (hfull : RowNoUniversalNonunitDivisor u0 u1) :
    ∃ v0 v1 : RowKernel u0 u1,
      v0 ≠ 0 ∧
      NoCommonNonunitDivisor
        (sectionPolynomial 5848704 131071 717 9 32
          (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v0)
        (sectionPolynomial 5848704 131071 717 9 32
          (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v1) := by
  obtain ⟨rows, hrows⟩ := exists_row6660_three_independent_kernel_rows u0 u1
  let v0 := rows 0
  have hv0 : v0 ≠ 0 := hrows.ne_zero 0
  obtain ⟨v1, hcoprime⟩ := exists_coprime_second_section
    5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v0 hv0 hfull
    (row6660_factor_count_lt_field u0 u1 v0 hv0)
  exact ⟨v0, v1, hv0, hcoprime⟩

 


theorem exists_row6660_coprime_interpolants
    (u0 u1 : IRSProfile.Index -> IRSProfile.Field)
    (hfull : RowNoUniversalNonunitDivisor u0 u1) :
    ∃ F0 F1 : MvPolynomial (Fin 4) IRSProfile.Field,
      F0 ≠ 0 ∧
      F0 ∈ globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 ∧
      F1 ∈ globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 ∧
      F0 ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        5848704 131071 717 9 ∧
      F1 ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        5848704 131071 717 9 ∧
      NoCommonNonunitDivisor F0 F1 ∧
      (∀ i : IRSProfile.Index,
        HasSecondContactEquations IRSProfile.Field F0
          (IRSProfile.domain i) (u0 i) (u1 i) 32) ∧
      ∀ i : IRSProfile.Index,
        HasSecondContactEquations IRSProfile.Field F1
          (IRSProfile.domain i) (u0 i) (u1 i) 32 := by
  obtain ⟨v0, v1, hv0, hcoprime⟩ :=
    exists_row6660_coprime_kernel_sections u0 u1 hfull
  let F0 := sectionPolynomial 5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v0
  let F1 := sectionPolynomial 5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v1
  have hF0 : F0 ≠ 0 := by
    dsimp [F0, sectionPolynomial]
    apply reconstruct_ne_zero IRSProfile.Field 5848704 131071 717 9 v0.1
    intro hz
    apply hv0
    exact Subtype.ext hz
  have hF0custom : F0 ∈ globalCoefficientBox IRSProfile.Field
      5848704 131071 717 9 := by
    dsimp [F0, sectionPolynomial]
    exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
      5848704 131071 717 9 v0.1
  have hF1custom : F1 ∈ globalCoefficientBox IRSProfile.Field
      5848704 131071 717 9 := by
    dsimp [F1, sectionPolynomial]
    exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
      5848704 131071 717 9 v1.1
  have hF0legacy :=
    ContactSecondContactLegacyBridge6660Research.mem_legacy_globalCoefficientBox
      IRSProfile.Field 5848704 131071 717 9 F0 hF0custom
  have hF1legacy :=
    ContactSecondContactLegacyBridge6660Research.mem_legacy_globalCoefficientBox
      IRSProfile.Field 5848704 131071 717 9 F1 hF1custom
  have heq0 : ∀ i : IRSProfile.Index,
      HasSecondContactEquations IRSProfile.Field F0
        (IRSProfile.domain i) (u0 i) (u1 i) 32 := by
    dsimp [F0, sectionPolynomial]
    exact equations_of_globalConstraint_zero IRSProfile.Field
      5848704 131071 717 9 32
      (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v0.1 v0.2
  have heq1 : ∀ i : IRSProfile.Index,
      HasSecondContactEquations IRSProfile.Field F1
        (IRSProfile.domain i) (u0 i) (u1 i) 32 := by
    dsimp [F1, sectionPolynomial]
    exact equations_of_globalConstraint_zero IRSProfile.Field
      5848704 131071 717 9 32
      (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 v1.1 v1.2
  refine ⟨F0, F1, hF0, hF0custom, hF1custom, hF0legacy, hF1legacy, ?_, heq0, heq1⟩
  simpa [F0, F1] using hcoprime

end

end ContactFullKernelCoprimePair6660Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.allFactors_card_le_coordinate_degree_sum
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.not_noUniversalNonunitDivisor_iff
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.exists_coprime_second_section
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.row6660_allFactors_card_le
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.row6660_factor_count_lt_field
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.exists_row6660_coprime_kernel_sections
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research.exists_row6660_coprime_interpolants

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research
import ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research
import ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research

 













namespace ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research

open scoped Classical
open UniqueFactorizationMonoid
open ContactFiniteFieldKernelSectionAvoidance6660Research
open ContactFullKernelCoprimePair6660Research
open ContactFullKernelHeightTwoRouting6660Research
open ContactFixedFactorQuotientLinear6750Research
open ContactInjectiveImageKernelIntersection6750Research
open ContactTranslation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v

section KernelDimension

universe w

 
theorem two_le_kernel_finrank_of_target_add_two_le_source
    {K : Type u} {V : Type v} {T : Type w}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (constraint : V →ₗ[K] T)
    (hslack : Module.finrank K T + 2 ≤ Module.finrank K V) :
    2 ≤ Module.finrank K (LinearMap.ker constraint) := by
  have hrange : Module.finrank K (LinearMap.range constraint) ≤
      Module.finrank K T := (LinearMap.range constraint).finrank_le
  have hnull := constraint.finrank_range_add_finrank_ker
  omega

 
theorem two_le_fixedProductConstraintKernel_finrank
    {K : Type u} [Field K]
    {T : Type w} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (G : MvPolynomial (Fin 4) K)
    (Low : Submodule K (MvPolynomial (Fin 4) K))
    [FiniteDimensional K Low]
    (constraint : MvPolynomial (Fin 4) K →ₗ[K] T)
    (hslack : Module.finrank K T + 2 ≤ Module.finrank K Low) :
    2 ≤ Module.finrank K (LinearMap.ker
      (constraint.comp (fixedLeftMultiplicationFromSubmodule G Low))) :=
  two_le_kernel_finrank_of_target_add_two_le_source
    (constraint.comp (fixedLeftMultiplicationFromSubmodule G Low)) hslack

end KernelDimension

section AbstractSelection

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 

def linearDivisorSubmodule
    (f : V →ₗ[K] MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 4) K) : Submodule K V :=
  ((Ideal.span ({G} : Set (MvPolynomial (Fin 4) K))).restrictScalars K).comap f

theorem mem_linearDivisorSubmodule_iff
    (f : V →ₗ[K] MvPolynomial (Fin 4) K)
    (G : MvPolynomial (Fin 4) K) (v : V) :
    v ∈ linearDivisorSubmodule f G ↔ G ∣ f v := by
  simp only [linearDivisorSubmodule, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]

 


def NoUniversalNonunitDivisorForLinearFamily
    (f : V →ₗ[K] MvPolynomial (Fin 4) K) : Prop :=
  ∀ G : MvPolynomial (Fin 4) K, (∀ v : V, G ∣ f v) → IsUnit G

 


theorem noUniversalNonunitDivisor_fixedFactorQuotient_of_maximalCore
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (C : MvPolynomial (Fin 4) K) (hC : C ≠ 0)
    (hdiv : ∀ q : W, C ∣ (q : MvPolynomial (Fin 4) K))
    (hmax : ∀ D : MvPolynomial (Fin 4) K,
      (∀ q : W, D ∣ (q : MvPolynomial (Fin 4) K)) → D ∣ C) :
    NoUniversalNonunitDivisorForLinearFamily
      (fixedFactorQuotientLinearMap C hC W hdiv) := by
  intro D hD
  have hCD : C * D ∣ C := by
    apply hmax (C * D)
    intro q
    rw [← mul_fixedFactorQuotientLinearMap C hC W hdiv q]
    exact mul_dvd_mul_left C (hD q)
  apply isUnit_iff_dvd_one.mpr
  apply (mul_dvd_mul_iff_left hC).mp
  simpa using hCD

theorem linearDivisorSubmodule_ne_top
    (f : V →ₗ[K] MvPolynomial (Fin 4) K)
    (hfull : NoUniversalNonunitDivisorForLinearFamily f)
    (G : MvPolynomial (Fin 4) K) (hG : Irreducible G) :
    linearDivisorSubmodule f G ≠ ⊤ := by
  intro htop
  apply hG.not_isUnit
  apply hfull G
  intro v
  rw [← mem_linearDivisorSubmodule_iff f G v, htop]
  trivial

 



theorem exists_independent_coprime_image_from_first
    (f : V →ₗ[K] MvPolynomial (Fin 4) K) (hf : Function.Injective f)
    (hdim : 2 ≤ Module.finrank K V)
    (hfull : NoUniversalNonunitDivisorForLinearFamily f)
    (v0 : V) (hv0 : v0 ≠ 0)
    (hcard : (allFactors (f v0)).card + 1 < ENat.card K) :
    ∃ v1 : V,
      LinearIndependent K ![v0, v1] ∧
        NoCommonNonunitDivisor (f v0) (f v1) := by
  classical
  have hF0 : f v0 ≠ 0 := by
    intro hzero
    apply hv0
    apply hf
    simpa only [map_zero] using hzero
  let Factor := ↥(allFactors (f v0))
  let bad : Option Factor → Submodule K V
    | none => K ∙ v0
    | some q => linearDivisorSubmodule f q.1
  have hproper : ∀ q : Option Factor, bad q ≠ ⊤ := by
    intro q
    cases q with
    | none =>
        intro htop
        have hfin := congrArg
          (fun S : Submodule K V => Module.finrank K S) htop
        simp only [bad, finrank_span_singleton hv0, finrank_top] at hfin
        omega
    | some q =>
        exact linearDivisorSubmodule_ne_top f hfull q.1
          (irreducible_of_normalized_factor q.1
            (Multiset.mem_toFinset.mp q.2))
  have hbadCard : Fintype.card (Option Factor) < ENat.card K := by
    simpa [Factor] using hcard
  obtain ⟨v1, havoid⟩ :=
    exists_section_avoiding_bounded_proper_submodules bad hproper hbadCard
  have hv1notspan : v1 ∉ K ∙ v0 := by
    simpa [bad] using havoid none
  have hindependent : LinearIndependent K ![v0, v1] :=
    (LinearIndependent.pair_iff' hv0).mpr (by
      intro a ha
      apply hv1notspan
      rw [← ha]
      exact Submodule.smul_mem _ a
        (Submodule.subset_span (Set.mem_singleton v0)))
  refine ⟨v1, hindependent, ?_⟩
  intro G hGF0 hGF1
  by_contra hGunit
  have hG0 : G ≠ 0 := by
    intro hzero
    subst G
    simp only [zero_dvd_iff] at hGF0
    exact hF0 hGF0
  obtain ⟨p, hpG⟩ := exists_mem_normalizedFactors hG0 hGunit
  have hpirr : Irreducible p := irreducible_of_normalized_factor p hpG
  have hpF0 : p ∣ f v0 := (dvd_of_mem_normalizedFactors hpG).trans hGF0
  obtain ⟨q, hqF0, hpq⟩ :=
    exists_mem_normalizedFactors_of_dvd hF0 hpirr hpF0
  have hqF1 : q ∣ f v1 := by
    apply hpq.dvd_iff_dvd_left.mp
    exact (dvd_of_mem_normalizedFactors hpG).trans hGF1
  let qFactor : Factor := ⟨q, Multiset.mem_toFinset.mpr hqF0⟩
  apply havoid (some qFactor)
  change v1 ∈ linearDivisorSubmodule f qFactor.1
  simpa [qFactor] using
    ((mem_linearDivisorSubmodule_iff f q v1).mpr hqF1)

 


theorem exists_two_independent_coprime_images
    (f : V →ₗ[K] MvPolynomial (Fin 4) K) (hf : Function.Injective f)
    (hdim : 2 ≤ Module.finrank K V)
    (hfull : NoUniversalNonunitDivisorForLinearFamily f)
    (hcard : ∀ v : V, v ≠ 0 →
      (allFactors (f v)).card + 1 < ENat.card K) :
    ∃ v0 v1 : V,
      LinearIndependent K ![v0, v1] ∧
        NoCommonNonunitDivisor (f v0) (f v1) := by
  obtain ⟨rows, hrows⟩ := exists_linearIndependent_of_le_finrank hdim
  let v0 := rows 0
  have hv0 : v0 ≠ 0 := hrows.ne_zero 0
  obtain ⟨v1, hindependent, hcoprime⟩ :=
    exists_independent_coprime_image_from_first f hf hdim hfull v0 hv0
      (hcard v0 hv0)
  exact ⟨v0, v1, hindependent, hcoprime⟩

 


theorem exists_two_independent_members_realizing_common_core
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (C : MvPolynomial (Fin 4) K) (hC : C ≠ 0)
    (hdiv : ∀ q : W, C ∣ (q : MvPolynomial (Fin 4) K))
    (hdim : 2 ≤ Module.finrank K W)
    (hfull : NoUniversalNonunitDivisorForLinearFamily
      (fixedFactorQuotientLinearMap C hC W hdiv))
    (hcard : ∀ q : W, q ≠ 0 →
      (allFactors (fixedFactorQuotientLinearMap C hC W hdiv q)).card + 1 <
        ENat.card K) :
    ∃ q0 q1 : W,
      LinearIndependent K ![q0, q1] ∧
      NoCommonNonunitDivisor
        (fixedFactorQuotientLinearMap C hC W hdiv q0)
        (fixedFactorQuotientLinearMap C hC W hdiv q1) ∧
      C * fixedFactorQuotientLinearMap C hC W hdiv q0 =
        (q0 : MvPolynomial (Fin 4) K) ∧
      C * fixedFactorQuotientLinearMap C hC W hdiv q1 =
        (q1 : MvPolynomial (Fin 4) K) := by
  obtain ⟨q0, q1, hindependent, hcoprime⟩ :=
    exists_two_independent_coprime_images
      (fixedFactorQuotientLinearMap C hC W hdiv)
      (fixedFactorQuotientLinearMap_injective C hC W hdiv)
      hdim hfull hcard
  exact ⟨q0, q1, hindependent, hcoprime,
    mul_fixedFactorQuotientLinearMap C hC W hdiv q0,
    mul_fixedFactorQuotientLinearMap C hC W hdiv q1⟩

 

theorem exists_two_independent_members_of_maximal_common_core
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (C : MvPolynomial (Fin 4) K) (hC : C ≠ 0)
    (hdiv : ∀ q : W, C ∣ (q : MvPolynomial (Fin 4) K))
    (hmax : ∀ D : MvPolynomial (Fin 4) K,
      (∀ q : W, D ∣ (q : MvPolynomial (Fin 4) K)) → D ∣ C)
    (hdim : 2 ≤ Module.finrank K W)
    (hcard : ∀ q : W, q ≠ 0 →
      (allFactors (fixedFactorQuotientLinearMap C hC W hdiv q)).card + 1 <
        ENat.card K) :
    ∃ q0 q1 : W,
      LinearIndependent K ![q0, q1] ∧
      NoCommonNonunitDivisor
        (fixedFactorQuotientLinearMap C hC W hdiv q0)
        (fixedFactorQuotientLinearMap C hC W hdiv q1) ∧
      C * fixedFactorQuotientLinearMap C hC W hdiv q0 =
        (q0 : MvPolynomial (Fin 4) K) ∧
      C * fixedFactorQuotientLinearMap C hC W hdiv q1 =
        (q1 : MvPolynomial (Fin 4) K) :=
  exists_two_independent_members_realizing_common_core W C hC hdiv hdim
    (noUniversalNonunitDivisor_fixedFactorQuotient_of_maximalCore
      W C hC hdiv hmax)
    hcard

end AbstractSelection

section ProductAndCounting

variable {K : Type u} [Field K]

 
def RealizesExactCommonCore
    (C A0 A1 Q0 Q1 : MvPolynomial (Fin 4) K) : Prop :=
  Q0 = C * A0 ∧ Q1 = C * A1 ∧ NoCommonNonunitDivisor A0 A1

 

theorem two_quotient_specializations_zero_of_product_derivatives
    (G Q0 Q1 : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hGregular : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0)
    (hprod0 : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q0)) = 0)
    (hprod1 : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q1)) = 0) :
    specialization K P gamma Q0 = 0 ∧
      specialization K P gamma Q1 = 0 := by
  constructor
  all_goals
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
      hGzero, zero_mul, add_zero] at hprod0 hprod1
  · exact (mul_eq_zero.mp hprod0).resolve_left hGregular
  · exact (mul_eq_zero.mp hprod1).resolve_left hGregular

 

theorem quotient_zero_or_first_and_second_factor_derivatives_zero
    (G Q : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hfirst : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hsecond : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (MvPolynomial.pderiv (2 : Fin 4) (G * Q))) = 0) :
    specialization K P gamma Q = 0 ∨
      (specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) G) = 0 ∧
        specialization K P gamma
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) G)) = 0) := by
  by_cases hQzero : specialization K P gamma Q = 0
  · exact Or.inl hQzero
  · right
    have hGfirst : specialization K P gamma
        (MvPolynomial.pderiv (2 : Fin 4) G) = 0 := by
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
        hGzero, zero_mul, add_zero] at hfirst
      exact (mul_eq_zero.mp hfirst).resolve_right hQzero
    refine ⟨hGfirst, ?_⟩
    rw [MvPolynomial.pderiv_mul, map_add,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul] at hsecond
    simp only [map_add, map_mul, hGzero, hGfirst, zero_mul, mul_zero,
      zero_add, add_zero] at hsecond
    exact (mul_eq_zero.mp hsecond).resolve_right hQzero

def commonCoreZeroSeeds
    (C : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter
    (fun gamma => specialization K (selected gamma) gamma C = 0)

def coprimeResidualPairZeroSeeds
    (A0 A1 : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter (fun gamma =>
    specialization K (selected gamma) gamma A0 = 0 ∧
      specialization K (selected gamma) gamma A1 = 0)

 

theorem subset_commonCore_union_coprimeResidualPair
    (C A0 A1 Q0 Q1 : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hexact : RealizesExactCommonCore C A0 A1 Q0 Q1)
    (hzero0 : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q0 = 0)
    (hzero1 : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q1 = 0) :
    Gamma ⊆ commonCoreZeroSeeds C selected Gamma ∪
      coprimeResidualPairZeroSeeds A0 A1 selected Gamma := by
  classical
  letI : DecidableEq K := Classical.decEq K
  intro gamma hgamma
  have hz0 := hzero0 gamma hgamma
  have hz1 := hzero1 gamma hgamma
  rw [hexact.1, map_mul] at hz0
  rw [hexact.2.1, map_mul] at hz1
  by_cases hCzero : specialization K (selected gamma) gamma C = 0
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_filter.mpr ⟨hgamma, hCzero⟩))
  · have hA0zero := (mul_eq_zero.mp hz0).resolve_left hCzero
    have hA1zero := (mul_eq_zero.mp hz1).resolve_left hCzero
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨hgamma, hA0zero, hA1zero⟩))

 

theorem card_le_commonCore_add_coprimeResidualPair
    (C A0 A1 Q0 Q1 : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hexact : RealizesExactCommonCore C A0 A1 Q0 Q1)
    (hzero0 : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q0 = 0)
    (hzero1 : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q1 = 0) :
    Gamma.card ≤ (commonCoreZeroSeeds C selected Gamma).card +
      (coprimeResidualPairZeroSeeds A0 A1 selected Gamma).card := by
  classical
  letI : DecidableEq K := Classical.decEq K
  exact (Finset.card_le_card
    (subset_commonCore_union_coprimeResidualPair C A0 A1 Q0 Q1
      selected Gamma hexact hzero0 hzero1)).trans
    (Finset.card_union_le _ _)

end ProductAndCounting

end


end ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research

#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.exists_independent_coprime_image_from_first
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.two_le_fixedProductConstraintKernel_finrank
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.exists_two_independent_coprime_images
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.exists_two_independent_members_realizing_common_core
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.noUniversalNonunitDivisor_fixedFactorQuotient_of_maximalCore
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.exists_two_independent_members_of_maximal_common_core
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.two_quotient_specializations_zero_of_product_derivatives
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.quotient_zero_or_first_and_second_factor_derivatives_zero
#print axioms ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research.card_le_commonCore_add_coprimeResidualPair

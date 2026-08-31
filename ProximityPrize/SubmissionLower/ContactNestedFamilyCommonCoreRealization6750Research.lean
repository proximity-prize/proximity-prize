import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFiniteFieldKernelSectionAvoidance6660Research
import ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research
import ProximityPrize.SubmissionLower.ContactTwoLowQuotientCommonCore6800Research

 

















namespace ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research

open scoped Classical
open UniqueFactorizationMonoid
open ContactFiniteFieldKernelSectionAvoidance6660Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFullKernelCoprimePair6660Research
open ContactFullKernelHeightTwoRouting6660Research
open ContactTwoLowQuotientCommonCore6800Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v w x

section FamilySum

variable {K : Type u} [Field K]
variable {A : Type x} [AddCommGroup A] [Module K A]
variable {ι : Type w}
variable (Source : ι → Type v)
variable [∀ i, AddCommGroup (Source i)] [∀ i, Module K (Source i)]

 


def mappedFamilySum (extend : ∀ i, Source i →ₗ[K] A) : Submodule K A :=
  ⨆ i, LinearMap.range (extend i)

 
theorem extend_mem_mappedFamilySum
    (extend : ∀ i, Source i →ₗ[K] A) (i : ι) (v : Source i) :
    extend i v ∈ mappedFamilySum Source extend := by
  exact (le_iSup (fun j => LinearMap.range (extend j)) i) ⟨v, rfl⟩

 

theorem mappedFamilySum_le_hull
    (extend : ∀ i, Source i →ₗ[K] A) (Hull : Submodule K A)
    (hextend : ∀ i v, extend i v ∈ Hull) :
    mappedFamilySum Source extend ≤ Hull := by
  refine iSup_le fun i => ?_
  rintro _ ⟨v, rfl⟩
  exact hextend i v

 

def adjoinFixed (G : A) (W : Submodule K A) : Submodule K A :=
  K ∙ G ⊔ W

theorem fixed_mem_adjoinFixed (G : A) (W : Submodule K A) :
    G ∈ adjoinFixed G W := by
  exact (le_sup_left : K ∙ G ≤ adjoinFixed G W)
    (Submodule.subset_span (Set.mem_singleton G))

theorem mem_adjoinFixed_of_mem (G : A) (W : Submodule K A) {w : A}
    (hw : w ∈ W) : w ∈ adjoinFixed G W :=
  (le_sup_right : W ≤ adjoinFixed G W) hw

end FamilySum

section Divisibility

variable {K : Type u} [Field K]
variable {A : Type x} [CommRing A] [Algebra K A]

 
def ambientDivisorSubmodule (D : A) : Submodule K A :=
  (Ideal.span ({D} : Set A)).restrictScalars K

theorem mem_ambientDivisorSubmodule_iff (D a : A) :
    a ∈ ambientDivisorSubmodule (K := K) D ↔ D ∣ a := by
  simp [ambientDivisorSubmodule, Ideal.mem_span_singleton]

 

theorem dvd_all_adjoinFixed_iff (D G : A) (W : Submodule K A) :
    (∀ q : adjoinFixed G W, D ∣ (q : A)) ↔
      D ∣ G ∧ ∀ w : W, D ∣ (w : A) := by
  constructor
  · intro h
    constructor
    · exact h ⟨G, fixed_mem_adjoinFixed G W⟩
    · intro w
      exact h ⟨w, mem_adjoinFixed_of_mem G W w.2⟩
  · rintro ⟨hG, hW⟩ q
    let Div := ambientDivisorSubmodule (K := K) D
    have hfixed : K ∙ G ≤ Div := by
      apply Submodule.span_le.mpr
      intro a ha
      have haG : a = G := Set.mem_singleton_iff.mp ha
      subst a
      exact (mem_ambientDivisorSubmodule_iff (K := K) D G).mpr hG
    have hsub : W ≤ Div := by
      intro w hw
      exact (mem_ambientDivisorSubmodule_iff (K := K) D w).mpr
        (hW ⟨w, hw⟩)
    have hq : (q : A) ∈ Div := (sup_le hfixed hsub) q.2
    exact (mem_ambientDivisorSubmodule_iff (K := K) D q).mp hq

end Divisibility

section ExactCore

variable {K : Type u} [Field K]
abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

local instance : StrongNormalizationMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 


def IsExactAdjoinedCommonCore
    (H G : Poly4 K) (W : Submodule K (Poly4 K)) : Prop :=
  H ≠ 0 ∧ H ∣ G ∧
    (∀ w : W, H ∣ (w : Poly4 K)) ∧
    ∀ D : Poly4 K, D ∣ G →
      (∀ w : W, D ∣ (w : Poly4 K)) → D ∣ H

 

theorem isExactAdjoinedCommonCore_of_dvd_iff
    (H G : Poly4 K) (W : Submodule K (Poly4 K)) (hH : H ≠ 0)
    (hiff : ∀ D : Poly4 K,
      D ∣ H ↔ ∀ q : adjoinFixed G W, D ∣ (q : Poly4 K)) :
    IsExactAdjoinedCommonCore H G W := by
  refine ⟨hH, ?_, ?_, ?_⟩
  · exact (hiff H).mp dvd_rfl ⟨G, fixed_mem_adjoinFixed G W⟩
  · intro w
    exact (hiff H).mp dvd_rfl ⟨w, mem_adjoinFixed_of_mem G W w.2⟩
  · intro D hDG hDW
    exact (hiff D).mpr ((dvd_all_adjoinFixed_iff D G W).mpr ⟨hDG, hDW⟩)

 



theorem exactCore_dvd_each_extended_member
    {ι : Type w} (Source : ι → Type v)
    [∀ i, AddCommGroup (Source i)] [∀ i, Module K (Source i)]
    (extend : ∀ i, Source i →ₗ[K] Poly4 K)
    (H G : Poly4 K)
    (hcore : IsExactAdjoinedCommonCore H G
      (mappedFamilySum Source extend))
    (i : ι) (v : Source i) :
    H ∣ extend i v := by
  exact hcore.2.2.1
    ⟨extend i v, extend_mem_mappedFamilySum Source extend i v⟩

 





theorem exists_member_realizing_exact_common_core
    (W : Submodule K (Poly4 K))
    (H G R : Poly4 K)
    (hcore : IsExactAdjoinedCommonCore H G W)
    (hG : G = H * R) (hR : R ≠ 0)
    (hcard : (allFactors R).card < ENat.card K) :
    ∃ w : W,
      H * fixedFactorQuotientLinearMap H hcore.1 W hcore.2.2.1 w =
          (w : Poly4 K) ∧
      NoCommonNonunitDivisor R
        (fixedFactorQuotientLinearMap H hcore.1 W hcore.2.2.1 w) := by
  classical
  let qmap : W →ₗ[K] Poly4 K :=
    fixedFactorQuotientLinearMap H hcore.1 W hcore.2.2.1
  let Factor := ↥(allFactors R)
  let bad : Factor → Submodule K W := fun p =>
    (ambientDivisorSubmodule (K := K) p.1).comap qmap
  have hproper : ∀ p : Factor, bad p ≠ ⊤ := by
    intro p htop
    have hpirr : Irreducible p.1 :=
      irreducible_of_normalized_factor p.1
        (Multiset.mem_toFinset.mp p.2)
    apply hpirr.not_isUnit
    have hpall : ∀ w : W, p.1 ∣ qmap w := by
      intro w
      apply (mem_ambientDivisorSubmodule_iff (K := K) p.1 (qmap w)).mp
      have hwbad : w ∈ bad p := by
        rw [htop]
        trivial
      exact hwbad
    have hHpW : ∀ w : W, H * p.1 ∣ (w : Poly4 K) := by
      intro w
      rw [← mul_fixedFactorQuotientLinearMap H hcore.1 W hcore.2.2.1 w]
      exact mul_dvd_mul_left H (hpall w)
    have hpR : p.1 ∣ R :=
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp p.2)
    have hHpG : H * p.1 ∣ G := by
      rw [hG]
      exact mul_dvd_mul_left H hpR
    have hHpH : H * p.1 ∣ H :=
      hcore.2.2.2 (H * p.1) hHpG hHpW
    apply isUnit_iff_dvd_one.mpr
    apply (mul_dvd_mul_iff_left hcore.1).mp
    simpa using hHpH
  have hfactorCard : Fintype.card Factor < ENat.card K := by
    simpa [Factor] using hcard
  obtain ⟨w, hw⟩ :=
    exists_section_avoiding_bounded_proper_submodules bad hproper hfactorCard
  refine ⟨w, mul_fixedFactorQuotientLinearMap H hcore.1 W hcore.2.2.1 w,
    ?_⟩
  intro C hCR hCQ
  by_contra hCunit
  have hC0 : C ≠ 0 := by
    intro hzero
    subst C
    simp only [zero_dvd_iff] at hCR
    exact hR hCR
  obtain ⟨p, hpC⟩ := exists_mem_normalizedFactors hC0 hCunit
  have hpirr : Irreducible p := irreducible_of_normalized_factor p hpC
  have hpR : p ∣ R := (dvd_of_mem_normalizedFactors hpC).trans hCR
  obtain ⟨q, hqR, hpq⟩ :=
    exists_mem_normalizedFactors_of_dvd hR hpirr hpR
  have hqQ : q ∣ qmap w := by
    apply hpq.dvd_iff_dvd_left.mp
    exact (dvd_of_mem_normalizedFactors hpC).trans hCQ
  let qFactor : Factor := ⟨q, Multiset.mem_toFinset.mpr hqR⟩
  apply hw qFactor
  change qmap w ∈ ambientDivisorSubmodule (K := K) qFactor.1
  simpa [qFactor] using
    ((mem_ambientDivisorSubmodule_iff (K := K) q (qmap w)).mpr hqQ)

 



theorem nestedFamily_commonCore_and_realizer
    {ι : Type w} (Source : ι → Type v)
    [∀ i, AddCommGroup (Source i)] [∀ i, Module K (Source i)]
    (extend : ∀ i, Source i →ₗ[K] Poly4 K)
    (Hull : Submodule K (Poly4 K))
    (hextend : ∀ i v, extend i v ∈ Hull)
    (H G R : Poly4 K) (hH : H ≠ 0)
    (hiff : ∀ D : Poly4 K,
      D ∣ H ↔ ∀ q : adjoinFixed G (mappedFamilySum Source extend),
        D ∣ (q : Poly4 K))
    (hG : G = H * R) (hR : R ≠ 0)
    (hcard : (allFactors R).card < ENat.card K) :
    (∀ i v, H ∣ extend i v) ∧
      ∃ w : mappedFamilySum Source extend,
        (w : Poly4 K) ∈ Hull ∧
        H * fixedFactorQuotientLinearMap H hH
              (mappedFamilySum Source extend)
              (isExactAdjoinedCommonCore_of_dvd_iff H G
                (mappedFamilySum Source extend) hH hiff).2.2.1 w =
            (w : Poly4 K) ∧
        NoCommonNonunitDivisor R
          (fixedFactorQuotientLinearMap H hH
            (mappedFamilySum Source extend)
            (isExactAdjoinedCommonCore_of_dvd_iff H G
              (mappedFamilySum Source extend) hH hiff).2.2.1 w) := by
  let W := mappedFamilySum Source extend
  have hcore : IsExactAdjoinedCommonCore H G W :=
    isExactAdjoinedCommonCore_of_dvd_iff H G W hH hiff
  constructor
  · intro i v
    exact exactCore_dvd_each_extended_member Source extend H G hcore i v
  · obtain ⟨w, hrecon, hcoprime⟩ :=
      exists_member_realizing_exact_common_core W H G R hcore hG hR hcard
    refine ⟨w, mappedFamilySum_le_hull Source extend Hull hextend w.2,
      ?_, ?_⟩
    · simpa [W, hcore] using hrecon
    · simpa [W, hcore] using hcoprime

end ExactCore

end

end ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research

#print axioms ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research.mappedFamilySum_le_hull
#print axioms ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research.dvd_all_adjoinFixed_iff
#print axioms ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research.isExactAdjoinedCommonCore_of_dvd_iff
#print axioms ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research.exists_member_realizing_exact_common_core
#print axioms ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research.nestedFamily_commonCore_and_realizer

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactFiniteFieldKernelSectionAvoidance6660Research
import ProximityPrize.SubmissionLower.ContactGeometricFactorCover

namespace ProximityPrize.SubmissionLower.ContactKernelGenericChoice6750Research

open scoped Classical BigOperators
open Set UniqueFactorizationMonoid
open ContactFlagInterpolation6641Research
open ContactKernelCommonGCD6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactGeometricFactorCover
open ContactFiniteFieldKernelSectionAvoidance6660Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

universe u v w

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

local instance : StrongNormalizationMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

local instance : NormalizedGCDMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)

def quotientDvdSubmodule {V : Type v} [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] Poly4 K) (F : Poly4 K) : Submodule K V where
  carrier := {z | F ∣ q z}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x + y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' := by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

theorem quotientDvdSubmodule_ne_top {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (F : Poly4 K) (hF : Irreducible F) :
    quotientDvdSubmodule
      (commonQuotientLinear D w0 L s m nodes u0 u1 b hH) F ≠ ⊤ := by
  intro htop
  let V := ConstraintKernel (K := K) D w0 L s m nodes u0 u1
  let H := commonGCDAtMax V b
  have hall : ∀ z : V,
      F ∣ commonQuotientLinear D w0 L s m nodes u0 u1 b hH z := by
    intro z
    have hz : z ∈ quotientDvdSubmodule
        (commonQuotientLinear D w0 L s m nodes u0 u1 b hH) F := by
      rw [htop]
      trivial
    exact hz
  have hmul : H * F ∣ H := by
    apply (dvd_commonGCDAtMax_iff V b (H * F)).2
    intro z
    change H * F ∣ kernelReconstructLinear D w0 L s m nodes u0 u1 z
    rw [← mul_commonQuotientLinear D w0 L s m nodes u0 u1 b hH z]
    exact mul_dvd_mul_left H (hall z)
  have hFone : F ∣ (1 : Poly4 K) := by
    apply (mul_dvd_mul_iff_left hH).mp
    simpa only [mul_one] using hmul
  exact hF.not_isUnit (isUnit_iff_dvd_one.mpr hFone)

theorem exists_quotient_avoiding_normalized_factors
    {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (P : Poly4 K)
    (hcard : (normalizedFactorSet P).card < ENat.card K) :
    ∃ z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1,
      ∀ F ∈ normalizedFactorSet P,
        ¬ F ∣ commonQuotientLinear D w0 L s m nodes u0 u1 b hH z := by
  classical
  let V := ConstraintKernel (K := K) D w0 L s m nodes u0 u1
  let S := normalizedFactorSet P
  let bad : S → Submodule K V := fun F ↦
    quotientDvdSubmodule
      (commonQuotientLinear D w0 L s m nodes u0 u1 b hH) F.1
  have hproper : ∀ F : S, bad F ≠ ⊤ := by
    intro F
    exact quotientDvdSubmodule_ne_top D w0 L s m nodes u0 u1 b hH F.1
      (normalizedFactorSet_spec P F.1 F.2).1
  have hfactorCard : Fintype.card S < ENat.card K := by
    simpa [S] using hcard
  obtain ⟨z, hz⟩ :=
    exists_section_avoiding_bounded_proper_submodules bad hproper hfactorCard
  refine ⟨z, ?_⟩
  intro F hF hdiv
  have hnot := hz (⟨F, hF⟩ : S)
  apply hnot
  exact hdiv

theorem exists_nonzero_quotient_avoiding_normalized_factors
    {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (P : Poly4 K)
    (hcard : (normalizedFactorSet P).card < ENat.card K) :
    ∃ z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1,
      z ≠ 0 ∧
      ∀ F ∈ normalizedFactorSet P,
        ¬ F ∣ commonQuotientLinear D w0 L s m nodes u0 u1 b hH z := by
  classical
  by_cases hempty : normalizedFactorSet P = ∅
  · let i : beta := Classical.choice inferInstance
    refine ⟨b i, b.ne_zero i, ?_⟩
    intro F hF
    have : False := by simpa [hempty] using hF
    exact this.elim
  · obtain ⟨z, hz⟩ := exists_quotient_avoiding_normalized_factors
      D w0 L s m nodes u0 u1 b hH P hcard
    have hSne : (normalizedFactorSet P).Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr hempty
    have hz0 : z ≠ 0 := by
      intro hzero
      obtain ⟨F, hF⟩ := hSne
      apply hz F hF
      subst z
      simp
    exact ⟨z, hz0, hz⟩

theorem isRelPrime_of_avoids_normalizedFactorSet
    (P Q : Poly4 K) (hP : P ≠ 0)
    (havoid : ∀ F ∈ normalizedFactorSet P, ¬ F ∣ Q) :
    IsRelPrime Q P := by
  classical
  letI : DecidableEq (Fin 4) := Classical.decEq _
  apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
  · intro hzero
    exact hP hzero.2
  · intro d hd hdQ hdP
    obtain ⟨F, hFnorm, hassoc⟩ :=
      exists_mem_normalizedFactors_of_dvd hP hd hdP
    apply havoid F (Multiset.mem_toFinset.mpr hFnorm)
    exact hassoc.dvd_iff_dvd_left.mp hdQ

theorem exists_common_quotient_isRelPrime {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (P : Poly4 K) (hP : P ≠ 0)
    (hcard : (normalizedFactorSet P).card < ENat.card K) :
    ∃ z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1,
      z ≠ 0 ∧
      IsRelPrime
        (commonQuotientLinear D w0 L s m nodes u0 u1 b hH z) P := by
  classical
  letI : DecidableEq (Fin 4) := Classical.decEq _
  by_cases hunit : IsUnit P
  · let i : beta := Classical.choice inferInstance
    refine ⟨b i, b.ne_zero i, hunit.isRelPrime_right⟩
  · have hSne : (normalizedFactorSet P).Nonempty := by
      obtain ⟨F, hF⟩ := exists_mem_normalizedFactors hP hunit
      exact ⟨F, Multiset.mem_toFinset.mpr hF⟩
    obtain ⟨z, hz⟩ := exists_quotient_avoiding_normalized_factors
      D w0 L s m nodes u0 u1 b hH P hcard
    have hz0 : z ≠ 0 := by
      intro hzero
      obtain ⟨F, hF⟩ := hSne
      have hnot := hz F hF
      apply hnot
      subst z
      simp
    refine ⟨z, hz0, ?_⟩
    exact isRelPrime_of_avoids_normalizedFactorSet P _ hP hz

theorem irreducible_positive_degree_sum_fin4
    (F : Poly4 K) (hF : Irreducible F) :
    0 < F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by
  by_contra hn
  have hsum : F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 = 0 :=
    Nat.eq_zero_of_not_pos hn
  have h0 : F.degreeOf (0 : Fin 4) = 0 := by omega
  have h1 : F.degreeOf (1 : Fin 4) = 0 := by omega
  have h2 : F.degreeOf (2 : Fin 4) = 0 := by omega
  have h3 : F.degreeOf (3 : Fin 4) = 0 := by omega
  have hdeg (i : Fin 4) : F.degreeOf i = 0 := by
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have heq : F = MvPolynomial.C (F.coeff 0) := by
    apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    apply Nat.eq_zero_of_le_zero
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro d hd
    have hd0 : d = 0 := by
      ext i
      have hi := MvPolynomial.monomial_le_degreeOf i hd
      rw [hdeg i] at hi
      exact Nat.eq_zero_of_le_zero hi
    simp [hd0]
  have hc : F.coeff 0 ≠ 0 := by
    intro hz
    apply hF.ne_zero
    rw [heq, hz, map_zero]
  apply hF.not_isUnit
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

theorem normalizedFactorSet_card_le_degree_sum_fin4
    (P : Poly4 K) (hP : P ≠ 0) :
    (normalizedFactorSet P).card ≤
      P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3 := by
  classical
  calc
    (normalizedFactorSet P).card =
        ∑ _F ∈ normalizedFactorSet P, (1 : Nat) := by simp
    _ ≤ ∑ F ∈ normalizedFactorSet P,
        (F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) := by
      apply Finset.sum_le_sum
      intro F hF
      exact irreducible_positive_degree_sum_fin4 F
        (normalizedFactorSet_spec P F hF).1
    _ = (∑ F ∈ normalizedFactorSet P, F.degreeOf 0) +
          (∑ F ∈ normalizedFactorSet P, F.degreeOf 1) +
          (∑ F ∈ normalizedFactorSet P, F.degreeOf 2) +
          (∑ F ∈ normalizedFactorSet P, F.degreeOf 3) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3 := by
      gcongr <;> exact normalizedFactorSet_degree_budget P hP _

theorem degreeOf_X_le_of_mem_flagBox (P : Poly4 K)
    (D w0 L s : Nat) (hbox : P ∈ globalCoefficientBox K D w0 L s) :
    P.degreeOf (0 : Fin 4) ≤ D - 1 := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hc := (hbox hd).2.2
  omega

theorem normalizedFactorSet_card_le_of_mem_flagBox
    (P : Poly4 K) (D w0 L s : Nat) (hw : 0 < w0) (hP : P ≠ 0)
    (hbox : P ∈ globalCoefficientBox K D w0 L s) :
    (normalizedFactorSet P).card ≤
      (D - 1) + (D - 1) / w0 + s + L := by
  have hsum := normalizedFactorSet_card_le_degree_sum_fin4 P hP
  have hX := degreeOf_X_le_of_mem_flagBox P D w0 L s hbox
  have hY : P.degreeOf (1 : Fin 4) ≤ (D - 1) / w0 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    apply (Nat.le_div_iff_mul_le hw).mpr
    have hc := (hbox hd).2.2
    have hm : d 1 * w0 = w0 * d 1 := Nat.mul_comm _ _
    omega
  have hR : P.degreeOf (2 : Fin 4) ≤ s := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hZ : P.degreeOf (3 : Fin 4) ≤ L := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hL := (hbox hd).1
    omega
  omega

end

end ProximityPrize.SubmissionLower.ContactKernelGenericChoice6750Research

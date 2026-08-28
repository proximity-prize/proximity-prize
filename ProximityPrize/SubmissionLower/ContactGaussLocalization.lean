import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCover
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_Localization



/-!
# Actual Gauss localization and divisibility reflection for active factors

Model label: gpt-5.

An irreducible four-variable factor with positive Y/R/Z degree cannot
divide a nonzero pure-X polynomial. Its collected principal prime is
therefore disjoint from the coefficient denominators. Mathlib's actual
multivariable localization proves irreducibility over K(X) and contracts
the localized principal ideal back to the original one.

This is a localization bridge, not a claim about geometric irreducibility
after algebraic closure or an intersection/seed-count theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactGaussLocalization

open ContactGenericSurface ContactFactorCover

noncomputable section

variable (K : Type*) [Field K]

abbrev Collected := MvPolynomial (Fin 3) (Polynomial K)
abbrev RationalCoefficients := FractionRing (Polynomial K)
abbrev RationalPolynomials := MvPolynomial (Fin 3) (RationalCoefficients K)

attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientDenominators : Submonoid (Collected K) :=
  (nonZeroDivisors (Polynomial K)).map MvPolynomial.C

local instance : IsLocalization (coefficientDenominators K) (RationalPolynomials K) :=
  MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RationalCoefficients K)

def rationalSurfaceMap :
    MvPolynomial (Fin 4) K →+* RationalPolynomials K :=
  surfaceMap (algebraMap (Polynomial K) (RationalCoefficients K))

theorem rationalSurfaceMap_eq (F : MvPolynomial (Fin 4) K) :
    rationalSurfaceMap K F =
      algebraMap (Collected K) (RationalPolynomials K) (collectX K F) := rfl

/-- The inverse of collecting X, restricted to coefficient polynomials. -/
def xLift (P : Polynomial K) : MvPolynomial (Fin 4) K :=
  (collectX K).symm (MvPolynomial.C P)

theorem xLift_add (P Q : Polynomial K) : xLift K (P + Q) = xLift K P + xLift K Q := by
  simp [xLift]

theorem xLift_monomial (n : ℕ) (a : K) :
    xLift K (Polynomial.monomial n a) =
      MvPolynomial.C a * MvPolynomial.X (0 : Fin 4) ^ n := by
  apply (collectX K).injective
  simp [xLift, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem xLift_ne_zero (P : Polynomial K) (hP : P ≠ 0) : xLift K P ≠ 0 := by
  intro h
  have hh := congrArg (collectX K) h
  have hc : (MvPolynomial.C P : Collected K) = 0 := by
    simpa only [xLift, AlgEquiv.apply_symm_apply, map_zero] using hh
  apply hP
  apply MvPolynomial.C_injective
  simpa only [map_zero] using hc

theorem xLift_degreeOf_succ (P : Polynomial K) (i : Fin 3) :
    (xLift K P).degreeOf i.succ = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [xLift_add]
      apply Nat.eq_zero_of_le_zero
      simpa only [hP, hQ, max_self] using
        MvPolynomial.degreeOf_add_le i.succ (xLift K P) (xLift K Q)
  | monomial n a =>
      rw [xLift_monomial]
      have hx : (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K).degreeOf i.succ = 0 := by
        simp [MvPolynomial.degreeOf_X, Fin.succ_ne_zero]
      have hp := MvPolynomial.degreeOf_pow_le i.succ
        (MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) K) n
      rw [hx, Nat.mul_zero] at hp
      have hm := MvPolynomial.degreeOf_mul_le i.succ
        (MvPolynomial.C a : MvPolynomial (Fin 4) K) (MvPolynomial.X (0 : Fin 4) ^ n)
      rw [MvPolynomial.degreeOf_C, Nat.zero_add] at hm
      exact Nat.eq_zero_of_le_zero (hm.trans hp)

theorem not_dvd_xLift_of_positive_degree
    (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (hP : P ≠ 0)
    (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) :
    ¬ F ∣ xLift K P := by
  intro hdiv
  have hi : ∃ i : Fin 3, 0 < F.degreeOf i.succ := by
    by_cases hy : 0 < F.degreeOf 1
    · exact ⟨0, hy⟩
    by_cases hr : 0 < F.degreeOf 2
    · exact ⟨1, hr⟩
    exact ⟨2, by change 0 < F.degreeOf (3 : Fin 4); omega⟩
  obtain ⟨i, hi⟩ := hi
  have hb := ContactFactorCaps.degreeOf_le_of_dvd i.succ F (xLift K P)
    hdiv (xLift_ne_zero K P hP)
  rw [xLift_degreeOf_succ] at hb
  omega

theorem collected_principal_isPrime (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) :
    (Ideal.span ({collectX K F} : Set (Collected K))).IsPrime := by
  have hi : Irreducible (collectX K F) := (MulEquiv.irreducible_iff (collectX K)).mpr hF
  exact Ideal.isPrime_span_singleton_of_prime hi.prime

/-- The denominator-disjointness is proved from the actual original degrees. -/
theorem coefficientDenominators_disjoint (F : MvPolynomial (Fin 4) K)
    (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) :
    Disjoint (coefficientDenominators K : Set (Collected K))
      (Ideal.span ({collectX K F} : Set (Collected K)) : Set (Collected K)) := by
  rw [Set.disjoint_left]
  intro a ha hI
  obtain ⟨P, hP, rfl⟩ := Submonoid.mem_map.mp ha
  have hP0 : P ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hP
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton.mp hI
  have hdiv : F ∣ xLift K P := by
    refine ⟨(collectX K).symm G, ?_⟩
    apply (collectX K).injective
    simpa only [xLift, AlgEquiv.apply_symm_apply, map_mul] using hG
  exact not_dvd_xLift_of_positive_degree K F P hP0 hpos hdiv

theorem localized_principal_isPrime (F : MvPolynomial (Fin 4) K)
    (hF : Irreducible F) (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) :
    (Ideal.span ({rationalSurfaceMap K F} : Set (RationalPolynomials K))).IsPrime := by
  have hp := IsLocalization.isPrime_of_isPrime_disjoint
    (coefficientDenominators K) (RationalPolynomials K)
    (Ideal.span ({collectX K F} : Set (Collected K)))
    (collected_principal_isPrime K F hF) (coefficientDenominators_disjoint K F hpos)
  simpa only [Ideal.map_span, Set.image_singleton, ← rationalSurfaceMap_eq] using hp

/-- Actual Gauss localization: no primitive-content hypothesis is assumed. -/
theorem rationalSurfaceMap_irreducible (F : MvPolynomial (Fin 4) K)
    (hF : Irreducible F) (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) :
    Irreducible (rationalSurfaceMap K F) := by
  have hne : rationalSurfaceMap K F ≠ 0 :=
    surfaceMap_ne_zero (algebraMap (Polynomial K) (RationalCoefficients K))
      (IsFractionRing.injective (Polynomial K) (RationalCoefficients K)) F hF.ne_zero
  exact ((Ideal.span_singleton_prime hne).mp
    (localized_principal_isPrime K F hF hpos)).irreducible

/-- Divisibility by an active irreducible factor is reflected from K(X).
This is actual contraction of the localized principal prime, not a premise. -/
theorem rationalSurfaceMap_dvd_iff
    (F M : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) :
    rationalSurfaceMap K F ∣ rationalSurfaceMap K M ↔ F ∣ M := by
  constructor
  · intro hdiv
    have hm : algebraMap (Collected K) (RationalPolynomials K) (collectX K M) ∈
        Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
          (Ideal.span ({collectX K F} : Set (Collected K))) := by
      simpa only [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
        ← rationalSurfaceMap_eq] using hdiv
    have hu : collectX K M ∈
        (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
          (Ideal.span ({collectX K F} : Set (Collected K)))).under (Collected K) := hm
    rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
      (RationalPolynomials K) (collected_principal_isPrime K F hF)
      (coefficientDenominators_disjoint K F hpos)] at hu
    obtain ⟨G, hG⟩ := Ideal.mem_span_singleton.mp hu
    refine ⟨(collectX K).symm G, ?_⟩
    apply (collectX K).injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hG
  · intro hdiv
    exact map_dvd (rationalSurfaceMap K) hdiv

theorem activeFactor_rational_irreducible
    (Q F : MvPolynomial (Fin 4) K) (hF : F ∈ activeFactors Q) :
    Irreducible (rationalSurfaceMap K F) := by
  have hs := activeFactors_spec Q F hF
  exact rationalSurfaceMap_irreducible K F hs.1 hs.2.2

theorem activeFactor_rational_dvd_iff
    (Q F M : MvPolynomial (Fin 4) K) (hF : F ∈ activeFactors Q) :
    rationalSurfaceMap K F ∣ rationalSurfaceMap K M ↔ F ∣ M := by
  have hs := activeFactors_spec Q F hF
  exact rationalSurfaceMap_dvd_iff K F M hs.1 hs.2.2

#print axioms xLift_degreeOf_succ
#print axioms not_dvd_xLift_of_positive_degree
#print axioms collected_principal_isPrime
#print axioms coefficientDenominators_disjoint
#print axioms localized_principal_isPrime
#print axioms rationalSurfaceMap_irreducible
#print axioms rationalSurfaceMap_dvd_iff
#print axioms activeFactor_rational_irreducible
#print axioms activeFactor_rational_dvd_iff

end
end ProximityPrize.SubmissionLower.ContactGaussLocalization

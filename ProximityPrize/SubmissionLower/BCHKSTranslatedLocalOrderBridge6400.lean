import ProximityPrize.SubmissionLower.BCHKSCofactorRetuneAudit6400
import ProximityPrize.SubmissionLower.BCHKSNormalizedCofactorBridge6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTranslatedLocalOrderBridge6400
open Polynomial
open BCHKSRadicalMultiplicityBridge6400
open BCHKSCofactorRetuneAudit6400
open BCHKSLocalValuation6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
theorem evalX_zero_shift
    {A : Type*} [CommRing A]
    (R : Polynomial (Polynomial A)) (x y : A) :
    Polynomial.Bivariate.evalX 0 (Polynomial.Bivariate.shift R x y) =
      (Polynomial.Bivariate.evalX x R).comp
        (Polynomial.X + Polynomial.C y) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [Polynomial.Bivariate.shift,
        Polynomial.Bivariate.evalX_eq_map] using
          congrArg₂ (fun p q => p + q) hR hS
  | monomial n a =>
      simp [Polynomial.Bivariate.shift,
        Polynomial.Bivariate.evalX_eq_map,
        Polynomial.monomial_comp, Polynomial.map_monomial]
theorem not_vertical_dvd_shift_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    (R : Polynomial (Polynomial A)) (x y : A)
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) :
    ¬ (Polynomial.C (Polynomial.X : Polynomial A) ∣
      Polynomial.Bivariate.shift R x y) := by
  intro hvertical
  have hzeroShift : Polynomial.Bivariate.evalX 0
      (Polynomial.Bivariate.shift R x y) = 0 := by
    obtain ⟨T, hT⟩ := hvertical
    rw [hT, Polynomial.Bivariate.evalX_eq_map]
    simp
  have hzeroFiber : Polynomial.Bivariate.evalX x R = 0 := by
    have hcomp : (Polynomial.Bivariate.evalX x R).comp
        (Polynomial.X + Polynomial.C y) = 0 := by
      rw [← evalX_zero_shift R x y]
      exact hzeroShift
    exact Polynomial.comp_X_add_C_eq_zero_iff.mp hcomp
  have hcoeffRoot : ∀ t, Polynomial.eval x (R.coeff t) = 0 := by
    intro t
    have hz := congrArg (fun p : Polynomial A ↦ p.coeff t) hzeroFiber
    simpa [Polynomial.Bivariate.evalX_eq_map,
      Polynomial.coeff_map] using hz
  have hlinearDvdCoeff : ∀ t,
      (Polynomial.X - Polynomial.C x : Polynomial A) ∣ R.coeff t := by
    intro t
    have h := Polynomial.X_sub_C_dvd_sub_C_eval (p := R.coeff t) (a := x)
    simpa [hcoeffRoot t] using h
  have hlinearDvd :
      Polynomial.C (Polynomial.X - Polynomial.C x : Polynomial A) ∣ R :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hlinearDvdCoeff
  rcases hirr.dvd_iff.mp hlinearDvd with hunit | hassoc
  · exact Polynomial.not_isUnit_X_sub_C x
      (Polynomial.isUnit_C.mp hunit)
  · have hdegree := Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated hassoc)
    have : R.natDegree = 0 := by simpa using hdegree
    omega
theorem natDegree_shift_le
    {A : Type*} [CommRing A] [Nontrivial A]
    (R : Polynomial (Polynomial A)) (x y : A) :
    (Polynomial.Bivariate.shift R x y).natDegree ≤ R.natDegree := by
  unfold Polynomial.Bivariate.shift
  calc
    ((R.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).map
        (Polynomial.compRingHom
          (Polynomial.X + Polynomial.C x))).natDegree ≤
        (R.comp
          (Polynomial.X + Polynomial.C (Polynomial.C y))).natDegree :=
      Polynomial.natDegree_map_le
    _ ≤ R.natDegree *
        (Polynomial.X + Polynomial.C (Polynomial.C y)).natDegree :=
      Polynomial.natDegree_comp_le
    _ = R.natDegree := by
      rw [Polynomial.natDegree_X_add_C, Nat.mul_one]
theorem normalized_owner_shift_localOrder_le_natDegree
    {F : Type*} [Field F]
    [NormalizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q q : Polynomial (Polynomial (Polynomial F)))
    (hqS : q ∈ positiveNormalizedFactors Q)
    (omega : F) (yZ : Polynomial F) :
    localOrder
        (Polynomial.Bivariate.shift q (Polynomial.C omega) yZ) ≤
      q.natDegree := by
  classical
  have hfilter : q ∈
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun H ↦ 0 < H.natDegree) := by
    simpa [positiveNormalizedFactors] using hqS
  have hqmem : q ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hfilter).1
  have hqirr : Irreducible q :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor q hqmem).irreducible
  have hqpos : 0 < q.natDegree := (Finset.mem_filter.mp hfilter).2
  have hnotVertical := not_vertical_dvd_shift_of_irreducible
    q (Polynomial.C omega) yZ hqirr hqpos
  exact (localOrder_le_natDegree_of_not_vertical _ hnotVertical).trans
    (natDegree_shift_le q (Polynomial.C omega) yZ)
end BCHKSTranslatedLocalOrderBridge6400
end ProximityPrize.SubmissionLower

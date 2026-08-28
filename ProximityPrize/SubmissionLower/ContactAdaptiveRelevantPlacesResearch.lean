import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch

/-!
# Relevant places with a component-dependent literal normalization

The old flag construction normalized every component at literal `Z`.  This
version uses the one `SeparableLiteralCoordinate` selected independently on
each prime component.  The resulting finite place set still covers every
nonzero order of every original coordinate.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveRelevantPlacesResearch

open scoped Classical WithZero
open IsDedekindDomain
open ContactLocalPoleBound
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers
open CoordinateBoxZeroCount
open ContactWeakSeparableSeparatorResearch

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

/-- Finite union of all nonzero literal-coordinate order supports, normalized
through an arbitrary selected literal separator. -/
def literalRelevantPlaces
    {P : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
    (D : SeparableLiteralCoordinate P) :
    Finset (Place Omega (CoordinateField Omega P)) := by
  classical
  let i0 := D.index
  let htr := D.transcendental
  letI : Algebra (Polynomial Omega) (CoordinateRing Omega P) :=
    quotientPolynomialAlgebra Omega P i0
  letI : Algebra (Polynomial Omega) (CoordinateField Omega P) :=
    polynomialBaseAlgebra Omega P i0
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    rationalBaseAlgebra Omega P i0 htr
  letI := quotientBaseScalarTower Omega P i0
  letI := polynomialBaseScalarTower Omega P i0
  letI := quotientFractionScalarTower Omega P i0
  letI := polynomialRationalScalarTower Omega P i0 htr
  letI := rationalBaseScalarTower Omega P i0 htr
  letI : FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) := D.finite
  letI : Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := D.separable
  exact Finset.univ.biUnion (fun i : Fin 3 =>
    if hi : coordinate Omega P i ≠ 0 then
      CommonPlaceBalance.placesFor Omega (CoordinateField Omega P)
        (coordinate Omega P i) hi
    else ∅)

/-- Outside `literalRelevantPlaces`, every original coordinate has pole order
zero. -/
theorem coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
    {P : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
    (D : SeparableLiteralCoordinate P)
    (v : Place Omega (CoordinateField Omega P))
    (hv : v ∉ literalRelevantPlaces D) (i : Fin 3) :
    poleOrder v.val (coordinate Omega P i) = 0 := by
  classical
  let i0 := D.index
  let htr := D.transcendental
  letI : Algebra (Polynomial Omega) (CoordinateRing Omega P) :=
    quotientPolynomialAlgebra Omega P i0
  letI : Algebra (Polynomial Omega) (CoordinateField Omega P) :=
    polynomialBaseAlgebra Omega P i0
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    rationalBaseAlgebra Omega P i0 htr
  letI := quotientBaseScalarTower Omega P i0
  letI := polynomialBaseScalarTower Omega P i0
  letI := quotientFractionScalarTower Omega P i0
  letI := polynomialRationalScalarTower Omega P i0 htr
  letI := rationalBaseScalarTower Omega P i0 htr
  letI : FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) := D.finite
  letI : Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := D.separable
  by_cases hi : coordinate Omega P i = 0
  · simp [hi, poleOrder]
  · have hnot : v ∉ CommonPlaceBalance.placesFor Omega
        (CoordinateField Omega P) (coordinate Omega P i) hi := by
      intro hmem
      apply hv
      unfold literalRelevantPlaces
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simp [hi, hmem]⟩
    have horder : CommonPlaceBalance.order Omega (CoordinateField Omega P) v
        (coordinate Omega P i) = 0 := by
      by_contra hne
      exact hnot (CommonPlaceBalance.placesFor_covers Omega
        (CoordinateField Omega P) (coordinate Omega P i) hi v hne)
    unfold CommonPlaceBalance.order at horder
    unfold poleOrder
    have hlog : (v.val (coordinate Omega P i)).log = 0 := by omega
    rw [hlog]
    simp

end

end ProximityPrize.SubmissionLower.ContactAdaptiveRelevantPlacesResearch

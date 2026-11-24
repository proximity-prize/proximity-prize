import ProximityPrize.SubmissionLower.R6960MonicChartClearing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Differential

/-- A primitive local equation has a reciprocal chart when the residue
field is infinite. -/
theorem exists_unit_evaluation {A : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] (f : (Polynomial A))
    (primitive : ∃ i, IsUnit (f.coeff i)) : ∃ c : A, IsUnit (f.eval c) := by
  let residue := IsLocalRing.residue A
  by_contra! no
  have all (x : IsLocalRing.ResidueField A) : (f.map residue).IsRoot x := by
    obtain ⟨c,rfl⟩ := IsLocalRing.residue_surjective (R:=A) x
    change (f.map residue).eval (residue c)=0
    rw [eval_map_apply]
    exact not_ne_iff.mp (fun h => no c ((IsLocalRing.residue_ne_zero_iff_isUnit (f.eval c)).mp h))
  have zero : f.map residue=0 := by
    apply eq_zero_of_infinite_isRoot
    simpa only [all, Set.setOf_true] using
      (Set.infinite_univ : (Set.univ : Set (IsLocalRing.ResidueField A)).Infinite)
  obtain ⟨i,h⟩ := primitive
  have eq := congrArg (fun p : (Polynomial (IsLocalRing.ResidueField A)) => p.coeff i) zero
  rw [coeff_map,coeff_zero] at eq
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h) eq

/-- Local derivative clearing by the raw square, choosing an affine
reciprocal coordinate from the coefficients of the equation. -/
theorem raw_square_clears_local {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential A] [Differential E] [DifferentialAlgebra A E]
    (b : PowerBasis F E) (f : (Polynomial A)) (primitive : ∃ i,IsUnit (f.coeff i))
    (degree : f.natDegree=b.dim) (positive : 2≤f.natDegree) (root : aeval b.gen f=0)
    (x : E) (hx : IsIntegral A x) :
    IsIntegral A (algebraMap A E ((f.resultant f.derivative f.natDegree (f.natDegree-1))^2)*x′) := by
  obtain ⟨c,u,h⟩ := exists_unit_evaluation f primitive
  exact raw_square_clears b f c u h.symm degree positive root x hx

#print axioms exists_unit_evaluation
#print axioms raw_square_clears_local
end
end Lower6960.MonicChart

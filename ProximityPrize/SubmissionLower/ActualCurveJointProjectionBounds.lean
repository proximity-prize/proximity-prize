import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
import ProximityPrize.SubmissionLower.ActualPlaneJointProjection

namespace ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds

open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateCaps ActualPlanePositiveOrder ActualPlaneCoordinateDegree
  ActualCurveProjectionBounds ActualCurveZeroCount ActualCoordinateDegreeSum
open ActualPlaneJointProjection

noncomputable section

variable (K : Type) [Field K]

private def fieldsSummary (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) : Prop :=
  letI := A
  FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K P)

theorem finite_separable_at_of_original_coordinate_gate
    (P : Ideal (Original K)) [P.IsPrime] (i : Fin 3)
    (hi : Transcendental K (coordinate K P i))
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P)
    (hproper : ¬ G ∣ H) (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed : coordinateMixedDegree K G H i < p) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have hbase : order 0 = i := Equiv.swap_apply_left _ _
  have ht : Transcendental K (coordinate K P (order 0)) := by
    simpa only [hbase] using hi
  have hresult :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P (order 0) ht
      FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    have h := original_finite_separable_finrank_bound K order P ht p G H
      hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
    exact ⟨h.1, h.2.1⟩
  change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
  change fieldsSummary K P (rationalBaseAlgebra K P i hi)
  rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
  exact hresult

end

end ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds

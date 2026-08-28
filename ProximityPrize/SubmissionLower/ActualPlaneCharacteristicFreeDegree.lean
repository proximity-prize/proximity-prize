import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneCharacteristicFreeRoots
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree

/-!
# Actual characteristic-free coordinate-field degree

This connects the characteristic-free plane-root theorem to the literal
prime-quotient coordinate field used by the contact development.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegree

open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateDegree

noncomputable section

variable (K : Type) [Field K]
variable (order : Fin 3 ≃ Fin 3)
variable (P : Ideal (Original K)) [P.IsPrime]
variable (ht : Transcendental K (coordinate K P (order 0)))

theorem actual_finite_finrank_le_resultant_natDegree
    (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P)
    (hproper : ¬ G ∣ H)
    (hpositive : 0 < (planeMap K order G).natDegree) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        (Polynomial.resultant (planeMap K order G) (planeMap K order H)
          (planeMap K order G).natDegree
          (planeMap K order H).natDegree).natDegree := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P (order 0) ht
  have hirr := planeMap_irreducible_of_component
    (K := K) (order := order) (P := P) (ht := ht) G hG hGmem
  have hproperPlane : ¬ planeMap K order G ∣ planeMap K order H := by
    intro h
    exact hproper ((planeMap_dvd_iff_of_component
      (K := K) (order := order) (P := P) (ht := ht)
      G H hG hGmem).mp h)
  have hGroots : PlaneFunctionFieldDegree.planeEval
      (RatFunc K) (CoordinateField K P)
      (coordinate K P (order 2)) (coordinate K P (order 1))
      (planeMap K order G) = 0 := by
    change actualPlaneEvaluation K order P ht (planeMap K order G) = 0
    exact (actualPlane_root_iff K order P ht G).mpr hGmem
  have hHroots : PlaneFunctionFieldDegree.planeEval
      (RatFunc K) (CoordinateField K P)
      (coordinate K P (order 2)) (coordinate K P (order 1))
      (planeMap K order H) = 0 := by
    change actualPlaneEvaluation K order P ht (planeMap K order H) = 0
    exact (actualPlane_root_iff K order P ht H).mpr hHmem
  exact PlaneCharacteristicFreeRoots.finite_finrank_le_resultant_natDegree
    (RatFunc K) (CoordinateField K P)
    (planeMap K order G) (planeMap K order H)
    hirr hpositive hproperPlane
    (coordinate K P (order 2)) (coordinate K P (order 1))
    (actual_generators K order P ht) hGroots hHroots

end

end ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegree

#print axioms ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegree.actual_finite_finrank_le_resultant_natDegree

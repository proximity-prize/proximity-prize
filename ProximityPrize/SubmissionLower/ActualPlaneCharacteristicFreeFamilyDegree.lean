import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneCharacteristicFreeFamilyRoots
import ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegree

/-!
# Actual characteristic-free degree for a finite component family

Distinct literal prime components have distinct actual bivariate
relation kernels.  The grouped family resultant theorem therefore
charges their complete field degrees to one resultant without
separability.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeFamilyDegree

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateDegree ActualPlaneCharacteristicFreeDegree

noncomputable section

variable (K : Type) [Field K]
variable (order : Fin 3 ≃ Fin 3)
variable {I : Type} [Fintype I]
variable (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

theorem actual_sum_finrank_le_resultant_natDegree
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P)
    (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i)
    (hHmem : ∀ i, H ∈ P i) (hproper : ¬ G ∣ H)
    (hpositive : 0 < (planeMap K order G).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i ↦ rationalBaseAlgebra K (P i) (order 0) (ht i)
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
      (Polynomial.resultant (planeMap K order G) (planeMap K order H)
        (planeMap K order G).natDegree
        (planeMap K order H).natDegree).natDegree := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
    fun i ↦ rationalBaseAlgebra K (P i) (order 0) (ht i)
  have hfields : ∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) := by
    intro i
    exact (actual_finite_finrank_le_resultant_natDegree
      K order (P i) (ht i) G H hG (hGmem i) (hHmem i) hproper hpositive).1
  letI : ∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) := hfields
  have hkernels : Function.Injective (fun i ↦
      PlaneFunctionFieldDegree.relationIdeal
        (RatFunc K) (CoordinateField K (P i))
        (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))) := by
    change Function.Injective (fun i ↦
      actualRelationKernel K order (P i) (ht i))
    exact actualRelationKernel_family_injective K order P ht hinj
  have hGroots : ∀ i, PlaneFunctionFieldDegree.planeEval
      (RatFunc K) (CoordinateField K (P i))
      (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
      (planeMap K order G) = 0 := by
    intro i
    change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G) = 0
    exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
  have hHroots : ∀ i, PlaneFunctionFieldDegree.planeEval
      (RatFunc K) (CoordinateField K (P i))
      (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
      (planeMap K order H) = 0 := by
    intro i
    change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H) = 0
    exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    have hirr₀ := planeMap_irreducible_of_component
      (K := K) (order := order) (P := P i₀) (ht := ht i₀)
      G hG (hGmem i₀)
    have hproperPlane₀ : ¬ planeMap K order G ∣ planeMap K order H := by
      intro h
      exact hproper ((planeMap_dvd_iff_of_component
        (K := K) (order := order) (P := P i₀) (ht := ht i₀)
        G H hG (hGmem i₀)).mp h)
    have hres := PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      (planeMap K order G) (planeMap K order H) hirr₀ hpositive hproperPlane₀
    exact PlaneCharacteristicFreeFamilyRoots.sum_finrank_le_resultant_natDegree
      (RatFunc K) (fun i ↦ CoordinateField K (P i))
      (fun i ↦ coordinate K (P i) (order 2))
      (fun i ↦ coordinate K (P i) (order 1))
      (fun i ↦ actual_generators K order (P i) (ht i)) hkernels
      (planeMap K order G) (planeMap K order H) hirr₀ hpositive
      hGroots hHroots hres
  · letI : IsEmpty I := ⟨fun i ↦ hI ⟨i⟩⟩
    simp

end

end ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeFamilyDegree

#print axioms ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeFamilyDegree.actual_sum_finrank_le_resultant_natDegree

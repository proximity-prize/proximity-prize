import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneRootSeparability
import ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree

/-!
# One actual planar budget after deriving finite separability

Model label: gpt-5.

This integration derives finite-dimensionality and separability from actual
common-root equations and strict characteristic-degree gates before using
the verified embedding count. For a family, distinct actual relation
kernels give one common planar budget for the sum of all field degrees.

The fields and their actual two-generator presentations are still explicit
inputs. Construction from prime coordinate rings is not assumed proved by
this file.
-/

namespace ProximityPrize.SubmissionLower.PlaneSmallCharacteristicDegree

open PlaneFunctionFieldDegree

noncomputable section

section SingleField

variable (K E : Type) [Field K] [Field E] [Algebra K E]

/-- The relation-kernel evaluation is the actual iterated polynomial
evaluation used by the minimal-polynomial separability argument. -/
theorem planeEval_eq_eval₂ (y r : E) (P : Polynomial (Polynomial K)) :
    planeEval K E y r P =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r P := by
  change (P.map (Polynomial.eval₂RingHom (algebraMap K E) y)).eval r = _
  rw [Polynomial.eval_map]

/-- The actual proper plane-root equations derive both field hypotheses,
then yield the actual planar degree bound without circularity. -/
theorem finite_separable_finrank_le_planar_bound
    (p : ℕ) [CharP K p] (P Q : Polynomial (Polynomial K))
    (hirreducible : Irreducible P) (hpositive : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q) (hRdegree : P.natDegree < p)
    (hresultantDegree : (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
    (y r : E)
    (hgenerate : IntermediateField.adjoin K ({y, r} : Set E) = ⊤)
    (hP : planeEval K E y r P = 0) (hQ : planeEval K E y r Q = 0) :
    FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
      Module.finrank K E ≤ Q.natDegree * Polynomial.Bivariate.degreeX P +
        P.natDegree * Polynomial.Bivariate.degreeX Q := by
  have hPeval : Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap K E) y) r P = 0 := by
    rw [← planeEval_eq_eval₂]
    exact hP
  have hQeval : Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap K E) y) r Q = 0 := by
    rw [← planeEval_eq_eval₂]
    exact hQ
  have hfields := PlaneRootSeparability.finite_separable_of_proper_plane_roots
    p P Q hirreducible hpositive hproper hRdegree hresultantDegree y r hPeval hQeval hgenerate
  letI : FiniteDimensional K E := hfields.1
  letI : Algebra.IsSeparable K E := hfields.2
  exact ⟨hfields.1, hfields.2,
    PlaneFunctionFieldDegree.finrank_le_planar_bound K E P Q
      hirreducible hpositive hproper y r hgenerate hP hQ⟩

end SingleField

section FiniteFamily

variable (K : Type) [Field K]
variable {I : Type} [Fintype I] (E : I → Type)
  [∀ i, Field (E i)] [∀ i, Algebra K (E i)]

/-- Every component is proved finite and separable first. Distinct actual
relation kernels then put the sum of all degrees in one planar budget. -/
theorem finite_separable_sum_finrank_le_planar_bound
    (p : ℕ) [CharP K p] (P Q : Polynomial (Polynomial K))
    (hirreducible : Irreducible P) (hpositive : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q) (hRdegree : P.natDegree < p)
    (hresultantDegree : (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
    (y r : ∀ i, E i)
    (hgenerate : ∀ i, IntermediateField.adjoin K ({y i, r i} : Set (E i)) = ⊤)
    (hkernels : Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
    (hP : ∀ i, planeEval K (E i) (y i) (r i) P = 0)
    (hQ : ∀ i, planeEval K (E i) (y i) (r i) Q = 0) :
    (∀ i, FiniteDimensional K (E i) ∧ Algebra.IsSeparable K (E i)) ∧
      (∑ i, Module.finrank K (E i)) ≤
        Q.natDegree * Polynomial.Bivariate.degreeX P +
          P.natDegree * Polynomial.Bivariate.degreeX Q := by
  have hfields : ∀ i, FiniteDimensional K (E i) ∧ Algebra.IsSeparable K (E i) := by
    intro i
    have h := finite_separable_finrank_le_planar_bound K (E i)
      p P Q hirreducible hpositive hproper hRdegree hresultantDegree
      (y i) (r i) (hgenerate i) (hP i) (hQ i)
    exact ⟨h.1, h.2.1⟩
  letI : ∀ i, FiniteDimensional K (E i) := fun i => (hfields i).1
  letI : ∀ i, Algebra.IsSeparable K (E i) := fun i => (hfields i).2
  exact ⟨hfields,
    PlaneFunctionFieldDegree.sum_finrank_le_planar_bound K E P Q
      hirreducible hpositive hproper y r hgenerate hkernels hP hQ⟩

end FiniteFamily

end


end ProximityPrize.SubmissionLower.PlaneSmallCharacteristicDegree

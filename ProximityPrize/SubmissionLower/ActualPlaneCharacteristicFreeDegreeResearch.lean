import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CharacteristicFreeProjectionAdapter
import ProximityPrize.SubmissionLower.ActualPlanePositiveOrder

/-! .










 -/

namespace ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegreeResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateCaps ActualPlanePositiveOrder ActualPlaneCoordinateDegree
  CharacteristicFreeMatrixMultiplicityResearch
  CharacteristicFreeProjectionAdapter

noncomputable section

variable (K : Type) [Field K]

private def familyFiniteSummary {I : Type} [Fintype I]
    (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i))) (B : ℕ) : Prop :=
  letI := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B

theorem rationalBaseAlgebra_congr
    (P : Ideal (Original K)) [P.IsPrime]
    (i j : Fin 3) (hij : i = j)
    (hi : Transcendental K (coordinate K P i))
    (hj : Transcendental K (coordinate K P j)) :
    rationalBaseAlgebra K P i hi = rationalBaseAlgebra K P j hj := by
  subst j
  rfl

theorem plane_budget_le_original (order : Fin 3 ≃ Fin 3) (G H : Original K) :
    (planeMap K order H).natDegree *
          Polynomial.Bivariate.degreeX (planeMap K order G) +
        (planeMap K order G).natDegree *
          Polynomial.Bivariate.degreeX (planeMap K order H) ≤
      originalMixedDegree K order G H :=
  Nat.add_le_add
    (Nat.mul_le_mul (planeMap_natDegree_le K order H)
      (planeMap_degreeX_le K order G))
    (Nat.mul_le_mul (planeMap_natDegree_le K order G)
      (planeMap_degreeX_le K order H))

section FixedOrder

variable (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
variable (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

/-- .

 -/
theorem actual_finite_sum_finrank_bound_without_separability
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P) (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i)
    (hHmem : ∀ i, H ∈ P i) (hproper : ¬ G ∣ H)
    (hpositive : 0 < (planeMap K order G).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        (planeMap K order H).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K order G) +
          (planeMap K order G).natDegree *
            Polynomial.Bivariate.degreeX (planeMap K order H) := by
  classical
  letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
    fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    have hirr : Irreducible (planeMap K order G) :=
      planeMap_irreducible_of_component
        (K := K) (order := order) (P := P i₀) (ht := ht i₀)
          G hG (hGmem i₀)
    have hproperPlane : ¬ planeMap K order G ∣ planeMap K order H := by
      intro hdiv
      exact hproper ((planeMap_dvd_iff_of_component
        (K := K) (order := order) (P := P i₀) (ht := ht i₀)
          G H hG (hGmem i₀)).mp hdiv)
    have hGroots : ∀ i,
        PlaneFunctionFieldDegree.planeEval (RatFunc K)
          (CoordinateField K (P i))
          (coordinate K (P i) (order 2))
          (coordinate K (P i) (order 1)) (planeMap K order G) = 0 := by
      intro i
      change actualPlaneEvaluation K order (P i) (ht i)
        (planeMap K order G) = 0
      exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
    have hHroots : ∀ i,
        PlaneFunctionFieldDegree.planeEval (RatFunc K)
          (CoordinateField K (P i))
          (coordinate K (P i) (order 2))
          (coordinate K (P i) (order 1)) (planeMap K order H) = 0 := by
      intro i
      change actualPlaneEvaluation K order (P i) (ht i)
        (planeMap K order H) = 0
      exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
    have hfinite : ∀ i,
        FiniteDimensional (RatFunc K) (CoordinateField K (P i)) := by
      intro i
      have hGeval : Polynomial.eval₂
          (Polynomial.eval₂RingHom
            (algebraMap (RatFunc K) (CoordinateField K (P i)))
            (coordinate K (P i) (order 2)))
          (coordinate K (P i) (order 1)) (planeMap K order G) = 0 := by
        rw [← PlaneSmallCharacteristicDegree.planeEval_eq_eval₂]
        exact hGroots i
      have hHeval : Polynomial.eval₂
          (Polynomial.eval₂RingHom
            (algebraMap (RatFunc K) (CoordinateField K (P i)))
            (coordinate K (P i) (order 2)))
          (coordinate K (P i) (order 1)) (planeMap K order H) = 0 := by
        rw [← PlaneSmallCharacteristicDegree.planeEval_eq_eval₂]
        exact hHroots i
      exact finite_of_proper_plane_roots
        (planeMap K order G) (planeMap K order H)
        hirr hpositive hproperPlane
        (coordinate K (P i) (order 2))
        (coordinate K (P i) (order 1))
        hGeval hHeval (actual_generators K order (P i) (ht i))
    letI : ∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) :=
      hfinite
    have hkernels : Function.Injective (fun i =>
        PlaneFunctionFieldDegree.relationIdeal (RatFunc K)
          (CoordinateField K (P i))
          (coordinate K (P i) (order 2))
          (coordinate K (P i) (order 1))) := by
      change Function.Injective (fun i =>
        actualRelationKernel K order (P i) (ht i))
      exact actualRelationKernel_family_injective K order P ht hinj
    constructor
    · exact hfinite
    · exact sum_finrank_le_planar_bound_without_separability
        (K := RatFunc K) (I := I)
        (fun i => CoordinateField K (P i))
        (planeMap K order G) (planeMap K order H)
        hirr hpositive hproperPlane
        (fun i => coordinate K (P i) (order 2))
        (fun i => coordinate K (P i) (order 1))
        (fun i => actual_generators K order (P i) (ht i))
        hkernels hGroots hHroots
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

end FixedOrder

section OriginalOrder

variable (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
variable (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

/-- .

 -/
theorem original_finite_sum_finrank_bound_without_separability
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P) (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i)
    (hHmem : ∀ i, H ∈ P i) (hproper : ¬ G ∣ H) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        originalMixedDegree K order G H := by
  classical
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    obtain ⟨order', hor, hbase, hpositive⟩ :=
      exists_positive_outer_order K order (P i₀) G hG (hGmem i₀) (ht i₀)
    have hbudget : originalMixedDegree K order' G H =
        originalMixedDegree K order G H := by
      rcases hor with rfl | rfl
      · rfl
      · exact originalMixedDegree_swap K order G H
    have ht' : ∀ i,
        Transcendental K (coordinate K (P i) (order' 0)) := by
      intro i
      simpa only [hbase] using ht i
    have hresult :
        letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
          fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
        (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
          (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
            originalMixedDegree K order' G H := by
      letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
        fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
      obtain ⟨hfinite, hbound⟩ :=
        actual_finite_sum_finrank_bound_without_separability
          K order' P ht' hinj G H hG hGmem hHmem hproper hpositive
      exact ⟨hfinite, hbound.trans (plane_budget_le_original K order' G H)⟩
    have halg :
        (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)) =
          (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)) := by
      funext i
      exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
        hbase (ht' i) (ht i)
    change familyFiniteSummary K P
      (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
        (originalMixedDegree K order' G H) at hresult
    rw [halg, hbudget] at hresult
    exact hresult
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

end OriginalOrder

end


end ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegreeResearch

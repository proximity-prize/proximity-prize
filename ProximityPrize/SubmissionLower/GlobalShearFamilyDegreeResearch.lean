import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ArbitraryPlaneEvaluationFamilyResearch
import ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch
import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum

/-!
# One common shear and the full family S-degree budget

The component fields and prime ideals are never transported.  We evaluate a
single common sheared polynomial family at `(Y,S,Z)` inside each original
coordinate field.  Contraction along the common shear recovers each original
prime, so the characteristic-free plane-family theorem applies directly.
-/

namespace ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCoordinateDegreeSum TrivariateRationalCollection
  ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps ActualPlanePositiveOrder
  ActualPlaneCharacteristicFreeDegreeResearch
  ArbitraryRationalProjectionResearch TrivariateShearResearch
  GlobalShearZeroCountResearch ArbitraryPlaneEvaluationFamilyResearch

noncomputable section

set_option maxHeartbeats 1000000

variable (K : Type) [Field K]

/-- Order `(S,Y,Z)` in the plane collection. -/
def shearOrder : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

@[simp] theorem shearOrder_zero : shearOrder 0 = 1 := by
  simp [shearOrder]

@[simp] theorem shearOrder_one : shearOrder 1 = 0 := by
  simp [shearOrder]

@[simp] theorem shearOrder_two : shearOrder 2 = 2 := by
  simp [shearOrder, Equiv.swap_apply_def]

variable (P : Ideal (Original K)) [P.IsPrime]

/-- Evaluation at the unchanged field elements `(Y,R+aZ,Z)`. -/
def shearedEvaluation (a : K) : Original K →ₐ[K] CoordinateField K P :=
  MvPolynomial.aeval
    ![coordinate K P 0, shearedFieldCoordinate K P a, coordinate K P 2]

@[simp] theorem shearedEvaluation_X_zero (a : K) :
    shearedEvaluation K P a (MvPolynomial.X 0) = coordinate K P 0 := by
  simp [shearedEvaluation]

@[simp] theorem shearedEvaluation_X_one (a : K) :
    shearedEvaluation K P a (MvPolynomial.X 1) = shearedFieldCoordinate K P a := by
  simp [shearedEvaluation]

@[simp] theorem shearedEvaluation_X_two (a : K) :
    shearedEvaluation K P a (MvPolynomial.X 2) = coordinate K P 2 := by
  simp [shearedEvaluation]

/-- Evaluating after the common polynomial shear is the original coordinate
evaluation. -/
theorem shearedEvaluation_shear (a : K) (F : Original K) :
    shearedEvaluation K P a (shearAlgHom a F) = coordinateEvaluation K P F := by
  change MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P))
      ![coordinate K P 0,
        coordinate K P 1 + a • coordinate K P 2,
        coordinate K P 2] (shearAlgHom a F) = _
  rw [show a • coordinate K P 2 =
      algebraMap K (CoordinateField K P) a * coordinate K P 2 by
        simp [Algebra.smul_def],
    GlobalShearZeroCountResearch.eval₂Hom_shear_at_add]
  rw [coordinateEvaluation_eq_aeval]
  have hx : (![coordinate K P 0, coordinate K P 1, coordinate K P 2] :
      Fin 3 → CoordinateField K P) = coordinate K P := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact (MvPolynomial.aeval_eq_eval₂Hom (coordinate K P) F).symm

/-- Contracting the sheared evaluation kernel along the common automorphism
recovers the original prime. -/
theorem shearedEvaluation_kernel_contract (a : K) :
    (RingHom.ker (shearedEvaluation K P a).toRingHom).comap
        (shearAlgHom a).toRingHom = P := by
  rw [RingHom.comap_ker]
  have hcomp : (shearedEvaluation K P a).comp (shearAlgHom a) =
      coordinateEvaluation K P := by
    apply AlgHom.ext
    intro F
    exact shearedEvaluation_shear K P a F
  have hring := congrArg
    (fun f : Original K →ₐ[K] CoordinateField K P ↦ f.toRingHom) hcomp
  rw [show (shearedEvaluation K P a).toRingHom.comp (shearAlgHom a).toRingHom =
      (coordinateEvaluation K P).toRingHom from hring,
    coordinateEvaluation_ker]

/-- `Y,Z` generate the original coordinate field over the rational base
`K(R+aZ)`.  The missing coordinate is `R=S-aZ`. -/
theorem sheared_generators (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a)) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P)
        (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({coordinate K P 2, coordinate K P 0} : Set (CoordinateField K P)) = ⊤ := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P)
      (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) (CoordinateField K P) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      ((elementEmbedding K (CoordinateField K P)
        (shearedFieldCoordinate K P a) hS).commutes c).symm
  let S : IntermediateField (RatFunc K) (CoordinateField K P) :=
    IntermediateField.adjoin (RatFunc K) {coordinate K P 2, coordinate K P 0}
  have hZ : coordinate K P 2 ∈ S :=
    IntermediateField.mem_adjoin_pair_left (RatFunc K)
      (coordinate K P 2) (coordinate K P 0)
  have hY : coordinate K P 0 ∈ S :=
    IntermediateField.mem_adjoin_pair_right (RatFunc K)
      (coordinate K P 2) (coordinate K P 0)
  have hbase : shearedFieldCoordinate K P a ∈ S := by
    have h := S.algebraMap_mem
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
    change elementEmbedding K (CoordinateField K P)
      (shearedFieldCoordinate K P a) hS
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ∈ S at h
    rwa [elementEmbedding_variable] at h
  have ha : algebraMap K (CoordinateField K P) a ∈ S := by
    have h := S.algebraMap_mem (algebraMap K (RatFunc K) a)
    simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
      (CoordinateField K P)] using h
  have hR : coordinate K P 1 ∈ S := by
    have h := S.sub_mem hbase (S.mul_mem ha hZ)
    simpa only [shearedFieldCoordinate, Algebra.smul_def, add_sub_cancel_right] using h
  have hcoords : Set.range (coordinate K P) ⊆ S.restrictScalars K := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hY
    · exact hR
    · exact hZ
  have htop : S.restrictScalars K = ⊤ := by
    apply top_unique
    rw [← adjoin_coordinates_eq_top K P]
    exact IntermediateField.adjoin_le_iff.mpr hcoords
  exact (IntermediateField.restrictScalars_eq_top_iff (K := K)).mp htop

/-- Exact rectangular mixed-budget expansion under `R=S-aZ`. -/
theorem shear_mixedDegree_le (a : K) (G H : Original K) :
    originalMixedDegree K shearOrder (shearAlgHom a G) (shearAlgHom a H) ≤
      coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2 := by
  calc
    _ = (shearAlgHom a H).degreeOf 0 * (shearAlgHom a G).degreeOf 2 +
        (shearAlgHom a G).degreeOf 0 * (shearAlgHom a H).degreeOf 2 := by
      simp only [originalMixedDegree, shearOrder_one, shearOrder_two]
    _ ≤ H.degreeOf 0 * (G.degreeOf 2 + G.degreeOf 1) +
        G.degreeOf 0 * (H.degreeOf 2 + H.degreeOf 1) :=
      Nat.add_le_add
        (Nat.mul_le_mul (shear_degreeOf_zero_le a H) (shear_degreeOf_two_le a G))
        (Nat.mul_le_mul (shear_degreeOf_zero_le a G) (shear_degreeOf_two_le a H))
    _ = coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2 := by
      simp only [coordinateMixedDegree_one, coordinateMixedDegree_two]
      ring

section Family

variable {I : Type} [Fintype I]
variable (Q : I → Ideal (Original K)) [∀ i, (Q i).IsPrime]

private def familyDegreeSummary
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i))) (B : ℕ) : Prop :=
  letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ B

theorem shearedEvaluation_kernel_family_injective
    (hinj : Function.Injective Q) (a : K) :
    Function.Injective (fun i ↦
      RingHom.ker (shearedEvaluation K (Q i) a).toRingHom) := by
  intro i j hij
  apply hinj
  have hc := congrArg (Ideal.comap (shearAlgHom a).toRingHom) hij
  simpa only [shearedEvaluation_kernel_contract] using hc

/-- Fixed `(S,Y,Z)` ordering. -/
theorem finite_sum_shear_finrank_of_positive
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (shearedFieldCoordinate K (Q i) a))
    (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hHmem : ∀ i, H ∈ Q i)
    (hproper : ¬ G ∣ H)
    (hpositive : 0 < (planeMap K shearOrder (shearAlgHom a G)).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
      (elementEmbedding K (CoordinateField K (Q i))
        (shearedFieldCoordinate K (Q i) a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2 := by
  classical
  let e : ∀ i, Original K →ₐ[K] CoordinateField K (Q i) :=
    fun i ↦ shearedEvaluation K (Q i) a
  have ht : ∀ i, Transcendental K (e i (MvPolynomial.X (shearOrder 0))) := by
    intro i
    simpa only [e, shearOrder_zero, shearedEvaluation_X_one] using hS i
  let A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
    (elementEmbedding K (CoordinateField K (Q i))
      (e i (MvPolynomial.X (shearOrder 0))) (ht i)).toRingHom.toAlgebra
  let A' : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
    (elementEmbedding K (CoordinateField K (Q i))
      (shearedFieldCoordinate K (Q i) a) (hS i)).toRingHom.toAlgebra
  have halg : A = A' := by
    funext i
    simp only [A, A', e, shearOrder_zero, shearedEvaluation_X_one]
  have hgen :
      letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := A
      ∀ i, IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (shearOrder 2)),
          e i (MvPolynomial.X (shearOrder 1))} :
          Set (CoordinateField K (Q i))) = ⊤ := by
    rw [halg]
    intro i
    simpa only [e, shearOrder_zero, shearOrder_one, shearOrder_two,
      shearedEvaluation_X_zero, shearedEvaluation_X_one,
      shearedEvaluation_X_two] using sheared_generators K (Q i) a (hS i)
  have hGroot : ∀ i, e i (shearAlgHom a G) = 0 := by
    intro i
    rw [show e i (shearAlgHom a G) = coordinateEvaluation K (Q i) G from
      shearedEvaluation_shear K (Q i) a G]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hHroot : ∀ i, e i (shearAlgHom a H) = 0 := by
    intro i
    rw [show e i (shearAlgHom a H) = coordinateEvaluation K (Q i) H from
      shearedEvaluation_shear K (Q i) a H]
    change H ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hHmem i
  have hresult := finite_sum_finrank_bound K shearOrder
    (fun i ↦ CoordinateField K (Q i)) e ht hgen
    (shearedEvaluation_kernel_family_injective K Q hinj a)
    (shearAlgHom a G) (shearAlgHom a H)
    ((shear_irreducible_iff a G).mpr hG) hGroot hHroot
    (by simpa only [shear_dvd_iff] using hproper) hpositive
  have hpack : familyDegreeSummary K Q A
      (coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2) := by
    refine ⟨hresult.1, hresult.2.trans ?_⟩
    exact (plane_budget_le_original K shearOrder (shearAlgHom a G)
      (shearAlgHom a H)).trans (shear_mixedDegree_le K a G H)
  rw [halg] at hpack
  change familyDegreeSummary K Q A'
    (coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2)
  exact hpack

/-- The same bound when Z, rather than Y, is chosen as the positive outer
plane variable.  The rational base remains the identical common S. -/
theorem finite_sum_shear_finrank_of_swapped_positive
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (shearedFieldCoordinate K (Q i) a))
    (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hHmem : ∀ i, H ∈ Q i)
    (hproper : ¬ G ∣ H)
    (hpositive : 0 <
      (planeMap K (swapOtherOrder shearOrder) (shearAlgHom a G)).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
      (elementEmbedding K (CoordinateField K (Q i))
        (shearedFieldCoordinate K (Q i) a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2 := by
  classical
  let order' := swapOtherOrder shearOrder
  let e : ∀ i, Original K →ₐ[K] CoordinateField K (Q i) :=
    fun i ↦ shearedEvaluation K (Q i) a
  have ht : ∀ i, Transcendental K (e i (MvPolynomial.X (order' 0))) := by
    intro i
    simpa only [order', e, swapOtherOrder_zero, shearOrder_zero,
      shearedEvaluation_X_one] using hS i
  let A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
    (elementEmbedding K (CoordinateField K (Q i))
      (e i (MvPolynomial.X (order' 0))) (ht i)).toRingHom.toAlgebra
  let A' : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
    (elementEmbedding K (CoordinateField K (Q i))
      (shearedFieldCoordinate K (Q i) a) (hS i)).toRingHom.toAlgebra
  have halg : A = A' := by
    funext i
    simp only [A, A', order', e, swapOtherOrder_zero, shearOrder_zero,
      shearedEvaluation_X_one]
  have hgen :
      letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := A
      ∀ i, IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order' 2)),
          e i (MvPolynomial.X (order' 1))} :
          Set (CoordinateField K (Q i))) = ⊤ := by
    rw [halg]
    intro i
    have hg := sheared_generators K (Q i) a (hS i)
    rw [Set.pair_comm] at hg
    simpa only [order', e, swapOtherOrder_one, swapOtherOrder_two,
      shearOrder_one, shearOrder_two, shearedEvaluation_X_zero,
      shearedEvaluation_X_two] using hg
  have hGroot : ∀ i, e i (shearAlgHom a G) = 0 := by
    intro i
    rw [show e i (shearAlgHom a G) = coordinateEvaluation K (Q i) G from
      shearedEvaluation_shear K (Q i) a G]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hHroot : ∀ i, e i (shearAlgHom a H) = 0 := by
    intro i
    rw [show e i (shearAlgHom a H) = coordinateEvaluation K (Q i) H from
      shearedEvaluation_shear K (Q i) a H]
    change H ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hHmem i
  have hresult := finite_sum_finrank_bound K order'
    (fun i ↦ CoordinateField K (Q i)) e ht hgen
    (shearedEvaluation_kernel_family_injective K Q hinj a)
    (shearAlgHom a G) (shearAlgHom a H)
    ((shear_irreducible_iff a G).mpr hG) hGroot hHroot
    (by simpa only [shear_dvd_iff] using hproper) hpositive
  have hpack : familyDegreeSummary K Q A
      (coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2) := by
    refine ⟨hresult.1, hresult.2.trans ?_⟩
    exact (plane_budget_le_original K order' (shearAlgHom a G)
      (shearAlgHom a H)).trans ((originalMixedDegree_swap K shearOrder
        (shearAlgHom a G) (shearAlgHom a H)).le.trans
          (shear_mixedDegree_le K a G H))
  rw [halg] at hpack
  change familyDegreeSummary K Q A'
    (coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2)
  exact hpack

/-- Complete common-shear family theorem.  One of Y or Z is automatically a
positive outer variable because the localized common component equation is
irreducible and nonconstant. -/
theorem finite_sum_shear_finrank
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (shearedFieldCoordinate K (Q i) a))
    (G H : Original K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hHmem : ∀ i, H ∈ Q i)
    (hproper : ¬ G ∣ H) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) := fun i ↦
      (elementEmbedding K (CoordinateField K (Q i))
        (shearedFieldCoordinate K (Q i) a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        coordinateMixedDegree K G H 1 + coordinateMixedDegree K G H 2 := by
  classical
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    let e := shearedEvaluation K (Q i₀) a
    have ht : Transcendental K (e (MvPolynomial.X (shearOrder 0))) := by
      simpa only [e, shearOrder_zero, shearedEvaluation_X_one] using hS i₀
    have hroot : e (shearAlgHom a G) = 0 := by
      rw [show e (shearAlgHom a G) = coordinateEvaluation K (Q i₀) G from
        shearedEvaluation_shear K (Q i₀) a G]
      change G ∈ RingHom.ker (coordinateEvaluation K (Q i₀)).toRingHom
      rw [coordinateEvaluation_ker]
      exact hGmem i₀
    have hirr : Irreducible (rationalMap K shearOrder (shearAlgHom a G)) :=
      rationalMap_irreducible_of_evaluation K (CoordinateField K (Q i₀))
        shearOrder e (shearAlgHom a G) ((shear_irreducible_iff a G).mpr hG)
          hroot ht
    rcases positive_degree_of_irreducible
      (rationalMap K shearOrder (shearAlgHom a G)) hirr with hY | hZ
    · apply finite_sum_shear_finrank_of_positive K Q hinj a hS G H hG
        hGmem hHmem hproper
      change 0 < (bivariateEquiv (RatFunc K)
        (rationalMap K shearOrder (shearAlgHom a G))).natDegree
      rwa [bivariateEquiv_natDegree]
    · apply finite_sum_shear_finrank_of_swapped_positive K Q hinj a hS G H hG
        hGmem hHmem hproper
      rwa [swapped_outer_degree]
  · letI : IsEmpty I := ⟨fun i ↦ hI ⟨i⟩⟩
    exact ⟨fun i ↦ isEmptyElim i, by simp⟩

end Family

end

end ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch

#print axioms ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch.sheared_generators
#print axioms ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch.shear_mixedDegree_le
#print axioms ProximityPrize.SubmissionLower.GlobalShearFamilyDegreeResearch.finite_sum_shear_finrank

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ArbitraryPlaneEvaluationFamilyResearch
import ProximityPrize.SubmissionLower.ContactFunctionFieldTrdeg6731Research

/-! Two proper polynomial relations in three generators leave at most one
transcendental parameter. The proof is characteristic-free elimination. -/

namespace ProximityPrize.SubmissionLower.ContactTrivariateTrdeg6731Research

open TrivariateRationalCollection ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps
  ActualPlanePositiveOrder
  ArbitraryRationalProjectionResearch ArbitraryPlaneEvaluationFamilyResearch
  CharacteristicFreeMatrixMultiplicityResearch
  ContactFunctionFieldTrdeg6731Research

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]

set_option maxHeartbeats 1000000

theorem trdeg_le_one_of_generated_relations
    (v : Fin 3 → L)
    (hgen : IntermediateField.adjoin K (Set.range v) = ⊤)
    (F T : MvPolynomial (Fin 3) K)
    (hF : Irreducible F) (hproper : ¬ F ∣ T)
    (hFzero : MvPolynomial.aeval v F = 0)
    (hTzero : MvPolynomial.aeval v T = 0) : Algebra.trdeg K L ≤ 1 := by
  classical
  by_cases halg : ∀ i, IsAlgebraic K (v i)
  · have hA := IntermediateField.isAlgebraic_adjoin
      (K := K) (L := L) (S := Set.range v) (by
        rintro x ⟨i, rfl⟩
        exact isAlgebraic_iff_isIntegral.mp (halg i))
    rw [hgen] at hA
    letI := hA
    letI : Algebra.IsAlgebraic K L := (IntermediateField.topEquiv).isAlgebraic
    exact (trdeg_eq_zero (R := K) (A := L)).trans_le zero_le
  push Not at halg
  obtain ⟨i, hi⟩ := halg
  let e : Original K →ₐ[K] L := MvPolynomial.aeval v
  let initial : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have hi0 : initial 0 = i := Equiv.swap_apply_left _ _
  have ht0 : Transcendental K (e (MvPolynomial.X (initial 0))) := by
    simpa [e, hi0] using (show Transcendental K (v i) from hi)
  have hex : ∃ order : Fin 3 ≃ Fin 3,
      Transcendental K (e (MvPolynomial.X (order 0))) ∧
      0 < (planeMap K order F).natDegree := by
    have hirr := rationalMap_irreducible_of_evaluation K L initial e F hF hFzero ht0
    rcases positive_degree_of_irreducible (rationalMap K initial F) hirr with h0 | h1
    · refine ⟨initial, ht0, ?_⟩
      change 0 < (bivariateEquiv (RatFunc K) (rationalMap K initial F)).natDegree
      rwa [bivariateEquiv_natDegree]
    · exact ⟨swapOtherOrder initial, by simpa only [swapOtherOrder_zero] using ht0,
        by rwa [swapped_outer_degree]⟩
  obtain ⟨order, ht, hpositive⟩ := hex
  let base := elementEmbedding K L (e (MvPolynomial.X (order 0))) ht
  letI : Algebra (RatFunc K) L := base.toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (base.commutes c).symm
  have hpair : IntermediateField.adjoin (RatFunc K)
      ({e (MvPolynomial.X (order 2)), e (MvPolynomial.X (order 1))} : Set L) = ⊤ := by
    let S := IntermediateField.adjoin (RatFunc K)
      ({e (MvPolynomial.X (order 2)), e (MvPolynomial.X (order 1))} : Set L)
    have hcoords : Set.range v ⊆ S.restrictScalars K := by
      rintro x ⟨l, rfl⟩
      obtain ⟨j, rfl⟩ := order.surjective l
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl | rfl
      · have hm := S.algebraMap_mem
          (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
        change elementEmbedding K L _ ht _ ∈ S at hm
        rw [elementEmbedding_variable] at hm
        simpa [e] using hm
      · simpa [S, e] using IntermediateField.mem_adjoin_pair_right (RatFunc K)
          (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
      · simpa [S, e] using IntermediateField.mem_adjoin_pair_left (RatFunc K)
          (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
    have htop : S.restrictScalars K = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact IntermediateField.adjoin_le_iff.mpr hcoords
    exact (IntermediateField.restrictScalars_eq_top_iff (K := K)).mp htop
  have hroot (G : Original K) (hG : e G = 0) :
      Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (RatFunc K) L)
        (e (MvPolynomial.X (order 2))))
        (e (MvPolynomial.X (order 1))) (planeMap K order G) = 0 := by
    rw [← PlaneSmallCharacteristicDegree.planeEval_eq_eval₂]
    change planeEvaluation K L order e ht (planeMap K order G) = 0
    rw [← RingHom.comp_apply, planeEvaluation_comp_planeMap]
    exact hG
  have hirr := planeMap_irreducible_of_evaluation K L order e F hF hFzero ht
  have hproperPlane : ¬ planeMap K order F ∣ planeMap K order T := by
    intro h
    exact hproper ((planeMap_dvd_iff_of_evaluation K L order e F T hF hFzero ht).mp h)
  letI : FiniteDimensional (RatFunc K) L := finite_of_proper_plane_roots
    (planeMap K order F) (planeMap K order T) hirr hpositive hproperPlane
    (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
    (hroot F hFzero) (hroot T hTzero) hpair
  exact trdeg_le_one_of_functionField K L

/-- A proper pair of relations cuts the generated field to transcendence degree
at most one. No reducedness, normality, separability or characteristic gate is
needed beyond the stated irreducibility and properness. -/
theorem trdeg_adjoin_le_one_of_irreducible_proper_relations
    (v : Fin 3 → L) (F T : MvPolynomial (Fin 3) K)
    (hF : Irreducible F) (hproper : ¬ F ∣ T)
    (hFzero : MvPolynomial.aeval v F = 0)
    (hTzero : MvPolynomial.aeval v T = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range v)) ≤ 1 := by
  classical
  let E := IntermediateField.adjoin K (Set.range v)
  let vE : Fin 3 → E := fun i ↦ ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hgen : IntermediateField.adjoin K (Set.range vE) = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    have himage : E.val '' Set.range vE = Set.range v := by
      ext x
      simp [vE]
    rw [himage]
  have heval : E.val.comp (MvPolynomial.aeval vE) = MvPolynomial.aeval v := by
    ext i
    simp [vE]
  have hroot (G : MvPolynomial (Fin 3) K) (hG : MvPolynomial.aeval v G = 0) :
      MvPolynomial.aeval vE G = 0 := by
    apply E.val.injective
    change (E.val.comp (MvPolynomial.aeval vE)) G = E.val 0
    rw [heval, hG, map_zero]
  exact trdeg_le_one_of_generated_relations K E vE hgen F T hF hproper
    (hroot F hFzero) (hroot T hTzero)

end

end ProximityPrize.SubmissionLower.ContactTrivariateTrdeg6731Research

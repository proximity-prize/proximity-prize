import ProximityPrize.SubmissionLower.MovingSourceSlicePrimeFamily6814
namespace ProximityPrize.SubmissionLower.MovingSourceIndexedMovingCoordinates6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators WithZero
open RCN002 RCN022 RCN064 RCN095 RCN187 RCN207 RCN208 RCN212 RCN264 RCN295 RCN341 RCN344
open RCN184 RCN133 RCN114 RCN005 RCN006 RCN044 RCN037 RCN042 RCN035

variable {E I : Type} [Field E] [IsAlgClosed E] [Fintype I]
local notation "Poly" => MvPolynomial (Fin 3) E

private theorem field_eval (P : Ideal Poly) [P.IsPrime] (A : Poly) :
    MvPolynomial.eval₂Hom (algebraMap E (CoordinateField E P)) (coordinate E P) A=coordinateEvaluation E P A := by
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm

theorem exists_indexed_moving_coordinates
    (P : I → Ideal Poly) [∀ i,(P i).IsPrime]
    (base : ∀ i, SeparableLiteralCoordinate (P i)) (H G : Poly) :
    ∃ (Q A : Poly) (projection : ∀ i, SeparableCoordinate E (CoordinateField E (P i))),
      PolynomialInFlag (2 • unitAllFlag) Q ∧ PolynomialInFlag unitYZFlag A ∧
      ∀ i, A∉P i ∧
        SeparableCoordinate.value E (CoordinateField E (P i)) (projection i)=movingValue (P i) H G Q A ∧
        ∀ nu : RCN026.Place E (CoordinateField E (P i)),
          poleOrder nu.val (SeparableCoordinate.value E (CoordinateField E (P i)) (projection i))=
            movingPoleTarget (P i) H G nu := by
  obtain ⟨c,hc⟩ := exists_common_coefficients (K:=E)
    (fun i => CoordinateField E (P i)) (fun i => coordinate E (P i))
    (fun i => movingRatio (P i) H G) (fun i => (base i).index)
    (fun i => base_differential_ne_zero (base i))
    (fun i => movingRelevantPlaces (base i) (movingRatio (P i) H G))
  let Q := quadraticPolynomial c
  let A := linearPolynomial c
  have hJ (i : I) :
      coefficientEvaluation (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) movingSupport c=
        movingValue (P i) H G Q A := by
    rw [coefficientEvaluation_eq,field_eval,field_eval]
    simp only [movingValue,movingRatio,Q,A,mul_div_assoc]
  have hA (i : I) : coefficientEvaluation (coordinate E (P i)) linearSupport (restrictU c)=
      coordinateEvaluation E (P i) A := field_eval (P i) A
  have hx (i : I) := hc i
  simp only [hA,hJ] at hx
  have hnot (i : I) : A∉P i := by
    intro hh
    exact (hx i).1 ((SecondJetComponentRoots.evaluation_zero_iff (P i) A).mpr hh)
  have gate (i : I) := moving_projection_gate (base i) H G Q A (hx i).2.1
  let projection (i : I) : SeparableCoordinate E (CoordinateField E (P i)) := {
    embedding := elementEmbedding E (CoordinateField E (P i)) (movingValue (P i) H G Q A) (gate i).choose
    finite := (gate i).choose_spec.1
    separable := (gate i).choose_spec.2.1 }
  have hv (i : I) : SeparableCoordinate.value E (CoordinateField E (P i)) (projection i)=
      movingValue (P i) H G Q A := elementEmbedding_variable E (CoordinateField E (P i)) _ (gate i).choose
  refine ⟨Q,A,projection,quadraticPolynomial_inFlag c,linearPolynomial_inFlag c,fun i => ⟨hnot i,hv i,?_⟩⟩
  intro nu
  rw [hv]
  by_cases hn : nu∈movingRelevantPlaces (base i) (movingRatio (P i) H G)
  · exact poleOrder_eq_of_valuation_eq_exp nu.val _ _
      (by dsimp [movingPoleTarget,poleOrder]; positivity) ((hx i).2.2 nu hn).1
  · obtain ⟨hcoord,hw⟩ := outside_movingRelevantPlaces (base i) (movingRatio (P i) H G) nu hn
    have hz : exponentSetPoleWeight nu.val (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G)) movingSupport=0 := by
      rw [exponentSetPoleWeight_moving]
      simp [hcoord,hw]
    have hp := (poleOrder_eval_le_support nu.val (algebraMap E (CoordinateField E (P i)))
      (constant_value_le_one E (CoordinateField E (P i)) nu)
      (movingCoordinates (coordinate E (P i)) (movingRatio (P i) H G))
      (polynomialOfSupport movingSupport c)).trans
      (supportPoleWeight_le_exponentSetPoleWeight _ _ _ movingSupport (support_polynomialOfSupport_subset _ _))
    change poleOrder nu.val (coefficientEvaluation _ _ c)≤_ at hp
    rw [hJ i,hz] at hp
    have hp0 := le_antisymm hp (le_max_left _ _)
    simpa [movingPoleTarget,hcoord,hw] using hp0

end
end ProximityPrize.SubmissionLower.MovingSourceIndexedMovingCoordinates6814

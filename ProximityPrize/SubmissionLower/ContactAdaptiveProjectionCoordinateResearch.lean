import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveAffineProjectionResearch

/-! .

 -/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveProjectionCoordinateResearch

open scoped Classical TensorProduct
open Polynomial KaehlerDifferential
open CoordinateBoxZeroCount
open ArbitraryRationalProjectionResearch
open SeparableShearKaehlerResearch SeparableShearTranscendenceResearch
  GlobalSeparableShearResearch
open ContactWeakSeparableSeparatorResearch

noncomputable section

variable {K : Type} {L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]

/-- .
 -/
def coordinateOfGate (x : L)
    (hgate : ∀ hx : Transcendental K x,
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L)) : Coordinate K L :=
  if hx : Transcendental K x then
    Sum.inr {
      embedding := elementEmbedding K L x hx
      finite := (hgate hx).1
      separable := (hgate hx).2 }
  else
    Sum.inl ((eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose)

@[simp] theorem coordinateOfGate_value (x : L)
    (hgate : ∀ hx : Transcendental K x,
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L)) :
    coordinateValue K L (coordinateOfGate x hgate) = x := by
  unfold coordinateOfGate
  split_ifs with hx
  · exact elementEmbedding_variable K L x hx
  · exact (eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose_spec

@[simp] theorem coordinateOfGate_degree_of_transcendental (x : L)
    (hgate : ∀ hx : Transcendental K x,
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L))
    (hx : Transcendental K x) :
    coordinateDegree K L (coordinateOfGate x hgate) =
      (letI : Algebra (RatFunc K) L :=
        (elementEmbedding K L x hx).toRingHom.toAlgebra
       Module.finrank (RatFunc K) L) := by
  unfold coordinateOfGate coordinateDegree SeparableCoordinate.degree
  rw [dif_pos hx]
  rfl

@[simp] theorem coordinateOfGate_degree_of_isAlgebraic (x : L)
    (hgate : ∀ hx : Transcendental K x,
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L))
    (hx : IsAlgebraic K x) :
    coordinateDegree K L (coordinateOfGate x hgate) = 0 := by
  unfold coordinateOfGate coordinateDegree
  rw [dif_neg (fun htr => htr hx)]
  rfl

/-- .
 -/
theorem one_le_coordinateDegree_of_transcendental_value
    (c : Coordinate K L)
    (hc : Transcendental K (coordinateValue K L c)) :
    1 ≤ coordinateDegree K L c := by
  rcases c with a | c
  · exact (hc (isAlgebraic_algebraMap a)).elim
  · letI : Algebra (RatFunc K) L := c.embedding.toRingHom.toAlgebra
    letI : FiniteDimensional (RatFunc K) L := c.finite
    exact Module.finrank_pos

section FiniteFamily

variable {I : Type*} [Fintype I]
variable (E : I → Type) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]

/-- .
 -/
theorem sum_coordinateOfGate_degree_eq
    (x : ∀ i, E i)
    (hgate : ∀ i, ∀ hx : Transcendental K (x i),
      (letI : Algebra (RatFunc K) (E i) :=
          (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (E i)) ∧
      (letI : Algebra (RatFunc K) (E i) :=
          (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (E i))) :
    (∑ i, coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i))) =
      ∑ i : {i : I // Transcendental K (x i)},
        (letI : Algebra (RatFunc K) (E i.1) :=
          (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
         Module.finrank (RatFunc K) (E i.1)) := by
  classical
  let s : Set I := {i | Transcendental K (x i)}
  let degree : s → ℕ := fun i =>
    letI : Algebra (RatFunc K) (E i.1) :=
      (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
    Module.finrank (RatFunc K) (E i.1)
  apply Finset.sum_congr_set s
    (fun i => coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i))) degree
  · intro i hi
    exact coordinateOfGate_degree_of_transcendental (x i) (hgate i) hi
  · intro i hi
    exact coordinateOfGate_degree_of_isAlgebraic (x i) (hgate i) (not_not.mp hi)

end FiniteFamily

/-- . -/
def literalToSeparableCoordinate
    {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
    (D : SeparableLiteralCoordinate P) :
    SeparableCoordinate K (ActualCurveCoordinateField.CoordinateField K P) where
  embedding := ActualCurveRationalProjection.rationalBaseEmbedding
    K P D.index D.transcendental
  finite := D.finite
  separable := D.separable

@[simp] theorem literalToSeparableCoordinate_value
    {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
    (D : SeparableLiteralCoordinate P) :
    coordinateValue K (ActualCurveCoordinateField.CoordinateField K P)
        (Sum.inr (literalToSeparableCoordinate D)) =
      ActualCurveCoordinateField.coordinate K P D.index := by
  exact ActualCurveRationalProjection.rational_variable_image
    K P D.index D.transcendental

/-- .
 -/
theorem differential_ne_zero_of_gate (x : L)
    (hx : Transcendental K x)
    (hgate :
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L x hx).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L)) :
    D K L x ≠ 0 := by
  have h := parameterDifferential_ne_zero_of_isSeparable K L
    (elementEmbedding K L x hx) hgate.1 hgate.2
  unfold parameterDifferential at h
  rwa [elementEmbedding_variable] at h

end

end ProximityPrize.SubmissionLower.ContactAdaptiveProjectionCoordinateResearch

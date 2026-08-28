import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveUnitPoleFamilyResearch
import ProximityPrize.SubmissionLower.ContactAdaptiveRelevantPlacesResearch
import ProximityPrize.SubmissionLower.ContactFlagDirectionalAvoidance6543Research
import ProximityPrize.SubmissionLower.ContactFlagGlobalPoleProjection6543Research
import ProximityPrize.SubmissionLower.ContactFlagPrincipalCycles6543Research

/-!
# Adaptive nested flag projections for score 66

This is the geometric coefficient-choice core.  The normalization coordinate
may vary with the component; the two affine coefficients remain common.
-/

namespace ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research

open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactAdaptiveAffineProjectionResearch
open ContactAdaptiveRelevantPlacesResearch
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagGlobalPoleProjection6543Research
open ContactFlagDirectionalAvoidance6543Research
open ContactFlagPoleInequality6543Research
open ContactFlagPrincipalCycles6543Research
open ContactSparsePoleSupportResearch
open ArbitraryRationalProjectionResearch
open SeparableShearKaehlerResearch SeparableShearTranscendenceResearch
  GlobalSeparableShearResearch

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- Finite-separable gate for one literal coordinate, phrased through the
arbitrary-element embedding used by the adaptive affine theorem. -/
def LiteralProjectionGate
    (C : RegularComponent Omega G T H) (j : Fin 3) : Prop :=
  ∀ hj : Transcendental Omega (coordinate Omega C.1 j),
    (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)) ∧
    (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))

/-- The selected literal normalization has nonzero absolute differential. -/
theorem base_differential_ne_zero
    {P : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
    (B : SeparableLiteralCoordinate P) :
    D Omega (CoordinateField Omega P) (coordinate Omega P B.index) ≠ 0 := by
  have h := parameterDifferential_ne_zero_of_isSeparable Omega
    (CoordinateField Omega P)
    (rationalBaseEmbedding Omega P B.index B.transcendental)
    B.finite B.separable
  unfold SeparableShearKaehlerResearch.parameterDifferential at h
  have hvalue : rationalBaseEmbedding Omega P B.index B.transcendental
      (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X) =
        coordinate Omega P B.index :=
    (rationalBaseEmbedding_polynomial Omega P B.index B.transcendental
      Polynomial.X).trans (Polynomial.aeval_X _)
  rwa [hvalue] at h

/-- Algebraic functions on a curve over the algebraically closed base have
zero normalized pole order. -/
theorem poleOrder_eq_zero_of_isAlgebraic
    {L : Type*} [Field L] [Algebra Omega L]
    (v : CoordinatePoleMass.Place Omega L) (x : L)
    (hx : IsAlgebraic Omega x) :
    ContactLocalPoleBound.poleOrder v.val x = 0 := by
  obtain ⟨a, rfl⟩ := eq_algebraMap_of_isAlgebraic Omega L x hx
  exact CoordinatePoleMass.poleOrder_eq_zero_of_le_one Omega L v _
    (constant_value_le_one Omega L v a)

/-- Common nested projections with exact all-place pole maxima. -/
structure AdaptiveNestedProjectionData
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Omega G T H, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Omega G T H, LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) where
  lam : Omega
  lam_ne : lam ≠ 0
  mu : Omega
  mu_ne : mu ≠ 0
  uProjection : ∀ C : RegularComponent Omega G T H,
    Coordinate Omega (CoordinateField Omega C.1)
  allProjection : ∀ C : RegularComponent Omega G T H,
    Coordinate Omega (CoordinateField Omega C.1)
  uGate : ∀ C : RegularComponent Omega G T H,
    ∀ htr : Transcendental Omega (affineU Omega C.1 lam),
      (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
          (elementEmbedding Omega (CoordinateField Omega C.1)
            (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)) ∧
      (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
          (elementEmbedding Omega (CoordinateField Omega C.1)
            (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
  allAffineTranscendental : ∀ C : RegularComponent Omega G T H,
    Transcendental Omega (affineV Omega C.1 mu (mu * lam))
  allFinite : ∀ C : RegularComponent Omega G T H,
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
      (elementEmbedding Omega (CoordinateField Omega C.1)
        (affineV Omega C.1 mu (mu * lam))
        (allAffineTranscendental C)).toRingHom.toAlgebra
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
  allSeparable : ∀ C : RegularComponent Omega G T H,
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
      (elementEmbedding Omega (CoordinateField Omega C.1)
        (affineV Omega C.1 mu (mu * lam))
        (allAffineTranscendental C)).toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)
  uValue : ∀ C : RegularComponent Omega G T H,
    coordinateValue Omega (CoordinateField Omega C.1) (uProjection C) =
      affineU Omega C.1 lam
  allValue : ∀ C : RegularComponent Omega G T H,
    coordinateValue Omega (CoordinateField Omega C.1) (allProjection C) =
      affineV Omega C.1 mu (mu * lam)
  allTranscendental : ∀ C : RegularComponent Omega G T H,
    Transcendental Omega
      (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
  uPole : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    ContactLocalPoleBound.poleOrder v.val
        (coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)) =
      max (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 0))
        (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 2))
  allPole : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    ContactLocalPoleBound.poleOrder v.val
        (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C)) =
      max (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 1))
        (max (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 0))
          (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 2)))
  directional : MvPolynomial.pderiv (0 : Fin 3) G -
    MvPolynomial.C mu * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0

/-- Component-adaptive finite avoidance constructs both nested projections
and avoids the sole directional-derivative bad coefficient. -/
theorem exists_adaptiveNestedProjectionData
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Omega G T H, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Omega G T H, LiteralProjectionGate C 2)
    (hSderiv : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    Nonempty (AdaptiveNestedProjectionData base hY hZ hSderiv) := by
  classical
  let ActiveU := {C : RegularComponent Omega G T H //
    D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0}
  let EU : ActiveU → Type := fun C => CoordinateField Omega C.1.1
  let rY : ∀ C : ActiveU, EU C := fun C => coordinate Omega C.1.1 0
  let z : ∀ C : ActiveU, EU C := fun C => coordinate Omega C.1.1 2
  let WU : ∀ C : ActiveU, Finset (Place Omega (EU C)) :=
    fun C => literalRelevantPlaces (base C.1)
  let baseU : ∀ C : ActiveU, SeparableCoordinate Omega (EU C) :=
    fun C => literalToSeparableCoordinate (base C.1)
  obtain ⟨lam, hlam0, hlam⟩ :=
    exists_common_exact_finite_separable_affine_adaptive EU rY z WU
      baseU (fun C => C.2)
  let U : ∀ C : RegularComponent Omega G T H,
      CoordinateField Omega C.1 :=
    fun C => affineU Omega C.1 lam
  have hUgate : ∀ C : RegularComponent Omega G T H,
      ∀ htr : Transcendental Omega (U C),
        (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
            (elementEmbedding Omega (CoordinateField Omega C.1)
              (U C) htr).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)) ∧
        (letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
            (elementEmbedding Omega (CoordinateField Omega C.1)
              (U C) htr).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)) := by
    intro C htr
    by_cases hactive :
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
          D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0
    · let CU : ActiveU := ⟨C, hactive⟩
      obtain ⟨hs, hfinite, hsep, _⟩ := hlam CU
      have hp : htr = hs := Subsingleton.elim _ _
      cases hp
      exact ⟨hfinite, hsep⟩
    · have hzero := not_or.mp hactive
      have hYalg : IsAlgebraic Omega (coordinate Omega C.1 0) := by
        apply not_not.mp
        intro hy
        exact (differential_ne_zero_of_gate _ hy (hY C hy))
          (not_ne_iff.mp hzero.1)
      have hZalg : IsAlgebraic Omega (coordinate Omega C.1 2) := by
        apply not_not.mp
        intro hz
        exact (differential_ne_zero_of_gate _ hz (hZ C hz))
          (not_ne_iff.mp hzero.2)
      exact (htr (hYalg.add (hZalg.smul lam))).elim
  let uProjection : ∀ C : RegularComponent Omega G T H,
      Coordinate Omega (CoordinateField Omega C.1) :=
    fun C => coordinateOfGate (U C) (hUgate C)
  have huValue : ∀ C : RegularComponent Omega G T H,
      coordinateValue Omega (CoordinateField Omega C.1) (uProjection C) = U C :=
    fun C => coordinateOfGate_value (U C) (hUgate C)
  have huPole : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
      ContactLocalPoleBound.poleOrder v.val (U C) =
        max (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 0))
          (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 2)) := by
    intro C v
    by_cases hactive :
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
          D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0
    · let CU : ActiveU := ⟨C, hactive⟩
      by_cases hv : v ∈ literalRelevantPlaces (base C)
      · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
          simpa only [WU, rY, z, U, affineU] using
            (hlam CU).choose_spec.2.2 v hv)
      · have h0 := coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
            (base C) v hv 0
        have h2 := coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
            (base C) v hv 2
        have h0le := valuation_le_one_of_poleOrder_eq_zero v.val _ h0
        have h2le := valuation_le_one_of_poleOrder_eq_zero v.val _ h2
        letI : v.val.IsTrivialOn Omega := v.property.2
        have hscalar : v.val (lam • coordinate Omega C.1 2) =
            v.val (coordinate Omega C.1 2) := by
          rw [Algebra.smul_def, map_mul,
            Valuation.IsTrivialOn.eq_one lam hlam0, one_mul]
        have hUle : v.val (U C) ≤ 1 := by
          exact (v.val.map_add _ _).trans
            (by rw [hscalar]; exact max_le h0le h2le)
        have hU0 : ContactLocalPoleBound.poleOrder v.val (U C) = 0 :=
          CoordinatePoleMass.poleOrder_eq_zero_of_le_one Omega
            (CoordinateField Omega C.1) v _ hUle
        rw [hU0, h0, h2]
        simp
    · have hzero := not_or.mp hactive
      have hYalg : IsAlgebraic Omega (coordinate Omega C.1 0) := by
        apply not_not.mp
        intro hy
        exact (differential_ne_zero_of_gate _ hy (hY C hy))
          (not_ne_iff.mp hzero.1)
      have hZalg : IsAlgebraic Omega (coordinate Omega C.1 2) := by
        apply not_not.mp
        intro hz
        exact (differential_ne_zero_of_gate _ hz (hZ C hz))
          (not_ne_iff.mp hzero.2)
      have hUalg : IsAlgebraic Omega (U C) := hYalg.add (hZalg.smul lam)
      rw [poleOrder_eq_zero_of_isAlgebraic v _ hUalg,
        poleOrder_eq_zero_of_isAlgebraic v _ hYalg,
        poleOrder_eq_zero_of_isAlgebraic v _ hZalg]
      simp
  have hactiveV : ∀ C : RegularComponent Omega G T H,
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 1) ≠ 0 ∨
        D Omega (CoordinateField Omega C.1) (U C) ≠ 0 := by
    intro C
    by_cases hactive :
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0) ≠ 0 ∨
          D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2) ≠ 0
    · let CU : ActiveU := ⟨C, hactive⟩
      obtain ⟨hs, hfinite, hsep, _⟩ := hlam CU
      exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite, hsep⟩)
    · have hzero := not_or.mp hactive
      have hb := base_differential_ne_zero (base C)
      generalize hidx : (base C).index = i at hb
      fin_cases i
      · exact (hb (not_ne_iff.mp hzero.1)).elim
      · exact Or.inl hb
      · exact (hb (not_ne_iff.mp hzero.2)).elim
  let EC : RegularComponent Omega G T H → Type :=
    fun C => CoordinateField Omega C.1
  let rS : ∀ C, EC C := fun C => coordinate Omega C.1 1
  let W : ∀ C, Finset (Place Omega (EC C)) :=
    fun C => literalRelevantPlaces (base C)
  let baseC : ∀ C, SeparableCoordinate Omega (EC C) :=
    fun C => literalToSeparableCoordinate (base C)
  let Extra : Omega → Prop := fun mu =>
    MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C mu * MvPolynomial.pderiv (1 : Fin 3) G = 0
  have hextra : ∀ {a b}, Extra a → Extra b → a = b := by
    exact directional_bad_coefficient_subsingleton G hSderiv
  obtain ⟨mu, hmu0, hmudir, hmu⟩ :=
    exists_common_exact_finite_separable_affine_adaptive_avoiding_one
      EC rS U W Extra hextra baseC hactiveV
  let V : ∀ C : RegularComponent Omega G T H,
      CoordinateField Omega C.1 :=
    fun C => coordinate Omega C.1 1 + mu • U C
  let hV : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (V C) := fun C => (hmu C).choose
  let vProjection : ∀ C : RegularComponent Omega G T H,
      Coordinate Omega (CoordinateField Omega C.1) := fun C => Sum.inr {
    embedding := elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C)
    finite := (hmu C).choose_spec.1
    separable := (hmu C).choose_spec.2.1 }
  have hvValue : ∀ C : RegularComponent Omega G T H,
      coordinateValue Omega (CoordinateField Omega C.1) (vProjection C) = V C := by
    intro C
    exact elementEmbedding_variable Omega (CoordinateField Omega C.1) (V C) (hV C)
  have hvPole : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
      ContactLocalPoleBound.poleOrder v.val (V C) =
        max (ContactLocalPoleBound.poleOrder v.val (coordinate Omega C.1 1))
          (ContactLocalPoleBound.poleOrder v.val (U C)) := by
    intro C v
    by_cases hv : v ∈ literalRelevantPlaces (base C)
    · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
        simpa only [W, rS, V] using (hmu C).choose_spec.2.2 v hv)
    · have hS := coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
          (base C) v hv 1
      have hY := coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
          (base C) v hv 0
      have hZ := coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
          (base C) v hv 2
      have hU : ContactLocalPoleBound.poleOrder v.val (U C) = 0 := by
        rw [huPole C v, hY, hZ]
        simp
      have hSle := valuation_le_one_of_poleOrder_eq_zero v.val _ hS
      have hUle := valuation_le_one_of_poleOrder_eq_zero v.val _ hU
      letI : v.val.IsTrivialOn Omega := v.property.2
      have hscalar : v.val (mu • U C) = v.val (U C) := by
        rw [Algebra.smul_def, map_mul,
          Valuation.IsTrivialOn.eq_one mu hmu0, one_mul]
      have hVle : v.val (V C) ≤ 1 :=
        (v.val.map_add _ _).trans
          (by rw [hscalar]; exact max_le hSle hUle)
      have hV0 : ContactLocalPoleBound.poleOrder v.val (V C) = 0 :=
        CoordinatePoleMass.poleOrder_eq_zero_of_le_one Omega
          (CoordinateField Omega C.1) v _ hVle
      rw [hV0, hS, hU]
      simp
  let hVAff : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (affineV Omega C.1 mu (mu * lam)) := fun C => by
    rw [show affineV Omega C.1 mu (mu * lam) = V C by
      simp only [V, U, affineU, affineV]
      module]
    exact hV C
  have hembV (C : RegularComponent Omega G T H) :
      elementEmbedding Omega (CoordinateField Omega C.1)
          (affineV Omega C.1 mu (mu * lam)) (hVAff C) =
        elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C) :=
    elementEmbedding_congr (hVAff C) (hV C) (by
      simp only [V, U, affineU, affineV]
      simp only [smul_add, smul_smul, add_assoc])
  refine ⟨{
    lam := lam
    lam_ne := hlam0
    mu := mu
    mu_ne := hmu0
    uProjection := uProjection
    allProjection := vProjection
    uGate := hUgate
    allAffineTranscendental := hVAff
    allFinite := ?_
    allSeparable := ?_
    uValue := huValue
    allValue := ?_
    allTranscendental := ?_
    uPole := ?_
    allPole := ?_
    directional := hmudir }⟩
  · intro C
    rw [hembV C]
    exact (hmu C).choose_spec.1
  · intro C
    rw [hembV C]
    exact (hmu C).choose_spec.2.1
  · intro C
    rw [hvValue C]
    simp only [V, U, affineU, affineV]
    simp only [smul_add, smul_smul, add_assoc]
  · intro C
    rw [hvValue C]
    exact hV C
  · intro C v
    rw [huValue C]
    exact huPole C v
  · intro C v
    rw [hvValue C, hvPole C v, huPole C v]

end

end ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research

#print axioms ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research.exists_adaptiveNestedProjectionData

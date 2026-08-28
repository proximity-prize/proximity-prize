import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactLeadingCancellationResearch
import ProximityPrize.SubmissionLower.ContactTropicalBKKSeamResearch

/-! .


















 -/

namespace ProximityPrize.SubmissionLower.ContactDependentGenericity6543Research

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ContactLocalPoleBound
open ContactGenericCoefficientAvoidanceResearch
open ContactLeadingCancellationResearch
open ContactSparsePoleSupportResearch
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount
open ContactRegularComponentCover
open ContactResidualSparsePoleProviderResearch
open ContactTropicalBKKSeamResearch

noncomputable section

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

/-- .

 -/
def componentRelevantPlaces
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (C : RegularComponent Ω G T H) :
    Finset (Place Ω (CoordinateField Ω C.1)) := by
  classical
  let htr := hseparator C
  letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
    quotientPolynomialAlgebra Ω C.1 separator
  letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
    polynomialBaseAlgebra Ω C.1 separator
  letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
    rationalBaseAlgebra Ω C.1 separator htr
  letI := quotientBaseScalarTower Ω C.1 separator
  letI := polynomialBaseScalarTower Ω C.1 separator
  letI := quotientFractionScalarTower Ω C.1 separator
  letI := polynomialRationalScalarTower Ω C.1 separator htr
  letI := rationalBaseScalarTower Ω C.1 separator htr
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).1
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).2
  exact Finset.univ.biUnion (fun i : Fin 3 ↦
    if hi : coordinate Ω C.1 i ≠ 0 then
      CommonPlaceBalance.placesFor Ω (CoordinateField Ω C.1)
        (coordinate Ω C.1 i) hi
    else ∅)

/-- . -/
theorem coordinate_poleOrder_eq_zero_of_not_mem_relevant
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (C : RegularComponent Ω G T H)
    (v : Place Ω (CoordinateField Ω C.1))
    (hv : v ∉ componentRelevantPlaces hseparator hproj C) (i : Fin 3) :
    poleOrder v.val (coordinate Ω C.1 i) = 0 := by
  classical
  let htr := hseparator C
  letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
    quotientPolynomialAlgebra Ω C.1 separator
  letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
    polynomialBaseAlgebra Ω C.1 separator
  letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
    rationalBaseAlgebra Ω C.1 separator htr
  letI := quotientBaseScalarTower Ω C.1 separator
  letI := polynomialBaseScalarTower Ω C.1 separator
  letI := quotientFractionScalarTower Ω C.1 separator
  letI := polynomialRationalScalarTower Ω C.1 separator htr
  letI := rationalBaseScalarTower Ω C.1 separator htr
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).1
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).2
  by_cases hi : coordinate Ω C.1 i = 0
  · simp [hi, poleOrder]
  · have hnot : v ∉ CommonPlaceBalance.placesFor Ω
        (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi := by
      intro hmem
      apply hv
      unfold componentRelevantPlaces
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simp [hi, hmem]⟩
    have horder : CommonPlaceBalance.order Ω (CoordinateField Ω C.1) v
        (coordinate Ω C.1 i) = 0 := by
      by_contra hne
      exact hnot (CommonPlaceBalance.placesFor_covers Ω
        (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi v hne)
    unfold CommonPlaceBalance.order at horder
    unfold poleOrder
    have hlog : (v.val (coordinate Ω C.1 i)).log = 0 := by omega
    rw [hlog]
    simp

/-- .
 -/
theorem exponentSetPoleWeight_eq_zero_of_not_mem_relevant
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (E : Finset (Fin 3 →₀ ℕ))
    (C : RegularComponent Ω G T H)
    (v : Place Ω (CoordinateField Ω C.1))
    (hv : v ∉ componentRelevantPlaces hseparator hproj C) :
    exponentSetPoleWeight v.val (coordinate Ω C.1) E = 0 := by
  classical
  have hcoord : ∀ i : Fin 3,
      poleOrder v.val (coordinate Ω C.1 i) = 0 :=
    coordinate_poleOrder_eq_zero_of_not_mem_relevant
      hseparator hproj C v hv
  unfold exponentSetPoleWeight exponentPoleWeight
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    obtain rfl | hz := Finset.mem_insert.mp hz
    · exact le_rfl
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
      simp [hcoord]
  · exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)

/-- . -/
abbrev RelevantPlaceIndex
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1) :=
  Σ C : RegularComponent Ω G T H,
    {v : Place Ω (CoordinateField Ω C.1) //
      v ∈ componentRelevantPlaces hseparator hproj C}

/-- .
 -/
abbrev DependentGenericityIndex
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1) :=
  RegularComponent Ω G T H ⊕ RelevantPlaceIndex hseparator hproj

def dependentBadSubmodule
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (E : Finset (Fin 3 →₀ ℕ)) :
    DependentGenericityIndex hseparator hproj → Submodule Ω (E → Ω)
  | Sum.inl C => LinearMap.ker (coefficientEvaluation (coordinate Ω C.1) E)
  | Sum.inr ⟨C, v⟩ => cancellationSubmodule v.1.val
      (fun a ↦ constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
      (coordinate Ω C.1) E

theorem dependentBadSubmodule_ne_top
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (E : Finset (Fin 3 →₀ ℕ))
    (hdown : ExponentSetDownwardClosed E) (hzero : 0 ∈ E) :
    ∀ j : DependentGenericityIndex hseparator hproj,
      dependentBadSubmodule hseparator hproj E j ≠ ⊤ := by
  classical
  intro j
  rcases j with C | ⟨C, v⟩
  · intro htop
    let e0 : E := ⟨0, hzero⟩
    let c0 : E → Ω := deltaCoefficient E e0
    have hc0 : c0 ∈ dependentBadSubmodule hseparator hproj E (Sum.inl C) := by
      rw [htop]
      trivial
    have hzeroeval : coefficientEvaluation (coordinate Ω C.1) E c0 = 0 := by
      exact LinearMap.mem_ker.mp hc0
    have honeeval : coefficientEvaluation (coordinate Ω C.1) E c0 = 1 := by
      rw [coefficientEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
        polynomialOfSupport_deltaCoefficient]
      simp [e0]
    rw [honeeval] at hzeroeval
    exact one_ne_zero hzeroeval
  · obtain ⟨c, hc⟩ :=
      exists_exact_support_evaluation_of_downwardClosed
        (K := Ω) (L := CoordinateField Ω C.1) (σ := Fin 3)
        v.1.val (coordinate Ω C.1) E hdown hzero
    exact cancellationSubmodule_ne_top_of_exact v.1.val
      (fun a ↦ constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
      (coordinate Ω C.1) E c hc

/-- .
 -/
structure GenericExactPolePolynomial
    (G T H : MvPolynomial (Fin 3) Ω)
    (E : Finset (Fin 3 →₀ ℕ)) (separator : Fin 3)
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1) where
  polynomial : MvPolynomial (Fin 3) Ω
  support_subset : polynomial.support ⊆ E
  proper : ∀ C : RegularComponent Ω G T H, polynomial ∉ C.1
  exact_pole : ∀ C : RegularComponent Ω G T H,
    let htr := hseparator C
    letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
      quotientPolynomialAlgebra Ω C.1 separator
    letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
      polynomialBaseAlgebra Ω C.1 separator
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      rationalBaseAlgebra Ω C.1 separator htr
    letI := quotientBaseScalarTower Ω C.1 separator
    letI := polynomialBaseScalarTower Ω C.1 separator
    letI := quotientFractionScalarTower Ω C.1 separator
    letI := polynomialRationalScalarTower Ω C.1 separator htr
    letI := rationalBaseScalarTower Ω C.1 separator htr
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).1
    letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).2
    ∀ v : Place Ω (CoordinateField Ω C.1),
      poleOrder v.val
          (MvPolynomial.eval₂Hom
            (algebraMap Ω (CoordinateField Ω C.1))
            (coordinate Ω C.1) polynomial) =
        exponentSetPoleWeight v.val (coordinate Ω C.1) E

theorem exists_genericExactPolePolynomial
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (E : Finset (Fin 3 →₀ ℕ))
    (hdown : ExponentSetDownwardClosed E) (hzero : 0 ∈ E) :
    Nonempty (GenericExactPolePolynomial G T H E separator
      hseparator hproj) := by
  classical
  let bad := dependentBadSubmodule hseparator hproj E
  obtain ⟨c, hc⟩ := exists_avoiding_finite_proper_submodules bad
    (dependentBadSubmodule_ne_top hseparator hproj E hdown hzero)
  let B := polynomialOfSupport E c
  have hsupport : B.support ⊆ E := support_polynomialOfSupport_subset E c
  have hproper : ∀ C : RegularComponent Ω G T H, B ∉ C.1 := by
    intro C hmem
    apply hc (Sum.inl C)
    change c ∈ LinearMap.ker
      (coefficientEvaluation (coordinate Ω C.1) E)
    rw [LinearMap.mem_ker]
    have hker : B ∈ RingHom.ker
        (MvPolynomial.aeval (coordinate Ω C.1)).toRingHom := by
      rw [aeval_coordinate_ker]
      exact hmem
    have hz := RingHom.mem_ker.mp hker
    change MvPolynomial.aeval (coordinate Ω C.1) B = 0 at hz
    rw [MvPolynomial.aeval_eq_eval₂Hom] at hz
    change MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) B = 0
    exact hz
  refine ⟨⟨B, hsupport, hproper, ?_⟩⟩
  intro C
  dsimp only
  let htr := hseparator C
  letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
    quotientPolynomialAlgebra Ω C.1 separator
  letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
    polynomialBaseAlgebra Ω C.1 separator
  letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
    rationalBaseAlgebra Ω C.1 separator htr
  letI := quotientBaseScalarTower Ω C.1 separator
  letI := polynomialBaseScalarTower Ω C.1 separator
  letI := quotientFractionScalarTower Ω C.1 separator
  letI := polynomialRationalScalarTower Ω C.1 separator htr
  letI := rationalBaseScalarTower Ω C.1 separator htr
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).1
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
    (hproj C separator htr).2
  intro v
  by_cases hv : v ∈ componentRelevantPlaces hseparator hproj C
  · have havoid := hc (Sum.inr ⟨C, ⟨v, hv⟩⟩)
    change ¬v.val (coefficientEvaluation (coordinate Ω C.1) E c) <
      WithZero.exp (exponentSetPoleWeight v.val (coordinate Ω C.1) E) at havoid
    have hlower : WithZero.exp
        (exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
        v.val (coefficientEvaluation (coordinate Ω C.1) E c) :=
      le_of_not_gt havoid
    have hupper : v.val (coefficientEvaluation (coordinate Ω C.1) E c) ≤
        WithZero.exp
          (exponentSetPoleWeight v.val (coordinate Ω C.1) E) :=
      valuation_eval_le_exp_exponentSet v.val (algebraMap Ω _)
        (fun a ↦ constant_value_le_one Ω (CoordinateField Ω C.1) v a)
        (coordinate Ω C.1) E B hsupport
    exact poleOrder_eq_of_valuation_eq_exp v.val _ _
      (ContactLeadingCancellationResearch.exponentSetPoleWeight_nonneg
        v.val (coordinate Ω C.1) E)
      (le_antisymm hupper hlower)
  · have hweight : exponentSetPoleWeight v.val (coordinate Ω C.1) E = 0 :=
      exponentSetPoleWeight_eq_zero_of_not_mem_relevant
        hseparator hproj E C v hv
    have hle : poleOrder v.val
        (MvPolynomial.eval₂Hom
          (algebraMap Ω (CoordinateField Ω C.1))
          (coordinate Ω C.1) B) ≤
        exponentSetPoleWeight v.val (coordinate Ω C.1) E :=
      (poleOrder_eval_le_support v.val (algebraMap Ω _)
        (fun a ↦ constant_value_le_one Ω (CoordinateField Ω C.1) v a)
        (coordinate Ω C.1) B).trans
      (supportPoleWeight_le_exponentSetPoleWeight v.val
        (coordinate Ω C.1) B E hsupport)
    rw [hweight] at hle ⊢
    exact le_antisymm hle (by unfold poleOrder; exact le_max_left _ _)

/-- .
 -/
def GenericExactPolePolynomial.toGenericSparseBKKWitness
    {G T H : MvPolynomial (Fin 3) Ω}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3} {wholeCost : ℕ}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    (B : GenericExactPolePolynomial G T H E separator hseparator hproj)
    (cost : RegularComponent Ω G T H → ℕ)
    (cycle_le : ∀ C : RegularComponent Ω G T H,
      let htr := hseparator C
      letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
        quotientPolynomialAlgebra Ω C.1 separator
      letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
        polynomialBaseAlgebra Ω C.1 separator
      letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
        rationalBaseAlgebra Ω C.1 separator htr
      letI := quotientBaseScalarTower Ω C.1 separator
      letI := polynomialBaseScalarTower Ω C.1 separator
      letI := quotientFractionScalarTower Ω C.1 separator
      letI := polynomialRationalScalarTower Ω C.1 separator htr
      letI := rationalBaseScalarTower Ω C.1 separator htr
      letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
        (hproj C separator htr).1
      letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
        (hproj C separator htr).2
      let b := MvPolynomial.eval₂Hom
        (algebraMap Ω (CoordinateField Ω C.1))
        (coordinate Ω C.1) B.polynomial
      let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem
        C.1 B.polynomial (B.proper C)
      (∑ v ∈ CommonPlaceBalance.placesFor Ω
          (CoordinateField Ω C.1) b hb,
        CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
          (cost C : ℤ))
    (sum_cost_le : (∑ C : RegularComponent Ω G T H, cost C) ≤ wholeCost) :
    GenericSparseBKKWitness G T H E separator wholeCost hseparator hproj where
  polynomial := B.polynomial
  support_subset := B.support_subset
  proper := B.proper
  cost := cost
  exact_pole := B.exact_pole
  cycle_le := cycle_le
  sum_cost_le := sum_cost_le

end

end ProximityPrize.SubmissionLower.ContactDependentGenericity6543Research

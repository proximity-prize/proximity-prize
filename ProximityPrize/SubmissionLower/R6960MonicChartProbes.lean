import ProximityPrize.SubmissionLower.R6960MonicFourChartDescent
import ProximityPrize.SubmissionLower.R6960ChartTraceTests
import Mathlib.Algebra.Field.Subfield.Basic

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.MonicChartProbes
noncomputable section
open Polynomial
open K1_14 (L)
open MonicChart (ChartField Scalar)
open PlaneConstants (Plane)
open ChartSections (Chart)
open MonicFourChartDescent (baseChart chartCoordinate constants scalarCoordinate)
open RetainedCompression (Curve ordinate view)
open scoped Polynomial Lower6960.MonicChart
open Lower6960.MonicChart (root_finrank)

private def generators (s : Chart) : Set ChartField :=
  Set.range constants ∪ {chartCoordinate s.1 RatFunc.X, chartCoordinate s.2 scalarCoordinate}

private abbrev scalarX : Scalar := algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L))

private abbrev scalarConstants : L →+* Scalar := (algebraMap (Polynomial L) Scalar).comp Polynomial.C

private def scalarEval (inverse : Bool) : (Polynomial L) →+* Scalar :=
  Polynomial.eval₂RingHom scalarConstants (if inverse then scalarX⁻¹ else scalarX)

private def abscissaEval (inverse : Bool) : (Polynomial Scalar) →+* ChartField :=
  Polynomial.eval₂RingHom RatFunc.C (chartCoordinate inverse RatFunc.X)

/-- Evaluate the two polynomial variables independently in the chosen
abscissa and scalar coordinates of the actual chart. -/
def planeMap (s : Chart) : Plane L →+* ChartField :=
  (abscissaEval s.1).comp (Polynomial.mapRingHom (scalarEval s.2))

private theorem scalarEval_finite : scalarEval false = algebraMap (Polynomial L) Scalar := by
  apply Polynomial.ringHom_ext
  · intro c
    exact eval₂_C _ _
  · exact eval₂_X _ _

private theorem abscissaEval_finite : abscissaEval false = algebraMap (Polynomial Scalar) ChartField := by
  apply Polynomial.ringHom_ext
  · intro c
    exact (eval₂_C _ _).trans (RatFunc.algebraMap_C c).symm
  · exact (eval₂_X _ _).trans RatFunc.algebraMap_X.symm

private theorem scalarEval_injective (s : Bool) : Function.Injective (scalarEval s) := by
  let : Algebra L Scalar := scalarConstants.toAlgebra
  have trans : Transcendental L scalarX := transcendental_iff_injective.mpr (by
    change Function.Injective (scalarEval false)
    rw [scalarEval_finite]
    exact IsFractionRing.injective (Polynomial L) Scalar)
  cases s with
  | false => exact transcendental_iff_injective.mp trans
  | true =>
    have inv : Transcendental L (scalarX⁻¹) := by
      simpa only [Transcendental,IsAlgebraic.inv_iff] using trans
    exact transcendental_iff_injective.mp inv

private theorem abscissaEval_injective (s : Bool) : Function.Injective (abscissaEval s) := by
  cases s with
  | false => rw [abscissaEval_finite]; exact IsFractionRing.injective _ _
  | true => exact MonicChart.atInfinity_injective (K:=Scalar)

theorem planeMap_injective (s : Chart) : Function.Injective (planeMap s) :=
  (abscissaEval_injective s.1).comp (Polynomial.map_injective _ (scalarEval_injective s.2))

theorem planeMap_finite : planeMap (false,false) = algebraMap (Plane L) ChartField := by
  rw [planeMap,abscissaEval_finite,scalarEval_finite]
  rfl

@[simp] theorem planeMap_constants (s : Chart) (c : L) : planeMap s (C (C c)) = constants c := by
  change abscissaEval s.1 (Polynomial.map (scalarEval s.2) (C (C c))) = _
  rw [Polynomial.map_C]
  exact (eval₂_C _ _).trans (congrArg RatFunc.C (eval₂_C _ _))

@[simp] theorem planeMap_abscissa (s : Chart) :
    planeMap s (Polynomial.X (R:=(Polynomial L))) = chartCoordinate s.1 RatFunc.X := by
  change abscissaEval s.1 (Polynomial.map (scalarEval s.2) (Polynomial.X (R:=(Polynomial L)))) = _
  rw [Polynomial.map_X]
  exact eval₂_X _ _

@[simp] theorem planeMap_scalar (s : Chart) :
    planeMap s (C (Polynomial.X (R:=L))) = chartCoordinate s.2 scalarCoordinate := by
  change abscissaEval s.1 (Polynomial.map (scalarEval s.2) (C (Polynomial.X (R:=L)))) = _
  rw [Polynomial.map_C]
  refine (eval₂_C _ _).trans ((congrArg RatFunc.C (eval₂_X _ _)).trans ?_)
  cases s.2 <;> simp [chartCoordinate,scalarCoordinate,map_inv₀]

private theorem image_polynomial {R F : Type*} [CommRing R] [CommRing F]
    (j : (Polynomial R) →+* F) (S : Subring F) (coeffs : ∀ c,j (C c)∈S)
    (var : j (Polynomial.X (R:=R))∈S) (q : (Polynomial R)) : j q∈S := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact map_add j p q ▸ S.add_mem hp hq
  | monomial n c =>
    rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact S.mul_mem (coeffs c) (S.pow_mem var n)

/-- Each of the four concrete rings is exactly the image of a polynomial
plane, with the reciprocal choices made independently. -/
theorem planeMap_range (s : Chart) : (planeMap s).range = baseChart s := by
  apply le_antisymm
  · rintro _ ⟨q,rfl⟩
    have xmem : chartCoordinate s.1 RatFunc.X ∈ baseChart s :=
      Subring.subset_closure (Or.inr (by simp))
    have zmem : chartCoordinate s.2 scalarCoordinate ∈ baseChart s :=
      Subring.subset_closure (Or.inr (by simp))
    apply image_polynomial (planeMap s) (baseChart s) _ (planeMap_abscissa s ▸ xmem) q
    intro a
    apply image_polynomial ((planeMap s).comp C) (baseChart s) _ _ a
    · intro c
      change planeMap s (C (C c)) ∈ baseChart s
      rw [planeMap_constants]
      exact Subring.subset_closure (Or.inl ⟨c,rfl⟩)
    · change planeMap s (C (Polynomial.X (R:=L))) ∈ baseChart s
      rwa [planeMap_scalar]
  · apply Subring.closure_le.mpr
    intro x hx
    simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with ⟨c,rfl⟩ | rfl | rfl
    · exact ⟨C (C c),planeMap_constants s c⟩
    · exact ⟨Polynomial.X,planeMap_abscissa s⟩
    · exact ⟨C Polynomial.X,planeMap_scalar s⟩

/-- The coordinate plane identifies with the actual chart as a ring. -/
def planeEquiv (s : Chart) : Plane L ≃+* baseChart s :=
  (RingEquiv.ofBijective (planeMap s).rangeRestrict
    ⟨fun _ _ eq=>planeMap_injective s (congrArg Subtype.val eq),
      (planeMap s).rangeRestrict_surjective⟩).trans (RingEquiv.subringCongr (planeMap_range s))

scoped instance chartNoetherian (s : Chart) : IsNoetherianRing (baseChart s) :=
  isNoetherianRing_of_ringEquiv (Plane L) (planeEquiv s)

scoped instance chartIntegrallyClosed (s : Chart) : IsIntegrallyClosed (baseChart s) :=
  IsIntegrallyClosed.of_equiv (planeEquiv s)

private theorem unreciprocate (s : Bool) (x : ChartField) (T : Subfield ChartField)
    (h : chartCoordinate s x ∈ T) : x ∈ T := by
  cases s with
  | false => exact h
  | true => simpa only [chartCoordinate,ite_true,inv_inv] using T.inv_mem h

/-- The scalar and abscissa reciprocals generate the same full rational
function field as the two finite coordinates. -/
scoped instance chartFractionRing (s : Chart) : IsFractionRing (baseChart s) ChartField := by
  have : FaithfulSMul (baseChart s) ChartField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  let : IsFractionRing (Plane L) ChartField := MonicChart.plane_fractionRing
  let T := Subfield.closure (generators s)
  have hx : RatFunc.X ∈ T := unreciprocate s.1 _ T (Subfield.subset_closure (Or.inr (by simp)))
  have hz : scalarCoordinate ∈ T := unreciprocate s.2 _ T (Subfield.subset_closure (Or.inr (by simp)))
  have hc (c : L) : constants c ∈ T := Subfield.subset_closure (Or.inl ⟨c,rfl⟩)
  have finite : baseChart (false,false) ≤ T.toSubring := by
    apply Subring.closure_le.mpr
    intro q hq
    simp only [Set.mem_union,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff] at hq
    rcases hq with ⟨c,rfl⟩ | rfl | rfl
    · exact hc c
    · exact hx
    · exact hz
  have image (q : Plane L) : algebraMap (Plane L) ChartField q ∈ T := by
    apply finite
    rw [←planeMap_range,planeMap_finite]
    exact ⟨q,rfl⟩
  apply IsFractionRing.of_field
  intro q
  obtain ⟨a,b,_,eq⟩ := IsFractionRing.div_surjective (Plane L) q
  have full : q∈T := eq ▸ T.div_mem (image a) (image b)
  obtain ⟨x,hx',y,hy',ratio⟩ := Subfield.mem_closure_iff.mp full
  exact ⟨⟨x,hx'⟩,⟨y,hy'⟩,ratio.symm⟩

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- The small ordinate degree gives separability on the actual root field. -/
theorem actual_separable
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    Algebra.IsSeparable ChartField E := by
  classical
  let : FiniteDimensional ChartField E := basis.finite
  let : Algebra (Polynomial Scalar) E := ((algebraMap ChartField E).comp (algebraMap (Polynomial Scalar) ChartField)).toAlgebra
  let : IsScalarTower (Polynomial Scalar) ChartField E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial Scalar)) (S:=ChartField) (A:=E) fun _=>rfl
  have root_in_tower : aeval basis.gen (RetainedLinear.toSeed (view f))=0 := by
    rw [aeval_map_algebraMap] at root
    exact root
  have small : Module.finrank ChartField E<K1.p := by
    rw [Lower6960.MonicChart.root_finrank f ir lo basis root_in_tower]
    exact hi.trans (by decide +kernel)
  constructor
  intro x
  have integ : IsIntegral ChartField x := Algebra.IsIntegral.isIntegral x
  let : CharP ChartField K1.p := charP_of_injective_ringHom constants.injective K1.p
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible integ)).mpr
    (CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char K1.p _ (minpoly.natDegree_pos integ)
      ((minpoly.natDegree_le x).trans_lt small))

/-- The trace is in the same rational field on all four actual charts. -/
theorem actual_integral_iff_finite_traces
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    ∃ probes : Chart → Finset E, ∀ s (x : E), IsIntegral (baseChart s) x ↔
      ∀ d∈probes s, Algebra.trace ChartField E (d*x) ∈ baseChart s := by
  classical
  let : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := actual_separable f ir lo hi basis root
  have test (s : Chart) : ∃ probes : Finset E, ∀ x : E, IsIntegral (baseChart s) x ↔
      ∀ d∈probes, Algebra.trace ChartField E (d*x) ∈ baseChart s := by
    obtain ⟨probes,h⟩ := ChartTraceTests.integral_iff_finite_traces (baseChart s) ChartField E
    refine ⟨probes,?_⟩
    intro x
    rw [h]
    have mem (t : ChartField) : t ∈ (1 : Submodule (baseChart s) ChartField) ↔ t ∈ baseChart s := by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨v,eq⟩=>eq ▸ v.property,fun inside=>⟨⟨t,inside⟩,rfl⟩⟩
    simp only [mem,mul_comm x]
  choose probes ok using test
  exact ⟨probes,ok⟩

#print axioms planeMap_range
#print axioms chartFractionRing
#print axioms actual_integral_iff_finite_traces
end
end Lower6960.MonicChartProbes

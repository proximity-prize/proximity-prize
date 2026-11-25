import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import ProximityPrize.SubmissionLower.R6960MonicFourChartDescent
import Mathlib.Algebra.Field.Subfield.Basic
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace

-- merged module R6960ChartTraceTests
section Merged_R6960ChartTraceTests

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartTraceTests

open Algebra Submodule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra A E] [Algebra F E]
  [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- A finite set of trace probes detects the normalized affine chart, even when no
polynomial basis for its integral closure has been chosen. -/
theorem integral_iff_finite_traces :
    ∃ probes : Finset E, ∀ x : E, IsIntegral A x ↔
      ∀ d ∈ probes, trace F E (x*d) ∈ (1 : Submodule A F) := by
  classical
  let S := (integralClosure A E).toSubmodule
  let D := (traceForm F E).dualSubmodule S
  obtain ⟨indices,b,bint⟩ := FiniteDimensional.exists_is_basis_integral A F E
  have bound : D ≤ span A (Set.range b.traceDual) := by
    rw [Module.Basis.traceDual_def, ← LinearMap.BilinForm.dualSubmodule_span_of_basis]
    have leS : span A (Set.range b) ≤ S := by
      apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact bint i
    intro d hd x hx
    exact hd x (leS hx)
  let := isNoetherian_span_of_finite A (Set.finite_range b.traceDual)
  have : IsNoetherian A D := isNoetherian_of_le bound
  have fg : D.FG := (Submodule.fg_top D).mp (IsNoetherian.noetherian _)
  obtain ⟨probes,gen⟩ := fg
  have oneD : (1:E) ∈ D := by
    intro x hx
    rw [traceForm_apply,one_mul]
    exact mem_one.mpr (IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace (show IsIntegral A x from hx)))
  refine ⟨probes,fun x => ⟨?_,?_⟩⟩
  · intro hx d hd
    have member : d ∈ D := gen ▸ subset_span hd
    simpa only [traceForm_apply,mul_comm d x] using member x hx
  · intro tested
    have all (d : E) (hd : d ∈ D) : trace F E (x*d) ∈ (1 : Submodule A F) := by
      rw [← gen] at hd
      have le : span A (probes : Set E) ≤ (1 : Submodule A F).comap
          (((traceForm F E) x).restrictScalars A) := span_le.mpr (fun z hz => tested z hz)
      exact le hd
    apply isIntegral_of_smul_mem_submodule D (fun h => one_ne_zero (show (1:E) ∈ (⊥ : Submodule A E) from h ▸ oneD))
      ⟨probes,gen⟩ x
    intro d hd s hs
    have ds : d*s ∈ D := by
      intro t ht
      simpa only [traceForm_apply,mul_assoc] using hd (s*t) (IsIntegral.mul hs ht)
    simpa only [smul_eq_mul,traceForm_apply,mul_assoc] using all (d*s) ds

#print axioms integral_iff_finite_traces
end Lower6960.ChartTraceTests

end
end Merged_R6960ChartTraceTests

-- merged module R6960MonicChartProbes
section Merged_R6960MonicChartProbes
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
theorem actual_separable
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<64)
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
theorem actual_integral_iff_finite_traces
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<64)
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

end Merged_R6960MonicChartProbes

-- merged module R6960MarkedScalarAxis
section Merged_R6960MarkedScalarAxis
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar Infinity)
open MonicFourChartDescent (scalarCoordinate constants baseChart chartCoordinate)
open MonicChartProbes (planeMap)
open Polynomial
open scoped Polynomial Lower6960.MonicChart
open Lower6960.MonicChartProbes (planeMap_finite)
def swapBase : ChartField≃+*ChartField :=
  letI := MonicChart.plane_fractionRing
  IsFractionRing.ringEquivOfRingEquiv (K:=ChartField) (L:=ChartField) (Bivariate.swap (R:=L)).toRingEquiv
theorem swap_plane (p:PlaneConstants.Plane L) :
    swapBase (planeMap (false,false) p)=planeMap (false,false) (Bivariate.swap p) := by
  letI:=MonicChart.plane_fractionRing
  rw [Lower6960.MonicChartProbes.planeMap_finite]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
theorem swap_x : swapBase RatFunc.X=scalarCoordinate := by
  simpa only [Bivariate.swap_Y,MonicChartProbes.planeMap_abscissa,MonicChartProbes.planeMap_scalar,chartCoordinate,ite_false,
    Bool.false_eq_true] using swap_plane Polynomial.X
theorem swap_z : swapBase scalarCoordinate=RatFunc.X := by
  simpa only [Bivariate.swap_X,MonicChartProbes.planeMap_abscissa,MonicChartProbes.planeMap_scalar,chartCoordinate,ite_false,
    Bool.false_eq_true] using swap_plane (C Polynomial.X)
theorem swap_constant (c:L) : swapBase (constants c)=constants c := by
  simpa only [Bivariate.swap_C_C,MonicChartProbes.planeMap_constants] using swap_plane (C (C c))
def inner : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
def rowBase (c:L) : ChartField≃+*ChartField := (translateField ChartField (inner c)).trans swapBase
private theorem translate_const (c:L) (r:Scalar) : translateField ChartField (inner c) (RatFunc.C r)=RatFunc.C r := by
  rw [←RatFunc.algebraMap_C,translate_polynomial,taylor_C]
theorem row_abscissa (c:L) : rowBase c RatFunc.X=scalarCoordinate+constants c := by
  change swapBase (translateField ChartField (inner c) RatFunc.X)=_
  rw [←RatFunc.algebraMap_X,translate_polynomial,taylor_X,map_add,RatFunc.algebraMap_X,RatFunc.algebraMap_C,map_add,swap_x]
  exact congrArg (scalarCoordinate+·) (swap_constant c)
theorem row_parameter (c:L) : rowBase c scalarCoordinate=RatFunc.X := by
  change swapBase (translateField ChartField (inner c)
    (RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))))=_
  rw [translate_const]; exact swap_z
theorem row_constant (c a:L) : rowBase c (constants a)=constants a := by
  change swapBase (translateField ChartField (inner c)
    (RatFunc.C ((algebraMap (Polynomial L) Scalar).comp C a)))=_
  rw [translate_const]; exact swap_constant a
theorem finite_base (c:L) {a:ChartField} (h:a∈baseChart (false,false)) :
    rowBase c a ∈ (algebraMap (Polynomial Scalar) ChartField).range := by
  have le : baseChart (false,false)≤(algebraMap (Polynomial Scalar) ChartField).range.comap (rowBase c).toRingHom := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact ⟨C (inner r),(RatFunc.algebraMap_C _).trans (row_constant c r).symm⟩
    · change _=chartCoordinate false RatFunc.X at eq;subst_vars
      refine ⟨C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c),?_⟩
      rw [RatFunc.algebraMap_C,map_add]
      exact (row_abscissa c).symm
    · change _=chartCoordinate false scalarCoordinate at eq;subst_vars
      exact ⟨Polynomial.X,RatFunc.algebraMap_X.trans (row_parameter c).symm⟩
  exact le h
theorem infinity_base (c:L) [DecidableEq ChartField] {a:ChartField} (h:a∈baseChart (false,true)) :
    rowBase c a ∈ (algebraMap (Infinity Scalar) ChartField).range := by
  have le : baseChart (false,true)≤(algebraMap (Infinity Scalar) ChartField).range.comap (rowBase c).toRingHom := by
    apply Subring.closure_le.mpr
    rintro _ (⟨r,rfl⟩ | eq | eq)
    · exact ⟨MonicChart.inftyRingEval Scalar (C (inner r)),(aeval_C _ _).trans (row_constant c r).symm⟩
    · change _=chartCoordinate false RatFunc.X at eq;subst_vars
      refine ⟨MonicChart.inftyRingEval Scalar (C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c)),?_⟩
      change MonicChart.AtInfinity Scalar (C _) = rowBase c RatFunc.X
      rw [show MonicChart.AtInfinity Scalar (C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c))=
        RatFunc.C ((algebraMap (Polynomial L) Scalar) Polynomial.X+inner c) from aeval_C _ _,map_add,row_abscissa];rfl
    · change _=chartCoordinate true scalarCoordinate at eq;subst_vars
      refine ⟨MonicChart.inftyRingEval Scalar Polynomial.X,?_⟩
      change _=rowBase c scalarCoordinate⁻¹
      rw [map_inv₀,row_parameter];exact MonicChart.mapped_X_infty
  exact le h
theorem row_seed_polynomial (c:L) (p:(Polynomial L)) :
    rowBase c (RatFunc.C (algebraMap (Polynomial L) Scalar p))=
      algebraMap (Polynomial Scalar) ChartField (p.map inner) := by
  let f: (Polynomial L)→+*ChartField := (rowBase c).toRingHom.comp (RatFunc.C.comp (algebraMap (Polynomial L) Scalar))
  let g: (Polynomial L)→+*ChartField := (algebraMap (Polynomial Scalar) ChartField).comp (Polynomial.mapRingHom inner)
  have eq : f=g := by
    apply Polynomial.ringHom_ext
    · intro a
      change rowBase c (constants a)=algebraMap (Polynomial Scalar) ChartField ((C a).map inner)
      rw [row_constant,Polynomial.map_C,RatFunc.algebraMap_C];rfl
    · change rowBase c scalarCoordinate=algebraMap (Polynomial Scalar) ChartField ((Polynomial.X:(Polynomial L)).map inner)
      rw [row_parameter,Polynomial.map_X,RatFunc.algebraMap_X]
  exact DFunLike.congr_fun eq p
theorem integral_section {E Ω A : Type*} [Field E] [Field Ω] [CommRing A]
    [Algebra ChartField E] [Algebra ChartField Ω] [Algebra A ChartField]
    [Algebra A Ω] [IsScalarTower A ChartField Ω] (c:L) (s:ChartSections.Chart)
    (emb:E→+*Ω) (on_base:∀v,emb (algebraMap ChartField E v)=algebraMap ChartField Ω (rowBase c v))
    (inj:Function.Injective (algebraMap A ChartField))
    (base:∀a∈baseChart s,rowBase c a∈(algebraMap A ChartField).range)
    {v:E} (iv:IsIntegral (baseChart s) v) : IsIntegral A (emb v) := by
  let m := ((rowBase c).toRingHom.comp (baseChart s).subtype)
  let j:=algebraMap A ChartField
  let e : A≃+*j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b eq=>inj (congrArg Subtype.val eq),j.rangeRestrict_surjective⟩
  let lift:baseChart s→+*A := e.symm.toRingHom.comp (m.codRestrict j.range (fun x=>base x x.property))
  have comm (a:baseChart s) : algebraMap A Ω (lift a)=emb (algebraMap (baseChart s) E a) := by
    rw [IsScalarTower.algebraMap_apply A ChartField Ω]
    change algebraMap ChartField Ω (j (lift a))=emb (algebraMap ChartField E (a:ChartField))
    rw [on_base]
    exact congrArg (algebraMap ChartField Ω) (congrArg Subtype.val (e.apply_symm_apply ⟨m a,base a a.property⟩))
  obtain ⟨p,mon,root⟩:=iv
  refine ⟨p.map lift,mon.map _,?_⟩
  have eq: (algebraMap A Ω).comp lift=emb.comp (algebraMap (baseChart s) E) := RingHom.ext comm
  rw [eval₂_map,eq,←Polynomial.hom_eval₂,root,map_zero]
#print axioms finite_base
#print axioms infinity_base
#print axioms integral_section
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedScalarAxis

-- merged module R6960MarkedMatrixNorm
section Merged_R6960MarkedMatrixNorm

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Module Matrix Algebra Polynomial Finset
open scoped Polynomial Matrix BigOperators
variable {k K E I J:Type} [Field k] [Field K] [DecidableEq (RatFunc K)] [Field E]
  [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
  [Algebra (SheetNorm.Infinity K) E] [IsScalarTower (SheetNorm.Infinity K) (RatFunc K) E]
  [Fintype I] [DecidableEq I] [Fintype J]
local notation "ι" => algebraMap (RatFunc K) E
local notation "basePoly" => algebraMap (Polynomial K) (RatFunc K)

def polePolynomial (T:Finset K) : (Polynomial K) := ∏ z∈T,(Polynomial.X-C z)
theorem polePolynomial_monic (T:Finset K) : (polePolynomial T).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun z _=>monic_X_sub_C z)
theorem polePolynomial_degree (T:Finset K) : (polePolynomial T).natDegree=T.card := by
  rw [polePolynomial,Polynomial.natDegree_prod _ _ (fun z _=>X_sub_C_ne_zero z)]
  simp

theorem leading_unit (P:(Polynomial K)) (nz:P≠0) :
    let u:=basePoly P/(RatFunc.X^P.natDegree)
    u∈SheetNorm.Infinity K ∧ u⁻¹∈SheetNorm.Infinity K := by
  let u:=basePoly P/(RatFunc.X^P.natDegree)
  have val : RatFunc.inftyValuation K u=1 := by
    change RatFunc.inftyValuation K (basePoly P/(RatFunc.X^P.natDegree))=1
    rw [map_div₀,←zpow_natCast,RatFunc.inftyValuation.X_zpow]
    change RatFunc.inftyValuationDef K (basePoly P)/_=_
    rw [RatFunc.inftyValuation.polynomial _ nz,div_self (by simp)]
  exact ⟨show RatFunc.inftyValuation K u≤1 from val.le,
    show RatFunc.inftyValuation K u⁻¹≤1 from by rw [map_inv₀,val,inv_one]⟩

theorem integral_infty {u:RatFunc K} (h:u∈SheetNorm.Infinity K) :
    IsIntegral (SheetNorm.Infinity K) (ι u:E) := by
  have e := isIntegral_algebraMap (A:=E) (x:=(⟨u,h⟩:SheetNorm.Infinity K))
  rw [IsScalarTower.algebraMap_apply (SheetNorm.Infinity K) (RatFunc K) E] at e
  exact e

theorem count_from_original_columns [IsGalois (RatFunc K) E] (inK:k→+*K) (labels:Finset K)
    (Q:Matrix I J (Polynomial k)) (T:Matrix J I (Polynomial k)) (pick:I↪J) (pnonzero:(Q.submatrix _root_.id pick).det≠0)
    (A:Matrix I J E) (B:Matrix I I E) (det:B.det≠0)
    (repr : A=B*Q.map ((algebraMap (Polynomial K) E).comp (Polynomial.mapRingHom inK)))
    (generated : B=A*T.map ((algebraMap (Polynomial K) E).comp (Polynomial.mapRingHom inK)))
    (finite:∀i j,IsIntegral (Polynomial K) (algebraMap (Polynomial K) E (polePolynomial labels)*A i j))
    (infty:∀i j,IsIntegral (SheetNorm.Infinity K) (A i j))
    (e:ℕ) (ep:0<e)
    (O:K→Type) [∀z,CommRing (O z)] [∀z,IsDomain (O z)] [∀z,IsLocalRing (O z)]
    (φ:∀z,(Polynomial K)→+*O z) (incl:∀z,O z→+*E) (inj:∀z,Function.Injective (incl z))
    (base:∀z,(incl z).comp (φ z)=(algebraMap (RatFunc K) E).comp basePoly)
    (π:∀z,O z) (place:∀z∈labels,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (localA:∀z,SheetNorm.Aut K E→Matrix I J (O z)) (rows:K→SheetNorm.Aut K E→Finset I)
    (realize:∀z∈labels,∀g i j,incl z (localA z g i j)=g (algebraMap (Polynomial K) E (polePolynomial labels)*A i j))
    (off:∀z∈labels,∀g,∀i∈rows z g,∀j,π z∣localA z g i j)
    (freq:∀z∈labels,e*(∑g:SheetNorm.Aut K E,(rows z g).card)=
      Fintype.card (SheetNorm.Aut K E)*((e-1)*Fintype.card I)) :
    e*(Q.submatrix _root_.id pick).det.natDegree≤labels.card*Fintype.card I := by
  classical
  let D:=polePolynomial labels
  let q:=(Q.submatrix _root_.id pick).det
  let P:=q.map inK
  let d:=q.natDegree
  let r:=Fintype.card I
  let j:=algebraMap (Polynomial K) E
  let inc:=j.comp (Polynomial.mapRingHom inK)
  let H:Matrix I I E:=j D • B
  have dn:D≠0 := (polePolynomial_monic labels).ne_zero
  have ji : Function.Injective j := by
    rw [show j=(algebraMap (RatFunc K) E).comp basePoly from IsScalarTower.algebraMap_eq (Polynomial K) (RatFunc K) E]
    exact (algebraMap (RatFunc K) E).injective.comp (IsFractionRing.injective _ _)
  have hn:H.det≠0 := by
    rw [show H.det=(j D)^r*B.det from Matrix.det_smul ..]
    exact mul_ne_zero (pow_ne_zero _ (ji.ne_iff.mpr dn |> fun p=>by simpa using p)) det
  have fe:IsIntegral (Polynomial K) H.det := by
    apply IsIntegral.det
    intro u v
    change IsIntegral _ (j D*B u v)
    rw [generated,Matrix.mul_apply,Finset.mul_sum]
    apply IsIntegral.sum;intro l _
    rw [←mul_assoc]
    exact (finite u l).mul (isIntegral_algebraMap (A:=E) (x:=(T l v).map inK))
  have sub:(A.submatrix _root_.id pick).det=B.det*j P := by
    rw [repr,Matrix.submatrix_mul _ _ _root_.id _root_.id pick Function.bijective_id,Matrix.submatrix_id_id,Matrix.det_mul]
    exact congrArg (B.det*·) (RingHom.map_det inc (Q.submatrix _root_.id pick)).symm
  have pn:P≠0 := (Polynomial.map_ne_zero_iff inK.injective).mpr pnonzero
  have pd:P.natDegree=d := natDegree_map_eq_of_injective inK.injective q
  have normalized:=integral_infty (E:=E) (leading_unit (K:=K) P pn).2
  have weight:=integral_infty (E:=E) (leading_unit (K:=K) D dn).1
  have detInf:IsIntegral (SheetNorm.Infinity K) (A.submatrix _root_.id pick).det :=
    IsIntegral.det (fun u v=>infty u (pick v))
  have wz : IsIntegral (SheetNorm.Infinity K) ((ι RatFunc.X)^d*H.det/ι (RatFunc.X^(labels.card*r))) := by
    have ok:=((weight.pow r).mul normalized).mul detInf
    rw [sub] at ok
    rw [show H.det=(j D)^r*B.det from Matrix.det_smul ..]
    have J (p:(Polynomial K)) : ι (basePoly p)=j p := (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) E _).symm
    rw [map_inv₀,map_div₀,map_div₀,J P,J D,map_pow,map_pow,pd,polePolynomial_degree] at ok
    have xeq:ι (RatFunc.X^(labels.card*r))=(ι RatFunc.X ^labels.card)^r := by rw [map_pow,pow_mul]
    rw [xeq]
    have hP:j P≠0 := (map_ne_zero_iff _ ji).mpr pn
    have hX:(ι RatFunc.X:E)≠0 := (map_ne_zero_iff _ (algebraMap (RatFunc K) E).injective).mpr RatFunc.X_ne_zero
    have alg {x y z b:E} (yx:x≠0) (nz:z≠0) (n r d:ℕ) :
        x^d*(y^r*b)/(x^n)^r=(y/x^n)^r*(z/x^d)⁻¹*(b*z) := by
      rw [div_pow,inv_div]; field_simp [yx,nz] <;> ring
    exact (alg hX hP labels.card r d).symm ▸ ok
  let localH (z:K) (g:SheetNorm.Aut K E):=localA z g * T.map ((φ z).comp (Polynomial.mapRingHom inK))
  apply conjugate_bound e d ep labels H hn fe wz O φ incl inj base π place localH rows _ _ freq
  · intro z hz g u v
    change incl z (∑l,localA z g u l*φ z ((T l v).map inK))=g (j D*B u v)
    rw [generated,Matrix.mul_apply,Finset.mul_sum,map_sum,map_sum]
    apply Finset.sum_congr rfl; intro l _
    have coeff:=DFunLike.congr_fun (base z) ((T l v).map inK)
    change incl z (φ z ((T l v).map inK))=ι (basePoly ((T l v).map inK)) at coeff
    rw [map_mul,realize z hz g u l,coeff]
    change g (j D*A u l)*ι (basePoly ((T l v).map inK))=g (j D*(A u l*j ((T l v).map inK)))
    rw [←mul_assoc,map_mul g (j D*A u l)]
    exact congrArg (g (j D*A u l)*·) (by
      rw [show j ((T l v).map inK)=ι (basePoly ((T l v).map inK)) from IsScalarTower.algebraMap_apply _ _ _ _,g.commutes])
  · intro z hz g u hu v
    change π z∣∑l,localA z g u l*φ z ((T l v).map inK)
    exact Finset.dvd_sum (fun l _=>(off z hz g u hu l).trans (dvd_mul_right ..))

#print axioms count_from_original_columns
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedMatrixNorm

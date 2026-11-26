import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.High6966KnownRows
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import ProximityPrize.SubmissionLower.R6960HornerNative
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRow
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6966ProofFarChart
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked11
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked24
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks10
import ProximityPrize.SubmissionLower.R6966ProofPhysicalOriginal

section Merged6967_R6960MarkedMatrixNorm
set_option Elab.async false





set_option Elab.async false

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

end Merged6967_R6960MarkedMatrixNorm

section Merged6967_R6966ProofFarRescueGeometry
set_option Elab.async false













set_option Elab.async false

-- merged module R6966ProofFarSourceIndex
section Merged_R6966ProofFarSourceIndex

namespace Research6966.FarSourceData
open FarSourceArithmetic Lower6960

theorem free_checked (i : Fin 17) : Checked (free i) := by
  fin_cases i
  · exact free0
  · exact free1
  · exact free2
  · exact free3
  · exact free4
  · exact free5
  · exact free6
  · exact free7
  · exact free8
  · exact free9
  · exact free10
  · exact free11
  · exact free12
  · exact free13
  · exact free14
  · exact free15
  · exact free16

theorem helper_checked (test : HelperSource.HelperTest) : Checked (helper test) := by
  cases test
  · exact helper_twoSlopes
  · exact helper_seedBoundary
  · exact helper_mixedBoundary
  · exact helper_jetBoundary

theorem rescue_checked (rect : Fin 4) (i : Fin 17) : Checked (rescue rect i) := by
  fin_cases rect <;> fin_cases i
  · exact rescue0_0
  · exact rescue0_1
  · exact rescue0_2
  · exact rescue0_3
  · exact rescue0_4
  · exact rescue0_5
  · exact rescue0_6
  · exact rescue0_7
  · exact rescue0_8
  · exact rescue0_9
  · exact rescue0_10
  · exact rescue0_11
  · exact rescue0_12
  · exact rescue0_13
  · exact rescue0_14
  · exact rescue0_15
  · exact rescue0_16
  · exact rescue1_0
  · exact rescue1_1
  · exact rescue1_2
  · exact rescue1_3
  · exact rescue1_4
  · exact rescue1_5
  · exact rescue1_6
  · exact rescue1_7
  · exact rescue1_8
  · exact rescue1_9
  · exact rescue1_10
  · exact rescue1_11
  · exact rescue1_12
  · exact rescue1_13
  · exact rescue1_14
  · exact rescue1_15
  · exact rescue1_16
  · exact rescue2_0
  · exact rescue2_1
  · exact rescue2_2
  · exact rescue2_3
  · exact rescue2_4
  · exact rescue2_5
  · exact rescue2_6
  · exact rescue2_7
  · exact rescue2_8
  · exact rescue2_9
  · exact rescue2_10
  · exact rescue2_11
  · exact rescue2_12
  · exact rescue2_13
  · exact rescue2_14
  · exact rescue2_15
  · exact rescue2_16
  · exact rescue3_0
  · exact rescue3_1
  · exact rescue3_2
  · exact rescue3_3
  · exact rescue3_4
  · exact rescue3_5
  · exact rescue3_6
  · exact rescue3_7
  · exact rescue3_8
  · exact rescue3_9
  · exact rescue3_10
  · exact rescue3_11
  · exact rescue3_12
  · exact rescue3_13
  · exact rescue3_14
  · exact rescue3_15
  · exact rescue3_16

#print axioms free_checked
#print axioms helper_checked
#print axioms rescue_checked
end Research6966.FarSourceData

end Merged_R6966ProofFarSourceIndex

-- merged module R6966ProofFarSources
section Merged_R6966ProofFarSources

namespace Lower6960.FarFreeSource
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (debit)
open HelperSource (WidthGuard cutoffCount)
open Research6966.FarSourceData (free free_checked)
open Research6966.FarSourceArithmetic (agreement)

abbrev bank := FreeSource.bank
abbrev reserve := FreeSource.reserve
def cutoff (h : ℕ) (i : Fin 17) : ℕ := cutoffCount (bank i).shape agreement h (reserve i)-1

theorem shape_guards (i : Fin 17) :
    0<(bank i).shape.J ∧ (bank i).shape.J≤(bank i).shape.B ∧
      (bank i).shape.B<K1.p ∧ (bank i).shape.U<K1.p ∧ (bank i).shape.m*agreement<K1.p := by
  fin_cases i <;> decide +kernel

theorem cutoff_fit {h : ℕ} (lo : 2523≤h) (hi : h≤33697) (i : Fin 17) :
    cutoff h i+2*h*(reserve i)<(bank i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((free_checked i).window lo hi)

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) (i : Fin 17) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P≠0 := by
  have cert := free_checked i
  have positive := cert.gain lo hi
  change debit h (bank i)<HelperSource.gain (bank i).shape agreement h (reserve i)
    ((bank i).shape.J+1) 0 0 at positive
  rw [FreeSource.gain_eq_raw _ _ _ _ (by omega)] at positive
  exact FreeSource.nonzero_row Crt word (bank i) agreement (reserve i) (by omega) (by omega)
    cert.rank (cert.window lo hi) positive

#print axioms free_rows
end Lower6960.FarFreeSource

namespace Lower6960.FarHelperSource
open Polynomial
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open HelperSource (HelperTest cutoffCount WidthGuard)
open Research6966.FarSourceData (helper_checked)
open Research6966.FarSourceArithmetic (agreement)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev helperBank := HelperSource.helperBank
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape agreement h 10-1

theorem helper_width {h : ℕ} (lo : 2523≤h) (hi : h≤33697) : WidthGuard helperBank agreement h 10 :=
  (helper_checked .twoSlopes).window lo hi

theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬G∣Q := by
  have cert := helper_checked test
  exact HelperSource.crt_avoiding_row Crt word helperBank agreement 10 test.slope test.excess test.seed
    (by omega) (by omega) cert.positive_slope cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2
    (by decide) (cert.window lo hi) (cert.gain lo hi) irr seeded slope seed excess

theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have cert := helper_checked .twoSlopes
  have sup := HelperSource.crt_supply Crt word helperBank agreement 10 2 0 1 (by omega) (by omega)
    (by decide) cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2 (cert.window lo hi) (cert.gain lo hi)
  exact HelperSource.nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)

private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega

theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤85 ∧ (2≤jetDegree G → seedDegree G≤78) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperSource.HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 86≤seedDegree G; omega)
      (by simpa [HelperSource.HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 79≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)

theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have cert := helper_checked .twoSlopes
  have supply := HelperSource.crt_supply Crt word helperBank agreement 10 2 0 1 (by omega) (by omega) (by decide)
    cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2 (cert.window lo hi) (cert.gain lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape agreement h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH

#print axioms helper_common_caps
#print axioms helper_not_two
end Lower6960.FarHelperSource

namespace Lower6960.FarRescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (cutoffCount)
open Research6966.FarSourceData (rescue_checked)
open Research6966.FarSourceArithmetic (agreement)

abbrev bank := RescueSource.bank
abbrev reserve := RescueSource.reserve
abbrev excess := RescueSource.excess
abbrev seed := RescueSource.seed
abbrev jetCap := RescueSource.jetCap
abbrev seedCap := RescueSource.seedCap
def cutoff (h : ℕ) (rect : Fin 4) (i : Fin 17) : ℕ := cutoffCount (bank rect i).shape agreement h (reserve i)-1

theorem shape_guards (rect : Fin 4) (i : Fin 17) :
    0<(bank rect i).shape.J ∧ (bank rect i).shape.J≤(bank rect i).shape.B ∧
      (bank rect i).shape.B<K1.p ∧ (bank rect i).shape.U<K1.p ∧ (bank rect i).shape.m*agreement<K1.p := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem cutoff_fit {h : ℕ} (lo : 2523≤h) (hi : h≤33697) (rect : Fin 4) (i : Fin 17) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*agreement :=
  FreeSource.buffered_fit _ _ _ _ ((rescue_checked rect i).window lo hi)

theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) (rect : Fin 4) (i : Fin 17) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬G∣Q := by
  have cert := rescue_checked rect i
  exact HelperSource.crt_avoiding_row Crt word (bank rect i) agreement (reserve i) 1 (excess rect) (seed rect)
    (by omega) (by omega) (by decide) cert.rank.nodes cert.rank.moment.1 cert.rank.moment.2
    (shape_guards rect i).2.2.2.1 (cert.window lo hi) (cert.gain lo hi) irr seeded slope hs hj

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤78) :
    ∃ rect : Fin 4, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect := by
  by_cases hJ : 2≤j
  · refine ⟨3,?_⟩
    change 2≤j ∧ j≤7 ∧ 1≤u ∧ u≤78
    exact ⟨hJ,hiJ,loU,mixed hJ⟩
  · by_cases hU : u≤1
    · refine ⟨0,?_⟩
      change 1≤j ∧ j≤1 ∧ 1≤u ∧ u≤1
      omega
    · by_cases hU' : u≤6
      · refine ⟨1,?_⟩
        change 1≤j ∧ j≤1 ∧ 2≤u ∧ u≤6
        omega
      · refine ⟨2,?_⟩
        change 1≤j ∧ j≤1 ∧ 7≤u ∧ u≤85
        omega

theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2523≤h) (hi : h≤33697) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word FarHelperSource.helperBank.shape (FarHelperSource.helperCutoff h), G∣P) :
    ∃ rect : Fin 4, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      ∀ i : Fin 17, ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := FarHelperSource.helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,fun i => ?_⟩
  exact rescue_row Crt word lo hi rect i irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

#print axioms exceptional_rows
end Lower6960.FarRescueSource

end Merged_R6966ProofFarSources

-- merged module R6966ProofFarRescueGeometry
section Merged_R6966ProofFarRescueGeometry

section Merged_R6960RescueGeometry
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.FarRescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open FarRescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
abbrev Model (u : P1.Words) (deleted : Finset I) := P1.ModelAt 33697 u deleted
abbrev Family {u deleted} (M : Model u deleted) (Γ : Finset K) := P1.FamilyAt 179759 M Γ
def word {u deleted} (M : Model u deleted) : I→L := fun i => algebraMap K L (M.word i)
def OnMark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (A : Ideal Ambient) (γ : K) : Prop := OnJet A (M.label γ) (F.scalar γ)
theorem label_injective {u deleted} (M : Model u deleted) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h
def primeShape (rect : Fin 4) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩
def initialCap (rect : Fin 4) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape
theorem prime_shape_fit (rect : Fin 4) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide
theorem initial_small (rect : Fin 4) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel
theorem reserve_small (i : Fin 17) : reserve i<K1.p := by
  fin_cases i <;> decide +kernel
theorem contact_at_mark {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {s : Shape} {W r : ℕ} {P : Jet} (inside : P∈evaluated Crt (word M) s W)
    (width : W+2*M.overhead.toNat*r<s.m*179759)
    (γ : K) (hγ : γ∈Γ) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (r+1) P := by
  let B := F.mark γ hγ
  have degree : (liftPoly (F.scalar γ)).natDegree≤131071+M.overhead.toNat := by
    rw [liftPoly, Polynomial.natDegree_map]
    rcases B.scalar_degree with hzero | hd
    · simp [hzero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at hd
      omega
  refine PrefixRows.contact_of_crt Crt (word M) s P inside width noPole
    (M.label γ) (F.scalar γ) (residues γ hγ) degree B.bad.support B.bad.agreement ?_
  intro i hit
  rw [word,liftPoly,nodeL,Polynomial.eval_map,Polynomial.eval₂_hom]
  exact congrArg (algebraMap K L) (B.scalar_hits i hit)
theorem zero_of_contact {z : K} {S : (Polynomial K)} {P : Jet} {r : ℕ}
    (contact : Native (RingHom.ker (jetMarkHom z S)) (r+1) P) : jetAt P z S=0 := by
  have test := contact [] (by simp)
  change toJet P∈RingHom.ker (jetMarkHom z S) at test
  rwa [RingHom.mem_ker,K1_14_2.eval_toJet] at test
private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 4) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (FarRescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))
#print axioms initial_cover
#print axioms Initial.rank_ode
end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometry

section Merged_R6960RescueGeometryHistory
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace Lower6960.FarRescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open FarRescueSource (bank reserve cutoff jetCap seedCap)
open DifferentialContact (Native)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 4} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 17→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (bank rect i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (Q i)) ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
        (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c) ∧
      ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (FarRescueSource.shape_guards rect i).2.1 init.parents on (reserve i) (reserve_small i)
  let selected (i : Fin 17) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : reserve 0=0 := by decide
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (reserve 0+1) (Q 0) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 17) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (reserve i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 17) (c : Fin 4) :
      (reserve i+1)*mass (selected i) c≤pairCap (primeShape rect) (bank rect i).shape c := by
    by_cases zi : i = 0
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 17,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 17,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = 0 := Fin.ext (by omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ 0 := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩
structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 4
  row : Fin 17→Jet
  row_mem : ∀ i,row i∈evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i)
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (row i)
  cap : ∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
    (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c
  cut : ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0
theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2523≤M.overhead.toNat) (hi : M.overhead.toNat≤33697)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) FarHelperSource.helperBank.shape (FarHelperSource.helperCutoff M.overhead.toNat)) G) :
    Nonempty (Run F Crt G) := by
  obtain ⟨rect,linear,jCap,uCap,rows⟩ := FarRescueSource.exceptional_rows Crt (word M) lo hi
    common.1 common.2.2.1 common.2.1 common.2.2.2
  choose Q inside avoid using rows
  have capsG : RowCaps G (primeShape rect) :=
    (rowCaps_iff G _).mpr ⟨jCap,linear.le,uCap⟩
  have caps (i : Fin 17) : RowCaps (Q i) (bank rect i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin 17) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i) (FarRescueSource.cutoff_fit lo hi rect i) γ hγ
  obtain ⟨ini⟩ := initial_cover F common.1 (avoid 0) capsG (caps 0)
    (fun γ hγ=>zero_of_contact (contact 0 γ hγ))
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial common.1 capsG Q ini avoid caps contact
  exact ⟨⟨rect,Q,inside,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩⟩
theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)
#print axioms prepare
#print axioms history_from_initial
end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometryHistory

section Merged_R6960RescueGeometryCuts
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.FarRescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt atX seedEmbedding)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom eval_toJet CoordinateRing)
open K1_14_2_2 (RowCaps Active dual mass sectionDegree CutCover weight dot emptyCut joinCuts
  joinCuts_cost sum_dot)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open FarRescueSource (bank reserve)
open scoped Classical
open HighCore82258_3 (envelope_caps)
open K1_14_2_2_7 (seed_value_eq)
def terminalShape : Shape := ⟨4500,6286,1329,748778⟩
def terminalCutoff : ℕ := terminalShape.m*179759-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179759-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179759-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) :=
  (R.kept 17).filter (TerminalPass Crt (word M))
def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  if n<17 then R.kept (n+1) else R.final
def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  R.live n \ R.live (n+1)
theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<17
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]
    exact R.antitone (by omega)
  · have eq : i+1=17 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]
    exact filter_subset _ _
theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem
  exact (R.parent_geom mem).1
theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<17)]
  exact R.intro_pass
def rescueStage (rect : Fin 4) (i : Fin 17) : P1_7.Stage :=
  ⟨reserve i,⟨HelperPrefix.timesShape (reserve i+1) (primeShape rect),0,0⟩,bank rect i⟩
def cutShape (rect : Fin 4) (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape
theorem cutShape_fit (rect : Fin 4) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide
theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (FarRescueSource.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=17 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass =>
      lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179759)) (by decide : 0<1)) γ hγ
private theorem mark_on_cut {J : Ideal Ambient} {P : Jet} {z : K} {S : (Polynomial K)}
    (on : OnJet J z S) (zero : jetAt P z S=0) :
    ∃ Q∈cutComponents J P,OnJet Q z S := by
  let e := jetMarkHom z S
  have incl : J ⊔ Ideal.span {toJet P} ≤ RingHom.ker e :=
    sup_le on ((Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans zero)))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q,minimal,mark⟩ := Ideal.exists_minimalPrimes_le incl
  exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr minimal,mark⟩
theorem proper_cut {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (s : Shape) {J : Ideal Ambient} {P : Jet} (sl : s.J≤s.B) (act : Active J)
    (cap : RowCaps P s) (proper : toJet P∉J) (zero : ∀ γ∈Γ,jetAt P (M.label γ) (F.scalar γ)=0) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight s fee) (sectionDegree J)) ∧
      ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnMark F Q)
  let direct := (constantComponents J P).biUnion marked
  have card : direct.card≤(constantComponents J P).card := by
    have single (Q : Ideal Ambient) (mem : Q∈constantComponents J P) : (marked Q).card≤1 := by
      obtain ⟨comp,seed⟩ := mem_filter.mp mem
      let _ : Q.IsPrime := (cutComponent_curve act proper comp).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply label_injective M
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq seed (mem_filter.mp hγ).2).trans (seed_value_eq seed (mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈constantComponents J P,(marked Q).card := card_biUnion_le
      _ ≤ ∑ _∈constantComponents J P,1 := sum_le_sum single
      _ = _ := by simp
  let C : CutCover := ⟨direct,movingComponents J P,by
    intro Q hQ
    obtain ⟨comp,moving⟩ := mem_filter.mp hQ
    obtain ⟨prime,dim⟩ := cutComponent_curve act proper comp
    exact ⟨prime,dim,K1_14_2_2_7_1.proof Q prime dim moving⟩⟩
  refine ⟨C,?_,?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s J P sl act cap proper
    · exact P0_10R.Bridge.cut_ordinate_mass s J P sl act cap proper
    · exact card.trans (P0_10R.Bridge.cut_constant_count s J P sl act cap proper)
  · intro γ hγ on
    obtain ⟨Q,comp,mark⟩ := mark_on_cut on (zero γ hγ)
    by_cases c : ConstantSeed Q
    · exact Or.inl (mem_biUnion.mpr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mem_filter.mpr ⟨hγ,mark⟩⟩)
    · exact Or.inr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mark⟩
theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩
theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<17,J∈R.lost i := by
  by_cases h : ∃ i<17,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤17,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 17 le_rfl)
def OnSurface {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (q : Surface) (γ : K) : Prop :=
  ∀ P∈q.asIdeal,jetAt P (M.label γ) (F.scalar γ)=0
def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179759-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
theorem Run.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=R.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩
#print axioms Run.cutCover
#print axioms Run.retained_or_lost
#print axioms Run.terminal_surfaces
end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometryCuts

section Merged_R6960RescueGeometryBills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.FarRescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open FarRescueSource (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def initialMass (rect : Fin 4) : Mass := fun k => initialCap rect k
def history (rect : Fin 4) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve i+1))
    else history rect n k
theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))
theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve j+1)
    have pos : (0 : ℚ)<reserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound
theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k
theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k
def cutWeight (rect : Fin 4) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 4) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 4) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3
theorem seed_limit_small (rect : Fin 4) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel
theorem point_limit_bound (rect : Fin 4) : pointLimit rect ≤ 206700957314 := by
  fin_cases rect <;> decide +kernel
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)
theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ
theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩
theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)
def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i
private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i
theorem Run.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ R.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : R.jointLive 18 = R.final := by simp [Run.jointLive,Run.live]
    simpa only [beforeCuts,Run.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) R.final)).trans
    (R.joint_bill_with_final rank cut)

theorem inventory {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2523≤M.overhead.toNat) (hi : M.overhead.toNat≤33697)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (K1_14_1.evaluated Crt (word M) FarHelperSource.helperBank.shape (FarHelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (R : Run F Crt G) (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
        γ∈R.initial.seedMarks ∨ γ∈R.initial.ordinateMarks ∨
        (∃ J∈R.initial.rankExit,OnMark F J γ) ∨ γ∈C.pointMarks ∨
        (∃ i<17,∃ Q∈(C.cover i).curves,OnMark F Q γ) ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare F Crt lo hi noPole residues common
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨R,C,S,geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_filter.mpr ⟨hγ,seed⟩)
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pass γ hγ ⟨J,final,on⟩)))))
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | curve
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,curve⟩))))
#print axioms inventory
#print axioms Run.joint_bill
#print axioms seed_limit_small
#print axioms CutBooks.point_bill
end Lower6960.FarRescueGeometry

end
end Merged_R6960RescueGeometryBills

end Merged_R6966ProofFarRescueGeometry

end Merged6967_R6966ProofFarRescueGeometry

section Merged6967_R6966ProofHelperRescueRoutes0
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route0 (stage : Fin 17) : Checked (request 0 stage) := by
  fin_cases stage
  · exact step0_verified
  · exact step1_verified
  · exact step2_verified
  · exact step3_verified
  · exact step4_verified
  · exact step5_verified
  · exact step6_verified
  · exact step7_verified
  · exact step8_verified
  · exact step9_verified
  · exact step10_verified
  · exact step11_verified
  · exact step12_verified
  · exact step13_verified
  · exact step14_verified
  · exact step15_verified
  · exact step16_verified
theorem route1 (stage : Fin 17) : Checked (request 1 stage) := by
  fin_cases stage
  · exact step17_verified
  · exact step18_verified
  · exact step19_verified
  · exact step20_verified
  · exact step21_verified
  · exact step22_verified
  · exact step23_verified
  · exact step24_verified
  · exact step25_verified
  · exact step26_verified
  · exact step27_verified
  · exact step28_verified
  · exact step29_verified
  · exact step30_verified
  · exact step31_verified
  · exact step32_verified
  · exact step33_verified
theorem route2 (stage : Fin 17) : Checked (request 2 stage) := by
  fin_cases stage
  · exact step34_verified
  · exact step35_verified
  · exact step36_verified
  · exact step37_verified
  · exact step38_verified
  · exact step39_verified
  · exact step40_verified
  · exact step41_verified
  · exact step42_verified
  · exact step43_verified
  · exact step44_verified
  · exact step45_verified
  · exact step46_verified
  · exact step47_verified
  · exact step48_verified
  · exact step49_verified
  · exact step50_verified
theorem route3 (stage : Fin 17) : Checked (request 3 stage) := by
  fin_cases stage
  · exact step51_verified
  · exact step52_verified
  · exact step53_verified
  · exact step54_verified
  · exact step55_verified
  · exact step56_verified
  · exact step57_verified
  · exact step58_verified
  · exact step59_verified
  · exact step60_verified
  · exact step61_verified
  · exact step62_verified
  · exact step63_verified
  · exact step64_verified
  · exact step65_verified
  · exact step66_verified
  · exact step67_verified
theorem route4 (stage : Fin 17) : Checked (request 4 stage) := by
  fin_cases stage
  · exact step68_verified
  · exact step69_verified
  · exact step70_verified
  · exact step71_verified
  · exact step72_verified
  · exact step73_verified
  · exact step74_verified
  · exact step75_verified
  · exact step76_verified
  · exact step75_verified
  · exact step77_verified
  · exact step78_verified
  · exact step79_verified
  · exact step80_verified
  · exact step81_verified
  · exact step82_verified
  · exact step83_verified
theorem route5 (stage : Fin 17) : Checked (request 5 stage) := by
  fin_cases stage
  · exact step84_verified
  · exact step85_verified
  · exact step86_verified
  · exact step87_verified
  · exact step88_verified
  · exact step89_verified
  · exact step90_verified
  · exact step91_verified
  · exact step92_verified
  · exact step91_verified
  · exact step93_verified
  · exact step94_verified
  · exact step95_verified
  · exact step96_verified
  · exact step96_verified
  · exact step96_verified
  · exact step96_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes0

section Merged6967_R6966ProofHelperRescueRoutes1
set_option Elab.async false





set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route6 (stage : Fin 17) : Checked (request 6 stage) := by
  fin_cases stage
  · exact step97_verified
  · exact step98_verified
  · exact step99_verified
  · exact step100_verified
  · exact step101_verified
  · exact step102_verified
  · exact step103_verified
  · exact step104_verified
  · exact step105_verified
  · exact step104_verified
  · exact step106_verified
  · exact step107_verified
  · exact step108_verified
  · exact step109_verified
  · exact step110_verified
  · exact step111_verified
  · exact step112_verified
theorem route7 (stage : Fin 17) : Checked (request 7 stage) := by
  fin_cases stage
  · exact step113_verified
  · exact step114_verified
  · exact step115_verified
  · exact step116_verified
  · exact step117_verified
  · exact step118_verified
  · exact step119_verified
  · exact step120_verified
  · exact step121_verified
  · exact step120_verified
  · exact step122_verified
  · exact step123_verified
  · exact step124_verified
  · exact step125_verified
  · exact step126_verified
  · exact step127_verified
  · exact step128_verified
theorem route8 (stage : Fin 17) : Checked (request 8 stage) := by
  fin_cases stage
  · exact step129_verified
  · exact step130_verified
  · exact step131_verified
  · exact step132_verified
  · exact step133_verified
  · exact step134_verified
  · exact step135_verified
  · exact step136_verified
  · exact step137_verified
  · exact step136_verified
  · exact step138_verified
  · exact step139_verified
  · exact step139_verified
  · exact step140_verified
  · exact step141_verified
  · exact step142_verified
  · exact step143_verified
theorem route9 (stage : Fin 17) : Checked (request 9 stage) := by
  fin_cases stage
  · exact step144_verified
  · exact step145_verified
  · exact step146_verified
  · exact step147_verified
  · exact step148_verified
  · exact step149_verified
  · exact step150_verified
  · exact step151_verified
  · exact step152_verified
  · exact step151_verified
  · exact step153_verified
  · exact step154_verified
  · exact step154_verified
  · exact step155_verified
  · exact step155_verified
  · exact step155_verified
  · exact step155_verified
theorem route10 (stage : Fin 17) : Checked (request 10 stage) := by
  fin_cases stage
  · exact step156_verified
  · exact step157_verified
  · exact step158_verified
  · exact step159_verified
  · exact step160_verified
  · exact step161_verified
  · exact step162_verified
  · exact step163_verified
  · exact step164_verified
  · exact step163_verified
  · exact step165_verified
  · exact step166_verified
  · exact step167_verified
  · exact step168_verified
  · exact step168_verified
  · exact step168_verified
  · exact step168_verified
theorem route11 (stage : Fin 17) : Checked (request 11 stage) := by
  fin_cases stage
  · exact step169_verified
  · exact step170_verified
  · exact step171_verified
  · exact step172_verified
  · exact step173_verified
  · exact step174_verified
  · exact step175_verified
  · exact step176_verified
  · exact step177_verified
  · exact step176_verified
  · exact step178_verified
  · exact step179_verified
  · exact step180_verified
  · exact step181_verified
  · exact step181_verified
  · exact step181_verified
  · exact step181_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes1

section Merged6967_R6966ProofHelperRescueRoutes2
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route12 (stage : Fin 17) : Checked (request 12 stage) := by
  fin_cases stage
  · exact step182_verified
  · exact step183_verified
  · exact step184_verified
  · exact step185_verified
  · exact step186_verified
  · exact step187_verified
  · exact step188_verified
  · exact step189_verified
  · exact step190_verified
  · exact step189_verified
  · exact step191_verified
  · exact step192_verified
  · exact step193_verified
  · exact step194_verified
  · exact step194_verified
  · exact step194_verified
  · exact step194_verified
theorem route13 (stage : Fin 17) : Checked (request 13 stage) := by
  fin_cases stage
  · exact step195_verified
  · exact step196_verified
  · exact step197_verified
  · exact step198_verified
  · exact step199_verified
  · exact step200_verified
  · exact step201_verified
  · exact step202_verified
  · exact step203_verified
  · exact step202_verified
  · exact step204_verified
  · exact step205_verified
  · exact step206_verified
  · exact step207_verified
  · exact step207_verified
  · exact step207_verified
  · exact step207_verified
theorem route14 (stage : Fin 17) : Checked (request 14 stage) := by
  fin_cases stage
  · exact step208_verified
  · exact step209_verified
  · exact step210_verified
  · exact step211_verified
  · exact step212_verified
  · exact step213_verified
  · exact step214_verified
  · exact step215_verified
  · exact step216_verified
  · exact step215_verified
  · exact step217_verified
  · exact step218_verified
  · exact step219_verified
  · exact step220_verified
  · exact step221_verified
  · exact step222_verified
  · exact step223_verified
theorem route15 (stage : Fin 17) : Checked (request 15 stage) := by
  fin_cases stage
  · exact step224_verified
  · exact step225_verified
  · exact step226_verified
  · exact step227_verified
  · exact step228_verified
  · exact step229_verified
  · exact step230_verified
  · exact step231_verified
  · exact step232_verified
  · exact step231_verified
  · exact step233_verified
  · exact step234_verified
  · exact step235_verified
  · exact step236_verified
  · exact step237_verified
  · exact step238_verified
  · exact step239_verified
theorem route16 (stage : Fin 17) : Checked (request 16 stage) := by
  fin_cases stage
  · exact step240_verified
  · exact step241_verified
  · exact step242_verified
  · exact step243_verified
  · exact step244_verified
  · exact step245_verified
  · exact step246_verified
  · exact step247_verified
  · exact step248_verified
  · exact step247_verified
  · exact step249_verified
  · exact step250_verified
  · exact step251_verified
  · exact step252_verified
  · exact step253_verified
  · exact step254_verified
  · exact step255_verified
theorem route17 (stage : Fin 17) : Checked (request 17 stage) := by
  fin_cases stage
  · exact step256_verified
  · exact step257_verified
  · exact step258_verified
  · exact step259_verified
  · exact step260_verified
  · exact step261_verified
  · exact step262_verified
  · exact step263_verified
  · exact step264_verified
  · exact step263_verified
  · exact step265_verified
  · exact step266_verified
  · exact step267_verified
  · exact step268_verified
  · exact step269_verified
  · exact step270_verified
  · exact step271_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes2

section Merged6967_R6966ProofHelperRescueRoutes3
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route18 (stage : Fin 17) : Checked (request 18 stage) := by
  fin_cases stage
  · exact step272_verified
  · exact step273_verified
  · exact step274_verified
  · exact step275_verified
  · exact step276_verified
  · exact step277_verified
  · exact step278_verified
  · exact step279_verified
  · exact step280_verified
  · exact step279_verified
  · exact step281_verified
  · exact step282_verified
  · exact step282_verified
  · exact step283_verified
  · exact step284_verified
  · exact step285_verified
  · exact step286_verified
theorem route19 (stage : Fin 17) : Checked (request 19 stage) := by
  fin_cases stage
  · exact step287_verified
  · exact step288_verified
  · exact step289_verified
  · exact step290_verified
  · exact step291_verified
  · exact step292_verified
  · exact step293_verified
  · exact step294_verified
  · exact step295_verified
  · exact step294_verified
  · exact step296_verified
  · exact step297_verified
  · exact step298_verified
  · exact step299_verified
  · exact step300_verified
  · exact step301_verified
  · exact step302_verified
theorem route20 (stage : Fin 17) : Checked (request 20 stage) := by
  fin_cases stage
  · exact step303_verified
  · exact step304_verified
  · exact step305_verified
  · exact step306_verified
  · exact step307_verified
  · exact step308_verified
  · exact step309_verified
  · exact step310_verified
  · exact step311_verified
  · exact step310_verified
  · exact step312_verified
  · exact step313_verified
  · exact step314_verified
  · exact step315_verified
  · exact step316_verified
  · exact step317_verified
  · exact step318_verified
theorem route21 (stage : Fin 17) : Checked (request 21 stage) := by
  fin_cases stage
  · exact step319_verified
  · exact step320_verified
  · exact step321_verified
  · exact step322_verified
  · exact step323_verified
  · exact step324_verified
  · exact step325_verified
  · exact step326_verified
  · exact step327_verified
  · exact step326_verified
  · exact step328_verified
  · exact step329_verified
  · exact step330_verified
  · exact step331_verified
  · exact step332_verified
  · exact step333_verified
  · exact step334_verified
theorem route22 (stage : Fin 17) : Checked (request 22 stage) := by
  fin_cases stage
  · exact step335_verified
  · exact step336_verified
  · exact step337_verified
  · exact step338_verified
  · exact step339_verified
  · exact step340_verified
  · exact step341_verified
  · exact step342_verified
  · exact step343_verified
  · exact step342_verified
  · exact step344_verified
  · exact step345_verified
  · exact step346_verified
  · exact step347_verified
  · exact step348_verified
  · exact step349_verified
  · exact step350_verified
theorem route23 (stage : Fin 17) : Checked (request 23 stage) := by
  fin_cases stage
  · exact step351_verified
  · exact step352_verified
  · exact step353_verified
  · exact step354_verified
  · exact step355_verified
  · exact step356_verified
  · exact step357_verified
  · exact step358_verified
  · exact step359_verified
  · exact step358_verified
  · exact step360_verified
  · exact step361_verified
  · exact step362_verified
  · exact step363_verified
  · exact step364_verified
  · exact step365_verified
  · exact step366_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes3

section Merged6967_R6966ProofHelperRescueRoutes4
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route24 (stage : Fin 17) : Checked (request 24 stage) := by
  fin_cases stage
  · exact step367_verified
  · exact step368_verified
  · exact step369_verified
  · exact step370_verified
  · exact step371_verified
  · exact step372_verified
  · exact step373_verified
  · exact step374_verified
  · exact step375_verified
  · exact step374_verified
  · exact step376_verified
  · exact step377_verified
  · exact step378_verified
  · exact step379_verified
  · exact step380_verified
  · exact step381_verified
  · exact step382_verified
theorem route25 (stage : Fin 17) : Checked (request 25 stage) := by
  fin_cases stage
  · exact step383_verified
  · exact step384_verified
  · exact step385_verified
  · exact step386_verified
  · exact step387_verified
  · exact step388_verified
  · exact step389_verified
  · exact step390_verified
  · exact step391_verified
  · exact step390_verified
  · exact step392_verified
  · exact step393_verified
  · exact step394_verified
  · exact step395_verified
  · exact step396_verified
  · exact step397_verified
  · exact step398_verified
theorem route26 (stage : Fin 17) : Checked (request 26 stage) := by
  fin_cases stage
  · exact step399_verified
  · exact step400_verified
  · exact step401_verified
  · exact step402_verified
  · exact step403_verified
  · exact step404_verified
  · exact step405_verified
  · exact step406_verified
  · exact step407_verified
  · exact step406_verified
  · exact step408_verified
  · exact step409_verified
  · exact step410_verified
  · exact step411_verified
  · exact step412_verified
  · exact step413_verified
  · exact step414_verified
theorem route27 (stage : Fin 17) : Checked (request 27 stage) := by
  fin_cases stage
  · exact step415_verified
  · exact step416_verified
  · exact step417_verified
  · exact step418_verified
  · exact step419_verified
  · exact step420_verified
  · exact step421_verified
  · exact step422_verified
  · exact step423_verified
  · exact step422_verified
  · exact step424_verified
  · exact step425_verified
  · exact step426_verified
  · exact step427_verified
  · exact step428_verified
  · exact step429_verified
  · exact step430_verified
theorem route28 (stage : Fin 17) : Checked (request 28 stage) := by
  fin_cases stage
  · exact step431_verified
  · exact step432_verified
  · exact step433_verified
  · exact step434_verified
  · exact step435_verified
  · exact step436_verified
  · exact step437_verified
  · exact step438_verified
  · exact step439_verified
  · exact step438_verified
  · exact step440_verified
  · exact step441_verified
  · exact step442_verified
  · exact step443_verified
  · exact step444_verified
  · exact step445_verified
  · exact step446_verified
theorem route29 (stage : Fin 17) : Checked (request 29 stage) := by
  fin_cases stage
  · exact step447_verified
  · exact step448_verified
  · exact step449_verified
  · exact step450_verified
  · exact step451_verified
  · exact step452_verified
  · exact step453_verified
  · exact step454_verified
  · exact step455_verified
  · exact step454_verified
  · exact step456_verified
  · exact step457_verified
  · exact step458_verified
  · exact step459_verified
  · exact step460_verified
  · exact step461_verified
  · exact step462_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes4

section Merged6967_R6966ProofHelperRescueRoutes5
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route30 (stage : Fin 17) : Checked (request 30 stage) := by
  fin_cases stage
  · exact step463_verified
  · exact step464_verified
  · exact step465_verified
  · exact step466_verified
  · exact step467_verified
  · exact step468_verified
  · exact step469_verified
  · exact step470_verified
  · exact step471_verified
  · exact step470_verified
  · exact step472_verified
  · exact step473_verified
  · exact step474_verified
  · exact step475_verified
  · exact step476_verified
  · exact step477_verified
  · exact step478_verified
theorem route31 (stage : Fin 17) : Checked (request 31 stage) := by
  fin_cases stage
  · exact step479_verified
  · exact step480_verified
  · exact step481_verified
  · exact step482_verified
  · exact step483_verified
  · exact step484_verified
  · exact step485_verified
  · exact step486_verified
  · exact step487_verified
  · exact step486_verified
  · exact step488_verified
  · exact step489_verified
  · exact step490_verified
  · exact step491_verified
  · exact step492_verified
  · exact step493_verified
  · exact step494_verified
theorem route32 (stage : Fin 17) : Checked (request 32 stage) := by
  fin_cases stage
  · exact step495_verified
  · exact step496_verified
  · exact step497_verified
  · exact step498_verified
  · exact step499_verified
  · exact step500_verified
  · exact step501_verified
  · exact step502_verified
  · exact step503_verified
  · exact step502_verified
  · exact step504_verified
  · exact step505_verified
  · exact step506_verified
  · exact step507_verified
  · exact step508_verified
  · exact step509_verified
  · exact step510_verified
theorem route33 (stage : Fin 17) : Checked (request 33 stage) := by
  fin_cases stage
  · exact step511_verified
  · exact step512_verified
  · exact step513_verified
  · exact step514_verified
  · exact step515_verified
  · exact step516_verified
  · exact step517_verified
  · exact step518_verified
  · exact step519_verified
  · exact step518_verified
  · exact step520_verified
  · exact step521_verified
  · exact step522_verified
  · exact step523_verified
  · exact step524_verified
  · exact step525_verified
  · exact step526_verified
theorem route34 (stage : Fin 17) : Checked (request 34 stage) := by
  fin_cases stage
  · exact step527_verified
  · exact step528_verified
  · exact step529_verified
  · exact step530_verified
  · exact step531_verified
  · exact step532_verified
  · exact step533_verified
  · exact step534_verified
  · exact step535_verified
  · exact step534_verified
  · exact step536_verified
  · exact step537_verified
  · exact step538_verified
  · exact step539_verified
  · exact step540_verified
  · exact step541_verified
  · exact step542_verified
theorem route35 (stage : Fin 17) : Checked (request 35 stage) := by
  fin_cases stage
  · exact step543_verified
  · exact step544_verified
  · exact step545_verified
  · exact step546_verified
  · exact step547_verified
  · exact step548_verified
  · exact step549_verified
  · exact step550_verified
  · exact step551_verified
  · exact step550_verified
  · exact step552_verified
  · exact step553_verified
  · exact step554_verified
  · exact step555_verified
  · exact step556_verified
  · exact step557_verified
  · exact step558_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes5

section Merged6967_R6966ProofHelperRescueRoutes6
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route36 (stage : Fin 17) : Checked (request 36 stage) := by
  fin_cases stage
  · exact step559_verified
  · exact step560_verified
  · exact step561_verified
  · exact step562_verified
  · exact step563_verified
  · exact step564_verified
  · exact step565_verified
  · exact step566_verified
  · exact step567_verified
  · exact step566_verified
  · exact step568_verified
  · exact step569_verified
  · exact step570_verified
  · exact step571_verified
  · exact step572_verified
  · exact step573_verified
  · exact step574_verified
theorem route37 (stage : Fin 17) : Checked (request 37 stage) := by
  fin_cases stage
  · exact step575_verified
  · exact step576_verified
  · exact step577_verified
  · exact step578_verified
  · exact step579_verified
  · exact step580_verified
  · exact step581_verified
  · exact step582_verified
  · exact step583_verified
  · exact step582_verified
  · exact step584_verified
  · exact step585_verified
  · exact step586_verified
  · exact step587_verified
  · exact step588_verified
  · exact step589_verified
  · exact step590_verified
theorem route38 (stage : Fin 17) : Checked (request 38 stage) := by
  fin_cases stage
  · exact step591_verified
  · exact step592_verified
  · exact step593_verified
  · exact step594_verified
  · exact step595_verified
  · exact step596_verified
  · exact step597_verified
  · exact step598_verified
  · exact step599_verified
  · exact step598_verified
  · exact step600_verified
  · exact step601_verified
  · exact step602_verified
  · exact step603_verified
  · exact step604_verified
  · exact step605_verified
  · exact step606_verified
theorem route39 (stage : Fin 17) : Checked (request 39 stage) := by
  fin_cases stage
  · exact step607_verified
  · exact step608_verified
  · exact step609_verified
  · exact step610_verified
  · exact step611_verified
  · exact step612_verified
  · exact step613_verified
  · exact step614_verified
  · exact step615_verified
  · exact step614_verified
  · exact step616_verified
  · exact step617_verified
  · exact step618_verified
  · exact step619_verified
  · exact step620_verified
  · exact step621_verified
  · exact step622_verified
theorem route40 (stage : Fin 17) : Checked (request 40 stage) := by
  fin_cases stage
  · exact step623_verified
  · exact step624_verified
  · exact step625_verified
  · exact step626_verified
  · exact step627_verified
  · exact step628_verified
  · exact step629_verified
  · exact step630_verified
  · exact step631_verified
  · exact step630_verified
  · exact step632_verified
  · exact step633_verified
  · exact step634_verified
  · exact step635_verified
  · exact step636_verified
  · exact step637_verified
  · exact step638_verified
theorem route41 (stage : Fin 17) : Checked (request 41 stage) := by
  fin_cases stage
  · exact step639_verified
  · exact step640_verified
  · exact step641_verified
  · exact step642_verified
  · exact step643_verified
  · exact step644_verified
  · exact step645_verified
  · exact step646_verified
  · exact step647_verified
  · exact step646_verified
  · exact step648_verified
  · exact step649_verified
  · exact step650_verified
  · exact step651_verified
  · exact step652_verified
  · exact step653_verified
  · exact step654_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes6

section Merged6967_R6966ProofHelperRescueRoutes7
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route42 (stage : Fin 17) : Checked (request 42 stage) := by
  fin_cases stage
  · exact step655_verified
  · exact step656_verified
  · exact step657_verified
  · exact step658_verified
  · exact step659_verified
  · exact step660_verified
  · exact step661_verified
  · exact step662_verified
  · exact step663_verified
  · exact step662_verified
  · exact step664_verified
  · exact step665_verified
  · exact step666_verified
  · exact step667_verified
  · exact step668_verified
  · exact step669_verified
  · exact step670_verified
theorem route43 (stage : Fin 17) : Checked (request 43 stage) := by
  fin_cases stage
  · exact step671_verified
  · exact step672_verified
  · exact step673_verified
  · exact step674_verified
  · exact step675_verified
  · exact step676_verified
  · exact step677_verified
  · exact step678_verified
  · exact step679_verified
  · exact step678_verified
  · exact step680_verified
  · exact step681_verified
  · exact step682_verified
  · exact step683_verified
  · exact step684_verified
  · exact step685_verified
  · exact step686_verified
theorem route44 (stage : Fin 17) : Checked (request 44 stage) := by
  fin_cases stage
  · exact step687_verified
  · exact step688_verified
  · exact step689_verified
  · exact step690_verified
  · exact step691_verified
  · exact step692_verified
  · exact step693_verified
  · exact step694_verified
  · exact step695_verified
  · exact step694_verified
  · exact step696_verified
  · exact step697_verified
  · exact step698_verified
  · exact step699_verified
  · exact step700_verified
  · exact step701_verified
  · exact step702_verified
theorem route45 (stage : Fin 17) : Checked (request 45 stage) := by
  fin_cases stage
  · exact step703_verified
  · exact step704_verified
  · exact step705_verified
  · exact step706_verified
  · exact step707_verified
  · exact step708_verified
  · exact step709_verified
  · exact step710_verified
  · exact step711_verified
  · exact step710_verified
  · exact step712_verified
  · exact step713_verified
  · exact step714_verified
  · exact step715_verified
  · exact step716_verified
  · exact step717_verified
  · exact step718_verified
theorem route46 (stage : Fin 17) : Checked (request 46 stage) := by
  fin_cases stage
  · exact step719_verified
  · exact step720_verified
  · exact step721_verified
  · exact step722_verified
  · exact step723_verified
  · exact step724_verified
  · exact step725_verified
  · exact step726_verified
  · exact step727_verified
  · exact step726_verified
  · exact step728_verified
  · exact step729_verified
  · exact step730_verified
  · exact step731_verified
  · exact step732_verified
  · exact step733_verified
  · exact step734_verified
theorem route47 (stage : Fin 17) : Checked (request 47 stage) := by
  fin_cases stage
  · exact step735_verified
  · exact step736_verified
  · exact step737_verified
  · exact step738_verified
  · exact step739_verified
  · exact step740_verified
  · exact step741_verified
  · exact step742_verified
  · exact step743_verified
  · exact step742_verified
  · exact step744_verified
  · exact step745_verified
  · exact step746_verified
  · exact step747_verified
  · exact step748_verified
  · exact step749_verified
  · exact step750_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes7

section Merged6967_R6966ProofHelperRescueRoutes8
set_option Elab.async false






set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route48 (stage : Fin 17) : Checked (request 48 stage) := by
  fin_cases stage
  · exact step751_verified
  · exact step752_verified
  · exact step753_verified
  · exact step754_verified
  · exact step755_verified
  · exact step756_verified
  · exact step757_verified
  · exact step758_verified
  · exact step759_verified
  · exact step758_verified
  · exact step760_verified
  · exact step761_verified
  · exact step762_verified
  · exact step763_verified
  · exact step764_verified
  · exact step765_verified
  · exact step766_verified
theorem route49 (stage : Fin 17) : Checked (request 49 stage) := by
  fin_cases stage
  · exact step767_verified
  · exact step768_verified
  · exact step769_verified
  · exact step770_verified
  · exact step771_verified
  · exact step772_verified
  · exact step773_verified
  · exact step774_verified
  · exact step775_verified
  · exact step774_verified
  · exact step776_verified
  · exact step777_verified
  · exact step778_verified
  · exact step779_verified
  · exact step780_verified
  · exact step781_verified
  · exact step782_verified
theorem route50 (stage : Fin 17) : Checked (request 50 stage) := by
  fin_cases stage
  · exact step783_verified
  · exact step784_verified
  · exact step785_verified
  · exact step786_verified
  · exact step787_verified
  · exact step788_verified
  · exact step789_verified
  · exact step790_verified
  · exact step791_verified
  · exact step790_verified
  · exact step792_verified
  · exact step793_verified
  · exact step794_verified
  · exact step795_verified
  · exact step796_verified
  · exact step797_verified
  · exact step798_verified
theorem route51 (stage : Fin 17) : Checked (request 51 stage) := by
  fin_cases stage
  · exact step799_verified
  · exact step800_verified
  · exact step801_verified
  · exact step802_verified
  · exact step803_verified
  · exact step804_verified
  · exact step805_verified
  · exact step806_verified
  · exact step807_verified
  · exact step806_verified
  · exact step808_verified
  · exact step809_verified
  · exact step810_verified
  · exact step811_verified
  · exact step812_verified
  · exact step813_verified
  · exact step814_verified
theorem route52 (stage : Fin 17) : Checked (request 52 stage) := by
  fin_cases stage
  · exact step815_verified
  · exact step816_verified
  · exact step817_verified
  · exact step818_verified
  · exact step819_verified
  · exact step820_verified
  · exact step821_verified
  · exact step822_verified
  · exact step823_verified
  · exact step822_verified
  · exact step824_verified
  · exact step825_verified
  · exact step826_verified
  · exact step827_verified
  · exact step828_verified
  · exact step829_verified
  · exact step830_verified
theorem route53 (stage : Fin 17) : Checked (request 53 stage) := by
  fin_cases stage
  · exact step831_verified
  · exact step832_verified
  · exact step833_verified
  · exact step834_verified
  · exact step835_verified
  · exact step836_verified
  · exact step837_verified
  · exact step838_verified
  · exact step839_verified
  · exact step838_verified
  · exact step840_verified
  · exact step841_verified
  · exact step842_verified
  · exact step843_verified
  · exact step844_verified
  · exact step845_verified
  · exact step846_verified

end Research6966.HelperRescueCatalogue

end Merged6967_R6966ProofHelperRescueRoutes8

section Merged6967_R6966ProofHelperWindowCatalogue
set_option Elab.async false
























set_option Elab.async false
namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate
set_option maxRecDepth 18000
set_option maxHeartbeats 0
private def certified : Fin 264 → {w : Witness // Verified w} :=
  ![⟨bank0, bank0_verified⟩,
    ⟨bank1, bank1_verified⟩,
    ⟨bank2, bank2_verified⟩,
    ⟨bank3, bank3_verified⟩,
    ⟨bank4, bank4_verified⟩,
    ⟨bank5, bank5_verified⟩,
    ⟨bank6, bank6_verified⟩,
    ⟨bank7, bank7_verified⟩,
    ⟨bank8, bank8_verified⟩,
    ⟨bank9, bank9_verified⟩,
    ⟨bank10, bank10_verified⟩,
    ⟨bank11, bank11_verified⟩,
    ⟨bank12, bank12_verified⟩,
    ⟨bank13, bank13_verified⟩,
    ⟨bank14, bank14_verified⟩,
    ⟨bank15, bank15_verified⟩,
    ⟨bank16, bank16_verified⟩,
    ⟨bank17, bank17_verified⟩,
    ⟨bank18, bank18_verified⟩,
    ⟨bank19, bank19_verified⟩,
    ⟨bank20, bank20_verified⟩,
    ⟨bank21, bank21_verified⟩,
    ⟨bank22, bank22_verified⟩,
    ⟨bank23, bank23_verified⟩,
    ⟨bank24, bank24_verified⟩,
    ⟨bank25, bank25_verified⟩,
    ⟨bank26, bank26_verified⟩,
    ⟨bank27, bank27_verified⟩,
    ⟨bank28, bank28_verified⟩,
    ⟨bank29, bank29_verified⟩,
    ⟨bank30, bank30_verified⟩,
    ⟨bank31, bank31_verified⟩,
    ⟨bank32, bank32_verified⟩,
    ⟨bank33, bank33_verified⟩,
    ⟨bank34, bank34_verified⟩,
    ⟨bank35, bank35_verified⟩,
    ⟨bank36, bank36_verified⟩,
    ⟨bank37, bank37_verified⟩,
    ⟨bank38, bank38_verified⟩,
    ⟨bank39, bank39_verified⟩,
    ⟨bank40, bank40_verified⟩,
    ⟨bank41, bank41_verified⟩,
    ⟨bank42, bank42_verified⟩,
    ⟨bank43, bank43_verified⟩,
    ⟨bank44, bank44_verified⟩,
    ⟨bank45, bank45_verified⟩,
    ⟨bank46, bank46_verified⟩,
    ⟨bank47, bank47_verified⟩,
    ⟨bank48, bank48_verified⟩,
    ⟨bank49, bank49_verified⟩,
    ⟨bank50, bank50_verified⟩,
    ⟨bank51, bank51_verified⟩,
    ⟨bank52, bank52_verified⟩,
    ⟨bank53, bank53_verified⟩,
    ⟨bank54, bank54_verified⟩,
    ⟨bank55, bank55_verified⟩,
    ⟨bank56, bank56_verified⟩,
    ⟨bank57, bank57_verified⟩,
    ⟨bank58, bank58_verified⟩,
    ⟨bank59, bank59_verified⟩,
    ⟨bank60, bank60_verified⟩,
    ⟨bank61, bank61_verified⟩,
    ⟨bank62, bank62_verified⟩,
    ⟨bank63, bank63_verified⟩,
    ⟨bank64, bank64_verified⟩,
    ⟨bank65, bank65_verified⟩,
    ⟨bank66, bank66_verified⟩,
    ⟨bank67, bank67_verified⟩,
    ⟨bank68, bank68_verified⟩,
    ⟨bank69, bank69_verified⟩,
    ⟨bank70, bank70_verified⟩,
    ⟨bank71, bank71_verified⟩,
    ⟨bank72, bank72_verified⟩,
    ⟨bank73, bank73_verified⟩,
    ⟨bank74, bank74_verified⟩,
    ⟨bank75, bank75_verified⟩,
    ⟨bank76, bank76_verified⟩,
    ⟨bank77, bank77_verified⟩,
    ⟨bank78, bank78_verified⟩,
    ⟨bank79, bank79_verified⟩,
    ⟨bank80, bank80_verified⟩,
    ⟨bank81, bank81_verified⟩,
    ⟨bank82, bank82_verified⟩,
    ⟨bank83, bank83_verified⟩,
    ⟨bank84, bank84_verified⟩,
    ⟨bank85, bank85_verified⟩,
    ⟨bank86, bank86_verified⟩,
    ⟨bank87, bank87_verified⟩,
    ⟨bank88, bank88_verified⟩,
    ⟨bank89, bank89_verified⟩,
    ⟨bank90, bank90_verified⟩,
    ⟨bank91, bank91_verified⟩,
    ⟨bank92, bank92_verified⟩,
    ⟨bank93, bank93_verified⟩,
    ⟨bank94, bank94_verified⟩,
    ⟨bank95, bank95_verified⟩,
    ⟨bank96, bank96_verified⟩,
    ⟨bank97, bank97_verified⟩,
    ⟨bank98, bank98_verified⟩,
    ⟨bank99, bank99_verified⟩,
    ⟨bank100, bank100_verified⟩,
    ⟨bank101, bank101_verified⟩,
    ⟨bank102, bank102_verified⟩,
    ⟨bank103, bank103_verified⟩,
    ⟨bank104, bank104_verified⟩,
    ⟨bank105, bank105_verified⟩,
    ⟨bank106, bank106_verified⟩,
    ⟨bank107, bank107_verified⟩,
    ⟨bank108, bank108_verified⟩,
    ⟨bank109, bank109_verified⟩,
    ⟨bank110, bank110_verified⟩,
    ⟨bank111, bank111_verified⟩,
    ⟨bank112, bank112_verified⟩,
    ⟨bank113, bank113_verified⟩,
    ⟨bank114, bank114_verified⟩,
    ⟨bank115, bank115_verified⟩,
    ⟨bank116, bank116_verified⟩,
    ⟨bank117, bank117_verified⟩,
    ⟨bank118, bank118_verified⟩,
    ⟨bank119, bank119_verified⟩,
    ⟨bank120, bank120_verified⟩,
    ⟨bank121, bank121_verified⟩,
    ⟨bank122, bank122_verified⟩,
    ⟨bank123, bank123_verified⟩,
    ⟨bank124, bank124_verified⟩,
    ⟨bank125, bank125_verified⟩,
    ⟨bank126, bank126_verified⟩,
    ⟨bank127, bank127_verified⟩,
    ⟨bank128, bank128_verified⟩,
    ⟨bank129, bank129_verified⟩,
    ⟨bank130, bank130_verified⟩,
    ⟨bank131, bank131_verified⟩,
    ⟨bank132, bank132_verified⟩,
    ⟨bank133, bank133_verified⟩,
    ⟨bank134, bank134_verified⟩,
    ⟨bank135, bank135_verified⟩,
    ⟨bank136, bank136_verified⟩,
    ⟨bank137, bank137_verified⟩,
    ⟨bank138, bank138_verified⟩,
    ⟨bank139, bank139_verified⟩,
    ⟨bank140, bank140_verified⟩,
    ⟨bank141, bank141_verified⟩,
    ⟨bank142, bank142_verified⟩,
    ⟨bank143, bank143_verified⟩,
    ⟨bank144, bank144_verified⟩,
    ⟨bank145, bank145_verified⟩,
    ⟨bank146, bank146_verified⟩,
    ⟨bank147, bank147_verified⟩,
    ⟨bank148, bank148_verified⟩,
    ⟨bank149, bank149_verified⟩,
    ⟨bank150, bank150_verified⟩,
    ⟨bank151, bank151_verified⟩,
    ⟨bank152, bank152_verified⟩,
    ⟨bank153, bank153_verified⟩,
    ⟨bank154, bank154_verified⟩,
    ⟨bank155, bank155_verified⟩,
    ⟨bank156, bank156_verified⟩,
    ⟨bank157, bank157_verified⟩,
    ⟨bank158, bank158_verified⟩,
    ⟨bank159, bank159_verified⟩,
    ⟨bank160, bank160_verified⟩,
    ⟨bank161, bank161_verified⟩,
    ⟨bank162, bank162_verified⟩,
    ⟨bank163, bank163_verified⟩,
    ⟨bank164, bank164_verified⟩,
    ⟨bank165, bank165_verified⟩,
    ⟨bank166, bank166_verified⟩,
    ⟨bank167, bank167_verified⟩,
    ⟨bank168, bank168_verified⟩,
    ⟨bank169, bank169_verified⟩,
    ⟨bank170, bank170_verified⟩,
    ⟨bank171, bank171_verified⟩,
    ⟨bank172, bank172_verified⟩,
    ⟨bank173, bank173_verified⟩,
    ⟨bank174, bank174_verified⟩,
    ⟨bank175, bank175_verified⟩,
    ⟨bank176, bank176_verified⟩,
    ⟨bank177, bank177_verified⟩,
    ⟨bank178, bank178_verified⟩,
    ⟨bank179, bank179_verified⟩,
    ⟨bank180, bank180_verified⟩,
    ⟨bank181, bank181_verified⟩,
    ⟨bank182, bank182_verified⟩,
    ⟨bank183, bank183_verified⟩,
    ⟨bank184, bank184_verified⟩,
    ⟨bank185, bank185_verified⟩,
    ⟨bank186, bank186_verified⟩,
    ⟨bank187, bank187_verified⟩,
    ⟨bank188, bank188_verified⟩,
    ⟨bank189, bank189_verified⟩,
    ⟨bank190, bank190_verified⟩,
    ⟨bank191, bank191_verified⟩,
    ⟨bank192, bank192_verified⟩,
    ⟨bank193, bank193_verified⟩,
    ⟨bank194, bank194_verified⟩,
    ⟨bank195, bank195_verified⟩,
    ⟨bank196, bank196_verified⟩,
    ⟨bank197, bank197_verified⟩,
    ⟨bank198, bank198_verified⟩,
    ⟨bank199, bank199_verified⟩,
    ⟨bank200, bank200_verified⟩,
    ⟨bank201, bank201_verified⟩,
    ⟨bank202, bank202_verified⟩,
    ⟨bank203, bank203_verified⟩,
    ⟨bank204, bank204_verified⟩,
    ⟨bank205, bank205_verified⟩,
    ⟨bank206, bank206_verified⟩,
    ⟨bank207, bank207_verified⟩,
    ⟨bank208, bank208_verified⟩,
    ⟨bank209, bank209_verified⟩,
    ⟨bank210, bank210_verified⟩,
    ⟨bank211, bank211_verified⟩,
    ⟨bank212, bank212_verified⟩,
    ⟨bank213, bank213_verified⟩,
    ⟨bank214, bank214_verified⟩,
    ⟨bank215, bank215_verified⟩,
    ⟨bank216, bank216_verified⟩,
    ⟨bank217, bank217_verified⟩,
    ⟨bank218, bank218_verified⟩,
    ⟨bank219, bank219_verified⟩,
    ⟨bank220, bank220_verified⟩,
    ⟨bank221, bank221_verified⟩,
    ⟨bank222, bank222_verified⟩,
    ⟨bank223, bank223_verified⟩,
    ⟨bank224, bank224_verified⟩,
    ⟨bank225, bank225_verified⟩,
    ⟨bank226, bank226_verified⟩,
    ⟨bank227, bank227_verified⟩,
    ⟨bank228, bank228_verified⟩,
    ⟨bank229, bank229_verified⟩,
    ⟨bank230, bank230_verified⟩,
    ⟨bank231, bank231_verified⟩,
    ⟨bank232, bank232_verified⟩,
    ⟨bank233, bank233_verified⟩,
    ⟨bank234, bank234_verified⟩,
    ⟨bank235, bank235_verified⟩,
    ⟨bank236, bank236_verified⟩,
    ⟨bank237, bank237_verified⟩,
    ⟨bank238, bank238_verified⟩,
    ⟨bank239, bank239_verified⟩,
    ⟨bank240, bank240_verified⟩,
    ⟨bank241, bank241_verified⟩,
    ⟨bank242, bank242_verified⟩,
    ⟨bank243, bank243_verified⟩,
    ⟨bank244, bank244_verified⟩,
    ⟨bank245, bank245_verified⟩,
    ⟨bank246, bank246_verified⟩,
    ⟨bank247, bank247_verified⟩,
    ⟨bank248, bank248_verified⟩,
    ⟨bank249, bank249_verified⟩,
    ⟨bank250, bank250_verified⟩,
    ⟨bank251, bank251_verified⟩,
    ⟨bank252, bank252_verified⟩,
    ⟨bank253, bank253_verified⟩,
    ⟨bank254, bank254_verified⟩,
    ⟨bank255, bank255_verified⟩,
    ⟨bank256, bank256_verified⟩,
    ⟨bank257, bank257_verified⟩,
    ⟨bank258, bank258_verified⟩,
    ⟨bank259, bank259_verified⟩,
    ⟨bank260, bank260_verified⟩,
    ⟨bank261, bank261_verified⟩,
    ⟨bank262, bank262_verified⟩,
    ⟨bank263, bank263_verified⟩]
private theorem certified_val (i : Fin 264) : (certified i).val = ordinary i := by
  fin_cases i <;> rfl
theorem ordinary_verified (i : Fin 264) : Verified (ordinary i) := by
  rw [← certified_val i]
  exact (certified i).property
abbrev ordinary_projected_bounds (i : Fin 264) := @HelperWindowNative.projected_bounds (ordinary i) (ordinary_verified i)

end Research6966.HelperWindowCatalogue

end Merged6967_R6966ProofHelperWindowCatalogue

section Merged6967_R6966ProofNearAffineHelper
set_option Elab.async false




set_option Elab.async false

namespace Research6966.NearAffineHelper
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet FX Equation Seeds atX graphEval jetAt)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (SeedField SeedClosure Surface fibreRow)
open PadeNativeQuotient (Native)
open Lower6960.Rescue6966 (Model Family)
noncomputable section
set_option maxHeartbeats 850000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private def φ := algebraMap Seeds SeedField
def graph (H:Jet) : Pade.Row SeedField := ⟨(H.coeff 1).map φ,-(H.coeff 0).map φ⟩

theorem graph_data {H:Jet} (ir:Irreducible H) (slope:H.natDegree=1) (deg:jetDegree H=1) :
    (graph H).primitive ∧ (graph H).graphDegree=1 ∧ ∃ N:Native (graph H), N.poly=H := by
  have hn:H.coeff 1≠0:=by rw [←slope,coeff_natDegree];exact leadingCoeff_ne_zero.mpr ir.ne_zero
  have cap (j:ℕ) (nz:H.coeff j≠0) : (H.coeff j).natDegree+j≤1 := by
    have node:(H.coeff j).coeff (H.coeff j).natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz
    exact ((K1_14_2_2_2_1.jetDegree_le H 1).mp deg.le) _ _ node
  have an:(graph H).a≠0 := (Polynomial.map_ne_zero_iff (IsFractionRing.injective Seeds SeedField)).mpr hn
  have ad:(graph H).a.natDegree=0 := by
    have := cap 1 hn
    change ((H.coeff 1).map φ).natDegree=0
    rw [natDegree_map_eq_of_injective (show Function.Injective φ from IsFractionRing.injective Seeds SeedField)]
    omega
  have bd:(graph H).b.natDegree≤1 := by
    change (-(H.coeff 0).map φ).natDegree≤1
    rw [natDegree_neg]
    apply natDegree_map_le.trans
    by_cases zero:H.coeff 0=0
    · simp [zero]
    · simpa using cap 0 zero
  have cop:IsCoprime (graph H).a (graph H).b:=by
    have eq:=eq_C_of_natDegree_eq_zero ad
    have nz:(graph H).a.coeff 0≠0:=fun zero=>an (by rw [eq,zero,map_zero])
    refine ⟨C ((graph H).a.coeff 0)⁻¹,0,?_⟩
    conv_lhs => enter [1,2];rw [eq]
    simp [←Polynomial.C_mul,nz]
  refine ⟨⟨an,cop⟩,?_,?_⟩
  · unfold Pade.Row.graphDegree;rw [ad];omega
  · refine ⟨⟨H,ir.isPrimitive (by omega),1,one_ne_zero,?_⟩,rfl⟩
    let f:=algebraMap SeedField SeedClosure
    have comp (Q:Equation) : (Q.map φ).map f=Q.map K1_14_3.seedGeneric := by
      rw [Polynomial.map_map];rfl
    unfold Pade.Row.polynomial Pade.Row.map graph
    simp only [K1_14_1.jetConstant,map_one,one_mul,map_neg,map_neg,sub_neg_eq_add]
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one slope.le]
    simp [fibreRow,comp,f,φ,Polynomial.map_map,K1_14_3.seedGeneric]

private def point (z:K) (S:K[X]) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)

theorem helper_bound {u deleted} {M:Model u deleted} {Γ T:Finset K}
    (F:Family M Γ) (sub:T⊆Γ) (hi:M.overhead.toNat≤2522)
    {H:Jet} (ir:Irreducible H) (slope:H.natDegree=1) (degree:jetDegree H=1)
    (w:ℕ) (wp:0<w) (wide:seedDegree H≤w) (small:w<p)
    (zero:∀ γ∈T,jetAt H (M.label γ) (F.scalar γ)=0) :
    T.card ≤ p*w+(3*(133593*w)^2*(262144-133593)^3)/(179759-133593)^3 := by
  classical
  obtain ⟨gp,d,model,eq⟩:=graph_data ir slope degree
  let q (γ:K) : Surface := ⟨RingHom.ker (point (M.label γ) (F.scalar γ)), RingHom.ker_isPrime _⟩
  have own:NativeAffineRows.Owned F T (T.image q) model := by
    intro z hz
    refine ⟨q z,mem_image.mpr ⟨z,hz,rfl⟩,?_,fun _ h=>h⟩
    rw [eq]
    exact zero z hz
  have cap j i : (model.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _=>1) w := by
    rw [eq]
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [← Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le H w).mp wide j i)
  exact NativeAffineTariff.price_floor F sub model gp d w wp cap small 133593 (by omega)
    (by decide) (by decide) (by decide) (by decide) own

#print axioms helper_bound
end
end Research6966.NearAffineHelper

end Merged6967_R6966ProofNearAffineHelper

section Merged6967_R6966ProofPhysicalMonitor
set_option Elab.async false




set_option Elab.async false

namespace Research6966.PhysicalMonitor
open Polynomial Finset
open K1_14 (L FX Jet liftPoly graphEval atX)
open K1_14_1 (PoleData CRTLift Source seedPair poleProduct MarkResidues)
open K1_14_1_2 (markedLift markedLift_residue localLift)
open K1_14_1_4 (doubleMap)
open PhysicalChartAtMark (Chart AtSeeds H into atSeeds)
open PhysicalOriginal (atWord evalSeed)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

private abbrev inc {h} (D:PoleData h) (t:Fin 2→L):=algebraMap (AtSeeds t) (Chart D t)
private def sample {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) : Chart D t→+*F :=
  IsLocalization.Away.lift (H D t) (g:=e.comp (atSeeds t)) (by
    change IsUnit (e (atSeeds t (H D t)));rw [PhysicalChartAtMark.actual_H];exact nz.isUnit)

private theorem sample_base {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) (x:AtSeeds t) : sample D t e nz (inc D t x)=e (atSeeds t x) :=
  IsLocalization.Away.lift_eq _ _ _

private theorem sample_src {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) : (sample D t e nz).comp (into D t)=e.comp (evalSeed t) := by
  apply RingHom.ext
  intro x
  change sample D t e nz (inc D t (PhysicalChartAtMark.embed t x))=_
  rw [sample_base]
  exact congrArg e (RingHom.congr_fun (PhysicalChartAtMark.actual_comp t) x)

private theorem read_slope {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) (P:Source) (ord:L[X]) :
    ((doubleMap (into D t) P).coeff 1).eval₂ (sample D t e nz) (e ord)=e (atWord t ord (P.coeff 1)) := by
  simp only [doubleMap,coe_mapRingHom,coeff_map,eval₂_map,sample_src]
  exact (Polynomial.hom_eval₂ _ _ _ _).symm

/-- The global raw separant detects the native separant both at the
generic physical coordinate and at each regular code node. -/
theorem detects {F:Type*} [Field F] {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M) (t:Fin 2→L)
    (ok:∀ i,(Crt.denominator i).eval (t i)≠0) (S T:L[X])
    (word:poleProduct D*T+markedLift Crt t=S) (e:L[X]→+*F) (nz:e (poleProduct D)≠0) :
    e (atWord t T (data.raw.coeff 1))≠0 ↔ e (atWord t S (data.original.coeff 1))≠0 := by
  let read:=sample D t e nz
  let a:=CRTChartSpecialization.diag D t
  let b:=inc D t (localLift Crt t ok)
  let u:=inc D t (H D t).derivative
  let d:=inc D t (localLift Crt t ok).derivative
  obtain ⟨c,unit,eq⟩:=CRTChartSpecialization.chart_unit Crt t ok M data.original_prime data.raw_prime
    (data.original_slope ▸ Nat.zero_lt_one) (data.raw_slope ▸ Nat.zero_lt_one) data.original_eq data.raw_eq
  have pcap:(doubleMap (into D t) data.original).natDegree≤1:=
    natDegree_map_le.trans data.original_slope.le
  have qcap:(doubleMap (into D t) data.raw).natDegree≤1:=natDegree_map_le.trans data.raw_slope.le
  have compare:=PhysicalSeparant.nonzero_iff read (a:Chart D t) b u d c a.isUnit unit
    (doubleMap (into D t) data.original) (doubleMap (into D t) data.raw) pcap qcap eq (e T)
  have diagonal:read (a:Chart D t)=e (poleProduct D):=by
    change sample D t e nz ((CRTChartSpecialization.diag D t):Chart D t)=_
    rw [show (↑(CRTChartSpecialization.diag D t):Chart D t)=inc D t (H D t) from IsUnit.unit_spec _,
      sample_base,PhysicalChartAtMark.actual_H]
  have shift:read b=e (markedLift Crt t):=by
    change sample D t e nz (inc D t (localLift Crt t ok))=_
    rw [sample_base];exact congrArg e (K1_14_1_2.specialize_localLift Crt t ok)
  have value:read (a:Chart D t)*e T+read b=e S:=by rw [diagonal,shift,←map_mul,←map_add,word]
  rw [value] at compare
  exact (read_slope D t e nz data.raw T) ▸ (read_slope D t e nz data.original S) ▸ compare

private theorem lift_degree {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L) :
    (markedLift Crt t).natDegree≤2*h := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le ..).trans (natDegree_map_le.trans
    (natDegree_le_iff_degree_le.mpr (Crt.numerator_degree i).le))

private theorem monitor_degree {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M)
    (t:Fin 2→L) (w:ℕ) (T:L[X]) (degree:T.natDegree≤w) :
    (atWord t T (data.raw.coeff 1)).natDegree≤RawPhysicalDegree.weight w (w-1) M.raw-(w-1) := by
  change ((data.raw.coeff 1).eval₂ (evalSeed t) T).natDegree≤_
  rw [eval₂_eq_sum,Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have nz:((data.raw.coeff 1).coeff i)≠0:=mem_support_iff.mp hi
  have bound:=data.raw_weight w 1 i _ (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz)
  have nat:((evalSeed t) ((data.raw.coeff 1).coeff i)).natDegree≤((data.raw.coeff 1).coeff i).natDegree:=natDegree_map_le
  have product:=natDegree_mul_le.trans (Nat.add_le_add nat ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left i degree)))
  apply product.trans
  rw [Nat.mul_comm i w];simp only [mul_one] at bound;omega

/-- A low-weight quadratic on an actual marked word supplies one nonzero
physical polynomial of the priced degree, valid at every code node. -/
theorem witness {h} (hp:0<h) (hl:h≤131070) {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M)
    (z:K1.K) (S:K1.K[X]) (res:MarkResidues D z S) (degree:(liftPoly S).natDegree≤131071+h)
    (regular:(N.coeff 1).eval₂ (graphEval z) (atX S)≠0) :
    let w:=131071-h
    ∃ P:L[X],P≠0 ∧ P.natDegree≤RawPhysicalDegree.weight w (w-1) M.raw-(w-1) ∧
      ∀ x:L,(poleProduct D).eval x≠0 → P.eval x≠0 →
        (FixedNodeRows.evaluate (seedPair z) (liftPoly S) (PhysicalOriginal.integralA data.original)).eval x≠0 := by
  let t:=seedPair z
  let w:=131071-h
  have ok (i:Fin 2):(Crt.denominator i).eval (t i)≠0:=Crt.regular i _ (res i).1
  obtain ⟨T,divide⟩:=markedLift_residue Crt res
  have word:poleProduct D*T+markedLift Crt t=liftPoly S:=by rw [←divide];abel
  have hn:(poleProduct D)≠0:=((D.monic 0).mul (D.monic 1)).ne_zero
  have height:T.natDegree≤w := by
    by_cases zero:T=0
    · simp [zero]
    have top:=natDegree_sub_le (liftPoly S) (markedLift Crt t)
    rw [divide,natDegree_mul hn zero] at top
    have dh:(poleProduct D).natDegree=2*h:=by
      rw [poleProduct,natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero,D.degree,D.degree,two_mul]
    have fcap:=lift_degree Crt t
    rw [dh] at top;dsimp only [w];omega
  let P:=atWord t T (data.raw.coeff 1)
  have orig:=PhysicalOriginal.generically_regular data z S regular
  have embed:=IsFractionRing.injective L[X] FX
  have survives:=detects data t ok (liftPoly S) T word (algebraMap L[X] FX)
    ((map_ne_zero_iff _ embed).mpr hn)
  have nz:P≠0:=by
    have val:=survives.mpr ((map_ne_zero_iff _ embed).mpr orig)
    change algebraMap L[X] FX P≠0 at val
    exact (map_ne_zero_iff _ embed).mp val
  refine ⟨P,nz,monitor_degree data t w T height,?_⟩
  intro x good seen
  rw [PhysicalOriginal.integral_slope]
  exact (detects data t ok (liftPoly S) T word (evalRingHom x) good).mp seen

#print axioms detects
#print axioms witness
end
end Research6966.PhysicalMonitor

end Merged6967_R6966ProofPhysicalMonitor

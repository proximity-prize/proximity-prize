import ProximityPrize.SubmissionLower.R6960MarkedSheetFrame
import ProximityPrize.SubmissionLower.R6960MonicChartProbes

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
  change swapBase (translateField ChartField (inner c) (RatFunc.C (algebraMap (Polynomial L) Scalar (Polynomial.X (R:=L)))))=_
  rw [translate_const]; exact swap_z
theorem row_constant (c a:L) : rowBase c (constants a)=constants a := by
  change swapBase (translateField ChartField (inner c) (RatFunc.C (algebraMap (Polynomial L) Scalar (C a))))=_
  rw [translate_const]; exact swap_constant a

/-- In the scalar orientation, the physical abscissa and every translated
abscissa are constants. A finite scalar chart therefore remains polynomial,
and the scalar infinity chart remains integral at infinity. -/
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

/-- Move an actual integral section across a horizontal embedding into the
appropriate scalar chart. The chart test is only on the base coefficients. -/
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

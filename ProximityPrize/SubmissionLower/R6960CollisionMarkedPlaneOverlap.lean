import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapDiscriminant

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus MonicFourChartDescent
open CollisionTame Polynomial LaurentPolynomial Module
open scoped Lower6960.MonicChartProbes Polynomial
open private Lower6960.RetainedSurfaceClass.oriented_var Lower6960.RetainedSurfaceClass.oriented_line
  Lower6960.RetainedSurfaceClass.oriented_const from ProximityPrize.SubmissionLower.R6960RetainedAxisCharts
open private Lower6960.CollisionTame.overlapChart_localizes Lower6960.CollisionTame.overlapChart_fraction from ProximityPrize.SubmissionLower.R6960CollisionTameOverlapDiscriminant

private def outerPlane (j b:Bool) : Plane L≃+*baseChart (reference j b) :=
  Bivariate.swap.toRingEquiv.trans (oriented j b)

private def outerField (j b:Bool) : Plane L→+*ChartField :=
  (baseChart (reference j b)).subtype.comp (outerPlane j b).toRingHom

private theorem outerField_injective (j b:Bool) : Function.Injective (outerField j b) :=
  Subtype.val_injective.comp (outerPlane j b).injective

private theorem outer_X (j b:Bool) :
    outerField j b Polynomial.X=chartCoordinate b (coordinate (!j)) := by
  change ((oriented j b (Bivariate.swap Polynomial.X)):ChartField)=_
  rw [Bivariate.swap_Y]
  exact Lower6960.RetainedSurfaceClass.oriented_line j b

private theorem outer_CX (j b:Bool) :
    outerField j b (Polynomial.C Polynomial.X)=coordinate j := by
  change ((oriented j b (Bivariate.swap (Polynomial.C Polynomial.X))):ChartField)=_
  rw [Bivariate.swap_X]
  exact Lower6960.RetainedSurfaceClass.oriented_var j b

private theorem outer_CC (j b:Bool) (c:L) :
    outerField j b (Polynomial.C (Polynomial.C c))=constants c := by
  change ((oriented j b (Bivariate.swap (Polynomial.C (Polynomial.C c)))):ChartField)=_
  rw [Bivariate.swap_C_C]
  exact Lower6960.RetainedSurfaceClass.oriented_const j b c

private theorem outerField_fraction (j b:Bool) :
    let : Algebra (Plane L) ChartField := (outerField j b).toAlgebra
    IsFractionRing (Plane L) ChartField := by
  let : Algebra (Plane L) ChartField := (outerField j b).toAlgebra
  exact IsFractionRing.of_ringEquiv_left (outerPlane j b) (fun _=>rfl)

private def overlapField (j:Bool) : OverlapLaurent L→+*ChartField := by
  let A := Plane L
  let R := OverlapLaurent L
  let : Algebra A R := (overlapChart L false).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
  apply IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:A)) (g:=outerField j false)
  intro u
  have une : (u:A)≠0 := by
    obtain ⟨n,hn⟩ := u.property
    rw [←hn]
    exact pow_ne_zero _ Polynomial.X_ne_zero
  exact IsUnit.mk0 _ ((map_ne_zero_iff _ (outerField_injective j false)).mpr une)

private theorem overlap_finite (j:Bool) (a:Plane L) :
    overlapField j a.toLaurent=outerField j false a := by
  let : Algebra (Plane L) (OverlapLaurent L) := (overlapChart L false).toAlgebra
  let : IsLocalization.Away (Polynomial.X:Plane L) (OverlapLaurent L) :=
    Lower6960.CollisionTame.overlapChart_localizes L false
  exact IsLocalization.lift_eq _ _

private theorem overlap_field_chart (j b:Bool) :
    (overlapField j).comp (overlapChart L b)=outerField j b := by
  cases b with
  | false => exact RingHom.ext (overlap_finite j)
  | true =>
    apply Polynomial.ringHom_ext
    · intro r
      change overlapField j (invert ((Polynomial.C r).toLaurent))=outerField j true (Polynomial.C r)
      rw [Polynomial.toLaurent_C,invert_C,←Polynomial.toLaurent_C,overlap_finite]
      have eq : (outerField j false).comp Polynomial.C=(outerField j true).comp Polynomial.C :=
        Polynomial.ringHom_ext (fun c=>(outer_CC j false c).trans (outer_CC j true c).symm)
          ((outer_CX j false).trans (outer_CX j true).symm)
      exact DFunLike.congr_fun eq r
    · change overlapField j (invert ((Polynomial.X:Plane L).toLaurent))=outerField j true Polynomial.X
      rw [Polynomial.toLaurent_X,invert_T,outer_X]
      have finite : overlapField j (T 1)=coordinate (!j) := by
        rw [←Polynomial.toLaurent_X,overlap_finite,outer_X]
        rfl
      change overlapField j (T (-1))=(coordinate (!j))⁻¹
      have rel : overlapField j (T (-1))*coordinate (!j)=1 := by
        rw [←finite,←map_mul,←T_add]
        norm_num
      calc _ = (overlapField j (T (-1))*coordinate (!j))*(coordinate (!j))⁻¹ := by
             rw [mul_assoc,mul_inv_cancel₀ (coord_ne _),mul_one]
           _ = _ := by rw [rel,one_mul]

private theorem overlapField_fraction (j:Bool) :
    let : Algebra (OverlapLaurent L) ChartField := (overlapField j).toAlgebra
    IsFractionRing (OverlapLaurent L) ChartField := by
  let A := Plane L
  let R := OverlapLaurent L
  let : Algebra A R := (overlapChart L false).toAlgebra
  let : Algebra A ChartField := (outerField j false).toAlgebra
  let : IsFractionRing A ChartField := outerField_fraction j false
  let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
  let : Algebra R ChartField := (overlapField j).toAlgebra
  let : IsScalarTower A R ChartField := IsScalarTower.of_algebraMap_eq
    (R:=A) (S:=R) (A:=ChartField) (fun x=>(overlap_finite j x).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (Polynomial.X:A)) R ChartField

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

/-- Original chart discriminants for either ruling, always with its
fixed line coordinate placed outside. -/
def lineDiscriminant (j b:Bool) : Ideal (Plane L) :=
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := linePlaneTower j b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable (FractionRing (Plane L)) E := lineFraction_separable j b
  normalizationDiscriminant (A:=Plane L) (E:=E) (FractionRing (Plane L))

theorem line_discriminant_axis (b:Bool) : lineDiscriminant (E:=E) true b=axisDiscriminant (E:=E) b := rfl

/-- The finite plane generator in the transverse orientation is the
coordinate swap of the same discriminant; it comes from the same E. -/
theorem line_discriminant_swap :
    (lineDiscriminant (E:=E) true false).map Bivariate.swap.toRingHom =
      lineDiscriminant (E:=E) false false := by
  let A := Plane L
  let F := FractionRing A
  let e := Bivariate.swap (R:=L)
  -- Use the actual chart field on the target side to avoid identifying
  -- the two different polynomial actions on the same type.
  let T := baseChart (false,false)
  let t : A≃+*T := oriented false false
  let s : A≃+*T := oriented true false
  let D := normalizationDiscriminant (A:=T) (E:=E) ChartField
  have compare (j:Bool) :
      (lineDiscriminant (E:=E) j false).map (oriented j false).toRingHom=
        normalizationDiscriminant (A:=baseChart (reference j false)) (E:=E) ChartField := by
    let : Algebra A E := linePlaneAlgebra j false
    let : Algebra F E := lineFractionAlgebra j false
    let : SMul A F := (inferInstance : Algebra A F).toSMul
    let : IsScalarTower A F E := linePlaneTower j false
    let : FiniteDimensional F E := Module.Finite.of_basis
      (lineFractionBasis (E:=E) j false (Module.finBasis ChartField E)).val
    let : Algebra.IsSeparable F E := lineFraction_separable j false
    exact discriminant_transport (oriented j false) (linePlaneFractionEquiv j false)
      (fun a=>(linePlaneFractionEquiv_apply j false a).symm) (fun _=>rfl)
  have left : (lineDiscriminant (E:=E) true false).map s.toRingHom=D := compare true
  have right : (lineDiscriminant (E:=E) false false).map t.toRingHom=D := compare false
  have both : ((lineDiscriminant (E:=E) true false).map e.toRingHom).map t.toRingHom=
      (lineDiscriminant (E:=E) false false).map t.toRingHom := by
    rw [right,Ideal.map_map]
    exact left
  have h := congrArg (Ideal.comap t.toRingHom) both
  simpa only [Ideal.comap_map_of_bijective t.toRingHom t.bijective] using h

/-- The exact original chart generators agree up to a unit on their
actual Laurent overlap. The outer variable here is the running one. -/
theorem line_overlap_unit (j:Bool) (δf δi:Plane L)
    (f:lineDiscriminant (E:=E) j false=Ideal.span {δf})
    (i:lineDiscriminant (E:=E) j true=Ideal.span {δi}) :
    ∃ (c:L) (m:ℤ),c≠0 ∧
      (Bivariate.swap δf).toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*
        invert (Bivariate.swap δi).toLaurent := by
  let A := Plane L
  let R := OverlapLaurent L
  let F := FractionRing A
  let : Algebra R ChartField := (overlapField j).toAlgebra
  let : Algebra R E := ((algebraMap ChartField E).comp (overlapField j)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsFractionRing R ChartField := overlapField_fraction j
  let : IsNoetherianRing R := by
    let : Algebra A R := (overlapChart L false).toAlgebra
    let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
    exact IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X:A)) R inferInstance
  let : IsIntegrallyClosed R := by
    let : Algebra A R := (overlapChart L false).toAlgebra
    let : IsLocalization.Away (Polynomial.X:A) R := Lower6960.CollisionTame.overlapChart_localizes L false
    exact isIntegrallyClosed_of_isLocalization R (Submonoid.powers (Polynomial.X:A)) (by
      rintro _ ⟨n,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ Polynomial.X_ne_zero))
  have transport (b:Bool) :
    (lineDiscriminant (E:=E) j b).map Bivariate.swap.toRingHom =
      overlapChartDiscriminant L ChartField E b := by
    let aA : Algebra A E := linePlaneAlgebra j b
    let : Algebra A E := aA
    let : Algebra F E := lineFractionAlgebra j b
    let : SMul A F := (inferInstance : Algebra A F).toSMul
    let ta : IsScalarTower A F E := linePlaneTower j b
    let : IsScalarTower A F E := ta
    let : FiniteDimensional F E := Module.Finite.of_basis
      (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
    let : Algebra.IsSeparable F E := lineFraction_separable j b
    let : Algebra A ChartField := ((overlapField j).comp (overlapChart L b)).toAlgebra
    let B := A
    let aB : Algebra B E := ((algebraMap R E).comp (overlapChart L b)).toAlgebra
    let : Algebra B E := aB
    let : IsFractionRing B ChartField := Lower6960.CollisionTame.overlapChart_fraction L ChartField b
    let tb : IsScalarTower B ChartField E := IsScalarTower.of_algebraMap_eq
      (R:=B) (S:=ChartField) (A:=E) fun _=>rfl
    have same (x:A) : algebraMap B ChartField (Bivariate.swap x)=
        linePlaneFractionEquiv j b (algebraMap A F x) := by
      change ((overlapField j).comp (overlapChart L b)) (Bivariate.swap x)=_
      rw [overlap_field_chart,linePlaneFractionEquiv_apply]
      change ((oriented j b (Bivariate.swap (Bivariate.swap x))):ChartField)=_
      rw [Bivariate.swap_swap_apply]
    exact @discriminant_transport A B F ChartField E
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      aA aB inferInstance inferInstance ta tb
      inferInstance inferInstance inferInstance inferInstance
      Bivariate.swap.toRingEquiv (linePlaneFractionEquiv j b) same (fun _=>rfl)
  have df := (transport false).symm.trans (congrArg (Ideal.map Bivariate.swap.toRingHom) f)
  have di := (transport true).symm.trans (congrArg (Ideal.map Bivariate.swap.toRingHom) i)
  rw [Ideal.map_span,Set.image_singleton] at df di
  exact actual_overlap_unit L ChartField E _ _ df di

#print axioms line_overlap_unit
#print axioms line_discriminant_swap
end
end Lower6960.CollisionMarked

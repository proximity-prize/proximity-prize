import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionMarkedPlaneOverlap
import ProximityPrize.SubmissionLower.R6960CollisionMarkedGenericFrames

set_option Elab.async false

-- merged module R6961CollisionMarkedPlaneOverlap
section Merged_R6961CollisionMarkedPlaneOverlap

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass RetainedRestrictionTorus MonicFourChartDescent
open Lower6960.CollisionTame Lower6961.CollisionTame Polynomial LaurentPolynomial Module
open scoped Lower6961.MonicChartProbes Polynomial
open Lower6961.RetainedSurfaceClass (oriented_var oriented_line oriented_const)
open Lower6960.CollisionTame (overlapChart_localizes overlapChart_fraction)

def outerPlane (j b:Bool) : Plane L≃+*baseChart (reference j b) :=
  Bivariate.swap.toRingEquiv.trans (oriented j b)

def outerField (j b:Bool) : Plane L→+*ChartField :=
  (baseChart (reference j b)).subtype.comp (outerPlane j b).toRingHom

private theorem outerField_injective (j b:Bool) : Function.Injective (outerField j b) :=
  Subtype.val_injective.comp (outerPlane j b).injective

theorem outer_X (j b:Bool) :
    outerField j b Polynomial.X=chartCoordinate b (coordinate (!j)) := by
  change ((oriented j b (Bivariate.swap Polynomial.X)):ChartField)=_
  rw [Bivariate.swap_Y]
  exact Lower6961.RetainedSurfaceClass.oriented_line j b

theorem outer_CX (j b:Bool) :
    outerField j b (Polynomial.C Polynomial.X)=coordinate j := by
  change ((oriented j b (Bivariate.swap (Polynomial.C Polynomial.X))):ChartField)=_
  rw [Bivariate.swap_X]
  exact Lower6961.RetainedSurfaceClass.oriented_var j b

theorem outer_CC (j b:Bool) (c:L) :
    outerField j b (Polynomial.C (Polynomial.C c))=constants c := by
  change ((oriented j b (Bivariate.swap (Polynomial.C (Polynomial.C c)))):ChartField)=_
  rw [Bivariate.swap_C_C]
  exact Lower6961.RetainedSurfaceClass.oriented_const j b c

theorem outerField_fraction (j b:Bool) :
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
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedPlaneOverlap

-- merged module R6961CollisionMarkedGenericFrames
section Merged_R6961CollisionMarkedGenericFrames

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass MonicFourChartDescent
open Polynomial Module Lower6960.CollisionTame Lower6961.CollisionTame Lower6960.LineEuler
open scoped Polynomial Lower6961.MonicChartProbes
open Lower6961.CollisionMarked (outerPlane outerField outer_X outer_CC outer_CX outerField_fraction)
open Lower6960.CollisionTame (genericFinite_on_plane genericFinite_fraction genericLaurent_finite genericLaurent_inverse genericInverse_fractions genericInverse coeffDenominators)

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- The generic line orientation keeps its varying coordinate outside
the fixed polynomial coefficients. -/
def genericPlaneField (j:Bool) : FractionRing (Plane L)≃+*ChartField :=
  IsFractionRing.ringEquivOfRingEquiv (K:=FractionRing (Plane L)) (L:=ChartField)
    (Lower6961.CollisionMarked.outerPlane j false)

private theorem genericPlaneField_apply (j:Bool) (p:Plane L) :
    genericPlaneField j (algebraMap (Plane L) (FractionRing (Plane L)) p)=
      Lower6961.CollisionMarked.outerField j false p :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

def lineEmbedding (j b:Bool) : GenericLine L→+*ChartField :=
  (genericPlaneField j).toRingHom.comp ((genericLaurent L).comp (chartEmbedding b).toRingHom)

private theorem lineEmbedding_fraction (j b:Bool) :
    let : Algebra (GenericLine L) ChartField := (lineEmbedding j b).toAlgebra
    IsFractionRing (GenericLine L) ChartField := by
  let R := GenericLine L
  let F := FractionRing (Plane L)
  let g := (genericLaurent L).comp (chartEmbedding b).toRingHom
  let : Algebra R F := g.toAlgebra
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : IsFractionRing R F := by
    cases b
    · exact ((congrArg (fun h:R→+*F=>@IsFractionRing R _ F _ h.toAlgebra)
        (Lower6960.CollisionTame.genericLaurent_finite L)).symm ▸
          Lower6960.CollisionTame.genericFinite_fraction L)
    · exact ((congrArg (fun h:R→+*F=>@IsFractionRing R _ F _ h.toAlgebra)
        (Lower6960.CollisionTame.genericLaurent_inverse L)).symm ▸
          Lower6960.CollisionTame.genericInverse_fractions L)
  let e : F≃ₐ[R]ChartField := { genericPlaneField j with commutes' := fun _=>rfl }
  exact IsFractionRing.of_algEquiv e

/-- Localizing the fixed coefficients of either original plane chart
gives the corresponding actual generic polynomial chart. -/
theorem lineEmbedding_on_plane (j b:Bool) (p:Plane L) :
    lineEmbedding j b (algebraMap (Plane L) (GenericLine L) p)=
      Lower6961.CollisionMarked.outerField j b p := by
  let A := Plane L
  let R := GenericLine L
  let F := FractionRing A
  change ((genericPlaneField j).toRingHom.comp
    ((genericLaurent L).comp (chartEmbedding b).toRingHom)) (algebraMap A R p)=_
  cases b with
  | false =>
    rw [Lower6960.CollisionTame.genericLaurent_finite]
    change genericPlaneField j (genericFinite L (algebraMap A R p))=_
    rw [Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply]
  | true =>
    have map_eq :
        ((genericPlaneField j).toRingHom.comp (Lower6960.CollisionTame.genericInverse L)).comp (algebraMap A R)=
          Lower6961.CollisionMarked.outerField j true := by
      apply Polynomial.ringHom_ext
      · intro a
        have scalar : Lower6961.CollisionMarked.outerField j false (C a)=
            Lower6961.CollisionMarked.outerField j true (C a) := by
          apply DFunLike.congr_fun
            (f:=(Lower6961.CollisionMarked.outerField j false).comp C)
            (g:=(Lower6961.CollisionMarked.outerField j true).comp C)
          apply Polynomial.ringHom_ext
          · exact fun c=>(Lower6961.CollisionMarked.outer_CC j false c).trans
              (Lower6961.CollisionMarked.outer_CC j true c).symm
          · exact (Lower6961.CollisionMarked.outer_CX j false).trans
              (Lower6961.CollisionMarked.outer_CX j true).symm
        change genericPlaneField j (Lower6960.CollisionTame.genericInverse L
          ((C a : A).map (algebraMap (Polynomial L) (GenericCoefficients L))))=_
        rw [map_C]
        change genericPlaneField j ((C (algebraMap (Polynomial L) (GenericCoefficients L) a)).eval₂
          ((genericFinite L).comp C) ((genericFinite L Polynomial.X)⁻¹))=_
        rw [eval₂_C]
        change genericPlaneField j (genericFinite L (C (algebraMap (Polynomial L) (GenericCoefficients L) a)))=_
        rw [show C (algebraMap (Polynomial L) (GenericCoefficients L) a)=algebraMap A R (C a) from
          (map_C (algebraMap (Polynomial L) (GenericCoefficients L))).symm]
        rw [Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply,scalar]
      · change genericPlaneField j (Lower6960.CollisionTame.genericInverse L
          ((Polynomial.X:A).map (algebraMap (Polynomial L) (GenericCoefficients L))))=_
        rw [map_X]
        change genericPlaneField j (Polynomial.X.eval₂ ((genericFinite L).comp C)
          ((genericFinite L Polynomial.X)⁻¹))=_
        rw [eval₂_X,map_inv₀]
        have rel : genericPlaneField j (genericFinite L Polynomial.X)=coordinate (!j) := by
          have idX : (Polynomial.X:R)=algebraMap A R (Polynomial.X:A) := (map_X _).symm
          rw [idX,Lower6960.CollisionTame.genericFinite_on_plane,genericPlaneField_apply,
            Lower6961.CollisionMarked.outer_X]
          rfl
        rw [rel,Lower6961.CollisionMarked.outer_X]
        rfl
    rw [Lower6960.CollisionTame.genericLaurent_inverse]
    exact DFunLike.congr_fun map_eq p

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

/-- The actual common generic Laurent algebra, with the finite scalar
variable placed in the coefficient fraction field. -/
@[instance_reducible] def genericLineAlgebra (j:Bool) : Algebra (Laurent (GenericCoefficients L)) E :=
  (((algebraMap ChartField E).comp (genericPlaneField j).toRingHom).comp (genericLaurent L)).toAlgebra

theorem generic_line_basis (j b:Bool) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    Nonempty (Basis (Fin (finrank ChartField E)) (GenericLine L)
      (chartOrder (k:=GenericCoefficients L) (E:=E) b)) := by
  let R := GenericLine L
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : SMul R ChartField := (inferInstance : Algebra R ChartField).toSMul
  let : IsFractionRing R ChartField := lineEmbedding_fraction j b
  let : Algebra R E := ((algebraMap ChartField E).comp (lineEmbedding j b)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let C := integralClosure R E
  have inj : Function.Injective (algebraMap R E) := (algebraMap ChartField E).injective.comp
    (IsFractionRing.injective R ChartField)
  let : Module.IsTorsionFree R E := Module.IsTorsionFree.of_smul_eq_zero fun a x eq=>by
    rw [Algebra.smul_def,mul_eq_zero] at eq
    exact eq.imp (fun h=>inj (h.trans (map_zero _).symm)) id
  let : Module.Finite R C := IsIntegralClosure.finite R ChartField E C
  let : Module.Free R C := IsIntegralClosure.module_free R ChartField E C
  have rank : finrank R C=finrank ChartField E := IsIntegralClosure.rank R ChartField E C
  exact ⟨Module.finBasisOfFinrankEq R C rank⟩

/-- The trace determinant in the actual generic normalized chart is
associated to coefficient localization of the original plane generator.
Both the finite and the reciprocal charts use the same extension E. -/
theorem generic_line_trace_associated (j b:Bool) (δ:Plane L)
    (principal:lineDiscriminant (E:=E) j b=Ideal.span {δ}) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    ∀ a : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) b),
      Associated (Algebra.traceMatrix (GenericLine L) a).det
        ((Bivariate.swap δ).map (algebraMap (Polynomial L) (GenericCoefficients L))) := by
  let A := Plane L
  let B := A
  let F := FractionRing A
  let R := GenericLine L
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  let aA : Algebra A E := linePlaneAlgebra j b
  let : Algebra A E := aA
  let : Algebra F E := lineFractionAlgebra j b
  let : SMul A F := (inferInstance : Algebra A F).toSMul
  let tA : IsScalarTower A F E := linePlaneTower j b
  let : FiniteDimensional F E := Module.Finite.of_basis
    (lineFractionBasis (E:=E) j b (Module.finBasis ChartField E)).val
  let : Algebra.IsSeparable F E := lineFraction_separable j b
  let : Algebra B ChartField := (Lower6961.CollisionMarked.outerField j b).toAlgebra
  let : SMul B ChartField := (inferInstance : Algebra B ChartField).toSMul
  let : IsFractionRing B ChartField := Lower6961.CollisionMarked.outerField_fraction j b
  let aB : Algebra B E := ((algebraMap ChartField E).comp (Lower6961.CollisionMarked.outerField j b)).toAlgebra
  let : Algebra B E := aB
  let tB : IsScalarTower B ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower B ChartField E := tB
  let : Algebra R ChartField := (lineEmbedding j b).toAlgebra
  let : SMul R ChartField := (inferInstance : Algebra R ChartField).toSMul
  let : IsFractionRing R ChartField := lineEmbedding_fraction j b
  let : Algebra R E := ((algebraMap ChartField E).comp (lineEmbedding j b)).toAlgebra
  let : IsScalarTower R ChartField E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower B R ChartField := IsScalarTower.of_algebraMap_eq
    (R:=B) (S:=R) (A:=ChartField) fun p=>(lineEmbedding_on_plane j b p).symm
  let : IsScalarTower B R E := IsScalarTower.of_algebraMap_eq (R:=B) (S:=R) (A:=E) fun p=>by
    change algebraMap ChartField E (Lower6961.CollisionMarked.outerField j b p)=
      algebraMap ChartField E (lineEmbedding j b (algebraMap B R p))
    rw [lineEmbedding_on_plane]
  let e := Bivariate.swap.toRingEquiv (R:=L)
  have coord (p:A) : algebraMap B ChartField (e p)=linePlaneFractionEquiv j b (algebraMap A F p) := by
    rw [linePlaneFractionEquiv_apply]
    change (oriented j b (Bivariate.swap (Bivariate.swap p)):ChartField)=_
    rw [Bivariate.swap_swap_apply]
  have transport :=
    @discriminant_transport A B F ChartField E
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      aA aB inferInstance inferInstance tA tB
      inferInstance inferInstance inferInstance inferInstance
      e (linePlaneFractionEquiv j b) coord (fun _=>rfl)
  change (lineDiscriminant (E:=E) j b).map e.toRingHom=
    normalizationDiscriminant (A:=B) (E:=E) ChartField at transport
  rw [principal,Ideal.map_span,Set.image_singleton] at transport
  have loc := normalizationDiscriminant_map (A:=B) (R:=R) (F:=ChartField) (E:=E)
    (Lower6960.CollisionTame.coeffDenominators L)
  rw [←transport,Ideal.map_span,Set.image_singleton] at loc
  dsimp only
  intro a
  let aa : Basis (Fin (finrank ChartField E)) R (integralClosure R E) := a
  have basisDisc : normalizationDiscriminant (A:=R) (E:=E) ChartField=
      Ideal.span {(Algebra.traceMatrix R aa).det} :=
    normalizationDiscriminant_basis (A:=R) (E:=E) ChartField aa
  rw [basisDisc] at loc
  exact Ideal.span_singleton_eq_span_singleton.mp loc.symm

#print axioms generic_line_basis
#print axioms generic_line_trace_associated
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedGenericFrames

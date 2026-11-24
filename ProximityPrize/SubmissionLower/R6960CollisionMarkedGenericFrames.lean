import ProximityPrize.SubmissionLower.R6960CollisionMarkedPlaneOverlap
import ProximityPrize.SubmissionLower.R6960CollisionTameCoefficientLine

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass MonicFourChartDescent
open Polynomial Module CollisionTame LineEuler
open scoped Polynomial Lower6960.MonicChartProbes
open Lower6960.CollisionMarked (outerPlane outerField outer_X outer_CC outer_CX outerField_fraction)
open Lower6960.CollisionTame (genericFinite_on_plane genericFinite_fraction genericLaurent_finite genericLaurent_inverse genericInverse_fractions genericInverse coeffDenominators)

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- The generic line orientation keeps its varying coordinate outside
the fixed polynomial coefficients. -/
def genericPlaneField (j:Bool) : FractionRing (Plane L)≃+*ChartField :=
  IsFractionRing.ringEquivOfRingEquiv (K:=FractionRing (Plane L)) (L:=ChartField)
    (Lower6960.CollisionMarked.outerPlane j false)

private theorem genericPlaneField_apply (j:Bool) (p:Plane L) :
    genericPlaneField j (algebraMap (Plane L) (FractionRing (Plane L)) p)=
      Lower6960.CollisionMarked.outerField j false p :=
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
      Lower6960.CollisionMarked.outerField j b p := by
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
          Lower6960.CollisionMarked.outerField j true := by
      apply Polynomial.ringHom_ext
      · intro a
        have scalar : Lower6960.CollisionMarked.outerField j false (C a)=
            Lower6960.CollisionMarked.outerField j true (C a) := by
          apply DFunLike.congr_fun
            (f:=(Lower6960.CollisionMarked.outerField j false).comp C)
            (g:=(Lower6960.CollisionMarked.outerField j true).comp C)
          apply Polynomial.ringHom_ext
          · exact fun c=>(Lower6960.CollisionMarked.outer_CC j false c).trans
              (Lower6960.CollisionMarked.outer_CC j true c).symm
          · exact (Lower6960.CollisionMarked.outer_CX j false).trans
              (Lower6960.CollisionMarked.outer_CX j true).symm
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
            Lower6960.CollisionMarked.outer_X]
          rfl
        rw [rel,Lower6960.CollisionMarked.outer_X]
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
  let : Algebra B ChartField := (Lower6960.CollisionMarked.outerField j b).toAlgebra
  let : SMul B ChartField := (inferInstance : Algebra B ChartField).toSMul
  let : IsFractionRing B ChartField := Lower6960.CollisionMarked.outerField_fraction j b
  let aB : Algebra B E := ((algebraMap ChartField E).comp (Lower6960.CollisionMarked.outerField j b)).toAlgebra
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
    change algebraMap ChartField E (Lower6960.CollisionMarked.outerField j b p)=
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
end Lower6960.CollisionMarked

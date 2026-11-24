import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisLaurent
set_option synthInstance.maxHeartbeats 200000
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber MonicFourChartDescent RetainedSurfaceClass Module
open scoped Lower6960.MonicChartProbes
def linePlaneFractionEquiv (j b : Bool) : FractionRing (Plane L) ≃+* ChartField :=
  IsFractionRing.ringEquivOfRingEquiv (K:=FractionRing (Plane L)) (L:=ChartField) (oriented j b)
theorem linePlaneFractionEquiv_apply (j b : Bool) (x : Plane L) :
    linePlaneFractionEquiv j b (algebraMap (Plane L) (FractionRing (Plane L)) x)=
      ((oriented j b x):ChartField) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
variable {E : Type} [Field E] [Algebra ChartField E]
@[instance_reducible] def lineFractionAlgebra (j b:Bool) : Algebra (FractionRing (Plane L)) E :=
  ((algebraMap ChartField E).comp (linePlaneFractionEquiv j b).toRingHom).toAlgebra
theorem linePlaneTower (j b : Bool) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
    let : SMul (Plane L) (FractionRing (Plane L)) :=
      (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
    IsScalarTower (Plane L) (FractionRing (Plane L)) E := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  dsimp only
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap ChartField E ((oriented j b x):ChartField)=
    algebraMap ChartField E (linePlaneFractionEquiv j b (algebraMap (Plane L) (FractionRing (Plane L)) x))
  rw [linePlaneFractionEquiv_apply]
def lineFractionBasis {I : Type*} (j b:Bool) (v:Basis I ChartField E) :
    let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
    {w : Basis I (FractionRing (Plane L)) E // ∀ i,w i=v i} := by
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let e := linePlaneFractionEquiv j b
  have smul (r:ChartField) (x:E) : e.symm r • x=r • x := by
    rw [Algebra.smul_def,Algebra.smul_def]
    change algebraMap ChartField E (e (e.symm r))*x=algebraMap ChartField E r*x
    rw [e.apply_symm_apply]
  exact ⟨v.mapCoeffs e.symm smul,fun i=>v.mapCoeffs_apply e.symm smul i⟩
theorem lineFraction_separable [Algebra.IsSeparable ChartField E] (j b : Bool) :
    let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
    Algebra.IsSeparable (FractionRing (Plane L)) E := by
  let : Algebra (FractionRing (Plane L)) E := lineFractionAlgebra j b
  let e := linePlaneFractionEquiv j b
  apply Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl E)
  apply RingHom.ext
  intro r
  change algebraMap ChartField E (e (e.symm r))=algebraMap ChartField E r
  rw [e.apply_symm_apply]
abbrev axisPlaneFractionEquiv (b : Bool) := linePlaneFractionEquiv true b
@[instance_reducible] def axisFractionAlgebra (b : Bool) : Algebra (FractionRing (Plane L)) E :=
  lineFractionAlgebra true b
theorem axisPlaneTower (b : Bool) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    let : SMul (Plane L) (FractionRing (Plane L)) :=
      (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
    IsScalarTower (Plane L) (FractionRing (Plane L)) E :=
  linePlaneTower true b
abbrev axisFractionBasis {I : Type*} (b : Bool) (v : Basis I ChartField E) :=
  lineFractionBasis (E:=E) true b v
theorem axisFraction_separable [Algebra.IsSeparable ChartField E] (b : Bool) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra b
    Algebra.IsSeparable (FractionRing (Plane L)) E :=
  lineFraction_separable true b
#print axioms lineFractionBasis
#print axioms lineFraction_separable
end
end Lower6960.CollisionMarked

import ProximityPrize.SubmissionLower.R6960CollisionMarkedCommonAxis
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisField
import ProximityPrize.SubmissionLower.R6960CollisionMarkedProjected

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra Module
open RetainedRestrictionTorus
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct

variable {E : Type} [Field E] [Algebra ChartField E]

local instance wordAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance wordFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

private def relocatedPowerBasis (b:PowerBasis ChartField E) :
    let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
    PowerBasis (FractionRing (Plane L)) E := by
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let m := axisFractionBasis (E:=E) false b.basis
  exact { gen := b.gen, dim := b.dim, basis := m.val
          basis_eq_pow := fun i=>(m.property i).trans (b.basis_eq_pow i) }

/-- One common normalized ordinate in the torus, with its actual
leading-coefficient scaling. -/
def axisScaledOrdinate (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0) (g:E)
    (root : let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval g (projectedRaw P)=0) : Tor E := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  exact intoTorus E (reference true false)
    (axisPlaneOrder false (scaledRoot (projectedRaw P) g pn root))

/-- The matching word value uses the same scaling on each marked fibre. -/
def axisScaledWord (P:CurvatureSquares.Ordinate) (z:L) (S:L[X]) : Tor E :=
  along E true false ((projectedRaw P).leadingCoeff.eval (C z)*S)

/-- The actual marked word in the generic abscissa fibre admits its
unique nonzero projector in the common axis. The common fibre algebra
is reduced, and the original torus ordinate acts on its marked sheet
by the actual scaled word. -/
theorem actual_axis_projector [FiniteDimensional ChartField E] (p:ℕ)
    [CharP (FractionRing L[X]) p]
    (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0)
    (large:2≤P.natDegree) (small:P.natDegree<p)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root : let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (z:L) (nz:z≠0) (S:L[X]) (mark:RetainedCompression.MarkedFiber P z S) :
    ∃ η:AxisGeneric (E:=E) z, IsReduced (AxisGeneric (E:=E) z) ∧ η^2=η ∧ η≠0 ∧
      axisToGeneric (E:=E) z (red E true z
        (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S))*η=0 := by
  let : Algebra (Plane L) E := axisPlaneAlgebra false
  let : Algebra (FractionRing (Plane L)) E := axisFractionAlgebra false
  let : SMul (Plane L) (FractionRing (Plane L)) :=
    (inferInstance : Algebra (Plane L) (FractionRing (Plane L))).toSMul
  let : IsScalarTower (Plane L) (FractionRing (Plane L)) E := axisPlaneTower false
  let c := relocatedPowerBasis b
  let : FiniteDimensional (FractionRing (Plane L)) E := Module.Finite.of_basis c.basis
  let G := axisGenericData (E:=E) false z nz
  let q := (projectedRaw P).integralNormalization.map (genericFibreBase z)
  let g := G.val
  obtain ⟨e,H,_,sep,_,_,_,_,idem,nonzero,_,kills⟩ :=
    projected_word_sheet p P large small c dim root z S mark
  let η := g (e (AdjoinRoot.mk q H))
  have r : IsReduced (AdjoinRoot q) := separable_adjoinRoot_reduced q sep
  let f := g.symm.trans e.toRingEquiv.symm
  have redV : IsReduced (AxisGeneric (E:=E) z) := by
    constructor
    intro x hx
    apply f.injective
    rw [map_zero]
    exact r.eq_zero _ (hx.map f.toRingHom)
  refine ⟨η,redV,?_,fun h=>nonzero (g.map_eq_zero_iff.mp h),?_⟩
  · exact (map_pow g _ 2).symm.trans (congrArg g idem)
  let y := (projectedRaw P).leadingCoeff.eval (C z)*S
  let U := Axis E true z
  let V := FibreGeneric (E:=E) z
  let K := FractionRing L[X]
  let a := scaledRoot (projectedRaw P) b.gen pn root
  let φ := axisFibreData (E:=E) false z nz
  have wordVal : genericFibreBase z (projectedRaw P).leadingCoeff*RetainedCompression.incl S=
      algebraMap L[X] K y := by
    rw [map_mul]
    rfl
  have kills' : ((1 ⊗ₜ[L[X]] quotientMap E z a : V)-algebraMap L[X] V y)*
      e (AdjoinRoot.mk q H)=0 := by
    rw [wordVal] at kills
    exact kills
  have mapped := congrArg g kills'
  rw [map_mul,map_sub,map_zero,G.property.1,axisGenericData_scalar,φ.property.2.1] at mapped
  change (axisToGeneric (E:=E) z (red E true z (axisScaledOrdinate P pn b.gen root))-
    axisToGeneric (E:=E) z (red E true z (axisScaledWord P z S)))*η=0 at mapped
  change axisToGeneric (E:=E) z (Ideal.Quotient.mk (axisIdeal E true z)
    (axisScaledOrdinate P pn b.gen root-axisScaledWord P z S))*η=0
  rw [map_sub,map_sub]
  exact mapped

#print axioms actual_axis_projector
end
end Lower6960.CollisionMarked

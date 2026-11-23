import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisWord
import ProximityPrize.SubmissionLower.R6960MonicChartProbes
import ProximityPrize.SubmissionLower.R6960RetainedLinearAssembly

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (Scalar ChartField)
open NormalizedFiber RetainedSurfaceClass MonicChartProbes Polynomial
open scoped Polynomial Lower6960.MonicChart
open private Lower6960.MonicChartProbes.planeMap_finite from ProximityPrize.SubmissionLower.R6960MonicChartProbes

variable {E:Type} [Field E] [Algebra ChartField E]

/-- The root used in the actual bounded surface theorem is the root of
the same ordinate equation in the scalar-outside plane model. -/
theorem projected_root_of_seed (P:CurvatureSquares.Ordinate) (α:E)
    (root : aeval α ((RetainedLinear.toSeed P).map (algebraMap Scalar[X] ChartField))=0) :
    let : Algebra (Plane L) E := axisPlaneAlgebra false
    aeval α (projectedRaw P)=0 := by
  let A := Plane L
  let : Algebra A E := axisPlaneAlgebra false
  let i := Polynomial.mapRingHom (algebraMap L[X] Scalar)
  let j := algebraMap Scalar[X] ChartField
  let k := algebraMap ChartField E
  have co : (algebraMap A E).comp (Bivariate.swap (R:=L)).toRingHom=
      (k.comp j).comp i := by
    apply RingHom.ext
    intro p
    change k ((oriented true false (Bivariate.swap p)):ChartField)=k (j (i p))
    have x : ((oriented true false (Bivariate.swap p)):ChartField)=
        planeMap (false,false) p := by
      change planeMap (false,false) (Bivariate.swap (Bivariate.swap p))=_
      rw [Bivariate.swap_swap_apply]
    rw [x,Lower6960.MonicChartProbes.planeMap_finite]
    rfl
  change (P.map Bivariate.swap.toRingHom).eval₂ (algebraMap A E) α=0
  rw [eval₂_map,co]
  change ((P.map i).map j).eval₂ k α=0 at root
  rw [eval₂_map,eval₂_map] at root
  exact root

#print axioms projected_root_of_seed
end
end Lower6960.CollisionMarked

import ProximityPrize.SubmissionLower.R6960CollisionMarkedGenericFrames
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMeasuredSum
set_option synthInstance.maxHeartbeats 200000

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler CollisionTame
open LaurentPolynomial Polynomial Module Matrix
open scoped Polynomial Lower6960.RetainedSurfaceClass Matrix

variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
  [Algebra.IsSeparable ChartField E]

local instance genericMeasureNodeRing (x z:L) : CommRing (Crossing E x z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E false x⊔axisIdeal E true z)

/-- The exact deficit of a selected native line agrees with the
determinant deficit of its generic normalized line. The same overlap
unit is used in both comparisons. -/
theorem generic_measure_eq_native (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    [IsReduced (Crossing E x z)] [FiniteDimensional L (Crossing E x z)]
    (p:ℕ) [CharP L p] (small:finrank L (Crossing E x z)<p) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) true))
    (s:ℕ) (measure:(transition E j (atCoord j x z) (by cases j <;> assumption) bf bi).det.degree=
      ((-(s:ℤ):ℤ):WithBot ℤ)) :
    let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
    ∃ (f : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) false))
      (i : Basis (Fin (finrank ChartField E)) (GenericLine L)
        (chartOrder (k:=GenericCoefficients L) (E:=E) true)),
      (normalizedTransition f i).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) := by
  let : Algebra (Laurent (GenericCoefficients L)) E := genericLineAlgebra j
  obtain ⟨δf,nf,pf⟩ := line_principal_discriminant (E:=E) j false
  obtain ⟨δi,_,pi⟩ := line_principal_discriminant (E:=E) j true
  obtain ⟨_,u,un,glue⟩ := original_line_degree_cap j x z nx nz p small bf bi s measure δf δi nf pf pi
  obtain ⟨f⟩ := generic_line_basis (E:=E) j false
  obtain ⟨i⟩ := generic_line_basis (E:=E) j true
  let R := GenericLine L
  let K := GenericCoefficients L
  let A := Bivariate.swap δf
  let B := Bivariate.swap δi
  let spec := algebraMap (Polynomial L) K
  have an : A≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nf
  have nonzero : A.map spec≠0 :=
    (map_ne_zero_iff (Polynomial.mapRingHom spec)
      (Polynomial.map_injective _ (IsFractionRing.injective _ _))).mpr an
  have af := generic_line_trace_associated j false δf pf f
  have ai := generic_line_trace_associated j true δi pi i
  let G := (normalizedTransition f i).det
  have unit : IsUnit G := (Matrix.isUnit_iff_isUnit_det _).mp (normalizedTransition_unit f i)
  have trace := normalized_trace_transition f i
  obtain ⟨d,dd,eq⟩ := overlap_transition_exponent A B u un (2*(s:ℤ)) glue
    spec nonzero _ _ af ai G unit trace
  have de : d=-(s:ℤ) := by omega
  exact ⟨f,i,de ▸ dd⟩

#print axioms generic_measure_eq_native
end
end Lower6960.CollisionMarked

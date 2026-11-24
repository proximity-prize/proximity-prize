import ProximityPrize.SubmissionLower.R6961RetainedNativeEuler
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections RetainedRestrictionTorus
open Module Submodule LinearMap Algebra Polynomial Lower6960.LineEuler
open scoped Lower6961.RetainedSurfaceClass Polynomial
open Lower6961.RetainedSurfaceClass (chartSpace)
variable (E:Type) [Field E] [Algebra ChartField E]

def imageAlg (j:Bool) (c:L) (b:Bool) : Subalgebra L (Axis E j c) where
  carrier:=(chartImage E j c b : Set _)
  zero_mem':=(chartImage E j c b).zero_mem
  add_mem':=(chartImage E j c b).add_mem
  one_mem':=by
    change (1:Axis E j c)∈chartImage E j c b
    exact ⟨1,isIntegral_one,map_one (Ideal.Quotient.mk _)⟩
  mul_mem':=by
    rintro _ _ ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u*v,IsIntegral.mul hu hv,map_mul (Ideal.Quotient.mk _) _ _⟩
  algebraMap_mem' r:=by
    change algebraMap L (Axis E j c) r∈chartImage E j c b
    exact ⟨algebraMap L (Tor E) r,
      isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant _ r⟩:baseChart (reference j b))),rfl⟩

def imagePoly (j:Bool) (c:L) (b:Bool) : (Polynomial L)→+*imageAlg E j c b :=
  (polyMap E j c b).codRestrict (imageAlg E j c b) (fun p=>by
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    have h:1∈polyImage E j c b := (imageAlg E j c b).one_mem
    have v:=(polyImage E j c b).smul_mem p h
    change polyMap E j c b p * 1∈_ at v
    rw [mul_one] at v
    exact v)
scoped instance imagePolyAlgebra (j:Bool) (c:L) (b:Bool) :
    Algebra (Polynomial L) (imageAlg E j c b) :=
  RingHom.toAlgebra' (R:=(Polynomial L)) (S:=imageAlg E j c b) (imagePoly E j c b)
    (fun r x => mul_comm (imagePoly E j c b r) x)

private def ringBasis (j:Bool) (c:L) (b:Bool) {n:ℕ}
    (B : Basis (Fin n) (Polynomial L) (chartImage E j c b)) : Basis (Fin n) (Polynomial L) (imageAlg E j c b) :=
  let e : chartImage E j c b≃ₗ[(Polynomial L)]imageAlg E j c b :=
   { toFun:=fun v=>⟨v,v.property⟩
     invFun:=fun v=>⟨v,v.property⟩
     left_inv:=fun _=>rfl
     right_inv:=fun _=>rfl
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
  B.map e

def nodeRing (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₐ[L] Crossing E x z :=
  match j with
  | false=>Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ _⊔axisIdeal E true z from le_sup_left)
  | true=>Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x⊔_ from le_sup_right)

theorem eval_subtype (j:Bool) (x z:L) (u:chartImage E j (atCoord j x z) false) :
    nodeRing E j x z u.val=nodeMap E j x z u.val := by cases j <;> rfl

theorem vanishing_divides (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:imageAlg E j (atCoord j x z) false) (h:nodeRing E j x z u.val=0) :
    algebraMap (Polynomial L) (imageAlg E j (atCoord j x z) false) (Polynomial.X-C (atCoord (!j) x z)) ∣ u := by
  let w : chartImage E j (atCoord j x z) false:=⟨u.val,u.property⟩
  obtain ⟨v,eq⟩:=(kernel_at_node E j x z nx nz w).mp ((eval_subtype E j x z w) ▸ h)
  exact ⟨⟨v.val,v.property⟩,Subtype.ext eq⟩

/-- Global sections form a finite algebra. On the actual affine chart, their
evaluation is injective even if the selected fibre has several components. -/
theorem global_eval_injective (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)]
    [FiniteDimensional L (LineGlobals E j (atCoord j x z))] {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    Function.Injective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false⊓
      chartImage E j (atCoord j x z) true).subtype) := by
  let c:=atCoord j x z
  let R:=imageAlg E j c false
  let U:=imageAlg E j c false⊓imageAlg E j c true
  let e : U≃ₗ[L]LineGlobals E j c :=
    { toFun:=fun v=>⟨v,v.property⟩,invFun:=fun v=>⟨v,v.property⟩
      left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  have : FiniteDimensional L U := FiniteDimensional.of_injective e.toLinearMap e.injective
  let into : U→ₐ[L] R:=Subalgebra.inclusion inf_le_left
  let evaluate:= (nodeRing E j x z).toRingHom.comp R.subtype
  have free : Module.Free (Polynomial L) R := Module.Free.of_basis (ringBasis E j c false bf)
  have redRing : IsReduced R := RetainedLineEvaluation.reduced_of_point (S:=R) (D:=Crossing E x z)
    (atCoord (!j) x z) evaluate (vanishing_divides E j x z nx nz)
  intro u v eq
  let d:=e.symm (u-v)
  have alg : IsIntegral L (into d) := (Algebra.IsIntegral.isIntegral d).map into
  have van : evaluate (into d)=0 := by
    change nodeRing E j x z (u.val-v.val)=0
    rw [map_sub,sub_eq_zero]
    cases j <;> exact eq
  have zero:=RetainedLineEvaluation.detects_global (atCoord (!j) x z) (into d) alg
    (vanishing_divides E j x z nx nz _ van)
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact congrArg (fun w : R=>(w:Axis E j c)) zero

#print axioms global_eval_injective
end Lower6961.RetainedSurfaceClass

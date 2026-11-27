import ProximityPrize.SubmissionLower.R6960CollisionMarkedCommonAxis
import ProximityPrize.SubmissionLower.R6960CollisionMarkedTwoChart

set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra
open RetainedRestrictionTorus MarkedEvaluation
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct

variable {E : Type} [Field E] [Algebra ChartField E]

local instance multiplesAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

def chartSubring (b:Bool) (z:L) : Subring (Axis E true z) where
  carrier := chartImage E true z b
  zero_mem' := (chartImage E true z b).zero_mem
  one_mem' := ⟨1,isIntegral_one,map_one (Ideal.Quotient.mk (axisIdeal E true z))⟩
  add_mem' := (chartImage E true z b).add_mem
  mul_mem' := by
    rintro _ _ ⟨u,iu,rfl⟩ ⟨v,iv,rfl⟩
    exact ⟨u*v,iu.mul iv,map_mul (Ideal.Quotient.mk (axisIdeal E true z)) _ _⟩
  neg_mem' := (chartImage E true z b).neg_mem

theorem chart_poly_mem [FiniteDimensional ChartField E] (b:Bool) (z:L) (nz:z≠0) (h:(Polynomial L)) :
    polyMap E true z b h∈chartImage E true z b := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let e := axisFibreData (E:=E) b z nz
  refine (e.property.2.2 _).mp ⟨baseMap E z h,?_⟩
  exact axisFibreData_scalar b z nz h

/-- The original chart orders give a genuine two-chart marked section
once the calculated indices clear the finite multiple and the common
projector at the reciprocal boundary. -/
theorem marked_axis_multiple [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (z:L) (nz:z≠0) (η:AxisGeneric (E:=E) z)
    (h d : (Polynomial L)) (a:ℕ) (degree:h.natDegree≤a) (unit:d.eval 0≠0)
    (finite : ∃ v∈chartImage E true z false,
      axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z false h)*η)
    (infinity : ∃ v∈chartImage E true z true,
      axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z true d)*η) :
    ∃ v:Axis E true z,FibreSection (E:=E) a z v ∧
      axisToGeneric (E:=E) z v=axisToGeneric (E:=E) z (polyMap E true z false h)*η := by
  let U := Axis E true z
  let V := AxisGeneric (E:=E) z
  let Af := chartSubring (E:=E) false z
  let Ai := chartSubring (E:=E) true z
  let ρ := axisToGeneric (E:=E) z
  let ι := ρ.comp (algebraMap L U)
  let xu : Vˣ := Units.map ρ.toMonoidHom (axisX (E:=E) z)
  let φf : Af→+*V := ρ.comp Af.subtype
  let φi : Ai→+*V := ρ.comp Ai.subtype
  let poly := (polyMap E true z true).codRestrict Ai (fun h=>chart_poly_mem true z nz h)
  let : Algebra (Polynomial L) Ai := poly.toAlgebra
  have ev (b:Bool) (p:(Polynomial L)) :
      ρ (polyMap E true z b p)=p.eval₂ ι (if b then (↑xu⁻¹:V) else ↑xu) := by
    rw [axis_polyEval,Polynomial.hom_eval₂]
    cases b <;> rfl
  have scal (p:(Polynomial L)) : φi (algebraMap (Polynomial L) Ai p)=p.eval₂ ι (↑xu⁻¹) := ev true p
  have common (u:Af) : ∃ n:ℕ,∃ v:Ai,φi v=(↑xu⁻¹:V)^n*φf u := by
    let S := Submonoid.powers (Polynomial.X:(Polynomial L))
    let : Module (Polynomial L) U := Module.compHom U (chartEmbedding (k:=L) true).toRingHom
    let nmap := nativeMap E true z true
    let : IsLocalizedModule S nmap := native_localization E true z nz true
    obtain ⟨⟨v,p⟩,rel⟩ := IsLocalizedModule.surj S nmap (u:U)
    obtain ⟨n,pn⟩ := p.property
    let y : Ai := ⟨v.val,v.property⟩
    refine ⟨n,y,?_⟩
    change axisLaurent E true z (chartEmbedding true (p:(Polynomial L)))*(u:U)=v.val at rel
    have axisPow : axisLaurent E true z (chartEmbedding true (p:(Polynomial L)))=((↑(axisX (E:=E) z)⁻¹:U)^n) := by
      rw [show axisLaurent E true z (chartEmbedding true (p:(Polynomial L)))=polyMap E true z true p from
        DFunLike.congr_fun (signed_chart E true z true) _]
      rw [←pn,map_pow,axis_polyEval]
      exact congrArg (·^n) (eval₂_X _ _)
    rw [axisPow] at rel
    have mapped := congrArg ρ rel
    rw [map_mul,map_pow] at mapped
    exact mapped.symm
  obtain ⟨vf,vfm,vfeq⟩ := finite
  obtain ⟨vi,vim,vieq⟩ := infinity
  have fin : ∃ u:Af,φf u=h.eval₂ ι (xu:V)*η :=
    ⟨⟨vf,vfm⟩,vfeq.trans (congrArg (·*η) (ev false h))⟩
  have inf : ∃ u:Ai,φi u=d.eval₂ ι (↑xu⁻¹)*η :=
    ⟨⟨vi,vim⟩,vieq.trans (congrArg (·*η) (ev true d))⟩
  obtain ⟨u,v,ueq,veq⟩ := marked_multiple_two_charts ι xu φf φi scal common η d unit inf h a degree fin
  have target : (v:U)=((↑(axisX (E:=E) z)⁻¹:U)^a)*(u:U) := by
    apply axisToGeneric_injective z nz
    rw [map_mul,map_pow]
    exact veq
  have umf : (u:U)∈chartImage E true z false := u.property
  have vmi : (v:U)∈chartImage E true z true := v.property
  exact ⟨(u:U),fibreSection_of_chart_pair (E:=E) a z (u:U) umf (target ▸ vmi),
    ueq.trans (congrArg (·*η) (ev false h).symm)⟩

end
end Lower6960.CollisionMarked

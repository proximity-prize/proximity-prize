import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisLaurent
import ProximityPrize.SubmissionLower.R6961MarkedWordResidues
import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisGeneric
import ProximityPrize.SubmissionLower.R6960CollisionMarkedTwoChart

set_option Elab.async false

-- merged module R6961CollisionMarkedAxisSection
section Merged_R6961CollisionMarkedAxisSection

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open RetainedSurfaceClass RetainedRestrictionTorus Lower6960.ChartSections
open RetainedTwistedRestriction Lower6961.MarkedEvaluation

variable {E : Type} [Field E] [Algebra ChartField E]

local instance sectionAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

/-- The actual global abscissa function is a unit on the common axis. -/
def axisX (z:L) : (Axis E true z)ˣ :=
  Units.map (Ideal.Quotient.mk (axisIdeal E true z)).toMonoidHom (varUnit E false)

/-- A matching pair of regular original chart values is a section in the
literal interface used by the marked principal-parts construction. -/
theorem fibreSection_of_chart_pair (a:ℕ) (z:L) (v:Axis E true z)
    (finite : v∈chartImage E true z false)
    (infinity : ((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v∈chartImage E true z true) :
    FibreSection (E:=E) a z v := by
  intro b
  cases b
  · obtain ⟨u,reg,val⟩ := finite
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true false)=1 := by
      apply Subtype.ext
      change algebraMap ChartField E (localFrame (reference true false) false)=1
      rw [show localFrame (reference true false) false=1 from rfl,map_one]
    rw [eq,one_pow,one_mul]
    exact val
  · obtain ⟨u,reg,val⟩ := infinity
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true true)=(varUnit E false:Tor E) := rfl
    rw [eq]
    change Ideal.Quotient.mk (axisIdeal E true z) (((varUnit E false:Tor E)^a)*u)=v
    rw [map_mul,map_pow]
    have q : Ideal.Quotient.mk (axisIdeal E true z) (varUnit E false:Tor E)=
        (axisX (E:=E) z:Axis E true z) := rfl
    rw [q,show Ideal.Quotient.mk (axisIdeal E true z) u=((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v from val,
      ←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]

#print axioms fibreSection_of_chart_pair
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedAxisSection

-- merged module R6961CollisionMarkedCommonAxis
section Merged_R6961CollisionMarkedCommonAxis

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass Lower6960.LineEuler Polynomial Algebra Module
open scoped Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6961.RetainedSurfaceClass Polynomial TensorProduct

variable {E : Type} [Field E] [Algebra ChartField E]

local instance commonAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)

local instance commonAxisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

def axisToGeneric (z:L) : Axis E true z→+*AxisGeneric (E:=E) z :=
  (Algebra.TensorProduct.includeRight (R:=Laurent L) (A:=FractionRing (Laurent L))
    (B:=Axis E true z)).toRingHom

/-- The Laurent quotient itself embeds in its generic algebra. The
basis proving this is localized from the genuine free line chart. -/
theorem axisToGeneric_injective [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (z:L) (nz:z≠0) : Function.Injective (axisToGeneric (E:=E) z) := by
  let U := Axis E true z
  let B := chartImage E true z false
  let Λ := Laurent L
  let F := FractionRing Λ
  let : Module.Free (Polynomial L) B := chart_free E true z false
  let A := Module.Free.chooseBasis (Polynomial L) B
  let b := localFreeBasis false A (nativeMap E true z false) (native_localization E true z nz false)
  let bk := b.baseChange F
  intro v w eq
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have h := congrArg (fun a : F⊗[Λ] U=>bk.repr a i) eq
  change (b.baseChange F).repr ((1:F) ⊗ₜ[Λ] v) i=(b.baseChange F).repr ((1:F) ⊗ₜ[Λ] w) i at h
  rw [Basis.baseChange_repr_tmul,Basis.baseChange_repr_tmul,
    Algebra.smul_def,Algebra.smul_def,mul_one,mul_one] at h
  exact IsFractionRing.injective Λ F h

/-- Evaluation in the native line chart is literal polynomial evaluation
at either the abscissa unit or its reciprocal on the common torus. -/
theorem axis_polyEval (b:Bool) (z:L) (h:(Polynomial L)) :
    polyMap E true z b h=h.eval₂ (algebraMap L (Axis E true z))
      (if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)) := by
  let U := Axis E true z
  let π : Tor E→+*U := Ideal.Quotient.mk (axisIdeal E true z)
  let a : U := if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)
  let ev := eval₂RingHom (algebraMap L U) a
  have identity : polyMap E true z b=ev := by
    apply Polynomial.ringHom_ext
    · intro c
      change π (along E true b (C c))=ev (C c)
      rw [show along E true b (C c)=algebraMap L (Tor E) c from eval₂_C _ _,show ev (C c)=algebraMap L U c from eval₂_C _ _]
      rfl
    · rw [show ev Polynomial.X=a from eval₂_X _ _]
      change π (along E true b Polynomial.X)=a
      rw [show along E true b Polynomial.X=torVar E false b from eval₂_X _ _]
      cases b <;> rfl
  exact DFunLike.congr_fun identity h

/-- A scalar from either affine chart maps to the matching polynomial
in the common generic fibre. -/
theorem axisGenericData_scalar [FiniteDimensional ChartField E]
    (b:Bool) (z:L) (nz:z≠0) (h:(Polynomial L)) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let V := FibreGeneric (E:=E) z
    let g : V≃+*AxisGeneric (E:=E) z := (axisGenericData (E:=E) b z nz).val
    g (algebraMap (Polynomial L) V h)=axisToGeneric (E:=E) z (polyMap E true z b h) := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let B := Fiber E z
  let V := FibreGeneric (E:=E) z
  let g := axisGenericData (E:=E) b z nz
  let f := axisFibreData (E:=E) b z nz
  have j : algebraMap (Polynomial L) V h=(1 ⊗ₜ[(Polynomial L)] (algebraMap (Polynomial L) B h):V) :=
    (Algebra.TensorProduct.includeRight (R:=(Polynomial L)) (A:=FractionRing (Polynomial L)) (B:=B)).commutes h |>.symm
  change g.val (algebraMap (Polynomial L) V h)=axisToGeneric (E:=E) z (polyMap E true z b h)
  rw [j,g.property.1]
  change axisToGeneric (E:=E) z (f.val (baseMap E z h))=_
  rw [axisFibreData_scalar]

#print axioms axisToGeneric_injective
#print axioms axisGenericData_scalar
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedCommonAxis

-- merged module R6961CollisionMarkedAxisMultiples
section Merged_R6961CollisionMarkedAxisMultiples

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber RetainedSurfaceClass Lower6960.LineEuler Polynomial Algebra
open RetainedRestrictionTorus Lower6961.MarkedEvaluation
open scoped Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6961.RetainedSurfaceClass Polynomial TensorProduct

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

#print axioms marked_axis_multiple
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedAxisMultiples

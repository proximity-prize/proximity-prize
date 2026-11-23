import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel

noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedNodalIndex
open Module LinearMap Submodule
variable {k M N U V C : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]

/-- For the affine pieces on the two lines, d₁ and d₂ take differences of local
sections. A pair of local representatives on the crossing is permitted exactly
when its evaluation difference is zero. -/
def boundaries (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C) :
    Submodule k (U×V) :=
  (LinearMap.ker (x.coprod (-z))).map (d₁.prodMap d₂)

private theorem representative (d : M→ₗ[k]U) :
    ∃ p : U→ₗ[k]M, ∀ x∈d.range, d (p x)=x := by
  obtain ⟨r,hr⟩:=d.rangeRestrict.exists_rightInverse_of_surjective d.range_rangeRestrict
  obtain ⟨q,hq⟩:=d.range.exists_isCompl
  refine ⟨r.comp (d.range.projectionOnto q hq),fun x hx=>?_⟩
  have l:=LinearMap.congr_fun hr (⟨x,hx⟩ : d.range)
  rw [comp_apply,projectionOnto_apply_of_mem_left hq hx]
  exact congrArg Subtype.val l

/-- The two individual cokernels charge their own obstructions. Only crossing values
outside the image of global sections can contribute to the remaining cokernel. -/
theorem dimension (d₁ : M→ₗ[k]U) (d₂ : N→ₗ[k]V) (x : M→ₗ[k]C) (z : N→ₗ[k]C)
    [FiniteDimensional k (U ⧸ d₁.range)] [FiniteDimensional k (V ⧸ d₂.range)] [FiniteDimensional k C] :
    let B := boundaries d₁ d₂ x z
    let W := d₁.ker.map x ⊔ d₂.ker.map z
    FiniteDimensional k ((U×V) ⧸ B) ∧
      finrank k ((U×V) ⧸ B)+finrank k W ≤
        finrank k (U ⧸ d₁.range)+finrank k (V ⧸ d₂.range)+finrank k C := by
  let B:=boundaries d₁ d₂ x z
  let W:=d₁.ker.map x ⊔ d₂.ker.map z
  let J:=x.coprod (-z)
  obtain ⟨p,hp⟩:=representative d₁
  obtain ⟨q,hq⟩:=representative d₂
  let pick:=p.prodMap q
  let h: (U×V) →ₗ[k] ((U ⧸ d₁.range)×(V ⧸ d₂.range))×(C ⧸ W) :=
    (d₁.range.mkQ.prodMap d₂.range.mkQ).prod (W.mkQ.comp (J.comp pick))
  have kernel : h.ker=B := by
    ext e
    rcases e with ⟨u,v⟩
    have calc_ker : (u,v)∈h.ker ↔ u∈d₁.range ∧ v∈d₂.range ∧ x (p u)-z (q v)∈W := by
      change ((d₁.range.mkQ u,d₂.range.mkQ v),W.mkQ (x (p u)+ -z (q v)))=0 ↔ _
      simp only [Prod.mk_eq_zero,←sub_eq_add_neg,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,and_assoc]
    rw [calc_ker]
    constructor
    · rintro ⟨hu,hv,hj⟩
      obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp hj
      refine ⟨(p u-a,q v+b),?_,?_⟩
      · change x (p u-a)+(-z) (q v+b)=0
        rw [map_sub,neg_apply,map_add]
        calc _ = (x (p u)-z (q v))-(x a+z b) := by abel
             _ = 0 := sub_eq_zero.mpr eq.symm
      · change (d₁ (p u-a),d₂ (q v+b))=(u,v)
        rw [map_sub,map_add,mem_ker.mp ha,mem_ker.mp hb,hp u hu,hq v hv,sub_zero,add_zero]
    · rintro ⟨⟨a,b⟩,join,eq⟩
      obtain ⟨rfl,rfl⟩: d₁ a=u ∧ d₂ b=v :=
        ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
      change x a+(-z) b=0 at join
      have ju : x a=z b := sub_eq_zero.mp (by simpa only [neg_apply,←sub_eq_add_neg] using join)
      have h₁ : p (d₁ a)-a∈d₁.ker := by rw [mem_ker,map_sub,hp _ ⟨a,rfl⟩,sub_self]
      have h₂ : b-q (d₂ b)∈d₂.ker := by rw [mem_ker,map_sub,hq _ ⟨b,rfl⟩,sub_self]
      refine ⟨⟨a,rfl⟩,⟨b,rfl⟩,Submodule.mem_sup.mpr ⟨_,⟨_,h₁,rfl⟩,_,⟨_,h₂,rfl⟩,?_⟩⟩
      rw [map_sub,map_sub,ju]; abel
  let e:=((Submodule.quotEquivOfEq B h.ker kernel.symm).trans h.quotKerEquivRange)
  have : FiniteDimensional k ((U×V) ⧸ B) := FiniteDimensional.of_injective e.toLinearMap e.injective
  have bound:=Submodule.finrank_le h.range
  rw [←e.finrank_eq,Module.finrank_prod,Module.finrank_prod] at bound
  refine ⟨inferInstance,?_⟩
  change finrank k ((U×V) ⧸ B)+finrank k W ≤ _
  have eq:=W.finrank_quotient_add_finrank
  omega

#print axioms dimension
end Lower6960.RetainedNodalIndex

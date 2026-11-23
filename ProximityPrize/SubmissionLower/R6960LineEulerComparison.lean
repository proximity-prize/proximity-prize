import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

set_option Elab.async false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open Module Submodule LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- If `B` and `F` generate the ambient space and `A ≤ B`, replacing
`B` by `A` changes the intersection-minus-cokernel index by `dim(B/A)`.
The spaces are defined by the actual ambient intersection and quotient. -/
theorem compare_lattices (F A B : Submodule k V) (inc : A≤B) (cover : F⊔B=⊤)
    [FiniteDimensional k ↥(F⊓B)] [FiniteDimensional k (B ⧸ A.comap B.subtype)] :
    FiniteDimensional k ↥(F⊓A) ∧ FiniteDimensional k (V ⧸ (F⊔A)) ∧
    finrank k ↥(F⊓A) + finrank k (B ⧸ A.comap B.subtype) =
      finrank k (V ⧸ (F⊔A)) + finrank k ↥(F⊓B) := by
  let D := A.comap B.subtype
  let P := F⊔A
  let toB : ↥(F⊓B) →ₗ[k] B := Submodule.inclusion inf_le_right
  let f : ↥(F⊓B) →ₗ[k] (B ⧸ D) := D.mkQ ∘ₗ toB
  let g : (B ⧸ D) →ₗ[k] (V ⧸ P) := D.mapQ P B.subtype fun y hy=>Submodule.mem_sup_right hy
  have eval_g (b : B) : g (D.mkQ b)=P.mkQ (b:V) := rfl
  have eval_f (b : ↥(F⊓B)) : f b=D.mkQ (toB b) := rfl
  have g_surj : Function.Surjective g := by
    intro v
    obtain ⟨v,rfl⟩ := P.mkQ_surjective v
    have mem : v∈F⊔B := cover.symm ▸ Submodule.mem_top
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp mem
    refine ⟨D.mkQ ⟨y,hy⟩,?_⟩
    have zero : P.mkQ x=0 := by
      rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left hx
    rw [eval_g,map_add,zero,zero_add]
  have exact_fg : f.range = g.ker := by
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      rw [LinearMap.mem_ker,eval_f,eval_g,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left x.property.1
    · intro hv
      obtain ⟨b,rfl⟩ := D.mkQ_surjective v
      rw [LinearMap.mem_ker,eval_g,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hv
      obtain ⟨x,hx,y,hy,h⟩ := Submodule.mem_sup.mp hv
      have xB : x∈B := by
        rw [show x=(b:V)-y by rw [←h,add_sub_cancel_right]]
        exact B.sub_mem b.property (inc hy)
      refine ⟨⟨x,⟨hx,xB⟩⟩,?_⟩
      rw [eval_f,←sub_eq_zero,←map_sub,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      change x-(b:V)∈A
      rw [←h,sub_add_cancel_left]
      exact A.neg_mem hy
  have e : ↥(F⊓A) ≃ₗ[k] f.ker := by
    let into : ↥(F⊓A) →ₗ[k] ↥(F⊓B) := Submodule.inclusion (inf_le_inf_left _ inc)
    have kernel (v : ↥(F⊓B)) : v∈f.ker ↔ (v:V)∈A := by
      rw [LinearMap.mem_ker,eval_f,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
      rfl
    let i := into.codRestrict f.ker fun v=>(kernel (into v)).mpr v.property.2
    refine LinearEquiv.ofBijective i ⟨fun v w eq=>Subtype.ext (congrArg (fun z : f.ker=>(z.1:V)) eq),?_⟩
    intro z
    exact ⟨⟨z.1,⟨z.1.property.1,(kernel z.1).mp z.property⟩⟩,rfl⟩
  have : FiniteDimensional k (V ⧸ P) := FiniteDimensional.of_surjective g g_surj
  have : FiniteDimensional k ↥(F⊓A) := FiniteDimensional.of_injective e.toLinearMap e.injective
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hg := LinearMap.finrank_range_add_finrank_ker g
  rw [exact_fg,←e.finrank_eq] at hf
  rw [LinearMap.range_eq_top.mpr g_surj,finrank_top] at hg
  exact ⟨inferInstance,inferInstance,by dsimp only [P,D] at *; omega⟩

#print axioms compare_lattices
end
end Lower6960.LineEuler

import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import ProximityPrize.SubmissionLower.R6960LineEulerFree

set_option Elab.async false
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwoLineBound
open Module Submodule LinearMap LineEuler
section
variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]
def difference (P Q : Submodule k U) : (P×Q)→ₗ[k]U := P.subtype.coprod (-Q.subtype)
theorem image (P Q : Submodule k U) : (difference P Q).range = P⊔Q := by
  ext v
  constructor
  · rintro ⟨⟨u,w⟩,rfl⟩
    exact mem_sup.mpr ⟨u,u.property,-(w:U),Q.neg_mem w.property,rfl⟩
  · intro h
    obtain ⟨u,hu,w,hw,rfl⟩:=mem_sup.mp h
    exact ⟨(⟨u,hu⟩,⟨-w,Q.neg_mem hw⟩),by simp [difference]⟩
def diagonal (P Q : Submodule k U) : ↥(P⊓Q) ≃ₗ[k] (difference P Q).ker where
  toFun w:=⟨(⟨w,w.property.1⟩,⟨w,w.property.2⟩),by simp [difference]⟩
  invFun v:=⟨(v.val.1:U),v.val.1.property,by
    have diff : (v.val.1:U)+ -(v.val.2:U)=0 := v.property
    have eq : (v.val.1:U)=(v.val.2:U) := sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using diff)
    exact eq ▸ v.val.2.property⟩
  left_inv _:=rfl
  right_inv v:=by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext
      have diff : (v.val.1:U)+ -(v.val.2:U)=0 := v.property
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using diff)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
end
variable {k ι C : Type*} [Field k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup C] [Module k C] [FiniteDimensional k C]
abbrev diff (G : Matrix ι ι (Laurent k)) := difference (finiteLattice k ι) (transitionLattice G)
abbrev ev (G : Matrix ι ι (Laurent k)) (x : finiteLattice k ι →ₗ[k] C) :=
  x.comp (LinearMap.fst k (finiteLattice k ι) (transitionLattice G))
end Lower6960.RetainedTwoLineBound

import ProximityPrize.SubmissionLower.R6960RetainedNodalIndex
import ProximityPrize.SubmissionLower.R6960LineEuler

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
abbrev globals (G : Matrix ι ι (Laurent k)) (x : finiteLattice k ι →ₗ[k] C) :
    H0 G →ₗ[k] C := x.comp (Submodule.inclusion inf_le_left)

set_option synthInstance.maxHeartbeats 200000 in
/-- On two rank-e Laurent lines meeting in rank e, the joint obstruction space has
dimension at most the sum of their determinant deficits. The overlap equations have
one shared crossing evaluation. Each global section is detected there. -/
theorem two_line_bound (G H : Matrix ι ι (Laurent k)) (g : IsUnit G) (h : IsUnit H)
    (s t : ℕ) (dg : G.det.degree = ((-(s:ℤ) : ℤ) : WithBot ℤ))
    (dh : H.det.degree = ((-(t:ℤ) : ℤ) : WithBot ℤ))
    (x z : finiteLattice k ι →ₗ[k] C) (cross : finrank k C=Fintype.card ι)
    (ix : Function.Injective (globals G x)) (iz : Function.Injective (globals H z)) :
    let B:=RetainedNodalIndex.boundaries (diff G) (diff H) (ev G x) (ev H z)
    FiniteDimensional k (((ι→Laurent k)×(ι→Laurent k)) ⧸ B) ∧
      finrank k (((ι→Laurent k)×(ι→Laurent k)) ⧸ B) ≤ s+t := by
  obtain ⟨fg,fg',m,me,mval⟩:=euler_index G g
  obtain ⟨fh,fh',n,ne,nval⟩:=euler_index H h
  have mg : m= -(s:ℤ) := WithBot.coe_injective (me.symm.trans dg)
  have nh : n= -(t:ℤ) := WithBot.coe_injective (ne.symm.trans dh)
  rw [mg] at mval
  rw [nh] at nval
  have rg : (diff G).range = finiteLattice k ι ⊔ transitionLattice G := image ..
  have rh : (diff H).range = finiteLattice k ι ⊔ transitionLattice H := image ..
  have : FiniteDimensional k ((ι→Laurent k) ⧸ (diff G).range) := rg ▸ fg'
  have : FiniteDimensional k ((ι→Laurent k) ⧸ (diff H).range) := rh ▸ fh'
  obtain ⟨finite,bound⟩:=RetainedNodalIndex.dimension (diff G) (diff H) (ev G x) (ev H z)
  let W:=(diff G).ker.map (ev G x) ⊔ (diff H).ker.map (ev H z)
  have into (v:H0 H) : globals H z v∈W :=
    Submodule.mem_sup_right (Submodule.mem_map.mpr
      ⟨(diagonal _ _ v).val,(diagonal _ _ v).property,rfl⟩)
  let lift: H0 H→ₗ[k]W := (globals H z).codRestrict W into
  have iw := LinearMap.finrank_le_finrank_of_injective (f:=lift)
    (fun u v eq=>iz (congrArg (fun y:W=>(y:C)) eq))
  have c:=LinearMap.finrank_le_finrank_of_injective (f:=globals G x) ix
  rw [rg,rh,cross] at bound
  rw [cross] at c
  change _ + finrank k W ≤ finrank k (H1 G)+finrank k (H1 H)+Fintype.card ι at bound
  exact ⟨finite,by omega⟩

#print axioms two_line_bound
end Lower6960.RetainedTwoLineBound

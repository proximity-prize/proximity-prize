import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedCodimension
open Module Submodule LinearMap
variable {k U V W : Type*} [Field k] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def Fits (P : Submodule k U) (n:ℕ) : Prop :=
  FiniteDimensional k (U ⧸ P) ∧ finrank k (U ⧸ P)≤n

theorem from_map [FiniteDimensional k V] (f : U→ₗ[k]V) (P:Submodule k U)
    (ker : f.ker=P) {n:ℕ} (bound:finrank k V≤n) : Fits P n := by
  subst P
  let e:=f.quotKerEquivRange
  exact ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    (e.finrank_eq.trans_le (Submodule.finrank_le f.range)).trans bound⟩

/-- An obstruction vanishing on a line comes from the preceding twist.
The cokernel therefore grows by at most the obstruction dimension of that line. -/
theorem step [FiniteDimensional k W] (P:Submodule k U) (Q:Submodule k V)
    (f:U→ₗ[k]V) (r:V→ₗ[k]W) (inc:P≤Q.comap f)
    (lift:∀ x∈r.ker,∃ y, x-f y∈Q) {n t:ℕ} (old:Fits P n) (width:finrank k W≤t) :
    Fits Q (n+t) := by
  obtain ⟨fin,dim⟩:=old
  obtain ⟨sectionMap,inverse⟩:=r.rangeRestrict.exists_rightInverse_of_surjective r.range_rangeRestrict
  let cover := (P.mapQ Q f inc).coprod (Q.mkQ.comp sectionMap)
  have sur : Function.Surjective cover := by
    intro x
    obtain ⟨v,rfl⟩:=Q.mkQ_surjective x
    let z:=r.rangeRestrict v
    have rz : r (sectionMap z)=r v := congrArg Subtype.val (LinearMap.congr_fun inverse z)
    have kv : v-sectionMap z∈r.ker := by rw [mem_ker,map_sub,rz,sub_self]
    obtain ⟨y,hy⟩:=lift _ kv
    refine ⟨(P.mkQ y,z),?_⟩
    change P.mapQ Q f inc (P.mkQ y)+Q.mkQ (sectionMap z)=Q.mkQ v
    change Q.mkQ (f y)+Q.mkQ (sectionMap z)=Q.mkQ v
    rw [←map_add]
    apply (Submodule.Quotient.eq Q).mpr
    convert Q.neg_mem hy using 1 <;> abel
  have :=FiniteDimensional.of_surjective cover sur
  have b:=LinearMap.finrank_le_finrank_of_surjective sur
  rw [Module.finrank_prod] at b
  exact ⟨inferInstance,b.trans (Nat.add_le_add dim ((Submodule.finrank_le r.range).trans width))⟩

#print axioms from_map
#print axioms step

theorem pullback [FiniteDimensional k U] (P:Submodule k V) (f:U→ₗ[k]V) {n:ℕ} (size:Fits P n) :
    finrank k U≤n+finrank k (P.comap f) := by
  obtain ⟨finite,dim⟩:=size
  let q:=P.mkQ.comp f
  have ker:q.ker=P.comap f := by
    ext v
    change P.mkQ (f v)=0 ↔ _
    exact Submodule.Quotient.mk_eq_zero _
  have r:=q.finrank_range_add_finrank_ker
  rw [ker] at r
  exact r ▸ Nat.add_le_add_right ((Submodule.finrank_le q.range).trans dim) _

#print axioms pullback
theorem large_subspace [FiniteDimensional k U] (P:Submodule k V) (f:U→ₗ[k]V) {n:ℕ} (size:Fits P n) :
    ∃ D:Submodule k U,finrank k U≤n+finrank k D ∧ ∀u:D,f u.val∈P :=
  ⟨P.comap f,pullback P f size,fun u=>u.property⟩
end Lower6960.RetainedCodimension

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.BoundaryRank
open Module Submodule
universe u
variable {k L ι : Type u} [Field k] [Field L] [Algebra k L]
variable (slots : Submodule k L) [FiniteDimensional k slots]

/-- A boundary of fraction-field rank r costs at most r times the native
seed-slot dimension. A row reduction need not preserve the individual slot
space under arbitrary fraction-field coefficients. -/
theorem slots_times_rank (r : ℕ) :
    ∀ (U V : Type u) [AddCommGroup U] [Module L U] [FiniteDimensional L U]
      [Module k U] [IsScalarTower k L U] [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      finrank L U = r → ∀ (coord : U →ₗ[L] (ι → L)) (embed : V →ₗ[k] U),
      Function.Injective coord → Function.Injective embed →
      (∀ x i,coord (embed x) i ∈ slots) → finrank k V ≤ r * finrank k slots := by
  classical
  induction r using Nat.strong_induction_on with
  | ind r smaller =>
    intro U V _ _ _ _ _ _ _ _ dim coord embed coords_inj embed_inj fits
    by_cases trivial : ∀ x : V, x=0
    · rw [Module.finrank_zero_iff.mpr (show Subsingleton V from
        ⟨fun x y=> (trivial x).trans (trivial y).symm⟩)]
      exact Nat.zero_le _
    push Not at trivial
    obtain ⟨x,xnz⟩:=trivial
    have vx : embed x ≠ 0 := fun h=>xnz (embed_inj (h.trans embed.map_zero.symm))
    have ux : coord (embed x) ≠ 0 := fun h=>vx (coords_inj (h.trans coord.map_zero.symm))
    obtain ⟨i,ix⟩ : ∃ i, coord (embed x) i ≠ 0 := by
      by_contra! hz
      exact ux (funext hz)
    let axis : U →ₗ[L] L := (LinearMap.proj i).comp coord
    let f : V →ₗ[k] slots := ((axis.restrictScalars k).comp embed).codRestrict slots (fun y=>fits y i)
    have pos : 0<finrank L axis.range := by
      let value : axis.range := ⟨axis (embed x),⟨embed x,rfl⟩⟩
      have ne : value≠0 := fun eq=>ix (congrArg Subtype.val eq)
      have : Nontrivial axis.range := ⟨⟨value,0,ne⟩⟩
      exact Module.finrank_pos
    have Udim:=axis.finrank_range_add_finrank_ker
    have lt : finrank L axis.ker < r := by omega
    let component : axis.ker →ₗ[L] (ι→L) := coord.comp axis.ker.subtype
    let sub : f.ker →ₗ[k] axis.ker :=
      (embed.comp f.ker.subtype).codRestrict (axis.ker.restrictScalars k) (by
        intro z
        change axis (embed z.val)=0
        exact congrArg Subtype.val (LinearMap.mem_ker.mp z.property))
    have remain:=smaller _ lt axis.ker f.ker rfl component sub
      (coords_inj.comp Subtype.val_injective)
      (fun x y eq=>Subtype.ext (embed_inj (congrArg Subtype.val eq)))
      (fun z j=>fits z.val j)
    have Vdim:=f.finrank_range_add_finrank_ker
    have rank:=f.range.finrank_le
    have rest := Nat.mul_le_mul_right (finrank k slots) (show finrank L axis.ker + 1 ≤ r by omega)
    rw [Nat.add_mul,one_mul] at rest
    omega

#print axioms slots_times_rank
end Research6966.BoundaryRank

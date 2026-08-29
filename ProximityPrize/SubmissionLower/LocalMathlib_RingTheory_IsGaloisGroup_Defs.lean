/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Invariant_Defs

/-! . -/

/-! . -/

section ProximityFlatProofPort



variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/-- . -/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

namespace IsGaloisGroup

variable {G A B} in
theorem of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : ∀ h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : B), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

variable {G A B} in
theorem iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B]
    (e : H ≃* G) (he : ∀ h (x : B), e h • x = h • x) :
    IsGaloisGroup H A B ↔ IsGaloisGroup G A B := by
  refine ⟨fun h ↦ h.of_mulEquiv e.symm fun g x ↦ ?_, fun h ↦ h.of_mulEquiv e he⟩
  rw [← he, e.apply_symm_apply]

variable {G A B} in
@[simp]
theorem top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B :=
  iff_of_mulEquiv Subgroup.topEquiv fun _ _ ↦ rfl

instance [IsGaloisGroup G A B] : IsGaloisGroup (⊤ : Subgroup G) A B :=
  IsGaloisGroup.top_iff.mpr ‹_›

theorem of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
    [Algebra A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B')
    (he : ∀ (g : G) (x : B), e (g • x) = g • (e x)) :
    IsGaloisGroup G A B' where
  faithful := ⟨fun h ↦ hG.faithful.eq_of_smul_eq_smul fun b ↦ by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' ↦ by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' ↦ by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g ↦ by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

theorem of_ringHom_surjective [hG : IsGaloisGroup G A B] [CommSemiring A']
    [Algebra A' B] (e : A →+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a)
    (he' : Function.Surjective e) : IsGaloisGroup G A' B where
  faithful := hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : ∃ a, e a = a' := he' a'
    rw [Algebra.smul_def, Algebra.smul_def, he, ← Algebra.smul_def, ← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

theorem of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
    (e : A ≃+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a) :
    IsGaloisGroup G A' B :=
  .of_ringHom_surjective G A A' B e he e.surjective

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable [hA : IsGaloisGroup G A B] [FaithfulSMul A B]

/-- . -/
@[simps apply_coe]
noncomputable def ringEquivFixedPoints :
    A ≃+* FixedPoints.subsemiring B G where
  toFun x := ⟨algebraMap A B x, fun _ ↦ by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]
theorem algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) :
    algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x :=
 (hA.isInvariant.isInvariant x x.prop).choose_spec

variable [CommSemiring A'] [Algebra A' B] [FaithfulSMul A' B] [hA' : IsGaloisGroup G A' B]

/-- . -/
noncomputable def ringEquiv : A ≃+* A' :=
  (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]
theorem algebraMap_ringEquiv_apply (x : A) :
    algebraMap A' B (IsGaloisGroup.ringEquiv G A A' B x) = algebraMap A B x := by
  simp [ringEquiv]

@[simp]
theorem algebraMap_ringEquiv_symm_apply (x : A') :
    algebraMap A B ((IsGaloisGroup.ringEquiv G A A' B).symm x) = algebraMap A' B x := by
  simp [ringEquiv]

end IsGaloisGroup

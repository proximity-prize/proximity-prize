/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_GradedAlgebra_Basic
import ProximityPrize.SubmissionLower.LocalMathlib_Algebra_GradedMulAction

/-! . -/

/-! . -/

section ProximityFlatProofPort

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

/-- . -/
def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  SetLike.IsHomogeneous ℳ p

theorem Submodule.IsHomogeneous.mem_iff {p : Submodule A M}
    (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p :=
  AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

/-- . -/
structure HomogeneousSubmodule (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
    extends Submodule A M where
  is_homogeneous' : toSubmodule.IsHomogeneous ℳ

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

instance : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe «X» := «X».toSubmodule
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

instance : AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M where
  zero_mem p := p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy

instance : SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M where
  smul_mem := by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

variable {𝒜 ℳ} in
theorem HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.IsHomogeneous ℳ :=
  p.is_homogeneous'

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ fun (h : x = y) ↦ by simp [h]

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe p := p.toSubmodule
  coe_injective _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ <| SetLike.coe_injective h

instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

@[ext]
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule 𝒜 ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective _ _ h

/-- . -/
theorem HomogeneousSubmodule.ext' {I J : HomogeneousSubmodule 𝒜 ℳ}
    (h : ∀ i, ∀ x ∈ ℳ i, x ∈ I ↔ x ∈ J) :
    I = J := by
  ext
  rw [I.isHomogeneous.mem_iff, J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i ↦ h i _ (decompose ℳ _ i).2

@[simp]
theorem HomogeneousSubmodule.mem_toSubmodule_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x : M} :
    x ∈ I.toSubmodule (A := A) ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

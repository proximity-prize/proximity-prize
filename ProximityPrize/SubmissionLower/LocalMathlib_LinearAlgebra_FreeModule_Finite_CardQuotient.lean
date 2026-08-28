/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Xavier Roblot
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_Data_Int_Associated
import ProximityPrize.SubmissionLower.LocalMathlib_Data_Int_NatAbs
import ProximityPrize.SubmissionLower.LocalMathlib_LinearAlgebra_FreeModule_Finite_Quotient

/-!
Permitted flat proof port of Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 79993198e810d5cab56597d8c5df62c1526a603c2789891c1c83f34908712ea4.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .







 -/

section ProximityFlatProofPort

open Module Submodule

section Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- .


 -/
theorem Submodule.natAbs_det_equiv (N : Submodule ℤ M) {E : Type*} [EquivLike E M N]
    [AddEquivClass E M N] (e : E) :
    Int.natAbs
      (LinearMap.det
        (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) =
      Nat.card (M ⧸ N) := by
  let b := Module.Free.chooseBasis ℤ M
  --
  have h : Module.finrank ℤ N = Module.finrank ℤ M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N).symm.finrank_eq
  --
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ] M := N.subtype.comp (e' : M →ₗ[ℤ] N)
  let f_apply : ∀ x, f x = b'.equiv ab (Equiv.refl _) x := fun x ↦ rfl
  suffices (LinearMap.det f).natAbs = Nat.card (M ⧸ N) by
    calc
      _ = (LinearMap.det (N.subtype ∘ₗ
            (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N))).natAbs := rfl
      _ = (LinearMap.det (N.subtype ∘ₗ _)).natAbs :=
            Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
      _ = Nat.card (M ⧸ N) := this
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    rw [f_apply, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  calc
    Int.natAbs (LinearMap.det f) = Int.natAbs (LinearMap.toMatrix b' b' f).det := by
      rw [LinearMap.det_toMatrix]
    _ = Int.natAbs (Matrix.diagonal a).det := ?_
    _ = Int.natAbs (∏ i, a i) := by rw [Matrix.det_diagonal]
    _ = ∏ i, Int.natAbs (a i) := map_prod Int.natAbsHom a Finset.univ
    _ = Nat.card (M ⧸ N) := ?_
  --
  · congr 2; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  --
  --
  simp_rw [Nat.card_congr (quotientEquivPiZMod N b h).toEquiv, Nat.card_pi, Nat.card_zmod, a]

/-- .

 -/
theorem Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = Nat.card (M ⧸ N) := by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

end Submodule

section AddSubgroup

theorem AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (bE : Basis ι ℤ E) (N : AddSubgroup E) (bN : Basis ι ℤ N) :
    N.index = (bE.det (bN ·)).natAbs :=
  have : Module.Free ℤ E := Module.Free.of_basis bE
  have : Module.Finite ℤ E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

set_option backward.isDefEq.respectTransparency false in
theorem AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι ℤ L₁.toIntSubmodule) (b₂ : Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ = (b₂.det (fun i ↦ ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs := by
  rw [relIndex, index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

theorem AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂), Nat.cast_natAbs, Int.cast_abs]
  change |algebraMap ℤ ℚ _| = _
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix_apply]

end AddSubgroup

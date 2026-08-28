import ProximityPrize.SubmissionLower.BCHKSLocatorRelationReverse6400

/-!
# Degree-capped polynomial multiples as a linear family

This file packages the elementary dimension argument used by the local
rank-drop route.  If a nonzero polynomial pair `(U,V)` has enough remaining
degree room, multiplication by every polynomial of degree below that room
embeds the corresponding `degreeLT` space into the bounded pair space.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

variable {F : Type} [Field F]

private theorem bounded_multiple_mem_degreeLT
    (d r : Nat) (hr : 0 < r) (U : F[X])
    (hroom : r + U.natDegree ≤ d)
    (M : Polynomial.degreeLT F r) :
    M.1 * U ∈ Polynomial.degreeLT F d := by
  have hMdegree : M.1.natDegree < r :=
    natDegree_lt_of_mem_degreeLT_of_pos r hr M
  have hproduct : (M.1 * U).natDegree < d := by
    exact Polynomial.natDegree_mul_le.trans_lt (by omega)
  apply Polynomial.mem_degreeLT.mpr
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hproduct)

/-- Multiplication by a fixed bounded pair, with both output degree proofs
built into the codomain. -/
noncomputable def boundedPairMultipleMap
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h) :
    Polynomial.degreeLT F r →ₗ[F] PolynomialPairSpace F c h where
  toFun M :=
    (⟨M.1 * U,
        bounded_multiple_mem_degreeLT c r hr U hUroom M⟩,
      ⟨M.1 * V,
        bounded_multiple_mem_degreeLT h r hr V hVroom M⟩)
  map_add' M N := by
    apply Prod.ext
    · apply Subtype.ext
      change (M.1 + N.1) * U = M.1 * U + N.1 * U
      rw [add_mul]
    · apply Subtype.ext
      change (M.1 + N.1) * V = M.1 * V + N.1 * V
      rw [add_mul]
  map_smul' a M := by
    apply Prod.ext
    · apply Subtype.ext
      change (a • M.1) * U = a • (M.1 * U)
      rw [smul_mul_assoc]
    · apply Subtype.ext
      change (a • M.1) * V = a • (M.1 * V)
      rw [smul_mul_assoc]

@[simp]
theorem boundedPairMultipleMap_fst
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h)
    (M : Polynomial.degreeLT F r) :
    (boundedPairMultipleMap c h r hr U V hUroom hVroom M).1.1 =
      M.1 * U := rfl

@[simp]
theorem boundedPairMultipleMap_snd
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h)
    (M : Polynomial.degreeLT F r) :
    (boundedPairMultipleMap c h r hr U V hUroom hVroom M).2.1 =
      M.1 * V := rfl

/-- A nonzero second lane makes the bounded-multiple map injective. -/
theorem boundedPairMultipleMap_injective_of_snd_ne_zero
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h)
    (hV : V ≠ 0) :
    Function.Injective
      (boundedPairMultipleMap c h r hr U V hUroom hVroom) := by
  intro M N hMN
  apply Subtype.ext
  apply mul_right_cancel₀ hV
  exact congrArg (fun q : PolynomialPairSpace F c h ↦ q.2.1) hMN

/-- Coefficient-coordinate form of the bounded multiple family. -/
noncomputable def boundedPairMultipleCoordinateMap
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h) :
    Polynomial.degreeLT F r →ₗ[F] (MixedStackIndex c h → F) :=
  (mixedStackDomainEquiv c h).toLinearMap.comp
    (boundedPairMultipleMap c h r hr U V hUroom hVroom)

theorem boundedPairMultipleCoordinateMap_injective_of_snd_ne_zero
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h)
    (hV : V ≠ 0) :
    Function.Injective
      (boundedPairMultipleCoordinateMap
        c h r hr U V hUroom hVroom) := by
  intro M N hMN
  apply boundedPairMultipleMap_injective_of_snd_ne_zero
    c h r hr U V hUroom hVroom hV
  apply (mixedStackDomainEquiv c h).injective
  exact hMN

/-- If every bounded multiple lies in a linear kernel, that kernel has
dimension at least the multiplier degree room. -/
theorem room_le_finrank_ker_of_boundedPairMultiples
    {W : Type} [AddCommGroup W] [Module F W]
    (c h r : Nat) (hr : 0 < r) (U V : F[X])
    (hUroom : r + U.natDegree ≤ c)
    (hVroom : r + V.natDegree ≤ h)
    (hV : V ≠ 0)
    (T : (MixedStackIndex c h → F) →ₗ[F] W)
    (hker : ∀ M,
      boundedPairMultipleCoordinateMap
        c h r hr U V hUroom hVroom M ∈ LinearMap.ker T) :
    r ≤ Module.finrank F (LinearMap.ker T) := by
  let Φ := boundedPairMultipleCoordinateMap
    c h r hr U V hUroom hVroom
  let Φker : Polynomial.degreeLT F r →ₗ[F] LinearMap.ker T :=
    Φ.codRestrict (LinearMap.ker T) hker
  have hΦinjective : Function.Injective Φker := by
    intro M N hMN
    apply boundedPairMultipleCoordinateMap_injective_of_snd_ne_zero
      c h r hr U V hUroom hVroom hV
    have hval := congrArg Subtype.val hMN
    change Φ M = Φ N at hval
    simpa only [Φ] using hval
  have hle := LinearMap.finrank_le_finrank_of_injective hΦinjective
  have hsource : Module.finrank F (Polynomial.degreeLT F r) = r := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F r)]
    simp
  rw [hsource] at hle
  exact hle

end ProximityPrize.SubmissionLower

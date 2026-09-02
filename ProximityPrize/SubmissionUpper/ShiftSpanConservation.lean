/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Conservation of separation under deeper shift annihilation

Let `T` denote multiplication by the compressed variable and let `S` be the
linear span of one complement fibre.  Killing the first `n` Padé remainder
coefficients means quotienting by

`S + T(S) + ... + T^(n-1)(S)`.

The next possible challenge signature is `T^n z` in that quotient.  Applying
`T` sends every depth-`n` signature to the corresponding depth-`n+1`
signature.  Consequently deeper annihilation can only merge occupied
signature classes: it can never improve challenge separation, even on a
deficient complement span.

For the full octic ambient direction space, the `112`-dimensional subspace of
differences of degree at most `113` is carried back into the `113`-dimensional
ambient space by one multiplication by the compressed variable.  The final
theorem below therefore bounds every positive-depth signature range by the
one-dimensional boundary quotient.  For a deficient span the same theorem
identifies the only possible escape: its one-step-stable core must have
codimension at least two, and adding denominator depth cannot enlarge that
codimension.
-/

namespace ProximityPrize.SubmissionUpper.ShiftSpanConservation

open Submodule

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The `n`-fold iterate of one linear shift. -/
def shiftIterate (T : M →ₗ[K] M) : ℕ → M →ₗ[K] M
  | 0 => LinearMap.id
  | n + 1 => T.comp (shiftIterate T n)

@[simp]
theorem shiftIterate_zero (T : M →ₗ[K] M) : shiftIterate T 0 = LinearMap.id := rfl

@[simp]
theorem shiftIterate_succ_apply (T : M →ₗ[K] M) (n : ℕ) (x : M) :
    shiftIterate T (n + 1) x = T (shiftIterate T n x) := rfl

/-- The span of the first `n` shifts of `S`. -/
def shiftSpan (T : M →ₗ[K] M) (S : Submodule K M) : ℕ → Submodule K M
  | 0 => ⊥
  | n + 1 => S ⊔ (shiftSpan T S n).map T

@[simp]
theorem shiftSpan_zero (T : M →ₗ[K] M) (S : Submodule K M) :
    shiftSpan T S 0 = ⊥ := rfl

@[simp]
theorem shiftSpan_succ (T : M →ₗ[K] M) (S : Submodule K M) (n : ℕ) :
    shiftSpan T S (n + 1) = S ⊔ (shiftSpan T S n).map T := rfl

/-- Shifting the depth-`n` nuisance span lands in the depth-`n+1` nuisance span. -/
theorem map_shiftSpan_le_succ (T : M →ₗ[K] M) (S : Submodule K M) (n : ℕ) :
    (shiftSpan T S n).map T ≤ shiftSpan T S (n + 1) := by
  rw [shiftSpan_succ]
  exact le_sup_right

/-- Multiplication by the shift descends between two consecutive quotients. -/
def quotientShift (T : M →ₗ[K] M) (S : Submodule K M) (n : ℕ) :
    (M ⧸ shiftSpan T S n) →ₗ[K] (M ⧸ shiftSpan T S (n + 1)) :=
  (shiftSpan T S n).mapQ (shiftSpan T S (n + 1)) T <| by
    rw [← map_le_iff_le_comap]
    exact map_shiftSpan_le_succ T S n

/-- The observable on a direction space `U` after killing `n` leading
remainder coefficients. -/
def shiftSignature (T : M →ₗ[K] M) (S : Submodule K M) (U : Submodule K M) (n : ℕ) :
    U →ₗ[K] (M ⧸ shiftSpan T S n) :=
  (shiftSpan T S n).mkQ.comp ((shiftIterate T n).comp U.subtype)

/-- Every deeper signature is the image of the preceding signature. -/
theorem quotientShift_shiftSignature
    (T : M →ₗ[K] M) (S U : Submodule K M) (n : ℕ) (x : U) :
    quotientShift T S n (shiftSignature T S U n x) =
      shiftSignature T S U (n + 1) x := by
  rfl

/-- Once two directions collide, they remain collided at every deeper
annihilation depth. -/
theorem ker_shiftSignature_le_succ
    (T : M →ₗ[K] M) (S U : Submodule K M) (n : ℕ) :
    LinearMap.ker (shiftSignature T S U n) ≤
      LinearMap.ker (shiftSignature T S U (n + 1)) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  rw [← quotientShift_shiftSignature T S U n x,
    LinearMap.mem_ker.mp hx, LinearMap.map_zero]

/-- The exact finite-set consequence: adding one annihilated coefficient
cannot increase the number of occupied challenge signatures. -/
theorem card_image_shiftSignature_succ_le
    (T : M →ₗ[K] M) (S U : Submodule K M) (n : ℕ) (records : Finset U)
    [DecidableEq (M ⧸ shiftSpan T S n)]
    [DecidableEq (M ⧸ shiftSpan T S (n + 1))] :
    (records.image (shiftSignature T S U (n + 1))).card ≤
      (records.image (shiftSignature T S U n)).card := by
  classical
  calc
    (records.image (shiftSignature T S U (n + 1))).card =
        ((records.image (shiftSignature T S U n)).image (quotientShift T S n)).card := by
      rw [Finset.image_image]
      congr 2
    _ ≤ (records.image (shiftSignature T S U n)).card := Finset.card_image_le

/-- A direction whose first shift is already in `S` is invisible at every
positive depth. -/
theorem mem_ker_shiftSignature_succ_of_map_mem
    (T : M →ₗ[K] M) (S U : Submodule K M) {x : U}
    (hx : T x.1 ∈ S) (n : ℕ) :
    x ∈ LinearMap.ker (shiftSignature T S U (n + 1)) := by
  induction n with
  | zero =>
      apply LinearMap.mem_ker.mpr
      change (shiftSpan T S 1).mkQ (T x.1) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, shiftSpan_succ]
      exact (show S ≤ S ⊔ (shiftSpan T S 0).map T from le_sup_left) hx
  | succ n ih =>
      exact ker_shiftSignature_le_succ T S U (n + 1) ih

/-- A kernel subspace bounds the dimension of the observable range by its
codimension in the source. -/
theorem finrank_range_le_codim_of_le_ker
    {N : Type*} [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) [FiniteDimensional K M]
    (C : Submodule K M) (hC : C ≤ LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) ≤ Module.finrank K M - Module.finrank K C := by
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hmono := Submodule.finrank_mono hC
  omega

/-- If `C` is a one-step-stable core of the direction space, then every
positive-depth signature has range dimension at most `codim C`.  In the full
octic ambient space the relevant dimensions are `113` and `112`, so this is
the abstract one-boundary (`rank ≤ 1`) obstruction. -/
theorem finrank_range_shiftSignature_succ_le_stableCoreCodim
    (T : M →ₗ[K] M) (S U : Submodule K M) [FiniteDimensional K U]
    (C : Submodule K U) (hstable : ∀ x : U, x ∈ C → T x.1 ∈ S) (n : ℕ) :
    Module.finrank K (LinearMap.range (shiftSignature T S U (n + 1))) ≤
      Module.finrank K U - Module.finrank K C := by
  apply finrank_range_le_codim_of_le_ker (shiftSignature T S U (n + 1)) C
  intro x hx
  exact mem_ker_shiftSignature_succ_of_map_mem T S U (hstable x hx) n

#print axioms card_image_shiftSignature_succ_le
#print axioms finrank_range_shiftSignature_succ_le_stableCoreCodim

end ProximityPrize.SubmissionUpper.ShiftSpanConservation

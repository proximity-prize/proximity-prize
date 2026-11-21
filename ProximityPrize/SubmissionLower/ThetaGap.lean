import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic

/-!
Two gradings with a common filtration: the gap lemma.

`L a` is the space of index at most `a`, `G a` the space of index at least `a`.
The operator `D` is diagonal for a second grading; `D - w` keeps `L a`, lowers `G a` by at
most three levels, and is injective on `L a` when `a < w`.  A vector killed by
`(D - R) ⋯ (D - (R + δ - 1))` whose components vanish in a window of `3 δ` levels has no
component below the window.
-/

namespace ThetaGap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The operator `D - w`. -/
def shift (D : V →ₗ[k] V) (w : ℤ) : V →ₗ[k] V := D - (w : k) • LinearMap.id

/-- The product `(D - (R + n - 1)) ⋯ (D - R)`. -/
def shifted (D : V →ₗ[k] V) (R : ℤ) : ℕ → (V →ₗ[k] V)
  | 0 => LinearMap.id
  | n + 1 => shift D (R + n) ∘ₗ shifted D R n

theorem shifted_zero (D : V →ₗ[k] V) (R : ℤ) (x : V) : shifted D R 0 x = x := rfl

theorem shifted_succ (D : V →ₗ[k] V) (R : ℤ) (n : ℕ) (x : V) :
    shifted D R (n + 1) x = shift D (R + n) (shifted D R n x) := rfl

variable {D : V →ₗ[k] V} {G L : ℤ → Submodule k V}

theorem shifted_mem_low (hL : ∀ a w x, x ∈ L a → shift D w x ∈ L a) (R : ℤ) (n : ℕ) :
    ∀ a x, x ∈ L a → shifted D R n x ∈ L a := by
  induction n with
  | zero => intro a x hx; rw [shifted_zero]; exact hx
  | succ n ih => intro a x hx; rw [shifted_succ]; exact hL a _ _ (ih a x hx)

theorem shifted_mem_high (hG : ∀ a w x, x ∈ G a → shift D w x ∈ G (a - 3)) (R : ℤ) (n : ℕ) :
    ∀ a x, x ∈ G a → shifted D R n x ∈ G (a - 3 * (n : ℤ)) := by
  induction n with
  | zero =>
    intro a x hx
    rw [shifted_zero]
    have e : a - 3 * ((0 : ℕ) : ℤ) = a := by simp
    rw [e]
    exact hx
  | succ n ih =>
    intro a x hx
    rw [shifted_succ]
    have h := hG (a - 3 * (n : ℤ)) (R + n) _ (ih a x hx)
    have e : a - 3 * (n : ℤ) - 3 = a - 3 * ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at h
    exact h

theorem shifted_injective (hL : ∀ a w x, x ∈ L a → shift D w x ∈ L a) (M : ℤ)
    (hinj : ∀ a w x, a < w → w < M → x ∈ L a → shift D w x = 0 → x = 0) (R : ℤ) (n : ℕ) :
    R + (n : ℤ) ≤ M → ∀ a x, a < R → x ∈ L a → shifted D R n x = 0 → x = 0 := by
  induction n with
  | zero => intro _ a x _ _ h; rw [shifted_zero] at h; exact h
  | succ n ih =>
    intro hM a x ha hx h
    rw [shifted_succ] at h
    have hM' : R + ((n + 1 : ℕ) : ℤ) = R + (n : ℤ) + 1 := by push_cast; ring
    have h0 := hinj a (R + n) _ (by omega) (by omega) (shifted_mem_low hL R n a x hx) h
    exact ih (by omega) a x ha hx h0

/-- The gap lemma. -/
theorem gap (hLG : ∀ a, L a ⊓ G (a + 1) = ⊥)
    (hL : ∀ a w x, x ∈ L a → shift D w x ∈ L a)
    (hG : ∀ a w x, x ∈ G a → shift D w x ∈ G (a - 3))
    (M : ℤ) (hinj : ∀ a w x, a < w → w < M → x ∈ L a → shift D w x = 0 → x = 0)
    (l R : ℤ) (δ : ℕ) (hM : R + (δ : ℤ) ≤ M) (hlR : l - 3 * (δ : ℤ) - 1 < R)
    (q r : V) (hq : q ∈ L (l - 3 * (δ : ℤ) - 1)) (hr : r ∈ G l)
    (hp : shifted D R δ (q + r) = 0) : q = 0 := by
  have hq' := shifted_mem_low hL R δ _ q hq
  have hr' := shifted_mem_high hG R δ l r hr
  rw [map_add] at hp
  have hneg : shifted D R δ q = -shifted D R δ r := eq_neg_of_add_eq_zero_left hp
  have hmem : shifted D R δ q ∈ G (l - 3 * (δ : ℤ) - 1 + 1) := by
    rw [hneg]
    have e : l - 3 * (δ : ℤ) - 1 + 1 = l - 3 * (δ : ℤ) := by ring
    rw [e]
    exact (G _).neg_mem hr'
  have hbot : shifted D R δ q ∈ L (l - 3 * (δ : ℤ) - 1) ⊓ G (l - 3 * (δ : ℤ) - 1 + 1) :=
    ⟨hq', hmem⟩
  rw [hLG] at hbot
  exact shifted_injective hL M hinj R δ hM _ q hlR hq ((Submodule.mem_bot k).mp hbot)


end ThetaGap

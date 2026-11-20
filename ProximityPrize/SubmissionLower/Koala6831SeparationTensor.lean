import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace ProximityPrize.SubmissionLower.Koala6831Separation

variable {R S : Type*} [CommRing R] [CommRing S]

def wedge (A B : Fin 2 → R) (β : Fin 2 → Fin 2 → R) : R :=
  A 1 * (β 0 0 * B 1 - β 0 1 * B 0) -
    A 0 * (β 1 0 * B 1 - β 1 1 * B 0)

theorem wedge_eq_zero_of_decomposition (A B C D : Fin 2 → R)
    (β : Fin 2 → Fin 2 → R) (h : ∀ i j, β i j = C i * B j + A i * D j) :
    wedge A B β = 0 := by
  simp only [wedge, h]
  ring

theorem exists_integral_decomposition (A B : Fin 2 → R) (β : Fin 2 → Fin 2 → R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : wedge A B β = 0) :
    ∃ C D : Fin 2 → R, ∀ i j, β i j = C i * B j + A i * D j := by
  obtain ⟨a₀, a₁, ha⟩ := hA
  obtain ⟨b₀, b₁, hb⟩ := hB
  let u (i : Fin 2) := β i 0 * B 1 - β i 1 * B 0
  let s := a₀ * u 0 + a₁ * u 1
  have hw : A 1 * u 0 - A 0 * u 1 = 0 := h
  have hu (i : Fin 2) : u i = A i * s := by
    fin_cases i
    · change u 0 = A 0 * s
      dsimp only [s]
      linear_combination a₁ * hw - u 0 * ha
    · change u 1 = A 1 * s
      dsimp only [s]
      linear_combination -a₀ * hw - u 1 * ha
  let C (i : Fin 2) := β i 0 * b₀ + β i 1 * b₁
  let D (j : Fin 2) := if j = 0 then s * b₁ else -(s * b₀)
  refine ⟨C, D, fun i j ↦ ?_⟩
  have hui : β i 0 * B 1 - β i 1 * B 0 = A i * s := hu i
  fin_cases j
  · change β i 0 = C i * B 0 + A i * D 0
    simp only [C, D, ite_eq_left rfl]
    linear_combination b₁ * hui - β i 0 * hb
  · change β i 1 = C i * B 1 + A i * D 1
    simp only [C, D, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    linear_combination -b₀ * hui - β i 1 * hb

theorem exists_scalar_of_tensor_zero (A B C D : Fin 2 → R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : ∀ i j, C i * B j + A i * D j = 0) :
    ∃ t : R, (∀ i, C i = t * A i) ∧ ∀ j, D j = -(t * B j) := by
  obtain ⟨a₀, a₁, ha⟩ := hA
  obtain ⟨b₀, b₁, hb⟩ := hB
  let t := -(D 0 * b₀ + D 1 * b₁)
  have hC (i : Fin 2) : C i = t * A i := by
    dsimp only [t]
    linear_combination b₀ * h i 0 + b₁ * h i 1 - C i * hb
  refine ⟨t, hC, fun j ↦ ?_⟩
  have h0 : A 0 * (D j + t * B j) = 0 := by
    linear_combination h 0 j - B j * hC 0
  have h1 : A 1 * (D j + t * B j) = 0 := by
    linear_combination h 1 j - B j * hC 1
  linear_combination a₀ * h0 + a₁ * h1 - (D j + t * B j) * ha

theorem fixed_word (A B C D U V : Fin 2 → R) (d₀ d₁ : R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : ∀ i j, (d₀ * U i + C i) * B j + A i * (D j - d₁ * V j) = 0) :
    ∃ u : R, (∀ i, d₀ * U i + C i = u * A i) ∧
      ∀ j, d₁ * V j - D j = u * B j := by
  obtain ⟨u, hU, hV⟩ := exists_scalar_of_tensor_zero A B (fun i ↦ d₀ * U i + C i)
    (fun j ↦ D j - d₁ * V j) hA hB h
  exact ⟨u, hU, fun j ↦ by linear_combination -(hV j)⟩

end ProximityPrize.SubmissionLower.Koala6831Separation

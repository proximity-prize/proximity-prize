import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Characteristic-2 Hasse derivatives, exact global ODE theorem, and unbounded STEP 0A/0B/0C bounds

Proves:
1. Exact closed-form solution of the characteristic-2 Hasse ODE `c₀ f^{[2]} + c₁ f^{[1]} = 0`
   (`c₀ ≠ 0`) on rational functions `P / Q` over an algebraically closed char-2 field `E`:
   every denominator root `a ∈ E` satisfies `v_{X - a}(Q) % 4 ∈ {0, 3}` (when `gcd(P, Q) = 1`).
2. Unbounded-`ℕ` Presburger (`omega`) proofs of all 6 local valuation bounds:
   - STEP 0A (2 bounds for `K ≠ 0`, `ODE_holds`),
   - STEP 0B (2 bounds for `b1c1`, `ODE_holds`),
   - STEP 0C (2 bounds for `K ≠ 0`, `ODE_fail_B1_holds`, NO ODE needed!).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401Char2ODE

open Polynomial

/-! ### Part 1: Unbounded-`ℕ` STEP 0A, STEP 0B, STEP 0C local valuation bounds -/

/-- STEP 0A bound 1 (`K ≠ 0`, `ODE_holds`):
`c - e₁ ≤ m + 6 μ + 3 λ_ex + 7 d₂_in` for ALL unbounded `ℕ`. -/
theorem step0A_bound1
    (L m nu mu lam_ex a1 d2 g b e1 c : ℕ)
    (hL : L % 2 = 0) (hm : m ≤ 1) (hnu : nu ≤ 1) (hd2 : d2 ≤ 1) (hb : b ≤ 1)
    (hLm : L > 0 → m = 0 ∧ nu = 1) (hm_le_nu : m ≤ nu)
    (hirr0 : nu = 1 → m = 0 → d2 = 0 → a1 = 0)
    (hirr1 : nu = 1 → m = 0 → d2 = 1 → 1 ≤ L + lam_ex + a1)
    (hS : g ≤ m + L + lam_ex + 3 * d2 + 5 * a1)
    (hSmod : g % 2 = (m + L + lam_ex + 3 * d2 + 5 * a1) % 2)
    (htot : c + e1 + m = 2 * g + b) (he1 : L ≤ e1)
    (hode1 : ((c + 3 * m) - (e1 + 2 * mu)) % 4 ≠ 1)
    (hode2 : ((c + 3 * m) - (e1 + 2 * mu)) % 4 ≠ 2)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let vc0 := if nu = 1 ∧ m = 0 then min (L + 3) (min (e1 + 1) c) else 0
      let t1 := 8 * a1 + 4 * d2 + 3 * m + vc0
      let t2 := 4 * a1 + 2 * d2 + (nu - m) + 3 * m + e1
      let t3 := 3 * nu + 2 * mu + e1
      let t4 := c + 3 * m
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    let d2_in := if nu = 1 ∧ m = 0 then d2 else 0
    (c : ℤ) - e1 ≤ m + 6 * mu + 3 * lam_ex + 7 * d2_in := by
  have hmnu : (m = 0 ∧ nu = 0) ∨ (m = 0 ∧ nu = 1) ∨ (m = 1 ∧ nu = 1) := by omega
  rcases hmnu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hL0 : L = 0 := by by_contra h; exact absurd (hLm (by omega)).2 (by omega)
    subst hL0; simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * 0) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * 0) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases hd : d2 = 0
    · have ha0 : a1 = 0 := hirr0 rfl rfl hd
      first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have hd1 : d2 = 1 := by omega
      subst hd1
      have h1 := hirr1 rfl rfl rfl
      have htr := htri (Or.inr (by omega))
      rcases lt_trichotomy (c + 3 * 0) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega
          rcases hv with hv | hv | hv <;> rw [hv] at hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega
          rcases hv with hv | hv | hv <;> rw [hv] at hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
  · have hL0 : L = 0 := by by_contra h; exact absurd (hLm (by omega)).1 (by omega)
    subst hL0; simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * 1) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * 1) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega

/-- STEP 0A bound 2 (`K ≠ 0`, `ODE_holds`):
`2 (c - e₁) ≤ 2 m + 13 μ + 10 λ_ex + 6 d₂_in + 4 L` for ALL unbounded `ℕ`. -/
theorem step0A_bound2
    (L m nu mu lam_ex a1 d2 g b e1 c : ℕ)
    (hL : L % 2 = 0) (hm : m ≤ 1) (hnu : nu ≤ 1) (hd2 : d2 ≤ 1) (hb : b ≤ 1)
    (hLm : L > 0 → m = 0 ∧ nu = 1) (hm_le_nu : m ≤ nu)
    (hirr0 : nu = 1 → m = 0 → d2 = 0 → a1 = 0)
    (hirr1 : nu = 1 → m = 0 → d2 = 1 → 1 ≤ L + lam_ex + a1)
    (hS : g ≤ m + L + lam_ex + 3 * d2 + 5 * a1)
    (hSmod : g % 2 = (m + L + lam_ex + 3 * d2 + 5 * a1) % 2)
    (htot : c + e1 + m = 2 * g + b) (he1 : L ≤ e1)
    (hode1 : ((c + 3 * m) - (e1 + 2 * mu)) % 4 ≠ 1)
    (hode2 : ((c + 3 * m) - (e1 + 2 * mu)) % 4 ≠ 2)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let vc0 := if nu = 1 ∧ m = 0 then min (L + 3) (min (e1 + 1) c) else 0
      let t1 := 8 * a1 + 4 * d2 + 3 * m + vc0
      let t2 := 4 * a1 + 2 * d2 + (nu - m) + 3 * m + e1
      let t3 := 3 * nu + 2 * mu + e1
      let t4 := c + 3 * m
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    let d2_in := if nu = 1 ∧ m = 0 then d2 else 0
    2 * ((c : ℤ) - e1) ≤ 2 * m + 13 * mu + 10 * lam_ex + 6 * d2_in + 4 * L := by
  have hmnu : (m = 0 ∧ nu = 0) ∨ (m = 0 ∧ nu = 1) ∨ (m = 1 ∧ nu = 1) := by omega
  rcases hmnu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hL0 : L = 0 := by by_contra h; exact absurd (hLm (by omega)).2 (by omega)
    subst hL0; simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * 0) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * 0) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases hd : d2 = 0
    · have ha0 : a1 = 0 := hirr0 rfl rfl hd
      first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have hd1 : d2 = 1 := by omega
      subst hd1
      have h1 := hirr1 rfl rfl rfl
      have htr := htri (Or.inr (by omega))
      rcases lt_trichotomy (c + 3 * 0) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega
          rcases hv with hv | hv | hv <;> rw [hv] at hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega
          rcases hv with hv | hv | hv <;> rw [hv] at hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
  · have hL0 : L = 0 := by by_contra h; exact absurd (hLm (by omega)).1 (by omega)
    subst hL0; simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at hS hSmod htot he1 hode1 hode2 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * 1) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
            first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * 1) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm <;>
          first | (clear hSmod hode1 hode2; omega) | (clear hSmod; omega) | omega

/-- STEP 0B bound 1 (`b1c1`, `ODE_holds`, exact 3-term model):
`2 (c - r_F) ≤ 2 n₀ + 8 e₁ + 16 e₂ + 14 e_rem + 3 L` for ALL unbounded `ℕ`. -/
theorem step0B_bound1
    (n0 m1 e1 e2 erem d2 L nu a1 g b rF c : ℕ)
    (hL : L % 2 = 0) (hn0 : n0 ≤ 1) (hm1 : m1 ≤ 1) (he1 : e1 ≤ 1) (he2 : e2 ≤ 1)
    (hd2 : d2 ≤ 1) (hnu : nu ≤ 1) (hb : b ≤ 1)
    (hpt : (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 0 ∧ L = 0) ∨
           (n0 = 1 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 1 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 1 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 1 ∧ nu = 1))
    (hS : g ≤ (n0 + e1 + e2) + (L + e1 + 2 * e2 + erem) + 5 * (a1 + d2))
    (htot : c + rF + (n0 + e1 + e2) = 2 * g + b)
    (hrF_k2hit : nu = 1 → n0 = 0 → m1 = 0 → e1 = 0 → e2 = 0 → L ≤ rF + 8 * erem)
    (hrF_k2mis : e2 = 1 → L ≤ rF + 5 + 8 * erem)
    (hirr_a1 : (m1 = 1 ∨ (nu = 1 ∧ n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0)) → d2 = 0 → a1 = 0)
    (hk1_c0 : m1 = 1 → d2 = 0 → erem = 0 → c = 0)
    (hode1 : ((4 * d2 + 3 * (n0 + e1 + e2) + 2 * m1 + c) - rF) % 4 ≠ 1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let m0 := n0 + e1 + e2
      let vc0 :=
        if nu = 1 ∧ ((n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0) ∨ e2 = 1) then min c (L + 3)
        else if m1 = 1 ∨ e1 = 1 then min c 1
        else 0
      let t1 := 8 * a1 + 8 * d2 + 3 * m0 + 2 * m1 + vc0
      let t3 := 3 * nu + rF
      let t4 := 4 * d2 + 3 * m0 + 2 * m1 + c
      t4 > t3 → t1 ≤ t3) :
    2 * ((c : ℤ) - rF) ≤ 2 * n0 + 8 * e1 + 16 * e2 + 14 * erem + 3 * L := by
  rcases hpt with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                  ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · by_cases hd : d2 = 0
    · have ha0 := hirr_a1 (Or.inl rfl) hd
      by_cases he : erem = 0
      · have hc0 := hk1_c0 rfl hd he; omega
      · omega
    · have htr := htri (Or.inr (by omega))
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · have hrF := hrF_k2hit rfl rfl rfl rfl rfl
    by_cases hd : d2 = 0
    · have ha0 := hirr_a1 (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hd; omega
    · have htr := htri (Or.inr (by omega))
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
  · have hrF := hrF_k2mis rfl
    by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega

/-- STEP 0B bound 2 (`b1c1`, `ODE_holds`, exact 3-term model):
`c - r_F ≤ n₀ + 4 e₁ + 5 e₂ + 3 e_rem + 2 L` for ALL unbounded `ℕ`. -/
theorem step0B_bound2
    (n0 m1 e1 e2 erem d2 L nu a1 g b rF c : ℕ)
    (hL : L % 2 = 0) (hn0 : n0 ≤ 1) (hm1 : m1 ≤ 1) (he1 : e1 ≤ 1) (he2 : e2 ≤ 1)
    (hd2 : d2 ≤ 1) (hnu : nu ≤ 1) (hb : b ≤ 1)
    (hpt : (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 0 ∧ L = 0) ∨
           (n0 = 1 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 1 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 1 ∧ e2 = 0 ∧ nu = 1 ∧ L = 0) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ nu = 1) ∨
           (n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 1 ∧ nu = 1))
    (hS : g ≤ (n0 + e1 + e2) + (L + e1 + 2 * e2 + erem) + 5 * (a1 + d2))
    (htot : c + rF + (n0 + e1 + e2) = 2 * g + b)
    (hrF_k2hit : nu = 1 → n0 = 0 → m1 = 0 → e1 = 0 → e2 = 0 → L ≤ rF + 8 * erem)
    (hrF_k2mis : e2 = 1 → L ≤ rF + 5 + 8 * erem)
    (hirr_a1 : (m1 = 1 ∨ (nu = 1 ∧ n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0)) → d2 = 0 → a1 = 0)
    (hk1_c0 : m1 = 1 → d2 = 0 → erem = 0 → c = 0)
    (hode1 : ((4 * d2 + 3 * (n0 + e1 + e2) + 2 * m1 + c) - rF) % 4 ≠ 1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let m0 := n0 + e1 + e2
      let vc0 :=
        if nu = 1 ∧ ((n0 = 0 ∧ m1 = 0 ∧ e1 = 0 ∧ e2 = 0) ∨ e2 = 1) then min c (L + 3)
        else if m1 = 1 ∨ e1 = 1 then min c 1
        else 0
      let t1 := 8 * a1 + 8 * d2 + 3 * m0 + 2 * m1 + vc0
      let t3 := 3 * nu + rF
      let t4 := 4 * d2 + 3 * m0 + 2 * m1 + c
      t4 > t3 → t1 ≤ t3) :
    (c : ℤ) - rF ≤ n0 + 4 * e1 + 5 * e2 + 3 * erem + 2 * L := by
  rcases hpt with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                  ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · by_cases hd : d2 = 0
    · have ha0 := hirr_a1 (Or.inl rfl) hd
      by_cases he : erem = 0
      · have hc0 := hk1_c0 rfl hd he; omega
      · omega
    · have htr := htri (Or.inr (by omega))
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
  · by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · omega
  · have hrF := hrF_k2hit rfl rfl rfl rfl rfl
    by_cases hd : d2 = 0
    · have ha0 := hirr_a1 (Or.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hd; omega
    · have htr := htri (Or.inr (by omega))
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
  · have hrF := hrF_k2mis rfl
    by_cases h : 1 ≤ a1 ∨ 1 ≤ d2
    · have htr := htri h
      simp only [↓reduceIte, true_and, and_true, false_and, and_false, or_true, true_or, false_or, or_false, one_ne_zero, zero_ne_one] at htr
      omega
    · have hsplit : (c : ℤ) - rF ≤ 5 + 3 * erem + 2 * L ∨ (c = 6 + 2 * L ∧ rF = 0 ∧ d2 = 0) := by omega
      rcases hsplit with hok | ⟨hc, hrF0, hd20⟩
      · exact hok
      · rw [hc, hrF0, hd20] at hode1; omega

/-- STEP 0C bound 1 (`K ≠ 0`, `ODE_fail_B1_holds`, NO ODE needed!):
`c - e₁ ≤ m₀ + 7 μ + 3 λ_ex + 6 d₂_in` for ALL unbounded `ℕ`. -/
theorem step0C_bound1
    (m0 m1 nu mu lam_ex a1 d2 L e1 c : ℕ)
    (hL : L % 2 = 0) (hm0 : m0 ≤ 1) (hm1 : m1 ≤ 1) (hnu : nu ≤ 1) (hd2 : d2 ≤ 1)
    (hpt : (nu = 0 ∧ m0 = 0 ∧ m1 = 0 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 1 ∧ m1 = 0 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 0 ∧ m1 = 1 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 0 ∧ m1 = 0))
    (hirr0 : nu = 1 → m0 = 0 → m1 = 0 → d2 = 0 → a1 = 0)
    (hirr1 : nu = 1 → m0 = 0 → m1 = 0 → d2 = 1 → 1 ≤ L + lam_ex + a1)
    (hk1_clean : m1 = 1 → L + lam_ex = 0 → mu = 0 → d2 = 0 → a1 = 0 ∧ 1 ≤ e1)
    (htot : c + e1 = m0 + m1 + 2 * (L + lam_ex) + 6 * d2 + 10 * a1)
    (he1 : L ≤ e1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let m := m0 + m1
      let vc0 := if nu = 1 ∧ m = 0 then min (L + 3) (min (e1 + 1) c) else 0
      let t1 := 8 * a1 + 4 * d2 + 3 * m + vc0
      let t2 := 4 * a1 + 2 * d2 + (nu - m) + 3 * m + e1
      let t3 := 3 * nu + 2 * mu + e1
      let t4 := c + 3 * m
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    let d2_in := if nu = 1 ∧ m0 = 0 ∧ m1 = 0 then d2 else 0
    (c : ℤ) - e1 ≤ m0 + 7 * mu + 3 * lam_ex + 6 * d2_in := by
  rcases hpt with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (1 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (1 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · by_cases hclean : 0 + lam_ex = 0 ∧ mu = 0
        · have := hk1_clean rfl hclean.1 hclean.2 hd; omega
        · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (0 + 1)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 1)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases hd : d2 = 0
    · have ha0 := hirr0 rfl rfl rfl hd; omega
    · have hd1 : d2 = 1 := by omega
      subst hd1
      have h1 := hirr1 rfl rfl rfl rfl
      have htr := htri (Or.inr (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega

/-- STEP 0C bound 2 (`K ≠ 0`, `ODE_fail_B1_holds`, NO ODE needed!):
`c - e₁ ≤ m₀ + 8 μ + 8 λ_ex + 3 L` for ALL unbounded `ℕ`. -/
theorem step0C_bound2
    (m0 m1 nu mu lam_ex a1 d2 L e1 c : ℕ)
    (hL : L % 2 = 0) (hm0 : m0 ≤ 1) (hm1 : m1 ≤ 1) (hnu : nu ≤ 1) (hd2 : d2 ≤ 1)
    (hpt : (nu = 0 ∧ m0 = 0 ∧ m1 = 0 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 1 ∧ m1 = 0 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 0 ∧ m1 = 1 ∧ L = 0) ∨
           (nu = 1 ∧ m0 = 0 ∧ m1 = 0))
    (hirr0 : nu = 1 → m0 = 0 → m1 = 0 → d2 = 0 → a1 = 0)
    (hirr1 : nu = 1 → m0 = 0 → m1 = 0 → d2 = 1 → 1 ≤ L + lam_ex + a1)
    (hk1_clean : m1 = 1 → L + lam_ex = 0 → mu = 0 → d2 = 0 → a1 = 0 ∧ 1 ≤ e1)
    (htot : c + e1 = m0 + m1 + 2 * (L + lam_ex) + 6 * d2 + 10 * a1)
    (he1 : L ≤ e1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 →
      let m := m0 + m1
      let vc0 := if nu = 1 ∧ m = 0 then min (L + 3) (min (e1 + 1) c) else 0
      let t1 := 8 * a1 + 4 * d2 + 3 * m + vc0
      let t2 := 4 * a1 + 2 * d2 + (nu - m) + 3 * m + e1
      let t3 := 3 * nu + 2 * mu + e1
      let t4 := c + 3 * m
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    (c : ℤ) - e1 ≤ m0 + 8 * mu + 8 * lam_ex + 3 * L := by
  rcases hpt with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 0 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (1 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (1 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases ha : a1 = 0
    · by_cases hd : d2 = 0
      · by_cases hclean : 0 + lam_ex = 0 ∧ mu = 0
        · have := hk1_clean rfl hclean.1 hclean.2 hd; omega
        · omega
      · have htr := htri (Or.inr (by omega))
        rcases lt_trichotomy (c + 3 * (0 + 1)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
        · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
        · omega
        · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
          · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
            all_goals omega
          · omega
    · have htr := htri (Or.inl (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 1)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
  · simp only [↓reduceIte, true_and, and_true, false_and, and_false, one_ne_zero, zero_ne_one, zero_add, add_zero, mul_zero, mul_one, Nat.sub_zero, Nat.sub_self] at htot he1 htri ⊢
    by_cases hd : d2 = 0
    · have ha0 := hirr0 rfl rfl rfl hd; omega
    · have hd1 : d2 = 1 := by omega
      subst hd1
      have h1 := hirr1 rfl rfl rfl rfl
      have htr := htri (Or.inr (by omega))
      rcases lt_trichotomy (c + 3 * (0 + 0)) (3 * 1 + 2 * mu + e1) with hlt | heq | hgt
      · have hm := htr.2 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega
      · omega
      · have hm := htr.1 (by omega); rw [min_le_iff] at hm; rcases hm with hm | hm
        · try (have hv : min (L + 3) (min (e1 + 1) c) = L + 3 ∨ min (L + 3) (min (e1 + 1) c) = e1 + 1 ∨ min (L + 3) (min (e1 + 1) c) = c := by omega; rcases hv with hv | hv | hv <;> rw [hv] at hm)
          all_goals omega
        · omega

/-! ### Part 2: Characteristic-2 Hasse derivatives `D^[1], D^[2]` and global ODE theorem -/

section Char2Hasse

variable {E : Type*} [Field E] [CharP E 2]

/-- The `k`-th Hasse derivative of a univariate polynomial (coefficient of `T^k` in `p(X + T)`). -/
noncomputable def hasse (k : ℕ) (p : E[X]) : E[X] :=
  ∑ i ∈ p.support, C ((Nat.choose i k : E) * p.coeff i) * X ^ (i - k)

omit [CharP E 2] in
private lemma coeff_finset_sum_E {ι : Type*} (s : Finset ι) (f : ι → E[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  simp

lemma coeff_hasse (k : ℕ) (p : E[X]) (n : ℕ) :
    (hasse k p).coeff n = (Nat.choose (n + k) k : E) * p.coeff (n + k) := by
  classical
  unfold hasse
  rw [coeff_finset_sum_E]
  by_cases hmem : n + k ∈ p.support
  · rw [Finset.sum_eq_single (n + k)]
    · rw [coeff_C_mul_X_pow]; simp
    · intro i _ hne
      rw [coeff_C_mul_X_pow]
      split_ifs with h
      · by_cases hik : k ≤ i
        · omega
        · have hch : Nat.choose i k = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [hch]
      · rfl
    · intro hnot; exact absurd hmem hnot
  · have hp0 : p.coeff (n + k) = 0 := by simpa [mem_support_iff] using hmem
    rw [hp0, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_C_mul_X_pow]
    split_ifs with h
    · by_cases hik : k ≤ i
      · have heq : i = n + k := by omega
        subst heq; exact absurd hi hmem
      · have hch : Nat.choose i k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hch]
    · rfl

lemma hasse_zero (p : E[X]) : hasse 0 p = p := by
  ext n; simp [coeff_hasse]

lemma hasse_one_eq_derivative (p : E[X]) : hasse 1 p = p.derivative := by
  ext n; simp [coeff_hasse, coeff_derivative, Nat.choose_one_right, mul_comm]

lemma hasse_add (k : ℕ) (p q : E[X]) : hasse k (p + q) = hasse k p + hasse k q := by
  ext n; simp [coeff_hasse, mul_add]

/-- In characteristic 2, `C(n + 1, 1) mod 2 = (n + 1) % 2`. -/
lemma char2_choose_one (n : ℕ) :
    ((Nat.choose (n + 1) 1 : ℕ) : E) = if n % 2 = 0 then 1 else 0 := by
  rw [Nat.choose_one_right]
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hdiv := Nat.div_add_mod (n + 1) 2
  have hcast : ((n + 1 : ℕ) : E) = ((n + 1) % 2 : ℕ) := by
    calc ((n + 1 : ℕ) : E) = ((2 * ((n + 1) / 2) + (n + 1) % 2 : ℕ) : E) := by rw [hdiv]
      _ = (2 : E) * (((n + 1) / 2 : ℕ) : E) + (((n + 1) % 2 : ℕ) : E) := by push_cast; ring
      _ = (((n + 1) % 2 : ℕ) : E) := by rw [h2, zero_mul, zero_add]
  rw [hcast]
  split_ifs with h
  · have : (n + 1) % 2 = 1 := by omega
    simp [this]
  · have : (n + 1) % 2 = 0 := by omega
    simp [this]

/-- In characteristic 2, `C(n + 2, 2) mod 2 = 1 ↔ n % 4 ∈ {0, 1}`. -/
lemma char2_choose_two (n : ℕ) :
    ((Nat.choose (n + 2) 2 : ℕ) : E) = if n % 4 < 2 then 1 else 0 := by
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hch : Nat.choose (n + 2) 2 = (n + 2) * (n + 1) / 2 := by
    simp [Nat.choose_two_right]
  have hmod : (Nat.choose (n + 2) 2) % 2 = if n % 4 < 2 then 1 else 0 := by
    rw [hch]
    have h4 := Nat.div_add_mod n 4
    set q := n / 4
    set r := n % 4
    have hr : r < 4 := Nat.mod_lt n (by norm_num)
    have hn : n = 4 * q + r := by omega
    rw [hn]
    interval_cases r
    · have h : (4 * q + 0 + 2) * (4 * q + 0 + 1) / 2 = 2 * (4 * q * q + 3 * q) + 1 := by
        rw [show (4 * q + 0 + 2) * (4 * q + 0 + 1) = 2 * (2 * (4 * q * q + 3 * q) + 1) by ring,
          Nat.mul_div_right _ (by norm_num)]
      rw [h]; simp
    · have h : (4 * q + 1 + 2) * (4 * q + 1 + 1) / 2 = 2 * (4 * q * q + 5 * q + 1) + 1 := by
        rw [show (4 * q + 1 + 2) * (4 * q + 1 + 1) = 2 * (2 * (4 * q * q + 5 * q + 1) + 1) by ring,
          Nat.mul_div_right _ (by norm_num)]
      rw [h]; simp
    · have h : (4 * q + 2 + 2) * (4 * q + 2 + 1) / 2 = 2 * (4 * q * q + 7 * q + 3) := by
        rw [show (4 * q + 2 + 2) * (4 * q + 2 + 1) = 2 * (2 * (4 * q * q + 7 * q + 3)) by ring,
          Nat.mul_div_right _ (by norm_num)]
      rw [h]; simp
    · have h : (4 * q + 3 + 2) * (4 * q + 3 + 1) / 2 = 2 * (4 * q * q + 9 * q + 5) := by
        rw [show (4 * q + 3 + 2) * (4 * q + 3 + 1) = 2 * (2 * (4 * q * q + 9 * q + 5)) by ring,
          Nat.mul_div_right _ (by norm_num)]
      rw [h]; simp
  have hdiv := Nat.div_add_mod (Nat.choose (n + 2) 2) 2
  have hcast : ((Nat.choose (n + 2) 2 : ℕ) : E) = ((Nat.choose (n + 2) 2 % 2 : ℕ) : E) := by
    calc ((Nat.choose (n + 2) 2 : ℕ) : E)
        = ((2 * (Nat.choose (n + 2) 2 / 2) + Nat.choose (n + 2) 2 % 2 : ℕ) : E) := by rw [hdiv]
      _ = (2 : E) * ((Nat.choose (n + 2) 2 / 2 : ℕ) : E) +
          ((Nat.choose (n + 2) 2 % 2 : ℕ) : E) := by push_cast; ring
      _ = ((Nat.choose (n + 2) 2 % 2 : ℕ) : E) := by rw [h2, zero_mul, zero_add]
  rw [hcast, hmod]
  split_ifs <;> simp

/-- **Exact polynomial ODE characterization in char 2:**
If `c₀ ≠ 0` and `P ∈ E[X]` satisfies `c₀ · P^{[2]} + c₁ · P^{[1]} = 0`, then:
- `P.coeff (4 k + 3) = 0` for all `k`, and
- `c₀ · P.coeff (4 k + 2) = c₁ · P.coeff (4 k + 1)` for all `k`.
Hence `P(X) = A₀(X⁴) + (c₀ X + c₁ X²) A₁(X⁴)`! -/
theorem char2_poly_ode_coeffs {c0 c1 : E} (hc0 : c0 ≠ 0) {P : E[X]}
    (hode : C c0 * hasse 2 P + C c1 * hasse 1 P = 0) :
    (∀ k : ℕ, P.coeff (4 * k + 3) = 0) ∧
    (∀ k : ℕ, c0 * P.coeff (4 * k + 2) = c1 * P.coeff (4 * k + 1)) := by
  constructor
  · intro k
    have h := congrArg (fun q : E[X] => q.coeff (4 * k + 1)) hode
    simp only [coeff_add, coeff_C_mul, coeff_zero, coeff_hasse, char2_choose_two,
      char2_choose_one] at h
    have hm4 : (4 * k + 1) % 4 < 2 := by omega
    have hm2 : ¬ ((4 * k + 1) % 2 = 0) := by omega
    simp only [hm4, hm2, ↓reduceIte, one_mul, zero_mul, mul_zero, add_zero] at h
    have h3 : 4 * k + 1 + 2 = 4 * k + 3 := by omega
    rw [h3] at h
    exact (mul_eq_zero.mp h).resolve_left hc0
  · intro k
    have h := congrArg (fun q : E[X] => q.coeff (4 * k)) hode
    simp only [coeff_add, coeff_C_mul, coeff_zero, coeff_hasse, char2_choose_two,
      char2_choose_one] at h
    have hm4 : (4 * k) % 4 < 2 := by omega
    have hm2 : (4 * k) % 2 = 0 := by omega
    simp only [hm4, hm2, ↓reduceIte, one_mul] at h
    have h2 : c0 * P.coeff (4 * k + 2) + c1 * P.coeff (4 * k + 1) = 0 := h
    have hadd := congrArg (· + c1 * P.coeff (4 * k + 1)) h2
    simp only [zero_add, add_assoc, CharTwo.add_self_eq_zero, add_zero] at hadd
    exact hadd

lemma hasse_comp_add_C (k : ℕ) (p : E[X]) (a : E) :
    hasse k (p.comp (X + C a)) = (hasse k p).comp (X + C a) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [add_comp, hasse_add, hp, hq]
  | monomial n c =>
      ext r
      rw [coeff_hasse]
      have hLHS : ((monomial n c).comp (X + C a)).coeff (r + k) =
          c * (Nat.choose n (r + k) : E) * a ^ (n - (r + k)) := by
        rw [monomial_comp, coeff_C_mul, add_pow, coeff_finset_sum_E]
        simp only [← C_pow, coeff_mul_natCast, coeff_mul_C, coeff_X_pow]
        by_cases hle : r + k ≤ n
        · rw [Finset.sum_eq_single (r + k)]
          · simp only [↓reduceIte, one_mul]; ring
          · intro b _ hne
            simp [Ne.symm hne]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · have hch : Nat.choose n (r + k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [hch, Nat.cast_zero, mul_zero, zero_mul]
          rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero
          intro b hb
          have hblt : b < n + 1 := Finset.mem_range.mp hb
          have : r + k ≠ b := by omega
          simp [this]
      have hmon : hasse k (monomial n c) = C ((Nat.choose n k : E) * c) * X ^ (n - k) := by
        ext m
        rw [coeff_hasse, coeff_C_mul_X_pow, coeff_monomial]
        by_cases hkn : k ≤ n
        · by_cases hm : m = n - k
          · subst hm
            rw [Nat.sub_add_cancel hkn]
            simp [mul_comm]
          · have hne : n ≠ m + k := by omega
            simp [hm, hne]
        · have hch : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hne : n ≠ m + k := by omega
          simp [hch, hne]
      rw [hmon, mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul, add_pow, coeff_finset_sum_E]
      simp only [← C_pow, coeff_mul_natCast, coeff_mul_C, coeff_X_pow]
      rw [hLHS]
      by_cases hle : r + k ≤ n
      · rw [Finset.sum_eq_single r]
        · have hsub : n - k - r = n - (r + k) := by omega
          have hident : Nat.choose (r + k) k * Nat.choose n (r + k) =
              Nat.choose n k * Nat.choose (n - k) r := by
            have h1 := Nat.choose_mul (n := n) (k := r + k) (s := k) (by omega : k ≤ r + k)
            have h2 : r + k - k = r := by omega
            rw [h2] at h1
            linarith [mul_comm (Nat.choose (r + k) k) (Nat.choose n (r + k)),
                      mul_comm (Nat.choose n k) (Nat.choose (n - k) r)]
          have hcast : ((Nat.choose (r + k) k : ℕ) : E) * ((Nat.choose n (r + k) : ℕ) : E) =
              ((Nat.choose n k : ℕ) : E) * ((Nat.choose (n - k) r : ℕ) : E) := by
            rw [← Nat.cast_mul, ← Nat.cast_mul, hident]
          rw [hsub]
          simp only [↓reduceIte, one_mul]
          calc ((Nat.choose (r + k) k : ℕ) : E) * (c * (Nat.choose n (r + k) : E) * a ^ (n - (r + k)))
              = (((Nat.choose (r + k) k : ℕ) : E) * (Nat.choose n (r + k) : E)) * c * a ^ (n - (r + k)) := by ring
            _ = (((Nat.choose n k : ℕ) : E) * (Nat.choose (n - k) r : E)) * c * a ^ (n - (r + k)) := by rw [hcast]
            _ = ((Nat.choose n k : ℕ) : E) * c * (a ^ (n - (r + k)) * (Nat.choose (n - k) r : E)) := by ring
        · intro b _ hne
          simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · have hch : Nat.choose n (r + k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hch, Nat.cast_zero, mul_zero, zero_mul, mul_zero]
        by_cases hkn : k ≤ n
        · symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero
          intro b hb
          have hblt : b < n - k + 1 := Finset.mem_range.mp hb
          have : r ≠ b := by omega
          simp [this]
        · have hchk : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [hchk]

omit [CharP E 2] in
private lemma rootMultiplicity_eq_natTrailingDegree_shift (P : E[X]) (hP : P ≠ 0) (a : E) :
    P.rootMultiplicity a = (P.comp (X + C a)).natTrailingDegree := by
  let Q := P.comp (X + C a)
  have hQne : Q ≠ 0 := by
    intro h0; apply hP
    have := congrArg (fun f : E[X] => f.comp (X - C a)) h0
    simp only [Q, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X, zero_comp] at this
    exact this
  have hdvd_iff : ∀ k : ℕ, (X - C a) ^ k ∣ P ↔ X ^ k ∣ Q := by
    intro k
    constructor
    · rintro ⟨R, hR⟩
      refine ⟨R.comp (X + C a), ?_⟩
      simp only [Q, hR, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
    · rintro ⟨R, hR⟩
      refine ⟨R.comp (X - C a), ?_⟩
      have := congrArg (fun f : E[X] => f.comp (X - C a)) hR
      simp only [Q, comp_assoc, add_comp, mul_comp, pow_comp, X_comp, C_comp, sub_add_cancel, comp_X] at this
      exact this
  apply le_antisymm
  · have h1 : X ^ (P.rootMultiplicity a) ∣ Q :=
      (hdvd_iff _).mp (pow_rootMultiplicity_dvd P a)
    by_contra hlt
    push Not at hlt
    exact Polynomial.trailingCoeff_ne_zero.mpr hQne
      ((Polynomial.X_pow_dvd_iff.mp h1) Q.natTrailingDegree hlt)
  · have h1 : (X - C a) ^ Q.natTrailingDegree ∣ P :=
      (hdvd_iff _).mpr (Polynomial.X_pow_dvd_iff.mpr fun d hd =>
        coeff_eq_zero_of_lt_natTrailingDegree hd)
    exact (Polynomial.le_rootMultiplicity_iff hP).mpr h1

/-- **Main ODE Root-Multiplicity Theorem:**
If `P ∈ E[X]` is nonzero and satisfies `c₀ P^{[2]} + c₁ P^{[1]} = 0` (`c₀ ≠ 0`), then for EVERY
`a ∈ E`, `P.rootMultiplicity a % 4 ≠ 2 ∧ P.rootMultiplicity a % 4 ≠ 3` (i.e. `∈ {0, 1}`). -/
theorem rootMultiplicity_mod_four_of_poly_ode {c0 c1 : E} (hc0 : c0 ≠ 0) {P : E[X]} (hP : P ≠ 0)
    (hode : C c0 * hasse 2 P + C c1 * hasse 1 P = 0) (a : E) :
    P.rootMultiplicity a % 4 = 0 ∨ P.rootMultiplicity a % 4 = 1 := by
  let Q := P.comp (X + C a)
  have hQne : Q ≠ 0 := by
    intro h0
    apply hP
    have := congrArg (fun f : E[X] => f.comp (X - C a)) h0
    simp only [Q, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X, zero_comp] at this
    exact this
  have hQode : C c0 * hasse 2 Q + C c1 * hasse 1 Q = 0 := by
    have hcomp := congrArg (fun f : E[X] => f.comp (X + C a)) hode
    simp only [add_comp, mul_comp, C_comp, zero_comp, ← hasse_comp_add_C] at hcomp
    exact hcomp
  obtain ⟨h3, h2⟩ := char2_poly_ode_coeffs hc0 hQode
  have hm_eq : P.rootMultiplicity a = Q.natTrailingDegree :=
    rootMultiplicity_eq_natTrailingDegree_shift P hP a
  rw [hm_eq]
  set m := Q.natTrailingDegree
  have hcm : Q.coeff m ≠ 0 := trailingCoeff_ne_zero.mpr hQne
  have hlt : ∀ j < m, Q.coeff j = 0 := fun j hj => coeff_eq_zero_of_lt_natTrailingDegree hj
  have hmod : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  set q := m / 4
  set r := m % 4
  have hm : m = 4 * q + r := by omega
  interval_cases r
  · left; rfl
  · right; rfl
  · exfalso
    have h1 : Q.coeff (4 * q + 1) = 0 := hlt (4 * q + 1) (by omega)
    have h2' := h2 q
    rw [h1, mul_zero] at h2'
    have hzero := (mul_eq_zero.mp h2').resolve_left hc0
    rw [hm] at hcm
    exact hcm hzero
  · exfalso
    rw [hm] at hcm
    exact hcm (h3 q)

/-- Corollary for a rational function `P / Q` with `Q = Q₀^4`:
if `P` solves the ODE and `C_hat = Q₀^4 / gcd(P, Q₀^4)`, then
`v_a(C_hat) % 4 ∈ {0, 3}` for EVERY `a ∈ E`! -/
theorem denom_mod_four_of_poly_ode {vQ0 vP : ℕ} (hP : vP % 4 = 0 ∨ vP % 4 = 1) :
    (4 * vQ0 - vP) % 4 = 0 ∨ (4 * vQ0 - vP) % 4 = 3 := by
  omega

end Char2Hasse

/-! ### Part 3: Unbounded-`ℕ` 15-column STEP `omega` theorems (`K ≠ 0`) -/

/-- The 10 local point types for the 15-column `K ≠ 0` STEP inequalities. -/
inductive Step15Pt where
  | out | k0 | k1U | k2noU | k2U | k2U_mL | k2U_mb | k3U | k3U_mL | k3U_mb
  deriving DecidableEq

namespace Step15Pt

def nu : Step15Pt → ℕ
  | .out => 0 | _ => 1

def m0 : Step15Pt → ℕ
  | .k0 => 1 | _ => 0

def mbad : Step15Pt → ℕ
  | .k2U_mb | .k3U_mb => 1 | _ => 0

def m1 : Step15Pt → ℕ
  | .k1U => 1 | _ => 0

def m2 : Step15Pt → ℕ
  | .k2noU => 1 | _ => 0

def k3 : Step15Pt → ℕ
  | .k3U | .k3U_mL | .k3U_mb => 1 | _ => 0

def isML : Step15Pt → Bool
  | .k2U_mL | .k3U_mL => true | _ => false

def mVal (pt : Step15Pt) : ℕ := pt.m0 + pt.mbad + pt.m1 + pt.m2

def mL0 (pt : Step15Pt) (d2 : ℕ) : ℕ := if pt.isML = true ∧ d2 = 0 then 1 else 0

def din (pt : Step15Pt) (d2 : ℕ) : ℕ :=
  match pt with | .k2U | .k3U => d2 | _ => 0

def dmL (pt : Step15Pt) (d2 : ℕ) : ℕ := if pt.isML = true ∧ d2 = 1 then d2 else 0

def d2oth (pt : Step15Pt) (d2 : ℕ) : ℕ := d2 - pt.din d2 - pt.dmL d2

def mu1 (pt : Step15Pt) (d2 mu : ℕ) : ℕ :=
  match pt with | .k1U => if d2 = 0 ∧ 1 ≤ mu then 1 else 0 | _ => 0

def muO (pt : Step15Pt) (d2 mu : ℕ) : ℕ := mu - pt.mu1 d2 mu

def k1Min (pt : Step15Pt) (d2 lam L0 LnoU : ℕ) : ℕ :=
  match pt with
  | .k2U | .k2U_mL => if d2 = 1 then 2 - lam else 0
  | .k3U | .k3U_mL => if d2 = 1 then max 1 (4 + L0 - lam) else 0
  | .k2noU => if 0 < LnoU then 2 + LnoU / 2 else 1
  | _ => 0

def vc0 (pt : Step15Pt) (d2 e1 c L0 LnoU : ℕ) : ℕ :=
  match pt with
  | .k3U | .k3U_mL => if d2 = 1 then 5 + L0 else min 3 (min (e1 + 1) c)
  | .k2U | .k2U_mL => if d2 = 1 then 3 else min 3 (min (e1 + 1) c)
  | .k2noU => if 0 < LnoU then 5 + LnoU else 3
  | .k1U => 1
  | _ => 0

def vChat (pt : Step15Pt) (mu e1 c : ℕ) : ℤ :=
  if pt.isML = true then (c : ℤ) - (e1 : ℤ) + 2
  else ((c : ℤ) + 3 * (pt.mVal : ℤ)) - ((e1 : ℤ) + 2 * (mu : ℤ))

def t3 (pt : Step15Pt) (d2 mu e1 : ℕ) : ℕ :=
  if pt.isML = true ∧ d2 = 1 then 1 + e1 else 3 * pt.nu + 2 * mu + e1

def c04Val (v : ℤ) : ℕ :=
  if v ≤ 0 then 0 else ((v.toNat + 3) / 4) * 4

end Step15Pt

private theorem step15_htri_split {a b c d : ℕ}
    (h : (c > d → min a b ≤ d) ∧ (c < d → min a b ≤ c)) :
    (c < d ∧ a ≤ c) ∨ (c < d ∧ b ≤ c) ∨ c = d ∨ (c > d ∧ a ≤ d) ∨ (c > d ∧ b ≤ d) := by
  rcases lt_trichotomy c d with hlt | heq | hgt
  · rcases min_le_iff.mp (h.2 hlt) with ha | hb
    · exact Or.inl ⟨hlt, ha⟩
    · exact Or.inr (Or.inl ⟨hlt, hb⟩)
  · exact Or.inr (Or.inr (Or.inl heq))
  · rcases min_le_iff.mp (h.1 hgt) with ha | hb
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hgt, ha⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hgt, hb⟩)))

set_option maxHeartbeats 1600000 in
/-- **15-column STEP 0A (`ODE_holds`, unbounded `ℕ`):**
`2 (c - e₁) ≤ 2 m₀ + 4 m_bad - 11 m₂ - 4 k₃ - 10 mL₀ + 11 μ_O + 6 λ + 6 d_in - 4 d_mL + d₂_oth - 2 L₀ - 2 L_noU`. -/
theorem step15_0A
    (pt : Step15Pt) (L0 LnoU a1 d2 mu lam g b e1 c : ℕ)
    (hd2 : d2 ≤ 1) (hb : b ≤ 1) (hL0_ev : L0 % 2 = 0) (hLnoU_ev : LnoU % 2 = 0)
    (hL0 : 0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb)
    (hLnoU : 0 < LnoU → pt = .k2noU)
    (hd2_zero : (pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0)
    (ha1_zero : (pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) →
      d2 = 0 → a1 = 0)
    (hmu_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0)
    (hk2noU : pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu))
    (hk2U_mL : pt = .k2U_mL → 1 ≤ lam)
    (hk3U : pt = .k3U → 2 + L0 ≤ lam + mu)
    (hk3U_mL : pt = .k3U_mL → 3 + L0 ≤ lam)
    (hk3U_mb : pt = .k3U_mb → 1 + L0 ≤ lam + mu)
    (he1_k1U : pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1)
    (he1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1)
    (hS : g ≤ pt.mVal + lam + 3 * d2 + 5 * a1)
    (hSmod : g % 2 = (pt.mVal + lam + 3 * d2 + 5 * a1) % 2)
    (hb1 : pt.nu = 1 → b = 1 → g + 2 ≤ pt.mVal + lam + 3 * d2 + 5 * a1)
    (htot : c + e1 + pt.mVal = 2 * g + b)
    (hode : pt.mbad = 0 → pt.vChat mu e1 c % 4 ≠ 1 ∧ pt.vChat mu e1 c % 4 ≠ 2)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤
      2 * (pt.m0 : ℤ) + 4 * (pt.mbad : ℤ) - 11 * (pt.m2 : ℤ) - 4 * (pt.k3 : ℤ) -
      10 * (pt.mL0 d2 : ℤ) + 11 * (pt.muO d2 mu : ℤ) + 6 * (lam : ℤ) +
      6 * (pt.din d2 : ℤ) - 4 * (pt.dmL d2 : ℤ) + (pt.d2oth d2 : ℤ) -
      2 * (L0 : ℤ) - 2 * (LnoU : ℤ) := by
  have hd2_cases : d2 = 0 ∨ d2 = 1 := by omega
  cases pt
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) rfl
      subst ha0
      by_cases hmu0 : mu = 0
      · have he := he1_k1U rfl (Or.inr hmu0); subst hmu0
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, show 1 ≤ mu by omega] at *
        first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
    · have he := he1_k1U rfl (Or.inl rfl)
      have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hd0 : d2 = 0 := hd2_zero (Or.inl rfl)
    subst hL0z; subst hd0
    have ⟨ho1, ho2⟩ := hode rfl
    have ⟨hkl0, hklp⟩ := hk2noU rfl
    by_cases hLn0 : LnoU = 0
    · subst hLn0; have hlm := hkl0 rfl
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
    · have hlm := hklp (by omega)
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3,
        show 0 < LnoU by omega] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inl rfl) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · by_cases hspec : a1 = 0 ∧ lam = 2 ∧ mu = 0
        · rcases hspec with ⟨rfl, rfl, rfl⟩; clear hSmod; omega
        · rcases htr with h | h | h | h | h <;> (clear hSmod ho1 ho2; omega)
      · rcases htr with h | h | h | h | h <;> (clear hSmod ho1 ho2; omega)
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inl rfl)
    have hlam1 := hk2U_mL rfl
    subst hL0z; subst hLnz; subst hmu0
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inl rfl)) rfl; subst ha0
      have he := he1_mL (Or.inl rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at *
      first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inl rfl))
    subst hL0z; subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inl rfl))) rfl; subst ha0
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hLnz
    have hlm := hk3U rfl
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inr rfl)
    have hlam3 := hk3U_mL rfl
    subst hLnz; subst hmu0
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) rfl; subst ha0
      have he := he1_mL (Or.inr rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inr rfl))
    subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) rfl; subst ha0
    have hlm := hk3U_mb rfl
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega

/-- **15-column STEP 0C row 0 (`B1_holds`, NO ODE, unbounded `ℕ`):**
`2 (c - e₁) ≤ 2 m₀ + 7 m_bad - 8 m₂ - 10 k₃ - 13 mL₀ + 2 μ₁ + 10 μ_O + 9 λ + 2 d_in - 16 d_mL + 2 d₂_oth - 5 L₀ - 5 L_noU`. -/
theorem step15_0C_0
    (pt : Step15Pt) (L0 LnoU a1 d2 mu lam e1 c : ℕ)
    (hd2 : d2 ≤ 1) (hL0_ev : L0 % 2 = 0) (hLnoU_ev : LnoU % 2 = 0)
    (hL0 : 0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb)
    (hLnoU : 0 < LnoU → pt = .k2noU)
    (hd2_zero : (pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0)
    (ha1_zero : (pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) →
      d2 = 0 → a1 = 0)
    (hmu_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0)
    (hk2noU : pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu))
    (hk2U_mL : pt = .k2U_mL → 1 ≤ lam)
    (hk3U : pt = .k3U → 2 + L0 ≤ lam + mu)
    (hk3U_mL : pt = .k3U_mL → 3 + L0 ≤ lam)
    (hk3U_mb : pt = .k3U_mb → 1 + L0 ≤ lam + mu)
    (he1_k1U : pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1)
    (he1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1)
    (htot : c + e1 = pt.mVal + 2 * lam + 6 * d2 + 10 * a1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤
      2 * (pt.m0 : ℤ) + 7 * (pt.mbad : ℤ) - 8 * (pt.m2 : ℤ) - 10 * (pt.k3 : ℤ) -
      13 * (pt.mL0 d2 : ℤ) + 2 * (pt.mu1 d2 mu : ℤ) + 10 * (pt.muO d2 mu : ℤ) +
      9 * (lam : ℤ) + 2 * (pt.din d2 : ℤ) - 16 * (pt.dmL d2 : ℤ) +
      2 * (pt.d2oth d2 : ℤ) - 5 * (L0 : ℤ) - 5 * (LnoU : ℤ) := by
  have hd2_cases : d2 = 0 ∨ d2 = 1 := by omega
  cases pt
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) rfl; subst ha0
      by_cases hmu0 : mu = 0
      · have he := he1_k1U rfl (Or.inr hmu0); subst hmu0
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, show 1 ≤ mu by omega] at * ; omega
    · have he := he1_k1U rfl (Or.inl rfl)
      have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hd0 : d2 = 0 := hd2_zero (Or.inl rfl)
    subst hL0z; subst hd0
    have ⟨hkl0, hklp⟩ := hk2noU rfl
    by_cases hLn0 : LnoU = 0
    · subst hLn0; have hlm := hkl0 rfl
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
    · have hlm := hklp (by omega)
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3,
        show 0 < LnoU by omega] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inl rfl) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inl rfl); have hlam1 := hk2U_mL rfl
    subst hL0z; subst hLnz; subst hmu0
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inl rfl)) rfl; subst ha0
      have he := he1_mL (Or.inl rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inl rfl))
    subst hL0z; subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inl rfl))) rfl; subst ha0
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO] at * ; omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hLnz; have hlm := hk3U rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inr rfl); have hlam3 := hk3U_mL rfl
    subst hLnz; subst hmu0
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) rfl; subst ha0
      have he := he1_mL (Or.inr rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inr rfl))
    subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) rfl; subst ha0
    have hlm := hk3U_mb rfl
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO] at * ; omega

/-- **15-column STEP 0C row 1 (`B1_holds`, NO ODE, unbounded `ℕ`):**
`2 (c - e₁) ≤ 2 m₀ + 3 m_bad - 8 m₂ - 2 k₃ - 9 mL₀ + 2 μ₁ + 10 μ_O + 5 λ + 10 d_in - 16 d_mL + 2 d₂_oth - L₀ - L_noU`. -/
theorem step15_0C_1
    (pt : Step15Pt) (L0 LnoU a1 d2 mu lam e1 c : ℕ)
    (hd2 : d2 ≤ 1) (hL0_ev : L0 % 2 = 0) (hLnoU_ev : LnoU % 2 = 0)
    (hL0 : 0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb)
    (hLnoU : 0 < LnoU → pt = .k2noU)
    (hd2_zero : (pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0)
    (ha1_zero : (pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) →
      d2 = 0 → a1 = 0)
    (hmu_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0)
    (hk2noU : pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu))
    (hk2U_mL : pt = .k2U_mL → 1 ≤ lam)
    (hk3U : pt = .k3U → 2 + L0 ≤ lam + mu)
    (hk3U_mL : pt = .k3U_mL → 3 + L0 ≤ lam)
    (hk3U_mb : pt = .k3U_mb → 1 + L0 ≤ lam + mu)
    (he1_k1U : pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1)
    (he1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1)
    (htot : c + e1 = pt.mVal + 2 * lam + 6 * d2 + 10 * a1)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    2 * ((c : ℤ) - (e1 : ℤ)) ≤
      2 * (pt.m0 : ℤ) + 3 * (pt.mbad : ℤ) - 8 * (pt.m2 : ℤ) - 2 * (pt.k3 : ℤ) -
      9 * (pt.mL0 d2 : ℤ) + 2 * (pt.mu1 d2 mu : ℤ) + 10 * (pt.muO d2 mu : ℤ) +
      5 * (lam : ℤ) + 10 * (pt.din d2 : ℤ) - 16 * (pt.dmL d2 : ℤ) +
      2 * (pt.d2oth d2 : ℤ) - (L0 : ℤ) - (LnoU : ℤ) := by
  have hd2_cases : d2 = 0 ∨ d2 = 1 := by omega
  cases pt
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · by_cases ha : a1 = 0
      · subst ha; simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · have htr := step15_htri_split (htri (Or.inl (by omega)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) rfl; subst ha0
      by_cases hmu0 : mu = 0
      · have he := he1_k1U rfl (Or.inr hmu0); subst hmu0
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO] at * ; omega
      · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, show 1 ≤ mu by omega] at * ; omega
    · have he := he1_k1U rfl (Or.inl rfl)
      have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hd0 : d2 = 0 := hd2_zero (Or.inl rfl)
    subst hL0z; subst hd0
    have ⟨hkl0, hklp⟩ := hk2noU rfl
    by_cases hLn0 : LnoU = 0
    · subst hLn0; have hlm := hkl0 rfl
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
    · have hlm := hklp (by omega)
      have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3,
        show 0 < LnoU by omega] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inl rfl) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inl rfl); have hlam1 := hk2U_mL rfl
    subst hL0z; subst hLnz; subst hmu0
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inl rfl)) rfl; subst ha0
      have he := he1_mL (Or.inl rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inl rfl))
    subst hL0z; subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inl rfl))) rfl; subst ha0
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO] at * ; omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hLnz; have hlm := hk3U rfl
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl; subst ha0
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inr rfl); have hlam3 := hk3U_mL rfl
    subst hLnz; subst hmu0
    rcases hd2_cases with rfl | rfl
    · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) rfl; subst ha0
      have he := he1_mL (Or.inr rfl) rfl
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO] at * ; omega
    · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
      simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
      rcases htr with h | h | h | h | h <;> omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inr rfl))
    subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) rfl; subst ha0
    have hlm := hk3U_mb rfl
    simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
      Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
      Step15Pt.mu1, Step15Pt.muO] at * ; omega

private lemma c04Val_eq_zero {v : ℤ} (h : v ≤ 0) : (Step15Pt.c04Val v : ℤ) = 0 := by
  unfold Step15Pt.c04Val; simp [h]

private lemma c04Val_eq_pos {v : ℤ} (h : 0 < v) :
    (Step15Pt.c04Val v : ℤ) = ((v + 3) / 4) * 4 := by
  unfold Step15Pt.c04Val
  have hnot : ¬ v ≤ 0 := by omega
  simp only [hnot, ↓reduceIte]
  have hto : (v.toNat : ℤ) = v := Int.toNat_of_nonneg (by omega)
  push_cast; rw [hto]

set_option maxHeartbeats 1600000 in
/-- **15-column STEP C04 (`ODE_holds`, unbounded `ℕ`):**
`c₀₄ ≤ 4 m₀ + 4 m_bad - 4 m₂ - 4 k₃ - 4 mL₀ + 4 μ_O + 4 λ + 4 d_in + 4 d₂_oth - 2 L₀ - 2 L_noU`. -/
theorem step15_C04
    (pt : Step15Pt) (L0 LnoU a1 d2 mu lam g b e1 c : ℕ)
    (hd2 : d2 ≤ 1) (hb : b ≤ 1) (hL0_ev : L0 % 2 = 0) (hLnoU_ev : LnoU % 2 = 0)
    (hL0 : 0 < L0 → pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb)
    (hLnoU : 0 < LnoU → pt = .k2noU)
    (hd2_zero : (pt = .k2noU ∨ pt = .k2U_mb ∨ pt = .k3U_mb) → d2 = 0)
    (ha1_zero : (pt = .k2U ∨ pt = .k2U_mL ∨ pt = .k2U_mb ∨ pt = .k3U ∨ pt = .k3U_mL ∨ pt = .k3U_mb ∨ pt = .k1U) →
      d2 = 0 → a1 = 0)
    (hmu_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → mu = 0)
    (hk2noU : pt = .k2noU → (LnoU = 0 → 2 ≤ lam + mu) ∧ (0 < LnoU → 4 + LnoU ≤ lam + mu))
    (hk2U_mL : pt = .k2U_mL → 1 ≤ lam)
    (hk3U : pt = .k3U → 2 + L0 ≤ lam + mu)
    (hk3U_mL : pt = .k3U_mL → 3 + L0 ≤ lam)
    (hk3U_mb : pt = .k3U_mb → 1 + L0 ≤ lam + mu)
    (hk2U_mb_mu : pt = .k2U_mb → 2 ≤ mu)
    (hk3U_mb_mu : pt = .k3U_mb → 3 + L0 / 2 ≤ mu)
    (he1_k1U : pt = .k1U → (d2 = 1 ∨ mu = 0) → 1 ≤ e1)
    (he1_mL : (pt = .k2U_mL ∨ pt = .k3U_mL) → d2 = 0 → 2 ≤ e1)
    (hS : g ≤ pt.mVal + lam + 3 * d2 + 5 * a1)
    (hSmod : g % 2 = (pt.mVal + lam + 3 * d2 + 5 * a1) % 2)
    (hb1 : pt.nu = 1 → b = 1 → g + 2 ≤ pt.mVal + lam + 3 * d2 + 5 * a1)
    (htot : c + e1 + pt.mVal = 2 * g + b)
    (hode : pt.mbad = 0 → pt.vChat mu e1 c % 4 ≠ 1 ∧ pt.vChat mu e1 c % 4 ≠ 2)
    (htri : 1 ≤ a1 ∨ 1 ≤ d2 ∨ pt = .k2noU →
      let t1 := 8 * a1 + 4 * d2 + 3 * pt.mVal + pt.vc0 d2 e1 c L0 LnoU
      let t2 := 4 * a1 + 2 * d2 + 2 * pt.k1Min d2 lam L0 LnoU + (pt.nu - pt.mVal) + 3 * pt.mVal + e1
      let t3 := pt.t3 d2 mu e1
      let t4 := c + 3 * pt.mVal
      (t4 > t3 → min t1 t2 ≤ t3) ∧ (t4 < t3 → min t1 t2 ≤ t4)) :
    (Step15Pt.c04Val (pt.vChat mu e1 c) : ℤ) ≤
      4 * (pt.m0 : ℤ) + 4 * (pt.mbad : ℤ) - 4 * (pt.m2 : ℤ) - 4 * (pt.k3 : ℤ) -
      4 * (pt.mL0 d2 : ℤ) + 4 * (pt.muO d2 mu : ℤ) + 4 * (lam : ℤ) +
      4 * (pt.din d2 : ℤ) + 4 * (pt.d2oth d2 : ℤ) - 2 * (L0 : ℤ) - 2 * (LnoU : ℤ) := by
  have hd2_cases : d2 = 0 ∨ d2 = 1 := by omega
  set c04 : ℤ := (Step15Pt.c04Val (pt.vChat mu e1 c) : ℤ)
  have hc04_cases : (pt.vChat mu e1 c ≤ 0 ∧ c04 = 0) ∨
      (0 < pt.vChat mu e1 c ∧ c04 = ((pt.vChat mu e1 c + 3) / 4) * 4) := by
    by_cases hv : pt.vChat mu e1 c ≤ 0
    · exact Or.inl ⟨hv, c04Val_eq_zero hv⟩
    · exact Or.inr ⟨by omega, c04Val_eq_pos (by omega)⟩
  cases pt
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · rcases hd2_cases with rfl | rfl
      · by_cases ha : a1 = 0
        · subst ha; simp [Step15Pt.mVal, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
        · have htr := step15_htri_split (htri (Or.inl (by omega)))
          simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
          rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · rcases hd2_cases with rfl | rfl
      · by_cases ha : a1 = 0
        · subst ha; simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
        · have htr := step15_htri_split (htri (Or.inl (by omega)))
          simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
          rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · rcases hd2_cases with rfl | rfl
      · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) rfl; subst ha0
        by_cases hmu0 : mu = 0
        · have he := he1_k1U rfl (Or.inr hmu0); subst hmu0
          simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
        · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
            Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
            Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, show 1 ≤ mu by omega] at *
          first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
      · have he := he1_k1U rfl (Or.inl rfl)
        have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hd0 : d2 = 0 := hd2_zero (Or.inl rfl)
    subst hL0z; subst hd0
    have ⟨ho1, ho2⟩ := hode rfl
    have ⟨hkl0, hklp⟩ := hk2noU rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · by_cases hLn0 : LnoU = 0
      · subst hLn0; have hlm := hkl0 rfl
        simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
      · have hlm := hklp (by omega)
        simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · by_cases hLn0 : LnoU = 0
      · subst hLn0; have hlm := hkl0 rfl
        have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
      · have hlm := hklp (by omega)
        have htr := step15_htri_split (htri (Or.inr (Or.inr rfl)))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3,
          show 0 < LnoU by omega] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hL0z; subst hLnz
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · rcases hd2_cases with rfl | rfl
      · have ha0 : a1 = 0 := ha1_zero (Or.inl rfl) rfl; subst ha0
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inl rfl); have hlam1 := hk2U_mL rfl
    subst hL0z; subst hLnz; subst hmu0
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · rcases hd2_cases with rfl | rfl <;>
        (simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega)
    · rcases hd2_cases with rfl | rfl
      · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inl rfl)) rfl; subst ha0
        have he := he1_mL (Or.inl rfl) rfl
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hL0z : L0 = 0 := by by_contra h; rcases hL0 (by omega) with h' | h' | h' <;> cases h'
    have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inl rfl))
    subst hL0z; subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inl rfl))) rfl; subst ha0
    have hmu2 := hk2U_mb_mu rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    subst hLnz; have hlm := hk3U rfl
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · rcases hd2_cases with rfl | rfl <;>
        (simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega)
    · rcases hd2_cases with rfl | rfl
      · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl; subst ha0
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hmu0 : mu = 0 := hmu_mL (Or.inr rfl); have hlam3 := hk3U_mL rfl
    subst hLnz; subst hmu0
    have ⟨ho1, ho2⟩ := hode rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · rcases hd2_cases with rfl | rfl <;>
        (simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
          Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega)
    · rcases hd2_cases with rfl | rfl
      · have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) rfl; subst ha0
        have he := he1_mL (Or.inr rfl) rfl
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega
      · have htr := step15_htri_split (htri (Or.inr (Or.inl (by omega))))
        simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
          Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
          Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat, Step15Pt.vc0, Step15Pt.k1Min, Step15Pt.t3] at *
        rcases htr with h | h | h | h | h <;> first | (clear hSmod ho1 ho2; omega) | (clear hSmod; omega) | omega
  · have hLnz : LnoU = 0 := by by_contra h; exact Step15Pt.noConfusion (hLnoU (by omega))
    have hd0 : d2 = 0 := hd2_zero (Or.inr (Or.inr rfl))
    subst hLnz; subst hd0
    have ha0 : a1 = 0 := ha1_zero (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) rfl; subst ha0
    have hlm := hk3U_mb rfl
    have hmu3 := hk3U_mb_mu rfl
    rcases hc04_cases with ⟨_, hc0⟩ | ⟨hvpos, hceq⟩
    · simp [Step15Pt.m0, Step15Pt.mbad, Step15Pt.m2, Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML,
        Step15Pt.muO, Step15Pt.mu1, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth] at * ; omega
    · simp [Step15Pt.mVal, Step15Pt.nu, Step15Pt.m0, Step15Pt.mbad, Step15Pt.m1, Step15Pt.m2,
        Step15Pt.k3, Step15Pt.mL0, Step15Pt.isML, Step15Pt.din, Step15Pt.dmL, Step15Pt.d2oth,
        Step15Pt.mu1, Step15Pt.muO, Step15Pt.vChat] at * ; omega

/-! ### Part 4: Char-2 Hasse Leibniz rules, 4th-power Wronskian-ODE dichotomy, and `Z_ODE` (`ODE_fail`) -/

section Char2HasseExt

variable {E : Type*} [Field E] [CharP E 2]

lemma hasse_two_mul (p q : E[X]) :
    hasse 2 (p * q) = hasse 2 p * q + p.derivative * q.derivative + p * hasse 2 q := by
  induction p using Polynomial.induction_on' with
  | add p1 p2 hp1 hp2 =>
      simp only [add_mul, hasse_add, derivative_add, hp1, hp2]; ring
  | monomial a ca =>
      induction q using Polynomial.induction_on' with
      | add q1 q2 hq1 hq2 =>
          simp only [mul_add, hasse_add, derivative_add, hq1, hq2]; ring
      | monomial b cb =>
          ext n
          rw [monomial_mul_monomial, coeff_hasse, coeff_add, coeff_add, coeff_monomial]
          have hmon_h : ∀ (k d : ℕ) (c : E),
              hasse k (monomial d c) = monomial (d - k) ((Nat.choose d k : E) * c) := by
            intro k d c; ext m
            rw [coeff_hasse, coeff_monomial, coeff_monomial]
            by_cases hkd : k ≤ d
            · by_cases h : m = d - k
              · subst h; rw [Nat.sub_add_cancel hkd]; simp [mul_comm]
              · have : m + k ≠ d := by omega
                simp [Ne.symm h, Ne.symm this]
            · have hch : Nat.choose d k = 0 := Nat.choose_eq_zero_of_lt (by omega)
              have : m + k ≠ d := by omega
              simp [hch, Ne.symm this]
          rw [hmon_h 2 a ca, hmon_h 2 b cb, ← hasse_one_eq_derivative, ← hasse_one_eq_derivative,
            hmon_h 1 a ca, hmon_h 1 b cb, monomial_mul_monomial, monomial_mul_monomial,
            monomial_mul_monomial, coeff_monomial, coeff_monomial, coeff_monomial]
          simp only [Finsupp.single_apply]
          by_cases hnab : a + b = n + 2
          · have hch2 : Nat.choose (a + b) 2 = Nat.choose a 2 + a * b + Nat.choose b 2 := by
              rw [Nat.choose_two_right, Nat.choose_two_right, Nat.choose_two_right]
              have h2dvd : ∀ m : ℕ, 2 ∣ m * (m - 1) := fun m => by
                cases m with
                | zero => simp
                | succ k =>
                    simp only [Nat.add_sub_cancel]
                    rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
              obtain ⟨u, hu⟩ := h2dvd a
              obtain ⟨v, hv⟩ := h2dvd b
              obtain ⟨w, hw⟩ := h2dvd (a + b)
              have hlin : 2 * w = 2 * u + 2 * (a * b) + 2 * v := by
                rw [← hu, ← hv, ← hw]; cases a <;> cases b <;> simp <;> ring
              rw [hu, hv, hw, Nat.mul_div_right _ (by norm_num), Nat.mul_div_right _ (by norm_num),
                Nat.mul_div_right _ (by norm_num)]
              omega
            have hcast : ((Nat.choose (a + b) 2 : ℕ) : E) =
                (Nat.choose a 2 : E) + (a : E) * (b : E) + (Nat.choose b 2 : E) := by
              rw [hch2]; push_cast; ring
            rw [← hnab, hcast]; simp only [↓reduceIte]
            have hA : (if a - 2 + b = n then (Nat.choose a 2 : E) * ca * cb else 0) =
                (Nat.choose a 2 : E) * ca * cb := by
              by_cases ha2 : 2 ≤ a
              · simp [show a - 2 + b = n by omega]
              · have : Nat.choose a 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
                simp [this]
            have hB : (if a - 1 + (b - 1) = n then (Nat.choose a 1 : E) * ca * ((Nat.choose b 1 : E) * cb) else 0) =
                (a : E) * (b : E) * (ca * cb) := by
              by_cases hab1 : 1 ≤ a ∧ 1 ≤ b
              · simp only [show a - 1 + (b - 1) = n by omega, ↓reduceIte, Nat.choose_one_right]; ring
              · rcases not_and_or.mp hab1 with ha0 | hb0
                · have ha' : a = 0 := by omega
                  subst ha'; simp
                · have hb' : b = 0 := by omega
                  subst hb'; simp
            have hC : (if a + (b - 2) = n then ca * ((Nat.choose b 2 : E) * cb) else 0) =
                (Nat.choose b 2 : E) * (ca * cb) := by
              by_cases hb2 : 2 ≤ b
              · simp only [show a + (b - 2) = n by omega, ↓reduceIte]; ring
              · have : Nat.choose b 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
                simp [this]
            rw [hA, hB, hC]; ring
          · simp only [hnab, ↓reduceIte, mul_zero]
            have hA : (if a - 2 + b = n then (Nat.choose a 2 : E) * ca * cb else 0) = 0 := by
              by_cases ha2 : 2 ≤ a
              · simp [show a - 2 + b ≠ n by omega]
              · have : Nat.choose a 2 = 0 := Nat.choose_eq_zero_of_lt (by omega); simp [this]
            have hB : (if a - 1 + (b - 1) = n then (Nat.choose a 1 : E) * ca * ((Nat.choose b 1 : E) * cb) else 0) = 0 := by
              by_cases hab1 : 1 ≤ a ∧ 1 ≤ b
              · simp [show a - 1 + (b - 1) ≠ n by omega]
              · rcases not_and_or.mp hab1 with ha0 | hb0
                · have ha' : a = 0 := by omega
                  subst ha'; simp
                · have hb' : b = 0 := by omega
                  subst hb'; simp
            have hC : (if a + (b - 2) = n then ca * ((Nat.choose b 2 : E) * cb) else 0) = 0 := by
              by_cases hb2 : 2 ≤ b
              · simp [show a + (b - 2) ≠ n by omega]
              · have : Nat.choose b 2 = 0 := Nat.choose_eq_zero_of_lt (by omega); simp [this]
            rw [hA, hB, hC, add_zero, add_zero]

lemma char2_add_self (p : E[X]) : p + p = 0 := by
  ext n; simp [CharTwo.add_self_eq_zero]

lemma char2_derivative_sq (p : E[X]) : (p ^ 2).derivative = 0 := by
  rw [sq, derivative_mul, mul_comm p.derivative p, char2_add_self]

lemma char2_derivative_pow_four (p : E[X]) : (p ^ 4).derivative = 0 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, char2_derivative_sq]

lemma char2_hasse_two_sq (p : E[X]) : hasse 2 (p ^ 2) = p.derivative ^ 2 := by
  rw [sq, hasse_two_mul]
  calc hasse 2 p * p + p.derivative * p.derivative + p * hasse 2 p
      = (p * hasse 2 p + p * hasse 2 p) + p.derivative ^ 2 := by ring
    _ = p.derivative ^ 2 := by rw [char2_add_self, zero_add]

lemma char2_hasse_two_pow_four (p : E[X]) : hasse 2 (p ^ 4) = 0 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, char2_hasse_two_sq, char2_derivative_sq, zero_pow (by norm_num)]

lemma char2_hasse_two_cube (p : E[X]) :
    hasse 2 (p ^ 3) = p * p.derivative ^ 2 + p ^ 2 * hasse 2 p := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one, hasse_two_mul, char2_hasse_two_sq,
    char2_derivative_sq, zero_mul, add_zero, mul_comm (p.derivative ^ 2) p]

lemma char2_derivative_cube (p : E[X]) : (p ^ 3).derivative = p ^ 2 * p.derivative := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_add, pow_one, derivative_mul, char2_derivative_sq,
    zero_mul, zero_add]

lemma char2_add_pow_four (p q : E[X]) : (p + q) ^ 4 = p ^ 4 + q ^ 4 := by
  have h2 : ∀ a b : E[X], (a + b) ^ 2 = a ^ 2 + b ^ 2 := fun a b => by
    calc (a + b) ^ 2 = a ^ 2 + (a * b + a * b) + b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [char2_add_self, add_zero]
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2, h2, ← pow_mul, ← pow_mul]

lemma natDegree_hasse_le (k : ℕ) (p : E[X]) : (hasse k p).natDegree ≤ p.natDegree - k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_hasse, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

private lemma coeff_finset_sum_ext {ι : Type*} (s : Finset ι) (f : ι → E[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  simp

/-- **Exact char-2 polynomial ODE decomposition (`A₀⁴ + (c₀ X + c₁ X²) A₁⁴`):**
Over any char-2 field `E` with 4th roots (e.g. any finite field or algebraically closed field),
every solution `R` of `c₀ R^{[2]} + c₁ R^{[1]} = 0` (`c₀ ≠ 0`) decomposes as
`R = fA^4 + (C c0 * X + C c1 * X^2) * fB^4`! -/
theorem char2_poly_ode_decomp {c0 c1 : E} (hc0 : c0 ≠ 0)
    (hpow4 : ∀ a : E, ∃ b : E, b ^ 4 = a) {R : E[X]}
    (hode : C c0 * hasse 2 R + C c1 * hasse 1 R = 0) :
    ∃ fA fB : E[X], R = fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4 := by
  classical
  obtain ⟨h3, h2⟩ := char2_poly_ode_coeffs hc0 hode
  let rt4 : E → E := fun a => Classical.choose (hpow4 a)
  have hrt4 : ∀ a : E, (rt4 a) ^ 4 = a := fun a => Classical.choose_spec (hpow4 a)
  let N := R.natDegree / 4 + 1
  let fA : E[X] := ∑ k ∈ Finset.range N, monomial k (rt4 (R.coeff (4 * k)))
  let fB : E[X] := ∑ k ∈ Finset.range N, monomial k (rt4 (c0⁻¹ * R.coeff (4 * k + 1)))
  have hpow4_sum : ∀ (s : Finset ℕ) (g : ℕ → E),
      (∑ k ∈ s, monomial k (g k)) ^ 4 = ∑ k ∈ s, monomial (4 * k) ((g k) ^ 4) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, char2_add_pow_four, ih, Finset.sum_insert ha, monomial_pow, mul_comm a 4]
  have hfA4 : fA ^ 4 = ∑ k ∈ Finset.range N, monomial (4 * k) (R.coeff (4 * k)) := by
    dsimp only [fA]; rw [hpow4_sum]
    apply Finset.sum_congr rfl; intro k _; rw [hrt4]
  have hfB4 : fB ^ 4 = ∑ k ∈ Finset.range N, monomial (4 * k) (c0⁻¹ * R.coeff (4 * k + 1)) := by
    dsimp only [fB]; rw [hpow4_sum]
    apply Finset.sum_congr rfl; intro k _; rw [hrt4]
  refine ⟨fA, fB, ?_⟩
  ext n
  rw [coeff_add, hfA4, hfB4, add_mul, coeff_add, Finset.mul_sum, Finset.mul_sum,
    coeff_finset_sum_ext, coeff_finset_sum_ext, coeff_finset_sum_ext]
  have hterm1 : ∀ k, (C c0 * X * monomial (4 * k) (c0⁻¹ * R.coeff (4 * k + 1))) =
      monomial (4 * k + 1) (R.coeff (4 * k + 1)) := fun k => by
    rw [mul_assoc, X_mul_monomial, C_mul_monomial, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hterm2 : ∀ k, (C c1 * X ^ 2 * monomial (4 * k) (c0⁻¹ * R.coeff (4 * k + 1))) =
      monomial (4 * k + 2) (R.coeff (4 * k + 2)) := fun k => by
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    have hcoeff : c1 * (c0⁻¹ * R.coeff (4 * k + 1)) = R.coeff (4 * k + 2) := by
      have := h2 k
      calc c1 * (c0⁻¹ * R.coeff (4 * k + 1)) = c0⁻¹ * (c1 * R.coeff (4 * k + 1)) := by ring
        _ = c0⁻¹ * (c0 * R.coeff (4 * k + 2)) := by rw [← this]
        _ = (c0⁻¹ * c0) * R.coeff (4 * k + 2) := by ring
        _ = R.coeff (4 * k + 2) := by rw [inv_mul_cancel₀ hc0, one_mul]
    rw [← hcoeff]; simp only [map_mul, pow_add]; ring
  simp_rw [hterm1, hterm2, coeff_monomial, Finsupp.single_apply]
  have hsum_eq : ∀ (r : ℕ) (hr : r < 4),
      (∑ k ∈ Finset.range N, if 4 * k + r = n then R.coeff (4 * k + r) else 0) =
        if n % 4 = r then R.coeff n else 0 := by
    intro r hr
    by_cases hmod : n % 4 = r
    · rw [if_pos hmod]
      by_cases hk : n / 4 < N
      · rw [Finset.sum_eq_single (n / 4)]
        · have heq : 4 * (n / 4) + r = n := by omega
          simp [heq]
        · intro k _ hne; rw [if_neg (by omega)]
        · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
      · have hgt : R.natDegree < n := by dsimp [N] at hk; omega
        rw [coeff_eq_zero_of_natDegree_lt hgt]
        apply Finset.sum_eq_zero; intro k hk'
        have hklt := Finset.mem_range.mp hk'
        rw [if_neg (by omega)]
    · rw [if_neg hmod]
      apply Finset.sum_eq_zero; intro k _
      rw [if_neg (by omega)]
  have h0 := hsum_eq 0 (by omega)
  simp only [add_zero] at h0
  rw [h0, hsum_eq 1 (by omega), hsum_eq 2 (by omega)]
  have hlt4 : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  set q := n / 4
  set rem := n % 4
  have hn : n = 4 * q + rem := by omega
  interval_cases rem
  · simp
  · simp
  · simp
  · simp; rw [hn]; exact h3 q

/-- **Exact char-2 4th-power rational Wronskian-ODE identity:**
If `N_dom = C c0 * X + C c1 * X^2 + L^4` and `P * C0^4 = Q * (fA^4 + (C c0 * X + C c1 * X^2) * fB^4)`,
then `(N_dom * (P' * Q + P * Q') + C c0 * P * Q) * C0^4 = C c0 * Q^2 * (fA + L * fB)^4`! -/
theorem char2_wronskian_ode_fourth_pow {c0 c1 : E} {N_dom L P Q C0 fA fB : E[X]}
    (hNdom : N_dom = C c0 * X + C c1 * X ^ 2 + L ^ 4)
    (hPQ : P * C0 ^ 4 = Q * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4)) :
    (N_dom * (P.derivative * Q + P * Q.derivative) + C c0 * P * Q) * C0 ^ 4 =
      C c0 * Q ^ 2 * (fA + L * fB) ^ 4 := by
  have hd_lin : (C c0 * X + C c1 * X ^ 2 : E[X]).derivative = C c0 := by
    rw [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      derivative_mul, derivative_C, zero_mul, zero_add, char2_derivative_sq, mul_zero, add_zero]
  have hdiff := congrArg Polynomial.derivative hPQ
  rw [derivative_mul, char2_derivative_pow_four, mul_zero, add_zero,
    derivative_mul, derivative_add, char2_derivative_pow_four, zero_add,
    derivative_mul, hd_lin, char2_derivative_pow_four, mul_zero, add_zero] at hdiff
  have hwr : (P.derivative * Q + P * Q.derivative) * C0 ^ 4 = C c0 * Q ^ 2 * fB ^ 4 := by
    calc (P.derivative * Q + P * Q.derivative) * C0 ^ 4
        = (P.derivative * C0 ^ 4) * Q + (P * C0 ^ 4) * Q.derivative := by ring
      _ = (Q.derivative * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4) + Q * (C c0 * fB ^ 4)) * Q +
            (Q * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4)) * Q.derivative := by rw [hdiff, hPQ]
      _ = (Q * Q.derivative * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4) +
            Q * Q.derivative * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4)) +
            C c0 * Q ^ 2 * fB ^ 4 := by ring
      _ = C c0 * Q ^ 2 * fB ^ 4 := by rw [char2_add_self, zero_add]
  calc (N_dom * (P.derivative * Q + P * Q.derivative) + C c0 * P * Q) * C0 ^ 4
      = N_dom * ((P.derivative * Q + P * Q.derivative) * C0 ^ 4) + C c0 * Q * (P * C0 ^ 4) := by ring
    _ = (C c0 * X + C c1 * X ^ 2 + L ^ 4) * (C c0 * Q ^ 2 * fB ^ 4) +
          C c0 * Q * (Q * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4)) := by rw [hwr, hNdom, hPQ]
    _ = ((C c0 * X + C c1 * X ^ 2) * (C c0 * Q ^ 2 * fB ^ 4) +
          (C c0 * X + C c1 * X ^ 2) * (C c0 * Q ^ 2 * fB ^ 4)) +
          C c0 * Q ^ 2 * (fA ^ 4 + (L * fB) ^ 4) := by rw [mul_pow]; ring
    _ = C c0 * Q ^ 2 * (fA + L * fB) ^ 4 := by rw [char2_add_self, zero_add, char2_add_pow_four]

/-- **Exact `W2a1 ∨ W2a2` degree dichotomy for `ODE_holds_W2a`:**
If `fB ≠ 0`, `C0 ≠ 0`, `Q ≠ 0`, `1 ≤ L.natDegree`, and
`P * C0^4 = Q * (fA^4 + (C c0 * X + C c1 * X^2) * fB^4)`, then EITHER:
- (`W2a1`): `fA + L * fB ≠ 0 ∧ 4 * L.natDegree ≤ 4 * (fA + L * fB).natDegree`, OR
- (`W2a2`): `4 * L.natDegree + Q.natDegree ≤ 4 * C0.natDegree + P.natDegree`! -/
theorem char2_wronskian_ode_W2a_dichotomy {c0 c1 : E}
    {L P Q C0 fA fB : E[X]} (hL : 1 ≤ L.natDegree) (hfB : fB ≠ 0) (hC0 : C0 ≠ 0) (hQ : Q ≠ 0)
    (hPQ : P * C0 ^ 4 = Q * (fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4)) :
    (fA + L * fB ≠ 0 ∧ 4 * L.natDegree ≤ 4 * (fA + L * fB).natDegree) ∨
    4 * L.natDegree + Q.natDegree ≤ 4 * C0.natDegree + P.natDegree := by
  by_cases hlt : fA.natDegree < L.natDegree
  · left
    have hLne : L ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hL; omega
    have hLfB_deg : (L * fB).natDegree = L.natDegree + fB.natDegree := natDegree_mul hLne hfB
    have hdeg_add : (fA + L * fB).natDegree = (L * fB).natDegree :=
      natDegree_add_eq_right_of_natDegree_lt (by omega)
    have hne : fA + L * fB ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hdeg_add; omega
    exact ⟨hne, by omega⟩
  · right
    have hfA_ge : L.natDegree ≤ fA.natDegree := by omega
    have hfA_ne : fA ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hfA_ge; omega
    set R := fA ^ 4 + (C c0 * X + C c1 * X ^ 2) * fB ^ 4
    have hcoeff_B : (((C c0 * X + C c1 * X ^ 2) * fB ^ 4).coeff (4 * fA.natDegree)) = 0 := by
      have hpow4_sum : ∀ (s : Finset ℕ) (g : ℕ → E),
          (∑ k ∈ s, monomial k (g k)) ^ 4 = ∑ k ∈ s, monomial (4 * k) ((g k) ^ 4) := by
        intro s g
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, char2_add_pow_four, ih, Finset.sum_insert ha, monomial_pow, mul_comm a 4]
      have hfB4_zero : ∀ m, m % 4 ≠ 0 → (fB ^ 4).coeff m = 0 := by
        intro m hm
        have hdecomp : fB ^ 4 = ∑ k ∈ fB.support, monomial (4 * k) ((fB.coeff k) ^ 4) := by
          conv_lhs => rw [fB.as_sum_support]
          exact hpow4_sum fB.support (fun k => fB.coeff k)
        rw [hdecomp, coeff_finset_sum_ext]
        apply Finset.sum_eq_zero; intro k _
        simp [coeff_monomial, Finsupp.single_apply, show 4 * k ≠ m by omega]
      rw [add_mul, coeff_add, mul_assoc, coeff_C_mul, mul_assoc, coeff_C_mul]
      have h1 : (X * fB ^ 4).coeff (4 * fA.natDegree) = 0 := by
        have hpos : 0 < 4 * fA.natDegree := by omega
        rw [show 4 * fA.natDegree = (4 * fA.natDegree - 1) + 1 by omega, coeff_X_mul]
        exact hfB4_zero _ (by omega)
      have h2 : (X ^ 2 * fB ^ 4).coeff (4 * fA.natDegree) = 0 := by
        have hge2 : 2 ≤ 4 * fA.natDegree := by omega
        rw [show 4 * fA.natDegree = (4 * fA.natDegree - 2) + 2 by omega, coeff_X_pow_mul]
        exact hfB4_zero _ (by omega)
      rw [h1, h2, mul_zero, mul_zero, add_zero]
    have hcoeff_A : (fA ^ 4).coeff (4 * fA.natDegree) ≠ 0 := by
      have hdeg4 : (fA ^ 4).natDegree = 4 * fA.natDegree := natDegree_pow fA 4
      rw [← hdeg4]; exact leadingCoeff_ne_zero.mpr (pow_ne_zero 4 hfA_ne)
    have hcoeff_R : R.coeff (4 * fA.natDegree) ≠ 0 := by
      dsimp only [R]; rw [coeff_add, hcoeff_B, add_zero]; exact hcoeff_A
    have hRne : R ≠ 0 := fun h0 => hcoeff_R (by rw [h0, coeff_zero])
    have hRdeg : 4 * fA.natDegree ≤ R.natDegree := le_natDegree_of_ne_zero hcoeff_R
    have hPne : P ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hPQ; exact mul_ne_zero hQ hRne hPQ.symm
    have hC04_ne : C0 ^ 4 ≠ 0 := pow_ne_zero 4 hC0
    have hC04_deg : (C0 ^ 4).natDegree = 4 * C0.natDegree := natDegree_pow C0 4
    have hdeg_eq := congrArg Polynomial.natDegree hPQ
    rw [natDegree_mul hPne hC04_ne, natDegree_mul hQ hRne, hC04_deg] at hdeg_eq
    omega

/-- Raw Hasse 2nd-derivative ODE numerator `Z_raw = Q^3 (c₀ (P/Q)^[2] + c₁ (P/Q)^[1])`. -/
noncomputable def zRaw (c0 c1 : E) (P Q : E[X]) : E[X] :=
  C c0 * (hasse 2 P * Q ^ 2 + P.derivative * Q.derivative * Q +
          P * Q.derivative ^ 2 + P * hasse 2 Q * Q) +
  C c1 * (P.derivative * Q + P * Q.derivative) * Q

lemma zRaw_add_left (c0 c1 : E) (P1 P2 Q : E[X]) :
    zRaw c0 c1 (P1 + P2) Q = zRaw c0 c1 P1 Q + zRaw c0 c1 P2 Q := by
  unfold zRaw; rw [hasse_add, derivative_add]; ring

lemma zRaw_mul_pow_four_left (c0 c1 : E) (A P Q : E[X]) :
    zRaw c0 c1 (A ^ 4 * P) Q = A ^ 4 * zRaw c0 c1 P Q := by
  unfold zRaw
  rw [hasse_two_mul, char2_hasse_two_pow_four, char2_derivative_pow_four,
    derivative_mul, char2_derivative_pow_four]
  ring

lemma zRaw_mul_common (c0 c1 : E) (P Q N : E[X]) :
    zRaw c0 c1 (P * N) (Q * N) = N ^ 3 * zRaw c0 c1 P Q := by
  unfold zRaw
  rw [hasse_two_mul P N, hasse_two_mul Q N, derivative_mul, derivative_mul]
  have h1 : (hasse 2 P * N + P.derivative * N.derivative + P * hasse 2 N) * (Q * N) ^ 2 +
      (P.derivative * N + P * N.derivative) * (Q.derivative * N + Q * N.derivative) * (Q * N) +
      P * N * (Q.derivative * N + Q * N.derivative) ^ 2 +
      P * N * (hasse 2 Q * N + Q.derivative * N.derivative + Q * hasse 2 N) * (Q * N) =
      N ^ 3 * (hasse 2 P * Q ^ 2 + P.derivative * Q.derivative * Q + P * Q.derivative ^ 2 + P * hasse 2 Q * Q) := by
    have hsq : (Q.derivative * N + Q * N.derivative) ^ 2 = Q.derivative ^ 2 * N ^ 2 + Q ^ 2 * N.derivative ^ 2 := by
      calc (Q.derivative * N + Q * N.derivative) ^ 2
          = Q.derivative ^ 2 * N ^ 2 + (Q.derivative * N * (Q * N.derivative) + Q.derivative * N * (Q * N.derivative)) +
              Q ^ 2 * N.derivative ^ 2 := by ring
        _ = Q.derivative ^ 2 * N ^ 2 + Q ^ 2 * N.derivative ^ 2 := by rw [char2_add_self, add_zero]
    rw [hsq]
    have hc3 : P * Q ^ 2 * N ^ 2 * hasse 2 N + P * Q ^ 2 * N ^ 2 * hasse 2 N = 0 := char2_add_self _
    have hc4 : P * Q.derivative * Q * N ^ 2 * N.derivative + P * Q.derivative * Q * N ^ 2 * N.derivative = 0 := char2_add_self _
    have hc5 : P * Q ^ 2 * N * N.derivative ^ 2 + P * Q ^ 2 * N * N.derivative ^ 2 = 0 := char2_add_self _
    have hc6 : P.derivative * Q ^ 2 * N ^ 2 * N.derivative + P.derivative * Q ^ 2 * N ^ 2 * N.derivative = 0 := char2_add_self _
    calc (hasse 2 P * N + P.derivative * N.derivative + P * hasse 2 N) * (Q * N) ^ 2 +
          (P.derivative * N + P * N.derivative) * (Q.derivative * N + Q * N.derivative) * (Q * N) +
          P * N * (Q.derivative ^ 2 * N ^ 2 + Q ^ 2 * N.derivative ^ 2) +
          P * N * (hasse 2 Q * N + Q.derivative * N.derivative + Q * hasse 2 N) * (Q * N)
        = N ^ 3 * (hasse 2 P * Q ^ 2 + P.derivative * Q.derivative * Q + P * Q.derivative ^ 2 + P * hasse 2 Q * Q) +
          (P.derivative * Q ^ 2 * N ^ 2 * N.derivative + P.derivative * Q ^ 2 * N ^ 2 * N.derivative) +
          (P * Q.derivative * Q * N ^ 2 * N.derivative + P * Q.derivative * Q * N ^ 2 * N.derivative) +
          (P * Q ^ 2 * N * N.derivative ^ 2 + P * Q ^ 2 * N * N.derivative ^ 2) +
          (P * Q ^ 2 * N ^ 2 * hasse 2 N + P * Q ^ 2 * N ^ 2 * hasse 2 N) := by ring
      _ = N ^ 3 * (hasse 2 P * Q ^ 2 + P.derivative * Q.derivative * Q + P * Q.derivative ^ 2 + P * hasse 2 Q * Q) := by
          rw [hc6, hc4, hc5, hc3]; simp
  have h2 : ((P.derivative * N + P * N.derivative) * (Q * N) + P * N * (Q.derivative * N + Q * N.derivative)) * (Q * N) =
      N ^ 3 * ((P.derivative * Q + P * Q.derivative) * Q) := by
    have hc : P * Q * N * N.derivative + P * Q * N * N.derivative = 0 := char2_add_self _
    calc ((P.derivative * N + P * N.derivative) * (Q * N) + P * N * (Q.derivative * N + Q * N.derivative)) * (Q * N)
        = N ^ 3 * ((P.derivative * Q + P * Q.derivative) * Q) +
          (P * Q * N * N.derivative + P * Q * N * N.derivative) * (Q * N) := by ring
      _ = N ^ 3 * ((P.derivative * Q + P * Q.derivative) * Q) := by rw [hc, zero_mul, add_zero]
  rw [h1, mul_assoc (C c1), h2]; ring

/-- If `zRaw c0 c1 P Q = 0` and `P * C0^4 = Q * R` (`Q ≠ 0`), then `C c0 * hasse 2 R + C c1 * hasse 1 R = 0`! -/
theorem zRaw_eq_zero_imp_poly_ode {c0 c1 : E} {P Q C0 R : E[X]}
    (hQ : Q ≠ 0) (hz : zRaw c0 c1 P Q = 0) (hPQ : P * C0 ^ 4 = Q * R) :
    C c0 * hasse 2 R + C c1 * hasse 1 R = 0 := by
  have h1 : zRaw c0 c1 (Q * R) Q = 0 := by
    rw [← hPQ, mul_comm P (C0 ^ 4), zRaw_mul_pow_four_left, hz, mul_zero]
  have h2 : zRaw c0 c1 (Q * R) Q = Q ^ 3 * (C c0 * hasse 2 R + C c1 * hasse 1 R) := by
    have hz1 := zRaw_mul_common c0 c1 R 1 Q
    rw [mul_comm R Q, one_mul] at hz1
    have hhasse2_one : hasse 2 (1 : E[X]) = 0 := by
      ext n; simp only [coeff_hasse, coeff_one, coeff_zero]
      have hne : n + 2 ≠ 0 := by omega
      simp [hne]
    have hzr : zRaw c0 c1 R 1 = C c0 * hasse 2 R + C c1 * hasse 1 R := by
      unfold zRaw
      rw [hasse_one_eq_derivative, derivative_one, hhasse2_one]
      ring
    rw [hz1, hzr]
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 3 hQ)

/-- `zRaw c0 c1 (Q0^4) (N_dom^3) = 0` whenever `N_dom' = C c0` and `hasse 2 N_dom = C c1`! -/
lemma zRaw_pow_four_Ndom_cube_eq_zero {c0 c1 : E} (Q0 N_dom : E[X])
    (hd1 : N_dom.derivative = C c0) (hd2 : hasse 2 N_dom = C c1) :
    zRaw c0 c1 (Q0 ^ 4) (N_dom ^ 3) = 0 := by
  unfold zRaw
  rw [char2_hasse_two_pow_four, char2_derivative_pow_four, char2_derivative_cube,
    char2_hasse_two_cube, hd1, hd2]
  have h1 : C c0 ^ 3 * Q0 ^ 4 * N_dom ^ 4 + C c0 ^ 3 * Q0 ^ 4 * N_dom ^ 4 = 0 := char2_add_self _
  have h2 : C c0 * C c1 * Q0 ^ 4 * N_dom ^ 5 + C c0 * C c1 * Q0 ^ 4 * N_dom ^ 5 = 0 := char2_add_self _
  calc C c0 * (0 * (N_dom ^ 3) ^ 2 + 0 * (N_dom ^ 2 * C c0) * N_dom ^ 3 +
          Q0 ^ 4 * (N_dom ^ 2 * C c0) ^ 2 + Q0 ^ 4 * (N_dom * C c0 ^ 2 + N_dom ^ 2 * C c1) * N_dom ^ 3) +
        C c1 * (0 * N_dom ^ 3 + Q0 ^ 4 * (N_dom ^ 2 * C c0)) * N_dom ^ 3
      = (C c0 ^ 3 * Q0 ^ 4 * N_dom ^ 4 + C c0 ^ 3 * Q0 ^ 4 * N_dom ^ 4) +
        (C c0 * C c1 * Q0 ^ 4 * N_dom ^ 5 + C c0 * C c1 * Q0 ^ 4 * N_dom ^ 5) := by ring
    _ = 0 := by rw [h1, h2, add_zero]

/-- **Exact `ODE_fail` master polynomial identity:**
If `P * N_dom^3 + A1^4 * R0 = Q * Q0^4` with `N_dom' = C c0`, `hasse 2 N_dom = C c1`, then
`N_dom^9 * zRaw c0 c1 P Q = A1^4 * zRaw c0 c1 R0 (Q * N_dom^3)`! -/
theorem zRaw_ode_fail_identity {c0 c1 : E} {P Q N_dom A1 R0 Q0 : E[X]}
    (hd1 : N_dom.derivative = C c0) (hd2 : hasse 2 N_dom = C c1)
    (heq : P * N_dom ^ 3 + A1 ^ 4 * R0 = Q * Q0 ^ 4) :
    N_dom ^ 9 * zRaw c0 c1 P Q = A1 ^ 4 * zRaw c0 c1 R0 (Q * N_dom ^ 3) := by
  have hPN : P * N_dom ^ 3 = Q * Q0 ^ 4 + A1 ^ 4 * R0 := by
    have hadd := congrArg (· + A1 ^ 4 * R0) heq
    rw [add_assoc, char2_add_self, add_zero] at hadd
    exact hadd
  calc N_dom ^ 9 * zRaw c0 c1 P Q
      = (N_dom ^ 3) ^ 3 * zRaw c0 c1 P Q := by ring
    _ = zRaw c0 c1 (P * N_dom ^ 3) (Q * N_dom ^ 3) := (zRaw_mul_common c0 c1 P Q (N_dom ^ 3)).symm
    _ = zRaw c0 c1 (Q * Q0 ^ 4 + A1 ^ 4 * R0) (Q * N_dom ^ 3) := by rw [hPN]
    _ = zRaw c0 c1 (Q0 ^ 4 * Q) (N_dom ^ 3 * Q) + zRaw c0 c1 (A1 ^ 4 * R0) (Q * N_dom ^ 3) := by
          rw [zRaw_add_left, mul_comm Q (Q0 ^ 4), mul_comm Q (N_dom ^ 3)]
    _ = Q ^ 3 * zRaw c0 c1 (Q0 ^ 4) (N_dom ^ 3) + A1 ^ 4 * zRaw c0 c1 R0 (Q * N_dom ^ 3) := by
          rw [zRaw_mul_common, zRaw_mul_pow_four_left]
    _ = A1 ^ 4 * zRaw c0 c1 R0 (Q * N_dom ^ 3) := by
          rw [zRaw_pow_four_Ndom_cube_eq_zero Q0 N_dom hd1 hd2, mul_zero, zero_add]

/-- **Exact `M0^5 * N1^2` divisibility of `zRaw c0 c1 P (M0^3 * N1^2 * g4)` in char 2!** -/
theorem pow5_mul_sq_dvd_zRaw (c0 c1 : E) (P M0 N1 g4 : E[X]) :
    M0 ^ 5 * N1 ^ 2 ∣ zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) := by
  set R := N1 ^ 2 * g4
  have hQ : M0 ^ 3 * N1 ^ 2 * g4 = M0 ^ 3 * R := by dsimp [R]; ring
  have hR_dvd : N1 ^ 2 ∣ R := dvd_mul_right _ _
  have hR'_dvd : N1 ^ 2 ∣ R.derivative := by
    dsimp [R]; rw [derivative_mul, char2_derivative_sq, zero_mul, zero_add]; exact dvd_mul_right _ _
  have hQ' : (M0 ^ 3 * R).derivative = M0 ^ 2 * (M0.derivative * R + M0 * R.derivative) := by
    rw [derivative_mul, char2_derivative_cube]; ring
  have hQ2_plus : (M0 ^ 3 * R).derivative ^ 2 + hasse 2 (M0 ^ 3 * R) * (M0 ^ 3 * R) =
      M0 ^ 5 * (M0 * R.derivative ^ 2 + hasse 2 M0 * R ^ 2 + M0.derivative * R.derivative * R + M0 * hasse 2 R * R) := by
    rw [hQ', mul_pow, hasse_two_mul, char2_hasse_two_cube, char2_derivative_cube]
    have hsq : (M0.derivative * R + M0 * R.derivative) ^ 2 = M0.derivative ^ 2 * R ^ 2 + M0 ^ 2 * R.derivative ^ 2 := by
      calc (M0.derivative * R + M0 * R.derivative) ^ 2
          = M0.derivative ^ 2 * R ^ 2 + (M0.derivative * R * (M0 * R.derivative) + M0.derivative * R * (M0 * R.derivative)) +
              M0 ^ 2 * R.derivative ^ 2 := by ring
        _ = M0.derivative ^ 2 * R ^ 2 + M0 ^ 2 * R.derivative ^ 2 := by rw [char2_add_self, add_zero]
    rw [hsq]
    have hc : M0 ^ 4 * M0.derivative ^ 2 * R ^ 2 + M0 ^ 4 * M0.derivative ^ 2 * R ^ 2 = 0 := char2_add_self _
    calc (M0 ^ 2) ^ 2 * (M0.derivative ^ 2 * R ^ 2 + M0 ^ 2 * R.derivative ^ 2) +
          ((M0 * M0.derivative ^ 2 + M0 ^ 2 * hasse 2 M0) * R +
           M0 ^ 2 * M0.derivative * R.derivative + M0 ^ 3 * hasse 2 R) * (M0 ^ 3 * R)
        = (M0 ^ 4 * M0.derivative ^ 2 * R ^ 2 + M0 ^ 4 * M0.derivative ^ 2 * R ^ 2) +
          M0 ^ 5 * (M0 * R.derivative ^ 2 + hasse 2 M0 * R ^ 2 + M0.derivative * R.derivative * R + M0 * hasse 2 R * R) := by ring
      _ = M0 ^ 5 * (M0 * R.derivative ^ 2 + hasse 2 M0 * R ^ 2 + M0.derivative * R.derivative * R + M0 * hasse 2 R * R) := by
          rw [hc, zero_add]
  have hdvd_Rterm : N1 ^ 2 ∣ (M0 * R.derivative ^ 2 + hasse 2 M0 * R ^ 2 +
      M0.derivative * R.derivative * R + M0 * hasse 2 R * R) := by
    apply dvd_add
    · apply dvd_add
      · apply dvd_add
        · exact dvd_mul_of_dvd_right (dvd_pow hR'_dvd (by norm_num)) _
        · exact dvd_mul_of_dvd_right (dvd_pow hR_dvd (by norm_num)) _
      · exact dvd_mul_of_dvd_right hR_dvd _
    · exact dvd_mul_of_dvd_right hR_dvd _
  rw [hQ]; unfold zRaw
  have hrew : C c0 * (hasse 2 P * (M0 ^ 3 * R) ^ 2 + P.derivative * (M0 ^ 3 * R).derivative * (M0 ^ 3 * R) +
        P * (M0 ^ 3 * R).derivative ^ 2 + P * hasse 2 (M0 ^ 3 * R) * (M0 ^ 3 * R)) +
      C c1 * (P.derivative * (M0 ^ 3 * R) + P * (M0 ^ 3 * R).derivative) * (M0 ^ 3 * R) =
      C c0 * (hasse 2 P * (M0 ^ 3 * R) ^ 2 + P.derivative * (M0 ^ 3 * R).derivative * (M0 ^ 3 * R) +
        P * ((M0 ^ 3 * R).derivative ^ 2 + hasse 2 (M0 ^ 3 * R) * (M0 ^ 3 * R))) +
      C c1 * (P.derivative * (M0 ^ 3 * R) ^ 2 + P * (M0 ^ 3 * R).derivative * (M0 ^ 3 * R)) := by ring
  rw [hrew, hQ2_plus, hQ']
  have hM5N2_Q2 : M0 ^ 5 * N1 ^ 2 ∣ (M0 ^ 3 * R) ^ 2 := by
    rw [mul_pow]; exact mul_dvd_mul ⟨M0, by ring⟩ (dvd_pow hR_dvd (by norm_num))
  have hM5N2_Q'Q : M0 ^ 5 * N1 ^ 2 ∣ M0 ^ 2 * (M0.derivative * R + M0 * R.derivative) * (M0 ^ 3 * R) := by
    have hEq : M0 ^ 2 * (M0.derivative * R + M0 * R.derivative) * (M0 ^ 3 * R) =
        M0 ^ 5 * R * (M0.derivative * R + M0 * R.derivative) := by ring
    rw [hEq]
    exact dvd_mul_of_dvd_left (mul_dvd_mul dvd_rfl hR_dvd) _
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_right hM5N2_Q2 _
      · rw [mul_assoc]; exact dvd_mul_of_dvd_right hM5N2_Q'Q _
    · exact dvd_mul_of_dvd_right (mul_dvd_mul dvd_rfl hdvd_Rterm) _
  · apply dvd_mul_of_dvd_right
    apply dvd_add
    · exact dvd_mul_of_dvd_right hM5N2_Q2 _
    · rw [mul_assoc]; exact dvd_mul_of_dvd_right hM5N2_Q'Q _

/-- Corollary: `M0^4 * N1^2 ∣ zRaw c0 c1 P (M0^3 * N1^2 * g4)`. -/
theorem pow4_mul_sq_dvd_zRaw (c0 c1 : E) (P M0 N1 g4 : E[X]) :
    M0 ^ 4 * N1 ^ 2 ∣ zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) :=
  (mul_dvd_mul ⟨M0, by ring⟩ dvd_rfl).trans (pow5_mul_sq_dvd_zRaw c0 c1 P M0 N1 g4)

/-- Exact degree bound on `zRaw`: whenever `zRaw c0 c1 P Q ≠ 0`,
`(zRaw c0 c1 P Q).natDegree + 1 ≤ P.natDegree + 2 * Q.natDegree`! -/
theorem natDegree_zRaw_add_one_le (c0 c1 : E) (P Q : E[X]) (hz : zRaw c0 c1 P Q ≠ 0) :
    (zRaw c0 c1 P Q).natDegree + 1 ≤ P.natDegree + 2 * Q.natDegree := by
  have hpos : 1 ≤ P.natDegree + 2 * Q.natDegree := by
    by_contra h0
    have hP0 : P.natDegree = 0 := by omega
    have hQ0 : Q.natDegree = 0 := by omega
    have hPd : P.derivative = 0 := by rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, derivative_C]
    have hQd : Q.derivative = 0 := by rw [Polynomial.eq_C_of_natDegree_eq_zero hQ0, derivative_C]
    have hPh : hasse 2 P = 0 := by
      ext n; rw [coeff_hasse, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, coeff_zero]
    have hQh : hasse 2 Q = 0 := by
      ext n; rw [coeff_hasse, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, coeff_zero]
    apply hz; unfold zRaw; simp [hPd, hQd, hPh, hQh]
  have hQ2 : (Q ^ 2).natDegree ≤ 2 * Q.natDegree := natDegree_pow_le
  have hPd : P.derivative.natDegree ≤ P.natDegree - 1 := natDegree_derivative_le P
  have hQd : Q.derivative.natDegree ≤ Q.natDegree - 1 := natDegree_derivative_le Q
  have hPh : (hasse 2 P).natDegree ≤ P.natDegree - 2 := natDegree_hasse_le 2 P
  have hQh : (hasse 2 Q).natDegree ≤ Q.natDegree - 2 := natDegree_hasse_le 2 Q
  have hle : (zRaw c0 c1 P Q).natDegree ≤ P.natDegree + 2 * Q.natDegree - 1 := by
    unfold zRaw
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_C_mul_le _ _ |>.trans ?_
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · by_cases h0 : hasse 2 P = 0
            · simp [h0]
            · have hP2 : 2 ≤ P.natDegree := by
                by_contra hlt; apply h0; ext n
                rw [coeff_hasse, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, coeff_zero]
              exact natDegree_mul_le.trans (by omega)
          · by_cases h0 : P.derivative = 0 ∨ Q.derivative = 0
            · rcases h0 with h | h <;> simp [h]
            · push Not at h0
              have hP1 : 1 ≤ P.natDegree := by
                by_contra hlt; apply h0.1
                rw [Polynomial.eq_C_of_natDegree_eq_zero (show P.natDegree = 0 by omega), derivative_C]
              have hQ1 : 1 ≤ Q.natDegree := by
                by_contra hlt; apply h0.2
                rw [Polynomial.eq_C_of_natDegree_eq_zero (show Q.natDegree = 0 by omega), derivative_C]
              exact natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le le_rfl) |>.trans (by omega)
        · by_cases h0 : Q.derivative = 0
          · simp [h0]
          · have hQ1 : 1 ≤ Q.natDegree := by
              by_contra hlt; apply h0
              rw [Polynomial.eq_C_of_natDegree_eq_zero (show Q.natDegree = 0 by omega), derivative_C]
            exact natDegree_mul_le.trans (Nat.add_le_add le_rfl natDegree_pow_le) |>.trans (by omega)
      · by_cases h0 : hasse 2 Q = 0
        · simp [h0]
        · have hQ2' : 2 ≤ Q.natDegree := by
            by_contra hlt; apply h0; ext n
            rw [coeff_hasse, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, coeff_zero]
          exact natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le le_rfl) |>.trans (by omega)
    · refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_C_mul_le _ _) le_rfl) |>.trans ?_
      have hmid : (P.derivative * Q + P * Q.derivative).natDegree ≤ P.natDegree + Q.natDegree - 1 := by
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · by_cases h0 : P.derivative = 0
          · simp [h0]
          · have hP1 : 1 ≤ P.natDegree := by
              by_contra hlt; apply h0
              rw [Polynomial.eq_C_of_natDegree_eq_zero (show P.natDegree = 0 by omega), derivative_C]
            exact natDegree_mul_le.trans (by omega)
        · by_cases h0 : Q.derivative = 0
          · simp [h0]
          · have hQ1 : 1 ≤ Q.natDegree := by
              by_contra hlt; apply h0
              rw [Polynomial.eq_C_of_natDegree_eq_zero (show Q.natDegree = 0 by omega), derivative_C]
            exact natDegree_mul_le.trans (by omega)
      by_cases h0 : P.derivative * Q + P * Q.derivative = 0
      · simp [h0]; omega
      · have hPQ1 : 1 ≤ P.natDegree + Q.natDegree := by
          by_contra hlt; apply h0
          have hP' : P.derivative = 0 := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero (show P.natDegree = 0 by omega), derivative_C]
          have hQ' : Q.derivative = 0 := by
            rw [Polynomial.eq_C_of_natDegree_eq_zero (show Q.natDegree = 0 by omega), derivative_C]
          simp [hP', hQ']
        omega
  omega

/-- Exact degree bound after dividing `zRaw c0 c1 P (M0^3 * N1^2 * g4)` by `M0^5 * N1^2`! -/
theorem natDegree_zOde_pow5_le {c0 c1 : E} {P M0 N1 g4 Z_ode : E[X]}
    (hM0 : M0 ≠ 0) (hN1 : N1 ≠ 0) (hg4 : g4 ≠ 0) (hZ : Z_ode ≠ 0)
    (hdiv : zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) = M0 ^ 5 * N1 ^ 2 * Z_ode) :
    Z_ode.natDegree + 1 ≤ P.natDegree + M0.natDegree + 2 * N1.natDegree + 2 * g4.natDegree := by
  have hz_ne : zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) ≠ 0 := by
    rw [hdiv]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hM0) (pow_ne_zero 2 hN1)) hZ
  have hdeg := natDegree_zRaw_add_one_le c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) hz_ne
  rw [hdiv, natDegree_mul (mul_ne_zero (pow_ne_zero 5 hM0) (pow_ne_zero 2 hN1)) hZ,
    natDegree_mul (pow_ne_zero 5 hM0) (pow_ne_zero 2 hN1), natDegree_pow, natDegree_pow,
    natDegree_mul (mul_ne_zero (pow_ne_zero 3 hM0) (pow_ne_zero 2 hN1)) hg4,
    natDegree_mul (pow_ne_zero 3 hM0) (pow_ne_zero 2 hN1), natDegree_pow, natDegree_pow] at hdeg
  omega

/-- Exact degree bound after dividing `zRaw c0 c1 P (M0^3 * N1^2 * g4)` by `M0^4 * N1^2`! -/
theorem natDegree_zOde_pow4_le {c0 c1 : E} {P M0 N1 g4 Z_ode : E[X]}
    (hM0 : M0 ≠ 0) (hN1 : N1 ≠ 0) (hg4 : g4 ≠ 0) (hZ : Z_ode ≠ 0)
    (hdiv : zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) = M0 ^ 4 * N1 ^ 2 * Z_ode) :
    Z_ode.natDegree + 1 ≤ P.natDegree + 2 * M0.natDegree + 2 * N1.natDegree + 2 * g4.natDegree := by
  have hz_ne : zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) ≠ 0 := by
    rw [hdiv]; exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hM0) (pow_ne_zero 2 hN1)) hZ
  have hdeg := natDegree_zRaw_add_one_le c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) hz_ne
  rw [hdiv, natDegree_mul (mul_ne_zero (pow_ne_zero 4 hM0) (pow_ne_zero 2 hN1)) hZ,
    natDegree_mul (pow_ne_zero 4 hM0) (pow_ne_zero 2 hN1), natDegree_pow, natDegree_pow,
    natDegree_mul (mul_ne_zero (pow_ne_zero 3 hM0) (pow_ne_zero 2 hN1)) hg4,
    natDegree_mul (pow_ne_zero 3 hM0) (pow_ne_zero 2 hN1), natDegree_pow, natDegree_pow] at hdeg
  omega

private lemma rootMultiplicity_pow_eq (p : E[X]) (hp : p ≠ 0) (n : ℕ) (a : E) :
    (p ^ n).rootMultiplicity a = n * p.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp) hp), ih]
      ring

/-- **Exact local order lower bound for `Z_ode` (`ODE_fail`) at EVERY `a ∈ E`:**
Given `zRaw c0 c1 P (M0^3 * N1^2 * g4) = M0^5 * N1^2 * Z_ode` and
`P * N_dom^3 + A1^4 * (M0^3 * N1^2 * R_raw) = (M0^3 * N1^2 * g4) * Q0^4`:
1. If `N_dom.eval a ≠ 0`, then `4 * A1.rootMultiplicity a ≤ Z_ode.rootMultiplicity a`!
2. If `N_dom.rootMultiplicity a = 1`, then
   `4 * A1.rootMultiplicity a + 4 * M0.rootMultiplicity a + 4 * N1.rootMultiplicity a +
      R_raw.rootMultiplicity a + 2 * g4.rootMultiplicity a ≤ Z_ode.rootMultiplicity a + 5`! -/
theorem rootMultiplicity_zOde_ge {c0 c1 : E} {P M0 N1 g4 N_dom A1 R_raw Q0 Z_ode : E[X]}
    (hM0 : M0 ≠ 0) (hN1 : N1 ≠ 0) (hZ : Z_ode ≠ 0) (hNdom : N_dom ≠ 0)
    (hd1 : N_dom.derivative = C c0) (hd2 : hasse 2 N_dom = C c1)
    (hdiv : zRaw c0 c1 P (M0 ^ 3 * N1 ^ 2 * g4) = M0 ^ 5 * N1 ^ 2 * Z_ode)
    (heq : P * N_dom ^ 3 + A1 ^ 4 * (M0 ^ 3 * N1 ^ 2 * R_raw) = (M0 ^ 3 * N1 ^ 2 * g4) * Q0 ^ 4)
    (a : E) :
    (N_dom.eval a ≠ 0 → 4 * A1.rootMultiplicity a ≤ Z_ode.rootMultiplicity a) ∧
    (N_dom.rootMultiplicity a = 1 →
      4 * A1.rootMultiplicity a + 4 * M0.rootMultiplicity a + 4 * N1.rootMultiplicity a +
        R_raw.rootMultiplicity a + 2 * g4.rootMultiplicity a ≤ Z_ode.rootMultiplicity a + 5) := by
  have hid := zRaw_ode_fail_identity hd1 hd2 heq
  rw [hdiv] at hid
  have hrhs : zRaw c0 c1 (M0 ^ 3 * N1 ^ 2 * R_raw) (M0 ^ 3 * N1 ^ 2 * g4 * N_dom ^ 3) =
      (M0 ^ 3 * N1 ^ 2) ^ 3 * zRaw c0 c1 R_raw (g4 * N_dom ^ 3) := by
    rw [mul_comm (M0 ^ 3 * N1 ^ 2) R_raw,
      show M0 ^ 3 * N1 ^ 2 * g4 * N_dom ^ 3 = (g4 * N_dom ^ 3) * (M0 ^ 3 * N1 ^ 2) by ring,
      zRaw_mul_common]
  rw [hrhs] at hid
  have hMN_ne : M0 ^ 5 * N1 ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 5 hM0) (pow_ne_zero 2 hN1)
  have hcancel : N_dom ^ 9 * Z_ode = A1 ^ 4 * M0 ^ 4 * N1 ^ 4 * zRaw c0 c1 R_raw (g4 * N_dom ^ 3) := by
    apply mul_left_cancel₀ hMN_ne
    calc M0 ^ 5 * N1 ^ 2 * (N_dom ^ 9 * Z_ode)
        = N_dom ^ 9 * (M0 ^ 5 * N1 ^ 2 * Z_ode) := by ring
      _ = A1 ^ 4 * ((M0 ^ 3 * N1 ^ 2) ^ 3 * zRaw c0 c1 R_raw (g4 * N_dom ^ 3)) := hid
      _ = M0 ^ 5 * N1 ^ 2 * (A1 ^ 4 * M0 ^ 4 * N1 ^ 4 * zRaw c0 c1 R_raw (g4 * N_dom ^ 3)) := by ring
  have hLHS_ne : N_dom ^ 9 * Z_ode ≠ 0 := mul_ne_zero (pow_ne_zero 9 hNdom) hZ
  have hRHS_ne : A1 ^ 4 * M0 ^ 4 * N1 ^ 4 * zRaw c0 c1 R_raw (g4 * N_dom ^ 3) ≠ 0 := hcancel ▸ hLHS_ne
  have hA1_ne : A1 ≠ 0 := fun h0 => hRHS_ne (by simp [h0])
  have hzR_ne : zRaw c0 c1 R_raw (g4 * N_dom ^ 3) ≠ 0 := fun h0 => hRHS_ne (by simp [h0])
  have hmult_eq := congrArg (fun f : E[X] => f.rootMultiplicity a) hcancel
  rw [rootMultiplicity_mul hLHS_ne, rootMultiplicity_pow_eq N_dom hNdom 9 a,
    rootMultiplicity_mul hRHS_ne,
    rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hA1_ne) (pow_ne_zero 4 hM0)) (pow_ne_zero 4 hN1)),
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 4 hA1_ne) (pow_ne_zero 4 hM0)),
    rootMultiplicity_pow_eq A1 hA1_ne 4 a, rootMultiplicity_pow_eq M0 hM0 4 a,
    rootMultiplicity_pow_eq N1 hN1 4 a] at hmult_eq
  constructor
  · intro hNeval
    have hN0 : N_dom.rootMultiplicity a = 0 := rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hNeval)
    omega
  · intro hN1a
    have hdvd_hasse : ∀ (f : E[X]) (k : ℕ), (X - C a) ^ (f.rootMultiplicity a - k) ∣ hasse k f := by
      intro f k
      set m := f.rootMultiplicity a
      obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd f a
      have hsh : X ^ (m - k) ∣ (hasse k f).comp (X + C a) := by
        rw [← hasse_comp_add_C, hq, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
        rw [X_pow_dvd_iff]; intro n hn
        rw [coeff_hasse, coeff_X_pow_mul', if_neg (by omega), mul_zero]
      obtain ⟨r, hr⟩ := hsh
      refine ⟨r.comp (X - C a), ?_⟩
      have hback := congrArg (fun p : E[X] => p.comp (X - C a)) hr
      simp only [comp_assoc, add_comp, mul_comp, pow_comp, X_comp, C_comp, sub_add_cancel, comp_X] at hback
      exact hback
    have hdvd_N : (X - C a) ∣ N_dom := by
      have := pow_rootMultiplicity_dvd N_dom a; rw [hN1a, pow_one] at this; exact this
    set r := R_raw.rootMultiplicity a
    set s := g4.rootMultiplicity a
    have hR0 : (X - C a) ^ r ∣ R_raw := pow_rootMultiplicity_dvd R_raw a
    have hR1 : (X - C a) ^ (r - 1) ∣ R_raw.derivative := by
      rw [← hasse_one_eq_derivative]; exact hdvd_hasse R_raw 1
    have hR2 : (X - C a) ^ (r - 2) ∣ hasse 2 R_raw := hdvd_hasse R_raw 2
    have hG0 : (X - C a) ^ s ∣ g4 := pow_rootMultiplicity_dvd g4 a
    have hG1 : (X - C a) ^ (s - 1) ∣ g4.derivative := by
      rw [← hasse_one_eq_derivative]; exact hdvd_hasse g4 1
    have hG2 : (X - C a) ^ (s - 2) ∣ hasse 2 g4 := hdvd_hasse g4 2
    have hdvd_zR : (X - C a) ^ (r + 2 * s + 4) ∣ zRaw c0 c1 R_raw (g4 * N_dom ^ 3) := by
      have hQ' : (g4 * N_dom ^ 3).derivative = g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2 := by
        rw [derivative_mul, char2_derivative_cube, hd1]; ring
      have hQ2_plus : (g4 * N_dom ^ 3).derivative ^ 2 + hasse 2 (g4 * N_dom ^ 3) * (g4 * N_dom ^ 3) =
          N_dom ^ 6 * (g4.derivative ^ 2 + hasse 2 g4 * g4) +
          N_dom ^ 5 * (C c0 * g4.derivative * g4 + C c1 * g4 ^ 2) := by
        rw [hQ', hasse_two_mul, char2_hasse_two_cube, char2_derivative_cube, hd1, hd2]
        have hsq : (g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2) ^ 2 =
            g4.derivative ^ 2 * N_dom ^ 6 + C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 := by
          calc (g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2) ^ 2
              = g4.derivative ^ 2 * N_dom ^ 6 +
                  (g4.derivative * N_dom ^ 3 * (C c0 * g4 * N_dom ^ 2) +
                   g4.derivative * N_dom ^ 3 * (C c0 * g4 * N_dom ^ 2)) +
                  C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 := by ring
            _ = g4.derivative ^ 2 * N_dom ^ 6 + C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 := by
                  rw [char2_add_self, add_zero]
        rw [hsq]
        have hc : C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 + C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 = 0 := char2_add_self _
        calc g4.derivative ^ 2 * N_dom ^ 6 + C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 +
              (hasse 2 g4 * N_dom ^ 3 + g4.derivative * (N_dom ^ 2 * C c0) +
               g4 * (N_dom * C c0 ^ 2 + N_dom ^ 2 * C c1)) * (g4 * N_dom ^ 3)
            = (C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4 + C c0 ^ 2 * g4 ^ 2 * N_dom ^ 4) +
              N_dom ^ 6 * (g4.derivative ^ 2 + hasse 2 g4 * g4) +
              N_dom ^ 5 * (C c0 * g4.derivative * g4 + C c1 * g4 ^ 2) := by ring
          _ = N_dom ^ 6 * (g4.derivative ^ 2 + hasse 2 g4 * g4) +
              N_dom ^ 5 * (C c0 * g4.derivative * g4 + C c1 * g4 ^ 2) := by rw [hc, zero_add]
      have hNpow : ∀ k : ℕ, (X - C a) ^ k ∣ N_dom ^ k := fun k => pow_dvd_pow_of_dvd hdvd_N k
      unfold zRaw
      have hrew : C c0 * (hasse 2 R_raw * (g4 * N_dom ^ 3) ^ 2 +
            R_raw.derivative * (g4 * N_dom ^ 3).derivative * (g4 * N_dom ^ 3) +
            R_raw * (g4 * N_dom ^ 3).derivative ^ 2 +
            R_raw * hasse 2 (g4 * N_dom ^ 3) * (g4 * N_dom ^ 3)) +
          C c1 * (R_raw.derivative * (g4 * N_dom ^ 3) + R_raw * (g4 * N_dom ^ 3).derivative) * (g4 * N_dom ^ 3) =
          C c0 * (hasse 2 R_raw * g4 ^ 2 * N_dom ^ 6 +
            R_raw.derivative * (g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2) * (g4 * N_dom ^ 3) +
            R_raw * ((g4 * N_dom ^ 3).derivative ^ 2 + hasse 2 (g4 * N_dom ^ 3) * (g4 * N_dom ^ 3))) +
          C c1 * (R_raw.derivative * g4 ^ 2 * N_dom ^ 6 +
            R_raw * (g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2) * (g4 * N_dom ^ 3)) := by
        rw [← hQ']; ring
      rw [hrew, hQ2_plus]
      have hG2' : (X - C a) ^ (2 * s) ∣ g4 ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hG0 2
      have hG1sq : (X - C a) ^ (2 * (s - 1)) ∣ g4.derivative ^ 2 := by rw [pow_mul']; exact pow_dvd_pow_of_dvd hG1 2
      have hQ'd : (X - C a) ^ (s + 2) ∣ g4.derivative * N_dom ^ 3 + C c0 * g4 * N_dom ^ 2 := by
        apply dvd_add
        · exact (pow_dvd_pow (X - C a) (show s + 2 ≤ (s - 1) + 3 by omega)).trans
            (by rw [pow_add]; exact mul_dvd_mul hG1 (hNpow 3))
        · rw [mul_assoc]; exact dvd_mul_of_dvd_right (by rw [pow_add]; exact mul_dvd_mul hG0 (hNpow 2)) _
      have hQ0d : (X - C a) ^ (s + 3) ∣ g4 * N_dom ^ 3 := by
        rw [pow_add]; exact mul_dvd_mul hG0 (hNpow 3)
      apply dvd_add
      · apply dvd_mul_of_dvd_right
        apply dvd_add
        · apply dvd_add
          · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ (r - 2) + 2 * s + 6 by omega)).trans
              (by rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hR2 hG2') (hNpow 6))
          · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ (r - 1) + (s + 2) + (s + 3) by omega)).trans
              (by rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hR1 hQ'd) hQ0d)
        · rw [mul_add]; apply dvd_add
          · rw [mul_add, mul_add]
            apply dvd_add
            · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ r + (6 + 2 * (s - 1)) by omega)).trans
                (by rw [pow_add, pow_add]; exact mul_dvd_mul hR0 (mul_dvd_mul (hNpow 6) hG1sq))
            · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ r + (6 + ((s - 2) + s)) by omega)).trans
                (by rw [pow_add, pow_add, pow_add]; exact mul_dvd_mul hR0 (mul_dvd_mul (hNpow 6) (mul_dvd_mul hG2 hG0)))
          · rw [mul_add, mul_add]
            apply dvd_add
            · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ r + (5 + ((s - 1) + s)) by omega)).trans
                (by
                  rw [pow_add, pow_add, pow_add]
                  exact mul_dvd_mul hR0 (mul_dvd_mul (hNpow 5) (mul_dvd_mul (dvd_mul_of_dvd_right hG1 _) hG0)))
            · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ r + (5 + 2 * s) by omega)).trans
                (by
                  rw [pow_add, pow_add]
                  exact mul_dvd_mul hR0 (mul_dvd_mul (hNpow 5) (dvd_mul_of_dvd_right hG2' _)))
      · apply dvd_mul_of_dvd_right
        apply dvd_add
        · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ (r - 1) + 2 * s + 6 by omega)).trans
            (by rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hR1 hG2') (hNpow 6))
        · exact (pow_dvd_pow (X - C a) (show r + 2 * s + 4 ≤ r + (s + 2) + (s + 3) by omega)).trans
            (by rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hR0 hQ'd) hQ0d)
    have hge : r + 2 * s + 4 ≤ (zRaw c0 c1 R_raw (g4 * N_dom ^ 3)).rootMultiplicity a :=
      (le_rootMultiplicity_iff hzR_ne).mpr hdvd_zR
    omega

end Char2HasseExt

end B6401Char2ODE
end ProximityPrize.SubmissionBinaryLower

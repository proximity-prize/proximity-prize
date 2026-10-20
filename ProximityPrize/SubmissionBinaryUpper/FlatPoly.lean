/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.SubspacePoly

/-!
# Locators of affine flats

For any vectors `u 0, u 1, …` of `BF64`, the recursion `P₀ = X`,
`P_{k+1} = P_k (P_k - P_k(u k))` gives an additive polynomial of degree `2^k`
vanishing on the span of `u 0, …, u (k-1)`.  In characteristic two its square
step keeps every non-leading term at degree at most `2^(k-1)`, so the locator
`P_k - P_k(b)` of the flat `b + span` is `X^(2^k)` plus terms of degree at most
`2^(k-1)`.  Products of such locators keep the gap.

Domain words are `𝔽₂`-combinations of the powers `nodeN (2^i)`, which is how a
point given by coordinates is placed on a flat.
-/

namespace ProximityPrize.SubmissionBinaryUpper.FlatPoly

open Polynomial
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly

instance : CharP K 2 := inferInstance

/-- Coordinates in `𝔽₂` act on `BF64` through the characteristic-two cast. -/
noncomputable abbrev ψ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-! ## The recursion -/

noncomputable def P (u : ℕ → K) : ℕ → Polynomial K
  | 0 => Polynomial.X
  | k + 1 => P u k * (P u k - C ((P u k).eval (u k)))

theorem P_add (u : ℕ → K) (k : ℕ) (a b : K) :
    (P u k).eval (a + b) = (P u k).eval a + (P u k).eval b := by
  induction k with
  | zero => simp [P]
  | succ k ih =>
      simp only [P, eval_mul, eval_sub, eval_C, ih]
      linear_combination (P u k).eval a * (P u k).eval b * two_eq_zero

theorem P_zero (u : ℕ → K) (k : ℕ) : (P u k).eval 0 = 0 := by
  have h := P_add u k 0 0
  rw [add_zero] at h
  linear_combination -h

theorem P_monic_natDegree (u : ℕ → K) (k : ℕ) : (P u k).Monic ∧ (P u k).natDegree = 2 ^ k := by
  induction k with
  | zero => exact ⟨monic_X, by simp [P, natDegree_X]⟩
  | succ k ih =>
      obtain ⟨hm, hd⟩ := ih
      have hpos : 0 < (P u k).natDegree := by rw [hd]; positivity
      have hq : (P u k - C ((P u k).eval (u k))).Monic := by
        apply hm.sub_of_left
        calc (C ((P u k).eval (u k))).degree ≤ 0 := degree_C_le
          _ < (P u k).degree := by
            rw [degree_eq_natDegree hm.ne_zero]
            exact_mod_cast hpos
      refine ⟨hm.mul hq, ?_⟩
      rw [P, hm.natDegree_mul hq, natDegree_sub_C, hd, pow_succ]
      ring

theorem two_eq_zero_poly : (2 : Polynomial K) = 0 := by
  rw [← C_ofNat, two_eq_zero, C_0]

/-- The characteristic-two gap: below the leading term every coefficient sits in
degree at most `2^k`. -/
theorem P_gap (u : ℕ → K) (k : ℕ) : (P u (k + 1) - Polynomial.X ^ 2 ^ (k + 1)).natDegree ≤ 2 ^ k := by
  induction k with
  | zero =>
      have h : P u (0 + 1) - Polynomial.X ^ 2 ^ (0 + 1) = -(C (u 0) * Polynomial.X) := by simp [P]; ring
      rw [h, natDegree_neg]
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  | succ k ih =>
      have hd := (P_monic_natDegree u (k + 1)).2
      have hid : P u (k + 1 + 1) - Polynomial.X ^ 2 ^ (k + 1 + 1) =
          (P u (k + 1) - Polynomial.X ^ 2 ^ (k + 1)) ^ 2 - C ((P u (k + 1)).eval (u (k + 1))) * P u (k + 1) := by
        rw [show P u (k + 1 + 1) = P u (k + 1) * (P u (k + 1) - C ((P u (k + 1)).eval (u (k + 1))))
          from rfl, pow_succ 2 (k + 1), pow_mul]
        linear_combination (Polynomial.X ^ 2 ^ (k + 1) * (P u (k + 1) - Polynomial.X ^ 2 ^ (k + 1))) * two_eq_zero_poly
      rw [hid]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_pow_le.trans ((Nat.mul_le_mul_left 2 ih).trans ?_)
        rw [pow_succ]
        omega
      · refine (natDegree_C_mul_le _ _).trans ?_
        rw [hd]

/-- `P u k` vanishes on every `𝔽₂`-combination of `u 0, …, u (k-1)`. -/
theorem P_eval_span (u : ℕ → K) (a : ℕ → ZMod 2) (k : ℕ) :
    (P u k).eval (∑ i ∈ Finset.range k, ψ (a i) * u i) = 0 := by
  induction k with
  | zero => simp [P]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [P, eval_mul, eval_sub, eval_C, P_add, ih, zero_add]
      rcases zmod2_cases (a k) with h | h <;> simp [h, P_zero]

/-! ## Flat locators and the gap under products -/

/-- The locator of the flat through `b` with direction `span (u 0, …, u (k-1))`. -/
noncomputable def flatPoly (u : ℕ → K) (k : ℕ) (b : K) : Polynomial K :=
  P u k - C ((P u k).eval b)

theorem flatPoly_eval (u : ℕ → K) (k : ℕ) (b : K) (a : ℕ → ZMod 2) :
    (flatPoly u k b).eval (b + ∑ i ∈ Finset.range k, ψ (a i) * u i) = 0 := by
  rw [flatPoly, eval_sub, eval_C, P_add, P_eval_span, add_zero, sub_self]

theorem flatPoly_gap (u : ℕ → K) (k : ℕ) (b : K) :
    (flatPoly u (k + 1) b - Polynomial.X ^ 2 ^ (k + 1)).natDegree ≤ 2 ^ k := by
  have h : flatPoly u (k + 1) b - Polynomial.X ^ 2 ^ (k + 1) =
      (P u (k + 1) - Polynomial.X ^ 2 ^ (k + 1)) - C ((P u (k + 1)).eval b) := by
    rw [flatPoly]; ring
  rw [h, natDegree_sub_C]
  exact P_gap u k

theorem flatPoly_gap' (u : ℕ → K) (k : ℕ) (hk : 1 ≤ k) (b : K) :
    (flatPoly u k b - Polynomial.X ^ 2 ^ k).natDegree ≤ 2 ^ (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simpa using flatPoly_gap u k' b

theorem gap_mul {f g : Polynomial K} {a b w : ℕ} (hwa : w ≤ a) (hwb : w ≤ b)
    (hf : (f - Polynomial.X ^ a).natDegree ≤ a - w) (hg : (g - Polynomial.X ^ b).natDegree ≤ b - w) :
    (f * g - Polynomial.X ^ (a + b)).natDegree ≤ a + b - w := by
  have h : f * g - Polynomial.X ^ (a + b) =
      (f - Polynomial.X ^ a) * (g - Polynomial.X ^ b) + (Polynomial.X ^ a * (g - Polynomial.X ^ b) + Polynomial.X ^ b * (f - Polynomial.X ^ a)) := by ring
  rw [h]
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_add_le _ _).trans (max_le ?_ ?_)))
  · refine natDegree_mul_le.trans ?_
    omega
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_X_pow]
    omega
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_X_pow]
    omega

/-- `gap_mul` with the product exponent given by name, so that no numeral is
ever unfolded inside a power of `X`. -/
theorem gap_mul' {f g : Polynomial K} {a b c w : ℕ} (hwa : w ≤ a) (hwb : w ≤ b) (hc : a + b = c)
    (hf : (f - Polynomial.X ^ a).natDegree ≤ a - w) (hg : (g - Polynomial.X ^ b).natDegree ≤ b - w) :
    (f * g - Polynomial.X ^ c).natDegree ≤ c - w := by
  subst hc
  exact gap_mul hwa hwb hf hg

/-! ## Opaque powers of `X`

A closed power such as `X ^ 2 ^ 20` makes definitional unfolding walk the
exponent, so the gap is restated with an irreducible `Xp n = X ^ n`. -/

noncomputable irreducible_def Xp (n : ℕ) : Polynomial K := Polynomial.X ^ n

theorem Xp_natDegree (n : ℕ) : (Xp n).natDegree = n := by rw [Xp_def]; exact natDegree_X_pow n

theorem Xp_coeff_self (n : ℕ) : (Xp n).coeff n = 1 := by rw [Xp_def]; exact coeff_X_pow_self n

theorem flatPoly_gapX (u : ℕ → K) (k : ℕ) (hk : 1 ≤ k) (b : K) :
    (flatPoly u k b - Xp (2 ^ k)).natDegree ≤ 2 ^ (k - 1) := by
  rw [Xp_def]
  exact flatPoly_gap' u k hk b

theorem gap_mulX {f g : Polynomial K} {a b c w : ℕ} (hwa : w ≤ a) (hwb : w ≤ b) (hc : a + b = c)
    (hf : (f - Xp a).natDegree ≤ a - w) (hg : (g - Xp b).natDegree ≤ b - w) :
    (f * g - Xp c).natDegree ≤ c - w := by
  rw [Xp_def] at hf hg ⊢
  exact gap_mul' hwa hwb hc hf hg

/-! ## Domain words in coordinates -/

/-- The `i`-th binary digit of `y`, as an element of `𝔽₂`. -/
def bit (y i : ℕ) : ZMod 2 := if y.testBit i then 1 else 0

theorem bit_xor (a b i : ℕ) : bit (a ^^^ b) i = bit a i + bit b i := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem nodeN_bits (n : ℕ) : ∀ y < 2 ^ n,
    nodeN y = ∑ i ∈ Finset.range n, ψ (bit y i) * nodeN (2 ^ i) := by
  induction n with
  | zero =>
      intro y hy
      have : y = 0 := by simpa using hy
      subst this
      simp [nodeN_zero]
  | succ n ih =>
      intro y hy
      have hr : y % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
      have hq : y / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at hy)
      have hy' : y = 2 ^ n * (y / 2 ^ n) + y % 2 ^ n := (Nat.div_add_mod y (2 ^ n)).symm
      have hlow : ∀ i ∈ Finset.range n, bit y i = bit (y % 2 ^ n) i := by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        unfold bit
        conv_lhs => rw [hy']
        rw [Nat.testBit_two_pow_mul_add _ hr, if_pos hi']
      have htop : bit y n = bit (y / 2 ^ n) 0 := by
        unfold bit
        conv_lhs => rw [hy']
        rw [Nat.testBit_two_pow_mul_add _ hr, if_neg (lt_irrefl n), Nat.sub_self]
      rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun i hi => by rw [hlow i hi]),
        ← ih _ hr, htop]
      conv_lhs => rw [hy', two_pow_mul_add_eq_xor hr, nodeN_xor]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq) with h | h
      · rw [h]; simp [bit, nodeN_zero]
      · rw [h]; simp [bit]; ring

end ProximityPrize.SubmissionBinaryUpper.FlatPoly

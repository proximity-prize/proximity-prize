import ProximityPrize.Benchmark.BinaryTargetLower
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

set_option Elab.async false

/-!
# Concrete 64.01-bit parameters and linearized domain vanishing polynomial

Defines the 64.01-bit challenge parameters:
- `radius := 78633206 / 268435456` (`δ ≈ 0.292931535...`),
- `A := 1482831` (`⌈2^21 · (1 - δ)⌉ = 1482831`),
- `D := 1048575` (`baseDimension - 1`),
- `N := 2097152` (`2^21`),
- `score := 6401` (`(1 - δ)^128 ≤ 2^(-64.01)`),

and proves that the domain vanishing polynomial `N_dom = ∏ i, (X - C (domain i))`
is `𝔽₂`-linearized with nonzero linear coefficient `c₀ ≠ 0`, so every term above `X^2`
has exponent divisible by `4`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401Params

open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped NNReal BigOperators

abbrev Fld := BinaryIRSProfile.Field
abbrev Idx := BinaryIRSProfile.Index

def radNum : ℕ := 78633206
def radDen : ℕ := 268435456
def centiBits : ℕ := 6401
def N : ℕ := 2097152
def D : ℕ := 1048575
def wY : ℕ := 1048575
def A : ℕ := 1482831

/-- The exact 64.01-bit radius `δ = 78633206 / 2^28`. -/
noncomputable def radius : ℝ≥0 := claimedRadius radNum radDen

theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) BinaryIRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radNum, radDen,
    BinaryIRSProfile.minRelativeDistance]

theorem agreement_ge_A {k : ℕ} (hk : (Fintype.card Idx : ℝ) * (1 - (radius : ℝ)) ≤ k) :
    A ≤ k := by
  rw [BinaryIRSProfile.card_index] at hk
  have hr : ((radius : ℝ≥0) : ℝ) = (78633206 : ℝ) / 268435456 := by
    simp [radius, claimedRadius, radNum, radDen]
  rw [hr] at hk
  have hlt : (1482830 : ℝ) < (k : ℝ) := by norm_num at hk; linarith
  have : 1482830 < k := by exact_mod_cast hlt
  unfold A
  omega

/-- Auxiliary two-term binomial lower bound `(1 + u)^n ≥ 1 + n u + n(n-1)/2 · u^2` for `u ≥ 0`. -/
lemma one_add_pow_ge_quad {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    1 + (n : ℝ) * u + ((n * (n - 1) / 2 : ℕ) : ℝ) * u ^ 2 ≤ (1 + u) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
        cases k with
        | zero => simp
        | succ m =>
            simp only [Nat.add_sub_cancel]
            rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring]
            omega
      have hcast : (((k + 1) * k / 2 : ℕ) : ℝ) = ((k * (k - 1) / 2 : ℕ) : ℝ) + (k : ℝ) := by
        rw [h1]; push_cast; ring
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + u)
      have hnonneg : (0 : ℝ) ≤ ((k * (k - 1) / 2 : ℕ) : ℝ) * u ^ 3 := by positivity
      have hexp : (1 + (k : ℝ) * u + ((k * (k - 1) / 2 : ℕ) : ℝ) * u ^ 2) * (1 + u) =
          1 + ((k : ℝ) + 1) * u + (((k * (k - 1) / 2 : ℕ) : ℝ) + (k : ℝ)) * u ^ 2 +
            ((k * (k - 1) / 2 : ℕ) : ℝ) * u ^ 3 := by ring
      rw [pow_succ (1 + u) k, Nat.add_sub_cancel, hcast]
      push_cast
      linarith [hmul, hnonneg, hexp]

/-- Score proof: `(1 - 78633206 / 2^28)^128 ≤ 2^(-64.01)`. -/
theorem radius_score :
    (1 - radius) ^ BinaryIRSProfile.repetitions ≤ claimedError centiBits := by
  change (1 - radius) ^ (128 : ℕ) ≤ claimedError centiBits
  have hr1 : radius ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num [radius, claimedRadius, radNum, radDen]
  have hrad : ((radius : ℝ≥0) : ℝ) = 78633206 / 268435456 := by
    simp [radius, claimedRadius, radNum, radDen]
  have h128 : (1 - radius) ^ (128 : ℕ) ≤ (1 / 2 : ℝ≥0) ^ (64 : ℕ) * (9231 / 9232 : ℝ≥0) ^ (64 : ℕ) := by
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hr1]
    rw [hrad, show (128 : ℕ) = 2 * 64 by norm_num, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) 64
  have htail_pow : ((9231 / 9232 : ℝ≥0) ^ (64 : ℕ)) ^ (100 : ℕ) ≤ ((2 : ℝ≥0) ^ (-(1 : ℝ) / 100)) ^ (100 : ℕ) := by
    have hE1 : ((2 : ℝ≥0) ^ (-(1 : ℝ) / 100)) ^ (100 : ℕ) = (1 / 2 : ℝ≥0) := by
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul,
        show (-(1 : ℝ) / 100) * (100 : ℕ) = -1 by norm_num, NNReal.rpow_neg_one, one_div]
    rw [hE1, ← NNReal.coe_le_coe]
    push_cast
    have hbin : (1010891153 / 1000000000 : ℝ) ≤ (9232 / 9231 : ℝ) ^ (100 : ℕ) := by
      have hb := one_add_pow_ge_quad (u := (1 / 9231 : ℝ)) (by positivity) 100
      rw [show (1 : ℝ) + 1 / 9231 = 9232 / 9231 by norm_num] at hb
      exact le_trans (by norm_num) hb
    have hsq1 : (1021900923 / 1000000000 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 2 := by
      calc (1021900923 / 1000000000 : ℝ) ≤ (1010891153 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hbin 2
    have hsq2 : (1044281496 / 1000000000 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      calc (1044281496 / 1000000000 : ℝ) ≤ (1021900923 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hsq1 2
    have hsq3 : (1090523842 / 1000000000 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 8 := by
      rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul]
      calc (1090523842 / 1000000000 : ℝ) ≤ (1044281496 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hsq2 2
    have hsq4 : (1189242249 / 1000000000 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 16 := by
      rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul]
      calc (1189242249 / 1000000000 : ℝ) ≤ (1090523842 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hsq3 2
    have hsq5 : (1414297126 / 1000000000 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 32 := by
      rw [show (32 : ℕ) = 16 * 2 by norm_num, pow_mul]
      calc (1414297126 / 1000000000 : ℝ) ≤ (1189242249 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hsq4 2
    have hsq6 : (2 : ℝ) ≤ ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ 64 := by
      rw [show (64 : ℕ) = 32 * 2 by norm_num, pow_mul]
      calc (2 : ℝ) ≤ (1414297126 / 1000000000 : ℝ) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hsq5 2
    have hx0 : (0 : ℝ) ≤ ((9231 / 9232 : ℝ) ^ (64 : ℕ)) ^ (100 : ℕ) := by positivity
    have hprod : ((9231 / 9232 : ℝ) ^ (64 : ℕ)) ^ (100 : ℕ) *
        ((9232 / 9231 : ℝ) ^ (100 : ℕ)) ^ (64 : ℕ) = 1 := by
      rw [pow_right_comm (9231 / 9232 : ℝ) 64 100, ← mul_pow, ← mul_pow,
        show (9231 / 9232 : ℝ) * (9232 / 9231 : ℝ) = 1 by norm_num, one_pow, one_pow]
    have hmul := mul_le_mul_of_nonneg_left hsq6 hx0
    rw [hprod] at hmul
    exact (le_div_iff₀ (by norm_num)).mpr hmul
  have htail : (9231 / 9232 : ℝ≥0) ^ (64 : ℕ) ≤ (2 : ℝ≥0) ^ (-(1 : ℝ) / 100) :=
    le_of_pow_le_pow_left₀ (by norm_num : (100 : ℕ) ≠ 0) zero_le htail_pow
  have hhalf : (1 / 2 : ℝ≥0) ^ (64 : ℕ) = (2 : ℝ≥0) ^ (-(64 : ℝ)) := by
    rw [show -(64 : ℝ) = -((64 : ℕ) : ℝ) by norm_num, NNReal.rpow_neg, NNReal.rpow_natCast,
      ← inv_pow, one_div]
  calc (1 - radius) ^ (128 : ℕ)
      ≤ (1 / 2 : ℝ≥0) ^ (64 : ℕ) * (9231 / 9232 : ℝ≥0) ^ (64 : ℕ) := h128
    _ ≤ (1 / 2 : ℝ≥0) ^ (64 : ℕ) * (2 : ℝ≥0) ^ (-(1 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_left htail zero_le
    _ = (2 : ℝ≥0) ^ (-(64 : ℝ)) * (2 : ℝ≥0) ^ (-(1 : ℝ) / 100) := by rw [hhalf]
    _ = (2 : ℝ≥0) ^ (-(64 : ℝ) + -(1 : ℝ) / 100) := (NNReal.rpow_add (by norm_num) _ _).symm
    _ = claimedError centiBits := by
        unfold claimedError centiBits
        congr 1
        norm_num

/-! ### Linearized vanishing polynomial of the additive binary domain -/

lemma baseDomain_xor {a b : ℕ} (ha : a < 2 ^ 21) (hb : b < 2 ^ 21) :
    BinaryIRSProfile.baseDomain ⟨a ^^^ b, Nat.xor_lt_two_pow ha hb⟩ =
      BinaryIRSProfile.baseDomain ⟨a, ha⟩ + BinaryIRSProfile.baseDomain ⟨b, hb⟩ := by
  apply BF64.toBitVec_injective
  change BitVec.ofNat 64 (a ^^^ b) = BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b
  apply BitVec.eq_of_toNat_eq
  have ha64 : a < 2 ^ 64 := lt_trans ha (by norm_num)
  have hb64 : b < 2 ^ 64 := lt_trans hb (by norm_num)
  have hab64 : a ^^^ b < 2 ^ 64 := lt_trans (Nat.xor_lt_two_pow ha hb) (by norm_num)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_xor,
    Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hab64]

lemma domain_xor {a b : ℕ} (ha : a < 2 ^ 21) (hb : b < 2 ^ 21) :
    BinaryIRSProfile.domain ⟨a ^^^ b, Nat.xor_lt_two_pow ha hb⟩ =
      BinaryIRSProfile.domain ⟨a, ha⟩ + BinaryIRSProfile.domain ⟨b, hb⟩ := by
  change CompPoly.Extension.Ext.ofBase (BinaryIRSProfile.baseDomain ⟨a ^^^ b, _⟩) =
    CompPoly.Extension.Ext.ofBase (BinaryIRSProfile.baseDomain ⟨a, ha⟩) +
      CompPoly.Extension.Ext.ofBase (BinaryIRSProfile.baseDomain ⟨b, hb⟩)
  rw [baseDomain_xor ha hb]
  exact (CompPoly.Extension.Ext.ofBaseRingHom _).map_add _ _

/-- The vanishing polynomial on the first `2^k` domain points (`k ≤ 21`). -/
noncomputable def subDomPoly (k : ℕ) (hk : k ≤ 21) : Fld[X] :=
  ∏ i : Fin (2 ^ k), ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨i.val,
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hk)⟩))

/-- The full domain vanishing polynomial `N_dom(X) = ∏_{i : Idx} (X - domain i)`. -/
noncomputable def Ndom : Fld[X] :=
  ∏ i : Idx, ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain i))

lemma subDomPoly_21 : subDomPoly 21 le_rfl = Ndom := by
  unfold subDomPoly Ndom
  apply Finset.prod_congr rfl
  intro i _
  rfl

lemma subDomPoly_add_one (k : ℕ) (hk : k + 1 ≤ 21) :
    let vk : Fld := BinaryIRSProfile.domain ⟨2 ^ k,
      lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : k < 21)) le_rfl⟩
    subDomPoly (k + 1) hk =
      subDomPoly k (by omega) * (subDomPoly k (by omega)).comp ((Polynomial.X : Fld[X]) + C vk) := by
  intro vk
  have hk21 : k ≤ 21 := by omega
  unfold subDomPoly
  let f1 : ℕ → Fld[X] := fun m =>
    if hm : m < 2 ^ (k + 1) then
      (Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨m, lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hk)⟩)
    else 1
  let f0 : ℕ → Fld[X] := fun m =>
    if hm : m < 2 ^ k then
      (Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨m, lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hk21)⟩)
    else 1
  have hL : (∏ i : Fin (2 ^ (k + 1)), ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨i.val,
      lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hk)⟩))) =
      ∏ m ∈ Finset.range (2 ^ (k + 1)), f1 m := by
    rw [← Fin.prod_univ_eq_prod_range f1]
    apply Finset.prod_congr rfl; intro i _; simp [f1, i.isLt]
  have hR : (∏ i : Fin (2 ^ k), ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨i.val,
      lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hk21)⟩))) =
      ∏ m ∈ Finset.range (2 ^ k), f0 m := by
    rw [← Fin.prod_univ_eq_prod_range f0]
    apply Finset.prod_congr rfl; intro i _; simp [f0, i.isLt]
  rw [hL, hR, pow_succ, mul_two, Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro m hm
    have hm' : m < 2 ^ k := Finset.mem_range.mp hm
    have hm2 : m < 2 ^ (k + 1) := lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [f1, f0, hm', hm2]
  · rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro m hm
    have hm' : m < 2 ^ k := Finset.mem_range.mp hm
    have hm2 : 2 ^ k + m < 2 ^ (k + 1) := by rw [pow_succ]; omega
    have hxor : 2 ^ k + m = 2 ^ k ^^^ m := by
      have hor : 2 ^ k + m = 2 ^ k ||| m := by
        simpa using Nat.two_pow_add_eq_or_of_lt hm' 1
      rw [hor]
      apply Nat.eq_of_testBit_eq
      intro b
      rw [Nat.testBit_or, Nat.testBit_xor]
      have hdisj : (Nat.testBit (2 ^ k) b && Nat.testBit m b) = false := by
        rw [Nat.testBit_two_pow]
        by_cases hbk : k = b
        · subst hbk
          simp [Nat.testBit_lt_two_pow hm']
        · simp [hbk]
      cases h1 : Nat.testBit (2 ^ k) b <;> cases h2 : Nat.testBit m b <;> simp_all
    have hpow_lt : 2 ^ k < 2 ^ 21 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hm_lt : m < 2 ^ 21 := lt_trans hm' hpow_lt
    have hdom : BinaryIRSProfile.domain ⟨2 ^ k + m,
        lt_of_lt_of_le hm2 (Nat.pow_le_pow_right (by norm_num) hk)⟩ =
        vk + BinaryIRSProfile.domain ⟨m, hm_lt⟩ := by
      have heq : (⟨2 ^ k + m, lt_of_lt_of_le hm2 (Nat.pow_le_pow_right (by norm_num) hk)⟩ : Idx) =
          ⟨2 ^ k ^^^ m, Nat.xor_lt_two_pow hpow_lt hm_lt⟩ := Fin.ext hxor
      rw [heq, domain_xor hpow_lt hm_lt]
    simp only [f1, f0, hm', hm2, ↓reduceDIte, hdom, sub_comp, X_comp, C_comp, map_add]
    have hneg : ∀ x : Fld[X], -x = x := CharTwo.neg_eq
    simp only [sub_eq_add_neg, hneg]
    ring

/-- A polynomial over a char-2 field is `𝔽₂`-linearized if every nonzero term has degree `2^j`. -/
def IsLinearized (p : Fld[X]) : Prop :=
  ∀ n, p.coeff n ≠ 0 → ∃ j : ℕ, n = 2 ^ j

lemma linearized_comp_add (p : Fld[X]) (hp : IsLinearized p) (a : Fld) :
    p.comp ((Polynomial.X : Fld[X]) + C a) = p + C (p.eval a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlin : ∀ n, n ∈ p.support → (C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n).comp ((Polynomial.X : Fld[X]) + C a) =
      C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n + C (p.coeff n * a ^ n) := by
    intro n hn
    obtain ⟨j, rfl⟩ := hp n (mem_support_iff.mp hn)
    simp only [mul_comp, C_comp, pow_comp, X_comp, map_mul]
    rw [add_pow_char_pow (R := Fld[X]) (Polynomial.X : Fld[X]) (C a) 2 j, ← C_pow, mul_add]
  calc p.comp ((Polynomial.X : Fld[X]) + C a)
      = (∑ n ∈ p.support, C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n).comp ((Polynomial.X : Fld[X]) + C a) := by
          conv_lhs => rw [as_sum_support_C_mul_X_pow p]
    _ = ∑ n ∈ p.support, (C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n).comp ((Polynomial.X : Fld[X]) + C a) :=
          Polynomial.sum_comp _ _ _
    _ = ∑ n ∈ p.support, (C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n + C (p.coeff n * a ^ n)) :=
          Finset.sum_congr rfl hlin
    _ = (∑ n ∈ p.support, C (p.coeff n) * (Polynomial.X : Fld[X]) ^ n) + ∑ n ∈ p.support, C (p.coeff n * a ^ n) :=
          Finset.sum_add_distrib
    _ = p + C (p.eval a) := by
          rw [← as_sum_support_C_mul_X_pow, ← map_sum, Polynomial.eval_eq_sum]
          rfl

lemma linearized_sq (p : Fld[X]) (hp : IsLinearized p) : IsLinearized (p ^ 2) := by
  intro n hn
  have hfr : ∀ s : Finset ℕ, ∀ f : ℕ → Fld[X],
      (∑ k ∈ s, f k) ^ 2 = ∑ k ∈ s, (f k) ^ 2 := fun s f => by
    have h := map_sum (frobenius Fld[X] 2) f s
    simp only [frobenius_def] at h
    exact h
  have hsq : p ^ 2 = ∑ k ∈ p.support, C (p.coeff k ^ 2) * (Polynomial.X : Fld[X]) ^ (2 * k) := by
    conv_lhs => rw [as_sum_support_C_mul_X_pow p]
    rw [hfr]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← C_pow, ← pow_mul, mul_comm k 2]
  have hcoeff_sum : ∀ (s : Finset ℕ) (f : ℕ → Fld[X]) (m : ℕ),
      (∑ k ∈ s, f k).coeff m = ∑ k ∈ s, (f k).coeff m := fun s f m => by
    simp
  rw [hsq, hcoeff_sum] at hn
  obtain ⟨k, hk, hkn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨j, rfl⟩ := hp k (mem_support_iff.mp hk)
  rw [coeff_C_mul_X_pow] at hkn
  split_ifs at hkn with h
  · exact ⟨j + 1, by rw [h, pow_succ']⟩
  · exact absurd rfl hkn

lemma linearized_add {p q : Fld[X]} (hp : IsLinearized p) (hq : IsLinearized q) :
    IsLinearized (p + q) := by
  intro n hn
  rw [coeff_add] at hn
  by_cases h1 : p.coeff n = 0
  · rw [h1, zero_add] at hn; exact hq n hn
  · exact hp n h1

lemma linearized_C_mul {p : Fld[X]} (hp : IsLinearized p) (c : Fld) :
    IsLinearized (C c * p) := by
  intro n hn
  rw [Polynomial.coeff_C_mul] at hn
  exact hp n (right_ne_zero_of_mul hn)

/-- Every partial vanishing polynomial `subDomPoly k` is `𝔽₂`-linearized with nonzero linear coeff. -/
theorem subDomPoly_linearized_and_coeff1 (k : ℕ) (hk : k ≤ 21) :
    IsLinearized (subDomPoly k hk) ∧ (subDomPoly k hk).coeff 1 ≠ 0 := by
  induction k with
  | zero =>
      have h0 : subDomPoly 0 hk = (Polynomial.X : Fld[X]) := by
        unfold subDomPoly
        have h1 : (∏ i : Fin (2 ^ 0), ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨i.val,
            lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hk)⟩))) =
            (Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨0, by norm_num⟩) := by
          change (∏ i : Fin 1, ((Polynomial.X : Fld[X]) - C (BinaryIRSProfile.domain ⟨i.val,
            lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hk)⟩))) = _
          rw [Fin.prod_univ_one]
          rfl
        rw [h1]
        have hd0 : BinaryIRSProfile.domain ⟨0, by norm_num⟩ = 0 := by
          change CompPoly.Extension.Ext.ofBase (BF64.ofBitVec 0#64) = 0
          have hb0 : BF64.ofBitVec 0#64 = 0 := BF64.toBitVec_injective rfl
          rw [hb0]
          exact (CompPoly.Extension.Ext.ofBaseRingHom _).map_zero
        rw [hd0, map_zero, sub_zero]
      rw [h0]
      refine ⟨fun n hn => ?_, by simp⟩
      rw [coeff_X] at hn
      split_ifs at hn with h
      · exact ⟨0, by omega⟩
      · exact absurd rfl hn
  | succ k ih =>
      obtain ⟨hlin, hc1⟩ := ih (by omega)
      set vk : Fld := BinaryIRSProfile.domain ⟨2 ^ k,
        lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : k < 21)) le_rfl⟩
      have hrec := subDomPoly_add_one k hk
      change subDomPoly (k + 1) hk =
        subDomPoly k (by omega) * (subDomPoly k (by omega)).comp ((Polynomial.X : Fld[X]) + C vk) at hrec
      rw [linearized_comp_add _ hlin vk] at hrec
      have hsq : subDomPoly (k + 1) hk =
          (subDomPoly k (by omega)) ^ 2 +
            C ((subDomPoly k (by omega)).eval vk) * subDomPoly k (by omega) := by
        rw [hrec]; ring
      have hvk_ne : (subDomPoly k (by omega)).eval vk ≠ 0 := by
        unfold subDomPoly
        rw [eval_prod]
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        rw [eval_sub, eval_X, eval_C, sub_ne_zero]
        intro heq
        have hinj := BinaryIRSProfile.domain.injective heq
        have hval := congrArg Fin.val hinj
        dsimp only at hval
        have := i.isLt
        omega
      refine ⟨?_, ?_⟩
      · rw [hsq]
        exact linearized_add (linearized_sq _ hlin) (linearized_C_mul hlin _)
      · rw [hsq, coeff_add, coeff_C_mul]
        have hsq1 : ((subDomPoly k (by omega)) ^ 2).coeff 1 = 0 := by
          rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
            Finset.sum_singleton]
          simp only [zero_add]
          rw [mul_comm ((subDomPoly k (by omega)).coeff 1)]
          exact CharTwo.add_self_eq_zero _
        rw [hsq1, zero_add]
        exact mul_ne_zero hvk_ne hc1

private lemma linearized_tail_dvd_four (P : Fld[X]) (hlin : IsLinearized P) (hc1 : P.coeff 1 ≠ 0) :
    ∃ c0 c1 : Fld, c0 ≠ 0 ∧
      ∀ n, (P - C c0 * (Polynomial.X : Fld[X]) - C c1 * (Polynomial.X : Fld[X]) ^ 2).coeff n ≠ 0 → 4 ∣ n := by
  refine ⟨P.coeff 1, P.coeff 2, hc1, fun n hn => ?_⟩
  have h1 : n ≠ 1 := by
    intro h; subst h
    apply hn
    have hne : (1 : ℕ) ≠ 2 := by omega
    simp only [coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow, ↓reduceIte, hne,
      mul_one, mul_zero, sub_self]
  have h2 : n ≠ 2 := by
    intro h; subst h
    apply hn
    have hne : (1 : ℕ) ≠ 2 := by omega
    simp only [coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow, ↓reduceIte, hne,
      mul_one, mul_zero, sub_zero, sub_self]
  have hN : P.coeff n ≠ 0 := by
    intro h0
    apply hn
    simp only [coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow, Ne.symm h1, h2, h0,
      ↓reduceIte, mul_zero, sub_zero]
  obtain ⟨j, rfl⟩ := hlin n hN
  have hj : 2 ≤ j := by
    by_contra hjlt
    have hjle : j = 0 ∨ j = 1 := by omega
    rcases hjle with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl
  refine ⟨2 ^ (j - 2), ?_⟩
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, Nat.add_sub_of_le hj]

/-- Main domain theorem: `Ndom(X) = c₀ X + c₁ X² + tail(X)` with `c₀ ≠ 0` and every nonzero
coefficient of `tail` at degree divisible by `4`. -/
theorem Ndom_structure :
    ∃ c0 c1 : Fld, c0 ≠ 0 ∧
      ∀ n, (Ndom - C c0 * (Polynomial.X : Fld[X]) - C c1 * (Polynomial.X : Fld[X]) ^ 2).coeff n ≠ 0 → 4 ∣ n := by
  have ⟨hlin, hc1⟩ := subDomPoly_linearized_and_coeff1 21 le_rfl
  rw [subDomPoly_21] at hlin hc1
  exact linearized_tail_dvd_four Ndom hlin hc1

end B6401Params
end ProximityPrize.SubmissionBinaryLower

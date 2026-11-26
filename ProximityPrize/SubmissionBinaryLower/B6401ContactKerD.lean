import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

set_option Elab.async false

/-!
# Characteristic-2 contact polynomials, `ker(D)` basis `K_W(s)`, `varsKerD_exact`, and `rankKerD`

Formalizes the exact 3- and 4-variable characteristic-2 contact derivation `D = ∂_X + R ∂_Y`
on `ContactPoly A := A[X][Y][R]`:
1. `contactDeriv` is a derivation (`D(P · Q) = D(P) Q + P D(Q)`), so `ker(D)` is a subring.
2. Weighted degree `wdeg wY` with `W(X) = 1, W(Y) = wY, W(R) = wY - 1`:
   - `wdeg wY (contactDeriv F) + 1 ≤ wdeg wY F` whenever `contactDeriv F ≠ 0`,
   - hence over any domain, for `F ≠ 0`, `F ∣ contactDeriv F ↔ contactDeriv F = 0`!
3. Exact parity-disjoint direct-sum characterization of
   `K_W(s) = { Q ∈ ker(D) : deg_R(Q) ≤ s ∧ wdeg wY Q ≤ W }`
   with exact cardinality `varsKerDExact wY W s` and convex rational upper bound `varsKerDUpperQ`.
4. Exact local vanishing rank `rankKerD m s` and concavity of `rankKerD m s - rankKerD (m - k) (s - d)` in `k`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401ContactKerD

open Polynomial
open scoped BigOperators

/-! ### Exact combinatorial dimension and rank formulas -/

/-- Exact rank of `Φ_m : K(s) → F[t, w, R] / (t, w)^m` at one point. -/
def rankKerD (m s : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (min (s + 1) m),
    let mq := m - q
    mq * (mq + 1) / 2
      + (if q + 1 ≤ s then mq * (mq + 1) / 2 else 0)
      + (if q + 2 ≤ s then (s - 1 - q) * mq else 0)

/-- Exact dimension of `K_W(s) = { Q ∈ ker(D) : deg_R(Q) ≤ s ∧ W(Q) ≤ W }`. -/
def varsKerDExact (wY W s : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (s + 1),
    ∑ r ∈ Finset.range 2,
      if k + r ≤ s then
        let cost := k * (wY - 1) + r * wY
        if cost ≤ W then
          let rem0 := W - cost
          let bmax := rem0 / (2 * wY)
          let c0 := rem0 / 2 + 1
          (bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2
        else 0
      else 0

/-- Exact rational upper bound on `varsKerDExact wY ⌊W_q⌋ s`, convex and monotone in `W_q`. -/
def varsKerDUpperQ (wY : ℕ) (W_q : ℚ) (s : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (s + 1),
    ∑ r ∈ Finset.range 2,
      if k + r ≤ s then
        let u := W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ)
        let u1 := max 0 (u + (wY : ℚ))
        let u0 := max 0 u
        u1 * u1 / (8 * (wY : ℚ)) + u0 / (2 * (wY : ℚ)) + 1
      else 0

/-- Exact arithmetic sum for one `(k, r)` parity block of `K_W(s)`:
`∑_{b=0}^{⌊rem/(2 wY)⌋} (⌊(rem - 2 b wY)/2⌋ + 1) = (bmax + 1)(⌊rem/2⌋ + 1) - wY·bmax(bmax + 1)/2`. -/
lemma sum_parity_block_eq (wY rem : ℕ) (hwY : 0 < wY) :
    let bmax := rem / (2 * wY)
    let c0 := rem / 2 + 1
    ∑ b ∈ Finset.range (bmax + 1), ((rem - 2 * b * wY) / 2 + 1) =
      (bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2 := by
  intro bmax c0
  have hterm : ∀ b ∈ Finset.range (bmax + 1),
      (rem - 2 * b * wY) / 2 + 1 = c0 - b * wY := by
    intro b hb
    have hble : b ≤ bmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hmul : 2 * b * wY ≤ rem := by
      have h1 : b * (2 * wY) ≤ rem / (2 * wY) * (2 * wY) := Nat.mul_le_mul_right _ hble
      have h2 : rem / (2 * wY) * (2 * wY) ≤ rem := Nat.div_mul_le_self rem (2 * wY)
      linarith
    have hsub : (rem - 2 * b * wY) / 2 = rem / 2 - b * wY := by
      have : 2 * b * wY = 2 * (b * wY) := by ring
      rw [this]
      omega
    have hle2 : b * wY ≤ rem / 2 := by
      have : 2 * (b * wY) ≤ rem := by linarith
      omega
    dsimp [c0]; omega
  rw [Finset.sum_congr rfl hterm]
  -- Cast to ℤ to avoid Nat subtraction pain!
  have hle_tot : wY * bmax * (bmax + 1) / 2 ≤ (bmax + 1) * c0 := by
    have h1 : bmax * wY ≤ rem / 2 := by
      have h0 : 2 * (bmax * wY) ≤ rem := by
        have := Nat.div_mul_le_self rem (2 * wY)
        dsimp [bmax] at *; linarith
      omega
    have h2 : wY * bmax * (bmax + 1) / 2 ≤ bmax * wY * (bmax + 1) := by
      have : wY * bmax * (bmax + 1) = bmax * wY * (bmax + 1) := by ring
      rw [this]
      exact Nat.div_le_self _ 2
    have h3 : bmax * wY * (bmax + 1) ≤ (bmax + 1) * c0 := by
      dsimp [c0]
      nlinarith
    omega
  have hsum_int : ∀ n : ℕ, n ≤ bmax + 1 →
      (∑ b ∈ Finset.range n, ((c0 - b * wY : ℕ) : ℤ)) =
        (n : ℤ) * c0 - (wY : ℤ) * ((n * (n - 1) / 2 : ℕ) : ℤ) := by
    intro n hn
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        have hmle : m * wY ≤ c0 := by
          have hmb : m ≤ bmax := by omega
          have h0 : 2 * (bmax * wY) ≤ rem := by
            have := Nat.div_mul_le_self rem (2 * wY)
            dsimp [bmax] at *; linarith
          have hmw : m * wY ≤ bmax * wY := Nat.mul_le_mul_right wY hmb
          dsimp [c0]; omega
        have htri : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
          cases m with
          | zero => simp
          | succ k =>
              simp only [Nat.add_sub_cancel]
              rw [show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring]
              omega
        rw [Nat.add_sub_cancel, htri, Nat.cast_sub hmle]
        push_cast
        ring
  have hdiv_eq : ((wY * bmax * (bmax + 1) / 2 : ℕ) : ℤ) =
      (wY : ℤ) * (((bmax + 1) * bmax / 2 : ℕ) : ℤ) := by
    have h1 : 2 ∣ (bmax + 1) * bmax := by
      rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self bmax)
    have h2 : wY * bmax * (bmax + 1) / 2 = wY * ((bmax + 1) * bmax / 2) := by
      rw [show wY * bmax * (bmax + 1) = wY * ((bmax + 1) * bmax) by ring]
      exact Nat.mul_div_assoc wY h1
    rw [h2]; push_cast; rfl
  have hZ : ((∑ b ∈ Finset.range (bmax + 1), (c0 - b * wY) : ℕ) : ℤ) =
      (((bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2 : ℕ) : ℤ) := by
    rw [Nat.cast_sum, hsum_int (bmax + 1) le_rfl, Nat.add_sub_cancel, Nat.cast_sub hle_tot, hdiv_eq]
    push_cast; ring
  exact_mod_cast hZ

/-- Algebraic upper bound for a single parity block:
`varsKerDExact_block(rem) ≤ (rem + wY)^2 / (8 wY) + rem / (2 wY) + 1` for all `rem ∈ ℕ`! -/
lemma parity_block_le_upperQ (wY rem : ℕ) (hwY : 0 < wY) :
    let bmax := rem / (2 * wY)
    let c0 := rem / 2 + 1
    (((bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2 : ℕ) : ℚ) ≤
      ((rem : ℚ) + wY) ^ 2 / (8 * wY) + (rem : ℚ) / (2 * wY) + 1 := by
  intro bmax c0
  have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
  have hdiv : 2 * wY * bmax + rem % (2 * wY) = rem := Nat.div_add_mod rem (2 * wY)
  have hmod_lt : rem % (2 * wY) < 2 * wY := Nat.mod_lt rem (by omega)
  have hle_tot : wY * bmax * (bmax + 1) / 2 ≤ (bmax + 1) * c0 := by
    have h1 : bmax * wY ≤ rem / 2 := by
      have : 2 * (bmax * wY) ≤ rem := by
        rw [show 2 * (bmax * wY) = 2 * wY * bmax by ring]
        exact Nat.mul_div_le rem (2 * wY)
      omega
    have h2 : wY * bmax * (bmax + 1) / 2 ≤ bmax * wY * (bmax + 1) := by
      rw [show wY * bmax * (bmax + 1) = bmax * wY * (bmax + 1) by ring]
      exact Nat.div_le_self _ 2
    dsimp [c0]; nlinarith
  have heven : 2 ∣ wY * bmax * (bmax + 1) := by
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self bmax
    refine ⟨wY * t, ?_⟩
    calc wY * bmax * (bmax + 1) = wY * (bmax * (bmax + 1)) := by ring
      _ = wY * (t + t) := by rw [ht]
      _ = 2 * (wY * t) := by ring
  have hcast : (((bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2 : ℕ) : ℚ) =
      ((bmax : ℚ) + 1) * (c0 : ℚ) - (wY : ℚ) * (bmax : ℚ) * ((bmax : ℚ) + 1) / 2 := by
    rw [Nat.cast_sub hle_tot]
    have hdivQ : ((wY * bmax * (bmax + 1) / 2 : ℕ) : ℚ) =
        (wY : ℚ) * (bmax : ℚ) * ((bmax : ℚ) + 1) / 2 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk, Nat.mul_div_right _ (by norm_num)]
      have hkQ : (2 : ℚ) * (k : ℚ) = (wY : ℚ) * (bmax : ℚ) * ((bmax : ℚ) + 1) := by
        exact_mod_cast hk.symm
      linarith
    rw [hdivQ]; push_cast; ring
  rw [hcast]
  -- Let r = rem - 2 * wY * bmax ∈ [0, 2 wY); note c0 ≤ rem / 2 + 1 and bmax ≤ rem / (2 wY).
  set r : ℚ := (rem : ℚ) - 2 * (wY : ℚ) * (bmax : ℚ)
  have hr_lo : 0 ≤ r := by
    have : (2 * wY * bmax : ℕ) ≤ rem := by omega
    have : (2 : ℚ) * wY * bmax ≤ rem := by exact_mod_cast this
    dsimp [r]; linarith
  have hc0_le : (c0 : ℚ) ≤ (rem : ℚ) / 2 + 1 := by
    have : 2 * (rem / 2) ≤ rem := Nat.mul_div_le rem 2
    have hQ : (2 : ℚ) * ((rem / 2 : ℕ) : ℚ) ≤ rem := by exact_mod_cast this
    dsimp [c0]; push_cast; linarith
  have hbmax_le : (bmax : ℚ) ≤ (rem : ℚ) / (2 * wY) := by
    rw [le_div_iff₀ (by positivity)]
    have : (2 * wY * bmax : ℕ) ≤ rem := by omega
    have hQ : (2 : ℚ) * wY * bmax ≤ rem := by exact_mod_cast this
    linarith
  -- Key quadratic identity:
  --   ((rem + wY)^2 / (8 wY) + rem / (2 wY) + 1) - ((bmax + 1)(rem/2 + 1) - wY bmax (bmax + 1) / 2)
  --   = (r - wY)^2 / (8 wY) + (rem / (2 wY) - bmax) ≥ 0!!
  have hident :
      ((rem : ℚ) + wY) ^ 2 / (8 * wY) + (rem : ℚ) / (2 * wY) + 1 -
        (((bmax : ℚ) + 1) * ((rem : ℚ) / 2 + 1) - (wY : ℚ) * (bmax : ℚ) * ((bmax : ℚ) + 1) / 2) =
      (r - (wY : ℚ)) ^ 2 / (8 * (wY : ℚ)) + ((rem : ℚ) / (2 * (wY : ℚ)) - (bmax : ℚ)) := by
    dsimp [r]
    field_simp
    ring
  have h1 : ((bmax : ℚ) + 1) * (c0 : ℚ) ≤ ((bmax : ℚ) + 1) * ((rem : ℚ) / 2 + 1) :=
    mul_le_mul_of_nonneg_left hc0_le (by positivity)
  have hsq : 0 ≤ (r - (wY : ℚ)) ^ 2 / (8 * (wY : ℚ)) := by positivity
  linarith

/-- Global upper bound: for any `W : ℕ` and `W_q : ℚ` with `(W : ℚ) ≤ W_q`,
`(varsKerDExact wY W s : ℚ) ≤ varsKerDUpperQ wY W_q s`. -/
theorem varsKerDExact_le_upperQ (wY W s : ℕ) (W_q : ℚ) (hwY : 0 < wY) (hW : (W : ℚ) ≤ W_q) :
    (varsKerDExact wY W s : ℚ) ≤ varsKerDUpperQ wY W_q s := by
  unfold varsKerDExact varsKerDUpperQ
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro r _
  split_ifs with hkr
  · by_cases hcost : k * (wY - 1) + r * wY ≤ W
    · simp only [hcost, ↓reduceIte]
      have hblk := parity_block_le_upperQ wY (W - (k * (wY - 1) + r * wY)) hwY
      dsimp only at hblk
      set cost := k * (wY - 1) + r * wY
      set u := W_q - (cost : ℚ)
      have hrem_le : ((W - cost : ℕ) : ℚ) ≤ u := by
        rw [Nat.cast_sub hcost]; dsimp [u]; linarith
      have hrem_nn : (0 : ℚ) ≤ ((W - cost : ℕ) : ℚ) := Nat.cast_nonneg _
      have hu0 : ((W - cost : ℕ) : ℚ) ≤ max 0 u := le_max_of_le_right hrem_le
      have hu1 : ((W - cost : ℕ) : ℚ) + wY ≤ max 0 (u + wY) :=
        le_max_of_le_right (by linarith)
      have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
      have hsq : (((W - cost : ℕ) : ℚ) + wY) ^ 2 ≤ (max 0 (u + wY)) ^ 2 := by
        nlinarith
      have hdiv1 : (((W - cost : ℕ) : ℚ) + wY) ^ 2 / (8 * wY) ≤
          max 0 (u + wY) * max 0 (u + wY) / (8 * wY) := by
        rw [← sq]; exact div_le_div_of_nonneg_right hsq (by positivity)
      have hdiv2 : ((W - cost : ℕ) : ℚ) / (2 * wY) ≤ max 0 u / (2 * wY) :=
        div_le_div_of_nonneg_right hu0 (by positivity)
      linarith
    · simp only [hcost, ↓reduceIte, Nat.cast_zero]
      have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
      have h1 : 0 ≤ max (0 : ℚ) (W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ) + wY) *
          max 0 (W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ) + wY) / (8 * wY) := by positivity
      have h2 : 0 ≤ max (0 : ℚ) (W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ)) / (2 * wY) := by positivity
      linarith
  · simp

theorem varsKerDUpperQ_mono (wY s : ℕ) (hwY : 0 < wY) {a b : ℚ} (hab : a ≤ b) :
    varsKerDUpperQ wY a s ≤ varsKerDUpperQ wY b s := by
  have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
  unfold varsKerDUpperQ
  apply Finset.sum_le_sum; intro k _
  apply Finset.sum_le_sum; intro r _
  split_ifs with hkr
  · dsimp only
    set c : ℚ := ((k * (wY - 1) + r * wY : ℕ) : ℚ)
    have hm0 : max 0 (a - c) ≤ max 0 (b - c) := max_le_max le_rfl (by linarith)
    have hm1 : max 0 (a - c + wY) ≤ max 0 (b - c + wY) := max_le_max le_rfl (by linarith)
    have hnn : 0 ≤ max 0 (a - c + wY) := le_max_left _ _
    have hsq : max 0 (a - c + wY) * max 0 (a - c + wY) ≤
        max 0 (b - c + wY) * max 0 (b - c + wY) := by nlinarith
    have hd1 : max 0 (a - c + wY) * max 0 (a - c + wY) / (8 * wY) ≤
        max 0 (b - c + wY) * max 0 (b - c + wY) / (8 * wY) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have hd2 : max 0 (a - c) / (2 * wY) ≤ max 0 (b - c) / (2 * wY) :=
      div_le_div_of_nonneg_right hm0 (by positivity)
    linarith
  · exact le_rfl

theorem varsKerDUpperQ_convex (wY s : ℕ) (hwY : 0 < wY) (a b t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    varsKerDUpperQ wY ((1 - t) * a + t * b) s ≤
      (1 - t) * varsKerDUpperQ wY a s + t * varsKerDUpperQ wY b s := by
  have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
  set t1 := 1 - t
  have ht10 : 0 ≤ t1 := by dsimp [t1]; linarith
  have ht12 : t1 + t = 1 := by dsimp [t1]; ring
  unfold varsKerDUpperQ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro k _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro r _
  split_ifs with hkr
  · dsimp only
    set c : ℚ := ((k * (wY - 1) + r * wY : ℕ) : ℚ)
    have hmax_conv : ∀ (u v : ℚ), max 0 (t1 * u + t * v) ≤ t1 * max 0 u + t * max 0 v := by
      intro u v; apply max_le
      · positivity
      · have := mul_le_mul_of_nonneg_left (le_max_right 0 u) ht10
        have := mul_le_mul_of_nonneg_left (le_max_right 0 v) ht0
        linarith
    have hsq_conv : ∀ (p q : ℚ), (t1 * p + t * q) ^ 2 ≤ t1 * p ^ 2 + t * q ^ 2 := by
      intro p q
      have hdiff : t1 * p ^ 2 + t * q ^ 2 - (t1 * p + t * q) ^ 2 = t1 * t * (p - q) ^ 2 := by
        dsimp [t1]; ring
      have : 0 ≤ t1 * t * (p - q) ^ 2 := by positivity
      linarith
    have hu0 : t1 * a + t * b - c = t1 * (a - c) + t * (b - c) := by dsimp [t1]; ring
    have hu1 : t1 * a + t * b - c + wY = t1 * (a - c + wY) + t * (b - c + wY) := by dsimp [t1]; ring
    have hlin0 : max 0 (t1 * a + t * b - c) ≤ t1 * max 0 (a - c) + t * max 0 (b - c) := by
      rw [hu0]; exact hmax_conv _ _
    have hlin1 : max 0 (t1 * a + t * b - c + wY) ≤ t1 * max 0 (a - c + wY) + t * max 0 (b - c + wY) := by
      rw [hu1]; exact hmax_conv _ _
    have hsq1 : max 0 (t1 * a + t * b - c + wY) * max 0 (t1 * a + t * b - c + wY) ≤
        t1 * (max 0 (a - c + wY) * max 0 (a - c + wY)) +
        t * (max 0 (b - c + wY) * max 0 (b - c + wY)) := by
      have hm1 : 0 ≤ max 0 (t1 * a + t * b - c + wY) := le_max_left _ _
      have hstep : max 0 (t1 * a + t * b - c + wY) ^ 2 ≤ (t1 * max 0 (a - c + wY) + t * max 0 (b - c + wY)) ^ 2 := by
        nlinarith
      have hstep2 := hsq_conv (max 0 (a - c + wY)) (max 0 (b - c + wY))
      nlinarith
    have hd1 : max 0 (t1 * a + t * b - c + wY) * max 0 (t1 * a + t * b - c + wY) / (8 * wY) ≤
        t1 * (max 0 (a - c + wY) * max 0 (a - c + wY) / (8 * wY)) +
        t * (max 0 (b - c + wY) * max 0 (b - c + wY) / (8 * wY)) := by
      have := div_le_div_of_nonneg_right hsq1 (by positivity : (0 : ℚ) ≤ 8 * wY)
      linarith [show (t1 * (max 0 (a - c + wY) * max 0 (a - c + wY)) +
          t * (max 0 (b - c + wY) * max 0 (b - c + wY))) / (8 * wY) =
          t1 * (max 0 (a - c + wY) * max 0 (a - c + wY) / (8 * wY)) +
          t * (max 0 (b - c + wY) * max 0 (b - c + wY) / (8 * wY)) by ring]
    have hd2 : max 0 (t1 * a + t * b - c) / (2 * wY) ≤
        t1 * (max 0 (a - c) / (2 * wY)) + t * (max 0 (b - c) / (2 * wY)) := by
      have := div_le_div_of_nonneg_right hlin0 (by positivity : (0 : ℚ) ≤ 2 * wY)
      linarith [show (t1 * max 0 (a - c) + t * max 0 (b - c)) / (2 * wY) =
          t1 * (max 0 (a - c) / (2 * wY)) + t * (max 0 (b - c) / (2 * wY)) by ring]
    nlinarith [ht12]
  · simp

/-- `varsKerDUpperQ` is convex in `W_q`, so on `[c_lo, c_hi]` it is bounded above by the secant! -/
theorem varsKerDUpperQ_secant (wY s : ℕ) (hwY : 0 < wY) {a b x : ℚ}
    (hax : a ≤ x) (hxb : x ≤ b) (hab : a < b) :
    varsKerDUpperQ wY x s ≤
      ((b - x) / (b - a)) * varsKerDUpperQ wY a s +
      ((x - a) / (b - a)) * varsKerDUpperQ wY b s := by
  have hwQ : (0 : ℚ) < wY := by exact_mod_cast hwY
  have hba : (0 : ℚ) < b - a := by linarith
  set t1 := (b - x) / (b - a)
  set t2 := (x - a) / (b - a)
  have ht1 : 0 ≤ t1 := div_nonneg (by linarith) hba.le
  have ht2 : 0 ≤ t2 := div_nonneg (by linarith) hba.le
  have ht12 : t1 + t2 = 1 := by dsimp [t1, t2]; field_simp; ring
  have hx : x = t1 * a + t2 * b := by dsimp [t1, t2]; field_simp; ring
  unfold varsKerDUpperQ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  split_ifs with hkr
  · set c : ℚ := ((k * (wY - 1) + r * wY : ℕ) : ℚ)
    -- Convexity of f(u) = max(0, u)^2 and g(u) = max(0, u)
    have hmax_conv : ∀ (u v : ℚ), max 0 (t1 * u + t2 * v) ≤ t1 * max 0 u + t2 * max 0 v := by
      intro u v
      apply max_le
      · positivity
      · have := mul_le_mul_of_nonneg_left (le_max_right 0 u) ht1
        have := mul_le_mul_of_nonneg_left (le_max_right 0 v) ht2
        linarith
    have hsq_conv : ∀ (p q : ℚ), (t1 * p + t2 * q) ^ 2 ≤ t1 * p ^ 2 + t2 * q ^ 2 := by
      intro p q
      have hdiff : t1 * p ^ 2 + t2 * q ^ 2 - (t1 * p + t2 * q) ^ 2 = t1 * t2 * (p - q) ^ 2 := by
        have : t1 * (1 - t1) = t1 * t2 := by rw [show 1 - t1 = t2 by linarith]
        have : t2 * (1 - t2) = t1 * t2 := by rw [show 1 - t2 = t1 by linarith]; ring
        nlinarith [ht12]
      have : 0 ≤ t1 * t2 * (p - q) ^ 2 := by positivity
      linarith
    have hu0 : x - c = t1 * (a - c) + t2 * (b - c) := by
      calc x - c = t1 * a + t2 * b - (t1 + t2) * c := by rw [hx, ht12, one_mul]
        _ = t1 * (a - c) + t2 * (b - c) := by ring
    have hu1 : x - c + wY = t1 * (a - c + wY) + t2 * (b - c + wY) := by
      calc x - c + wY = t1 * a + t2 * b - (t1 + t2) * c + (t1 + t2) * wY := by rw [hx, ht12, one_mul, one_mul]
        _ = t1 * (a - c + wY) + t2 * (b - c + wY) := by ring
    have hlin0 : max 0 (x - c) ≤ t1 * max 0 (a - c) + t2 * max 0 (b - c) := by
      rw [hu0]; exact hmax_conv _ _
    have hlin1 : max 0 (x - c + wY) ≤ t1 * max 0 (a - c + wY) + t2 * max 0 (b - c + wY) := by
      rw [hu1]; exact hmax_conv _ _
    have hsq1 : max 0 (x - c + wY) * max 0 (x - c + wY) ≤
        t1 * (max 0 (a - c + wY) * max 0 (a - c + wY)) +
        t2 * (max 0 (b - c + wY) * max 0 (b - c + wY)) := by
      have hm1 : 0 ≤ max 0 (x - c + wY) := le_max_left _ _
      have hstep : max 0 (x - c + wY) ^ 2 ≤ (t1 * max 0 (a - c + wY) + t2 * max 0 (b - c + wY)) ^ 2 := by
        nlinarith
      have hstep2 := hsq_conv (max 0 (a - c + wY)) (max 0 (b - c + wY))
      nlinarith
    have hd1 : max 0 (x - c + wY) * max 0 (x - c + wY) / (8 * wY) ≤
        t1 * (max 0 (a - c + wY) * max 0 (a - c + wY) / (8 * wY)) +
        t2 * (max 0 (b - c + wY) * max 0 (b - c + wY) / (8 * wY)) := by
      have := div_le_div_of_nonneg_right hsq1 (by positivity : (0 : ℚ) ≤ 8 * wY)
      linarith [show (t1 * (max 0 (a - c + wY) * max 0 (a - c + wY)) +
          t2 * (max 0 (b - c + wY) * max 0 (b - c + wY))) / (8 * wY) =
          t1 * (max 0 (a - c + wY) * max 0 (a - c + wY) / (8 * wY)) +
          t2 * (max 0 (b - c + wY) * max 0 (b - c + wY) / (8 * wY)) by ring]
    have hd2 : max 0 (x - c) / (2 * wY) ≤
        t1 * (max 0 (a - c) / (2 * wY)) + t2 * (max 0 (b - c) / (2 * wY)) := by
      have := div_le_div_of_nonneg_right hlin0 (by positivity : (0 : ℚ) ≤ 2 * wY)
      linarith [show (t1 * max 0 (a - c) + t2 * max 0 (b - c)) / (2 * wY) =
          t1 * (max 0 (a - c) / (2 * wY)) + t2 * (max 0 (b - c) / (2 * wY)) by ring]
    nlinarith [ht12]
  · simp

/-- Single summand of `rankKerD m s` at index `q` (automatically `0` for `q ≥ m`). -/
def rankKerDTerm (m s q : ℕ) : ℕ :=
  let mq := m - q
  mq * (mq + 1) / 2
    + (if q + 1 ≤ s then mq * (mq + 1) / 2 else 0)
    + (if q + 2 ≤ s then (s - 1 - q) * mq else 0)

lemma rankKerDTerm_eq_zero_of_le {m s q : ℕ} (hq : m ≤ q) : rankKerDTerm m s q = 0 := by
  unfold rankKerDTerm
  have : m - q = 0 := Nat.sub_eq_zero_of_le hq
  simp [this]

lemma rankKerD_eq_sum_range_succ (m s : ℕ) :
    rankKerD m s = ∑ q ∈ Finset.range (s + 1), rankKerDTerm m s q := by
  unfold rankKerD
  apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left (s + 1) m))
  intro q hq hnot
  have hm : m ≤ q := by
    rw [Finset.mem_range] at hq hnot
    omega
  exact rankKerDTerm_eq_zero_of_le hm

lemma rankKerDTerm_succ (n s q : ℕ) :
    rankKerDTerm (n + 1) s q = rankKerDTerm n s q +
      if q ≤ n then
        (n + 1 - q)
          + (if q + 1 ≤ s then n + 1 - q else 0)
          + (if q + 2 ≤ s then s - 1 - q else 0)
      else 0 := by
  unfold rankKerDTerm
  by_cases hq : q ≤ n
  · simp only [hq, ↓reduceIte]
    have hsub : n + 1 - q = (n - q) + 1 := by omega
    rw [hsub]
    set k := n - q
    have htri : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
      have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
      omega
    rw [htri]
    split_ifs <;> ring_nf
  · have h1 : n + 1 - q = 0 := by omega
    have h2 : n - q = 0 := by omega
    simp [hq, h1, h2]

/-- `rankKerD m s` is convex in `m` (non-decreasing first differences in `m`), so
`rankKerD m s - rankKerD (m - k) (s - d)` is CONCAVE in `k`! -/
lemma rankKerD_diff_mono (s : ℕ) {n1 n2 : ℕ} (h : n1 ≤ n2) :
    rankKerD (n1 + 1) s - rankKerD n1 s ≤ rankKerD (n2 + 1) s - rankKerD n2 s := by
  have hstep : ∀ n : ℕ, rankKerD (n + 1) s - rankKerD n s =
      ∑ q ∈ Finset.range (s + 1),
        if q ≤ n then
          (n + 1 - q) + (if q + 1 ≤ s then n + 1 - q else 0) +
            (if q + 2 ≤ s then s - 1 - q else 0)
        else 0 := by
    intro n
    rw [rankKerD_eq_sum_range_succ (n + 1), rankKerD_eq_sum_range_succ n]
    simp_rw [rankKerDTerm_succ, Finset.sum_add_distrib, Nat.add_sub_cancel_left]
  rw [hstep n1, hstep n2]
  apply Finset.sum_le_sum
  intro q _
  split_ifs <;> omega

lemma rankKerD_mono_left (s : ℕ) {n1 n2 : ℕ} (h : n1 ≤ n2) :
    rankKerD n1 s ≤ rankKerD n2 s := by
  rw [rankKerD_eq_sum_range_succ n1, rankKerD_eq_sum_range_succ n2]
  apply Finset.sum_le_sum
  intro q _
  unfold rankKerDTerm
  dsimp only
  have hsub : n1 - q ≤ n2 - q := Nat.sub_le_sub_right h q
  have htri : (n1 - q) * (n1 - q + 1) / 2 ≤ (n2 - q) * (n2 - q + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul hsub (Nat.add_le_add_right hsub 1))
  have hlin : (s - 1 - q) * (n1 - q) ≤ (s - 1 - q) * (n2 - q) := Nat.mul_le_mul_left _ hsub
  split_ifs <;> omega

lemma rankKerD_mono_right (m : ℕ) {s1 s2 : ℕ} (h : s1 ≤ s2) :
    rankKerD m s1 ≤ rankKerD m s2 := by
  rw [rankKerD_eq_sum_range_succ m s1, rankKerD_eq_sum_range_succ m s2]
  calc ∑ q ∈ Finset.range (s1 + 1), rankKerDTerm m s1 q
      ≤ ∑ q ∈ Finset.range (s1 + 1), rankKerDTerm m s2 q := by
        apply Finset.sum_le_sum
        intro q _
        unfold rankKerDTerm
        dsimp only
        split_ifs <;> try omega
        · have : s1 - 1 - q ≤ s2 - 1 - q := by omega
          have := Nat.mul_le_mul_right (m - q) this
          omega
    _ ≤ ∑ q ∈ Finset.range (s2 + 1), rankKerDTerm m s2 q :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- Concavity of `rankDiff m s d k := rankKerD m s - rankKerD (m - k) (s - d)`:
for all `k ≥ K0 ≥ 1`, `rankDiff(k) ≤ rankDiff(K0) + (k - K0) * (rankDiff(K0) - rankDiff(K0 - 1))`! -/
theorem rankKerD_diff_le_linear_tail (m s d K0 k : ℕ) (hK0 : 1 ≤ K0) (hk : K0 ≤ k) :
    (rankKerD m s - rankKerD (m - k) (s - d) : ℕ) ≤
      (rankKerD m s - rankKerD (m - K0) (s - d)) +
        (k - K0) * ((rankKerD m s - rankKerD (m - K0) (s - d)) -
                    (rankKerD m s - rankKerD (m - (K0 - 1)) (s - d))) := by
  have hle_m : ∀ j, rankKerD (m - j) (s - d) ≤ rankKerD m s := fun j =>
    (rankKerD_mono_left (s - d) (Nat.sub_le m j)).trans (rankKerD_mono_right m (Nat.sub_le s d))
  have hstep : ∀ t : ℕ,
      rankKerD (m - K0) (s - d) - rankKerD (m - (K0 + t)) (s - d) ≤
        t * (rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d)) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hinc : rankKerD (m - (K0 + t)) (s - d) - rankKerD (m - (K0 + t + 1)) (s - d) ≤
            rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d) := by
          by_cases hlt : K0 + t < m
          · have heq1 : m - (K0 + t) = (m - (K0 + t + 1)) + 1 := by omega
            have heq2 : m - (K0 - 1) = (m - K0) + 1 := by omega
            rw [heq1, heq2]
            exact rankKerD_diff_mono (s - d) (by omega)
          · have h0 : m - (K0 + t) = 0 := by omega
            have h0' : m - (K0 + t + 1) = 0 := by omega
            rw [h0, h0', Nat.sub_self]
            exact Nat.zero_le _
        have hmono1 : rankKerD (m - (K0 + t + 1)) (s - d) ≤ rankKerD (m - (K0 + t)) (s - d) :=
          rankKerD_mono_left (s - d) (by omega)
        have hmono2 : rankKerD (m - (K0 + t)) (s - d) ≤ rankKerD (m - K0) (s - d) :=
          rankKerD_mono_left (s - d) (by omega)
        have hrew : K0 + (t + 1) = K0 + t + 1 := by omega
        rw [hrew]
        have : (t + 1) * (rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d)) =
            t * (rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d)) +
            (rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d)) := by ring
        omega
  have hkt := hstep (k - K0)
  rw [Nat.add_sub_of_le hk] at hkt
  have h1 := hle_m k
  have h2 := hle_m K0
  have h3 := hle_m (K0 - 1)
  have h4 : rankKerD (m - k) (s - d) ≤ rankKerD (m - K0) (s - d) :=
    rankKerD_mono_left (s - d) (Nat.sub_le_sub_left hk m)
  have h5 : rankKerD (m - K0) (s - d) ≤ rankKerD (m - (K0 - 1)) (s - d) :=
    rankKerD_mono_left (s - d) (Nat.sub_le_sub_left (by omega) m)
  have hdiff_eq : (rankKerD m s - rankKerD (m - K0) (s - d)) -
      (rankKerD m s - rankKerD (m - (K0 - 1)) (s - d)) =
      rankKerD (m - (K0 - 1)) (s - d) - rankKerD (m - K0) (s - d) := by omega
  rw [hdiff_eq]
  omega

/-! ### Contact polynomials `A[X][Y][R]`, derivation `D = ∂_X + R ∂_Y`, and weighted degree -/

section ContactRing

variable {A : Type*} [CommRing A]

/-- Bivariate polynomials `A[X][Y]` (outer `Y`, inner `X`). -/
abbrev BiPoly (A : Type*) [CommRing A] := Polynomial (Polynomial A)

/-- Contact polynomials `A[X][Y][R]` (outer `R`, middle `Y`, inner `X`). -/
abbrev ContactPoly (A : Type*) [CommRing A] := Polynomial (BiPoly A)

/-- Partial derivative `∂_X` on `A[X][Y]`. -/
noncomputable def dXBi (g : BiPoly A) : BiPoly A :=
  ∑ j ∈ g.support, monomial j (g.coeff j).derivative

lemma coeff_finset_sum {ι : Type*} {R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  simpa using map_sum (Polynomial.lcoeff R n) f s

lemma finset_sum_coeff {ι : Type*} {R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n :=
  coeff_finset_sum s f n

lemma coeff_dXBi (g : BiPoly A) (j : ℕ) : (dXBi g).coeff j = (g.coeff j).derivative := by
  classical
  unfold dXBi
  rw [coeff_finset_sum]
  by_cases hj : j ∈ g.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hne; simp [hne]
    · intro hnot; exact absurd hj hnot
  · have h0 : g.coeff j = 0 := by simpa [mem_support_iff] using hj
    rw [h0, derivative_zero]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : k ≠ j := fun h => hj (h ▸ hk)
    simp [hne]

lemma dXBi_add (f g : BiPoly A) : dXBi (f + g) = dXBi f + dXBi g := by
  ext j i; simp [coeff_dXBi]

lemma dXBi_mul (f g : BiPoly A) : dXBi (f * g) = dXBi f * g + f * dXBi g := by
  apply Polynomial.ext; intro j
  simp only [coeff_dXBi, coeff_add, coeff_mul, derivative_sum, derivative_mul]
  rw [Finset.sum_add_distrib]

/-- Contact derivation `D = ∂_X + R ∂_Y` on `A[X][Y][R]`. -/
noncomputable def contactDeriv (Q : ContactPoly A) : ContactPoly A :=
  (∑ k ∈ Q.support, monomial k (dXBi (Q.coeff k))) +
  (∑ k ∈ Q.support, monomial (k + 1) (Q.coeff k).derivative)

lemma coeff_contactDeriv (Q : ContactPoly A) (k : ℕ) :
    (contactDeriv Q).coeff k =
      dXBi (Q.coeff k) + (if k = 0 then 0 else (Q.coeff (k - 1)).derivative) := by
  classical
  unfold contactDeriv
  rw [coeff_add, coeff_finset_sum, coeff_finset_sum]
  congr 1
  · by_cases hk : k ∈ Q.support
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hne; simp [hne]
      · intro hnot; exact absurd hk hnot
    · have h0 : Q.coeff k = 0 := by simpa [mem_support_iff] using hk
      rw [h0]
      have hd0 : dXBi (0 : BiPoly A) = 0 := by ext j i; simp [coeff_dXBi]
      rw [hd0]
      apply Finset.sum_eq_zero
      intro j hj
      have hne : j ≠ k := fun h => hk (h ▸ hj)
      simp [hne]
  · cases k with
    | zero =>
        simp
    | succ k' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        by_cases hk : k' ∈ Q.support
        · rw [Finset.sum_eq_single k']
          · simp
          · intro j _ hne; simp [hne]
          · intro hnot; exact absurd hk hnot
        · have h0 : Q.coeff k' = 0 := by simpa [mem_support_iff] using hk
          rw [h0, derivative_zero]
          apply Finset.sum_eq_zero
          intro j hj
          have hne : j ≠ k' := fun h => hk (h ▸ hj)
          simp [hne]

lemma contactDeriv_add (P Q : ContactPoly A) :
    contactDeriv (P + Q) = contactDeriv P + contactDeriv Q := by
  ext k j i
  simp only [coeff_contactDeriv, coeff_add, dXBi_add, derivative_add]
  split_ifs <;> (simp; try ring)

lemma contactDeriv_mul (P Q : ContactPoly A) :
    contactDeriv (P * Q) = contactDeriv P * Q + P * contactDeriv Q := by
  apply Polynomial.ext; intro k
  simp only [coeff_contactDeriv, coeff_add, coeff_mul]
  -- Split dXBi(∑ P_a Q_b) = ∑ (dXBi P_a Q_b + P_a dXBi Q_b)
  have hdX : dXBi (∑ x ∈ Finset.antidiagonal k, P.coeff x.1 * Q.coeff x.2) =
      (∑ x ∈ Finset.antidiagonal k, dXBi (P.coeff x.1) * Q.coeff x.2) +
      (∑ x ∈ Finset.antidiagonal k, P.coeff x.1 * dXBi (Q.coeff x.2)) := by
    have hlin : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → BiPoly A),
        dXBi (∑ x ∈ s, f x) = ∑ x ∈ s, dXBi (f x) := by
      intro s f
      classical
      induction s using Finset.induction_on with
      | empty => ext j i; simp [coeff_dXBi]
      | insert a s ha ih => rw [Finset.sum_insert ha, dXBi_add, ih, Finset.sum_insert ha]
    rw [hlin]
    simp_rw [dXBi_mul]
    rw [Finset.sum_add_distrib]
  rw [hdX]
  -- Handle the k = 0 vs k = k' + 1 derivative sum
  cases k with
  | zero =>
      simp [Finset.Nat.antidiagonal_zero]
  | succ k' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, derivative_sum, derivative_mul]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ x ∈ Finset.antidiagonal (k' + 1),
          (dXBi (P.coeff x.1) + if x.1 = 0 then 0 else (P.coeff (x.1 - 1)).derivative) * Q.coeff x.2 =
          (∑ x ∈ Finset.antidiagonal (k' + 1), dXBi (P.coeff x.1) * Q.coeff x.2) +
          (∑ x ∈ Finset.antidiagonal k', (P.coeff x.1).derivative * Q.coeff x.2) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.Nat.sum_antidiagonal_succ]
        simp
      have h2 : ∑ x ∈ Finset.antidiagonal (k' + 1),
          P.coeff x.1 * (dXBi (Q.coeff x.2) + if x.2 = 0 then 0 else (Q.coeff (x.2 - 1)).derivative) =
          (∑ x ∈ Finset.antidiagonal (k' + 1), P.coeff x.1 * dXBi (Q.coeff x.2)) +
          (∑ x ∈ Finset.antidiagonal k', P.coeff x.1 * (Q.coeff x.2).derivative) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.Nat.sum_antidiagonal_succ']
        simp
      rw [h1, h2]
      ring

/-- Weighted degree of `Q ∈ A[X][Y][R]` with weights `W(X) = 1, W(Y) = wY, W(R) = wY - 1`. -/
noncomputable def wdeg (wY : ℕ) (Q : ContactPoly A) : ℕ :=
  Q.support.sup fun k =>
    (Q.coeff k).support.sup fun j =>
      ((Q.coeff k).coeff j).support.sup fun i =>
        i + j * wY + k * (wY - 1)

lemma wdeg_le_iff (wY W : ℕ) (Q : ContactPoly A) :
    wdeg wY Q ≤ W ↔
      ∀ k j i, ((Q.coeff k).coeff j).coeff i ≠ 0 → i + j * wY + k * (wY - 1) ≤ W := by
  unfold wdeg
  simp only [Finset.sup_le_iff, mem_support_iff]
  constructor
  · intro h k j i hi
    have hj : (Q.coeff k).coeff j ≠ 0 := fun h0 => hi (by simp [h0])
    have hk : Q.coeff k ≠ 0 := fun h0 => hj (by simp [h0])
    exact h k hk j hj i hi
  · intro h k _ j _ i hi
    exact h k j i hi

/-- **Key 1-line degree drop of `D = ∂_X + R ∂_Y`:**
Every nonzero monomial of `D(Q)` drops weighted degree by at least `1`! -/
theorem wdeg_contactDeriv_add_one_le (wY : ℕ) (hwY : 1 ≤ wY) (Q : ContactPoly A)
    (hDQ : contactDeriv Q ≠ 0) :
    wdeg wY (contactDeriv Q) + 1 ≤ wdeg wY Q := by
  -- Show every nonzero monomial (k, j, i) of D(Q) has weight + 1 ≤ wdeg wY Q
  have hle : wdeg wY (contactDeriv Q) ≤ wdeg wY Q - 1 := by
    rw [wdeg_le_iff]
    intro k j i hne
    rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative] at hne
    by_cases h1 : ((Q.coeff k).coeff j).coeff (i + 1) * ((i : A) + 1) ≠ 0
    · have hnz : ((Q.coeff k).coeff j).coeff (i + 1) ≠ 0 := left_ne_zero_of_mul h1
      have hw := (wdeg_le_iff wY (wdeg wY Q) Q).mp le_rfl k j (i + 1) hnz
      omega
    · push Not at h1
      rw [h1, zero_add] at hne
      cases k with
      | zero => simp at hne
      | succ k' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative] at hne
          rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C] at hne
          have hnz : ((Q.coeff k').coeff (j + 1)).coeff i ≠ 0 := left_ne_zero_of_mul hne
          have hw := (wdeg_le_iff wY (wdeg wY Q) Q).mp le_rfl k' (j + 1) i hnz
          -- Check: i + (j + 1) * wY + k' * (wY - 1) = (i + j * wY + (k' + 1) * (wY - 1)) + 1!
          have : i + (j + 1) * wY + k' * (wY - 1) = i + j * wY + (k' + 1) * (wY - 1) + 1 := by
            zify [hwY]; ring
          omega
  -- Also wdeg wY Q ≥ 1 since D(Q) ≠ 0 has some nonzero monomial of weight ≤ wdeg wY Q - 1 coming from weight ≥ 1
  have hpos : 1 ≤ wdeg wY Q := by
    by_contra h0
    have hw0 : wdeg wY Q = 0 := by omega
    apply hDQ
    ext k j i
    rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative, coeff_zero]
    have hzero_ge1 : ∀ k' j' i', 1 ≤ i' + j' * wY + k' * (wY - 1) →
        ((Q.coeff k').coeff j').coeff i' = 0 := by
      intro k' j' i' hge
      by_contra hnz
      have := (wdeg_le_iff wY 0 Q).mp (by rw [hw0]) k' j' i' hnz
      omega
    have hA : ((Q.coeff k).coeff j).coeff (i + 1) = 0 := hzero_ge1 k j (i + 1) (by omega)
    rw [hA, zero_mul, zero_add]
    cases k with
    | zero => simp
    | succ k' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative]
        rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C]
        have hB : ((Q.coeff k').coeff (j + 1)).coeff i = 0 := hzero_ge1 k' (j + 1) i (by nlinarith)
        rw [hB, zero_mul, coeff_zero, coeff_zero]
  omega

/-- Over an integral domain `A`, `wdeg` is additive on nonzero products! -/
theorem wdeg_mul [IsDomain A] (wY : ℕ) {P Q : ContactPoly A} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    wdeg wY (P * Q) = wdeg wY P + wdeg wY Q := by
  -- Upper bound is immediate from coeff_mul; lower bound picks the lex-maximal top-weight monomial!
  apply le_antisymm
  · rw [wdeg_le_iff]
    intro k j i hne
    rw [coeff_mul, coeff_finset_sum, coeff_finset_sum] at hne
    obtain ⟨⟨k1, k2⟩, hk12, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [coeff_mul, coeff_finset_sum] at hne1
    obtain ⟨⟨j1, j2⟩, hj12, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
    rw [coeff_mul] at hne2
    obtain ⟨⟨i1, i2⟩, hi12, hne3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne2
    have hp1 : ((P.coeff k1).coeff j1).coeff i1 ≠ 0 := left_ne_zero_of_mul hne3
    have hq2 : ((Q.coeff k2).coeff j2).coeff i2 ≠ 0 := right_ne_zero_of_mul hne3
    have hwP := (wdeg_le_iff wY (wdeg wY P) P).mp le_rfl k1 j1 i1 hp1
    have hwQ := (wdeg_le_iff wY (wdeg wY Q) Q).mp le_rfl k2 j2 i2 hq2
    have hk := Finset.mem_antidiagonal.mp hk12
    have hj := Finset.mem_antidiagonal.mp hj12
    have hi := Finset.mem_antidiagonal.mp hi12
    have : i + j * wY + k * (wY - 1) =
        (i1 + j1 * wY + k1 * (wY - 1)) + (i2 + j2 * wY + k2 * (wY - 1)) := by
      rw [← hk, ← hj, ← hi]; ring
    omega
  · -- Pick the unique lex-maximal `(weight, k, j, i)` monomial in P and Q!
    classical
    let supp3 (F : ContactPoly A) : Finset (ℕ × ℕ × ℕ) :=
      F.support.biUnion fun k =>
        (F.coeff k).support.biUnion fun j =>
          ((F.coeff k).coeff j).support.image fun i => (k, j, i)
    have hmem3 : ∀ (F : ContactPoly A) (k j i : ℕ),
        (k, j, i) ∈ supp3 F ↔ ((F.coeff k).coeff j).coeff i ≠ 0 := by
      intro F k j i
      simp only [supp3, Finset.mem_biUnion, Finset.mem_image, mem_support_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨k', _, j', _, i', hi', rfl, rfl, rfl⟩; exact hi'
      · intro hi
        have hj : (F.coeff k).coeff j ≠ 0 := fun h => hi (by simp [h])
        have hk : F.coeff k ≠ 0 := fun h => hj (by simp [h])
        exact ⟨k, hk, j, hj, i, hi, rfl, rfl, rfl⟩
    have hne3 : ∀ (F : ContactPoly A), F ≠ 0 → (supp3 F).Nonempty := by
      intro F hF
      have hk : F.support.Nonempty := Polynomial.support_nonempty.mpr hF
      obtain ⟨k, hk'⟩ := hk
      have hj : (F.coeff k).support.Nonempty :=
        Polynomial.support_nonempty.mpr (mem_support_iff.mp hk')
      obtain ⟨j, hj'⟩ := hj
      have hi : ((F.coeff k).coeff j).support.Nonempty :=
        Polynomial.support_nonempty.mpr (mem_support_iff.mp hj')
      obtain ⟨i, hi'⟩ := hi
      exact ⟨(k, j, i), (hmem3 F k j i).mpr (mem_support_iff.mp hi')⟩
    let key (p : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
      (p.2.2 + p.2.1 * wY + p.1 * (wY - 1), p.1, p.2.1)
    have hkey_inj : ∀ p q : ℕ × ℕ × ℕ, key p = key q → p = q := by
      rintro ⟨k1, j1, i1⟩ ⟨k2, j2, i2⟩ h
      simp only [key, Prod.mk.injEq] at h
      obtain ⟨hw, rfl, rfl⟩ := h
      have : i1 = i2 := by omega
      subst this; rfl
    -- Note Prod uses Lex order? Use Prod.Lex explicitly via a linear order on ℕ × ℕ × ℕ!
    let score (p : ℕ × ℕ × ℕ) : ℕ ×ₗ ℕ ×ₗ ℕ :=
      toLex (p.2.2 + p.2.1 * wY + p.1 * (wY - 1), toLex (p.1, p.2.1))
    have hscore_add : ∀ p q : ℕ × ℕ × ℕ,
        let pq := (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)
        (pq.2.2 + pq.2.1 * wY + pq.1 * (wY - 1)) =
          (p.2.2 + p.2.1 * wY + p.1 * (wY - 1)) + (q.2.2 + q.2.1 * wY + q.1 * (wY - 1)) := by
      rintro ⟨k1, j1, i1⟩ ⟨k2, j2, i2⟩; dsimp; ring
    obtain ⟨pM, hpM_mem, hpM_max⟩ := Finset.exists_max_image (supp3 P) score (hne3 P hP)
    obtain ⟨qM, hqM_mem, hqM_max⟩ := Finset.exists_max_image (supp3 Q) score (hne3 Q hQ)
    -- Show wdeg P = wt(pM) and wdeg Q = wt(qM)
    have hwtP : wdeg wY P = pM.2.2 + pM.2.1 * wY + pM.1 * (wY - 1) := by
      apply le_antisymm
      · rw [wdeg_le_iff]
        intro k j i hne
        have hle := hpM_max (k, j, i) ((hmem3 P k j i).mpr hne)
        exact (Prod.Lex.le_iff.mp hle).elim (fun h => le_of_lt h) (fun h => h.1.le)
      · exact (wdeg_le_iff wY (wdeg wY P) P).mp le_rfl pM.1 pM.2.1 pM.2.2 ((hmem3 P _ _ _).mp hpM_mem)
    have hwtQ : wdeg wY Q = qM.2.2 + qM.2.1 * wY + qM.1 * (wY - 1) := by
      apply le_antisymm
      · rw [wdeg_le_iff]
        intro k j i hne
        have hle := hqM_max (k, j, i) ((hmem3 Q k j i).mpr hne)
        exact (Prod.Lex.le_iff.mp hle).elim (fun h => le_of_lt h) (fun h => h.1.le)
      · exact (wdeg_le_iff wY (wdeg wY Q) Q).mp le_rfl qM.1 qM.2.1 qM.2.2 ((hmem3 Q _ _ _).mp hqM_mem)
    -- The coefficient of (pM + qM) in P * Q is the single nonzero product P[pM] * Q[qM]!
    have hcoeff_ne : (((P * Q).coeff (pM.1 + qM.1)).coeff (pM.2.1 + qM.2.1)).coeff (pM.2.2 + qM.2.2) ≠ 0 := by
      have huniq : ∀ k1 k2 j1 j2 i1 i2,
          k1 + k2 = pM.1 + qM.1 → j1 + j2 = pM.2.1 + qM.2.1 → i1 + i2 = pM.2.2 + qM.2.2 →
          ((P.coeff k1).coeff j1).coeff i1 * ((Q.coeff k2).coeff j2).coeff i2 ≠ 0 →
          (k1, j1, i1) = pM ∧ (k2, j2, i2) = qM := by
        intro k1 k2 j1 j2 i1 i2 hk hj hi hprod
        have hp1 : (k1, j1, i1) ∈ supp3 P := (hmem3 P _ _ _).mpr (left_ne_zero_of_mul hprod)
        have hq2 : (k2, j2, i2) ∈ supp3 Q := (hmem3 Q _ _ _).mpr (right_ne_zero_of_mul hprod)
        have hleP := hpM_max (k1, j1, i1) hp1
        have hleQ := hqM_max (k2, j2, i2) hq2
        have hw1 : i1 + j1 * wY + k1 * (wY - 1) ≤ pM.2.2 + pM.2.1 * wY + pM.1 * (wY - 1) :=
          (Prod.Lex.le_iff.mp hleP).elim le_of_lt (fun h => h.1.le)
        have hw2 : i2 + j2 * wY + k2 * (wY - 1) ≤ qM.2.2 + qM.2.1 * wY + qM.1 * (wY - 1) :=
          (Prod.Lex.le_iff.mp hleQ).elim le_of_lt (fun h => h.1.le)
        have hweq : (i1 + j1 * wY + k1 * (wY - 1)) + (i2 + j2 * wY + k2 * (wY - 1)) =
            (pM.2.2 + pM.2.1 * wY + pM.1 * (wY - 1)) + (qM.2.2 + qM.2.1 * wY + qM.1 * (wY - 1)) := by
          have : (i1 + i2) + (j1 + j2) * wY + (k1 + k2) * (wY - 1) =
              (pM.2.2 + qM.2.2) + (pM.2.1 + qM.2.1) * wY + (pM.1 + qM.1) * (wY - 1) := by
            rw [hi, hj, hk]
          linarith
        have hweq1 : i1 + j1 * wY + k1 * (wY - 1) = pM.2.2 + pM.2.1 * wY + pM.1 * (wY - 1) := by omega
        have hweq2 : i2 + j2 * wY + k2 * (wY - 1) = qM.2.2 + qM.2.1 * wY + qM.1 * (wY - 1) := by omega
        have hleP2 : toLex (k1, j1) ≤ toLex (pM.1, pM.2.1) := by
          rcases Prod.Lex.le_iff.mp hleP with hlt | ⟨_, h2⟩
          · exfalso; dsimp [score] at hlt; omega
          · exact h2
        have hleQ2 : toLex (k2, j2) ≤ toLex (qM.1, qM.2.1) := by
          rcases Prod.Lex.le_iff.mp hleQ with hlt | ⟨_, h2⟩
          · exfalso; dsimp [score] at hlt; omega
          · exact h2
        have hk1le : k1 ≤ pM.1 := (Prod.Lex.le_iff.mp hleP2).elim le_of_lt (fun h => h.1.le)
        have hk2le : k2 ≤ qM.1 := (Prod.Lex.le_iff.mp hleQ2).elim le_of_lt (fun h => h.1.le)
        have hk1eq : k1 = pM.1 := by omega
        have hk2eq : k2 = qM.1 := by omega
        have hj1le : j1 ≤ pM.2.1 := by
          rcases Prod.Lex.le_iff.mp hleP2 with hlt | ⟨_, h2⟩
          · exfalso; simp at hlt; omega
          · exact h2
        have hj2le : j2 ≤ qM.2.1 := by
          rcases Prod.Lex.le_iff.mp hleQ2 with hlt | ⟨_, h2⟩
          · exfalso; simp at hlt; omega
          · exact h2
        have hj1eq : j1 = pM.2.1 := by omega
        have hj2eq : j2 = qM.2.1 := by omega
        have hi1eq : i1 = pM.2.2 := by rw [hk1eq, hj1eq] at hweq1; omega
        have hi2eq : i2 = qM.2.2 := by rw [hk2eq, hj2eq] at hweq2; omega
        exact ⟨Prod.ext hk1eq (Prod.ext hj1eq hi1eq), Prod.ext hk2eq (Prod.ext hj2eq hi2eq)⟩
      rw [coeff_mul, coeff_finset_sum, coeff_finset_sum]
      rw [Finset.sum_eq_single (pM.1, qM.1)]
      · rw [coeff_mul, coeff_finset_sum]
        rw [Finset.sum_eq_single (pM.2.1, qM.2.1)]
        · rw [coeff_mul]
          rw [Finset.sum_eq_single (pM.2.2, qM.2.2)]
          · exact mul_ne_zero ((hmem3 P _ _ _).mp hpM_mem) ((hmem3 Q _ _ _).mp hqM_mem)
          · intro x hx hne
            by_contra hnz
            have := huniq pM.1 qM.1 pM.2.1 qM.2.1 x.1 x.2 rfl rfl (Finset.mem_antidiagonal.mp hx) hnz
            exact hne (Prod.ext (congrArg (fun t => t.2.2) this.1) (congrArg (fun t => t.2.2) this.2))
          · intro hnot; simp at hnot
        · intro y hy hne
          rw [coeff_mul]
          apply Finset.sum_eq_zero
          intro x hx
          by_contra hnz
          have := huniq pM.1 qM.1 y.1 y.2 x.1 x.2 rfl (Finset.mem_antidiagonal.mp hy) (Finset.mem_antidiagonal.mp hx) hnz
          exact hne (Prod.ext (congrArg (fun t => t.2.1) this.1) (congrArg (fun t => t.2.1) this.2))
        · intro hnot; simp at hnot
      · intro z hz hne
        rw [coeff_mul, coeff_finset_sum]
        apply Finset.sum_eq_zero
        intro y hy
        rw [coeff_mul]
        apply Finset.sum_eq_zero
        intro x hx
        by_contra hnz
        have := huniq z.1 z.2 y.1 y.2 x.1 x.2 (Finset.mem_antidiagonal.mp hz)
          (Finset.mem_antidiagonal.mp hy) (Finset.mem_antidiagonal.mp hx) hnz
        exact hne (Prod.ext (congrArg (fun t => t.1) this.1) (congrArg (fun t => t.1) this.2))
      · intro hnot; simp at hnot
    have hlb := (wdeg_le_iff wY (wdeg wY (P * Q)) (P * Q)).mp le_rfl
      (pM.1 + qM.1) (pM.2.1 + qM.2.1) (pM.2.2 + qM.2.2) hcoeff_ne
    rw [hwtP, hwtQ]
    have := hscore_add pM qM
    dsimp at this
    omega

/-- **1-line `D(F) ≠ 0` elimination theorem:**
Over any integral domain `A`, for `F ≠ 0` and `1 ≤ wY`:
`F ∣ contactDeriv F ↔ contactDeriv F = 0`!
Hence whenever `contactDeriv F ≠ 0` and `F` is irreducible, `F ∤ contactDeriv F` and
`Res_R(F, contactDeriv F) ≠ 0` immediately eliminates `R`! -/
theorem dvd_contactDeriv_iff [IsDomain A] (wY : ℕ) (hwY : 1 ≤ wY) {F : ContactPoly A} (hF : F ≠ 0) :
    F ∣ contactDeriv F ↔ contactDeriv F = 0 := by
  constructor
  · rintro ⟨G, hG⟩
    by_contra hne
    have hGne : G ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hG; exact hne hG
    have h1 := wdeg_contactDeriv_add_one_le wY hwY F hne
    rw [hG, wdeg_mul wY hF hGne] at h1
    omega
  · intro h0; rw [h0]; exact dvd_zero F

end ContactRing

end B6401ContactKerD
end ProximityPrize.SubmissionBinaryLower

import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Full `ker(D)` basis `K_W(s)`, local `(t, w, R)` basis `B(m, s)`, global & quotient 4-var interpolation

Proves the complete interpolation engine for the 64.01 binary contact proof:
1. `KerDIdx wY W s`: exact finite index set of cardinality `varsKerDExact wY W s`, giving an
   `A`-basis of `K_W(s) = { Q ∈ ker(D) : deg_R(Q) ≤ s ∧ wdeg wY Q ≤ W }` over any char-2 ring `A`.
2. `LocalPoly A := A[R][w][t]` and `LocalBasisIdx m s`: exact finite index set of cardinality
   `rankKerD m s`, forming a **free `A`-basis** of `Φ_m(K(s)) ⊆ A[R][w][t] / (t, w)^m` over ANY
   char-2 commutative ring `A`, with `GF(2)`-linear normal form `localNF` preserving `Z`-degrees!
3. Multiplicative `(t, w)`-valuation `twOrdGE` and exact contact evaluation:
   `twOrdGE (localShift x0 y0 Q) m → P.eval x0 = y0 → (X - C x0)^(2*m) ∣ evalContact Q P`.
4. Global 4-variable contact interpolation (`exists_global_contact_interpolant`) for any `(m0, s0, D_ZF, W0)`
   with `varsKerDExact wY W0 s0 * (D_ZF + 1) > N * rankKerD m0 s0 * (D_ZF + 1 + W0 / wY)`.
5. Denominator-free 4-variable quotient interpolation (`exists_quotient_contact_interpolant`):
   given nonzero `F ∈ K_{W_F}(d)[Z]_{≤ D_ZF}` with exact local orders `k_i`, produces nonzero
   `G ∈ K_W(s)[Z]_{≤ D_Z'}` with `F ∤ G` over `F(Z)` and `evalContact G_z P = 0` for every `(z, P)`
   with `A` agreements and `evalContact F_z P = 0`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401QuotInterp

open Polynomial B6401ContactKerD
open scoped BigOperators

/-! ### Part 1: Exact `ker(D)` basis `KerDIdx` and `K_W(s)` characterization -/

/-- Exact index set for the parity-disjoint basis of `K_W(s)`:
monomials `R^k * (Y + X R)^r * X^(2a) * Y^(2b)` with `r < 2`, `k + r ≤ s`,
and `k*(wY - 1) + r*wY + 2*b*wY + 2*a ≤ W`. -/
def kerDIdxFinset (wY W s : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (s + 1)).biUnion fun k =>
    (Finset.range 2).biUnion fun r =>
      if k + r ≤ s then
        let cost := k * (wY - 1) + r * wY
        if cost ≤ W then
          let rem0 := W - cost
          let bmax := rem0 / (2 * wY)
          (Finset.range (bmax + 1)).biUnion fun b =>
            (Finset.range ((rem0 - 2 * b * wY) / 2 + 1)).image fun a => (k, r, b, a)
        else ∅
      else ∅

abbrev KerDIdx (wY W s : ℕ) := { e : ℕ × ℕ × ℕ × ℕ // e ∈ kerDIdxFinset wY W s }

lemma mem_kerDIdxFinset_iff (wY W s : ℕ) (hwY : 0 < wY) (k r b a : ℕ) :
    (k, r, b, a) ∈ kerDIdxFinset wY W s ↔
      r < 2 ∧ k + r ≤ s ∧ k * (wY - 1) + r * wY + 2 * b * wY + 2 * a ≤ W := by
  unfold kerDIdxFinset
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', r', hr', hmem⟩
    split_ifs at hmem with hkr hcost
    · simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq] at hmem
      rcases hmem with ⟨b', hb', a', ha', rfl, rfl, rfl, rfl⟩
      refine ⟨hr', hkr, ?_⟩
      have hbw : 2 * b' * wY ≤ W - (k' * (wY - 1) + r' * wY) := by
        have h1 : b' * (2 * wY) ≤ ((W - (k' * (wY - 1) + r' * wY)) / (2 * wY)) * (2 * wY) :=
          Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp hb')
        have h2 := Nat.div_mul_le_self (W - (k' * (wY - 1) + r' * wY)) (2 * wY)
        linarith
      omega
    · simp at hmem
    · simp at hmem
  · rintro ⟨hr, hkr, hle⟩
    refine ⟨k, by omega, r, hr, ?_⟩
    have hcost : k * (wY - 1) + r * wY ≤ W := by omega
    simp only [hkr, ↓reduceIte, hcost]
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
    have hb : b < (W - (k * (wY - 1) + r * wY)) / (2 * wY) + 1 := by
      have : b * (2 * wY) ≤ W - (k * (wY - 1) + r * wY) := by
        have hcomm : b * (2 * wY) = 2 * b * wY := by ring
        omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * wY)).mpr this
      omega
    have ha : a < (W - (k * (wY - 1) + r * wY) - 2 * b * wY) / 2 + 1 := by omega
    exact ⟨b, hb, a, ha, by simp⟩

theorem card_kerDIdxFinset (wY W s : ℕ) (hwY : 0 < wY) :
    (kerDIdxFinset wY W s).card = varsKerDExact wY W s := by
  unfold kerDIdxFinset varsKerDExact
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro r _
      by_cases hkr : k + r ≤ s
      · simp only [hkr, ↓reduceIte]
        by_cases hcost : k * (wY - 1) + r * wY ≤ W
        · simp only [hcost, ↓reduceIte]
          rw [Finset.card_biUnion]
          · trans ∑ b ∈ Finset.range ((W - (k * (wY - 1) + r * wY)) / (2 * wY) + 1),
                ((W - (k * (wY - 1) + r * wY) - 2 * b * wY) / 2 + 1)
            · apply Finset.sum_congr rfl
              intro b _
              rw [Finset.card_image_of_injective]
              · exact Finset.card_range _
              · intro a1 a2 h; exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2
            · exact sum_parity_block_eq wY (W - (k * (wY - 1) + r * wY)) hwY
          · intro b1 _ b2 _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            simp only [Finset.mem_image] at hx1 hx2
            rcases hx1 with ⟨_, _, rfl⟩
            rcases hx2 with ⟨_, _, h⟩
            exact hne (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1.symm
        · simp [hcost]
      · simp [hkr]
    · intro r1 _ r2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
      split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
      simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨_, _, _, _, rfl⟩
      rcases hx2 with ⟨_, _, _, _, h⟩
      exact hne (Prod.mk.inj (Prod.mk.inj h).2).1.symm
  · intro k1 _ k2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_biUnion] at hx1 hx2
    rcases hx1 with ⟨r1, _, hx1⟩
    rcases hx2 with ⟨r2, _, hx2⟩
    split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
    split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
    simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨_, _, _, _, rfl⟩
    rcases hx2 with ⟨_, _, _, _, h⟩
    exact hne (Prod.mk.inj h).1.symm

lemma card_kerDIdx (wY W s : ℕ) (hwY : 0 < wY) :
    Fintype.card (KerDIdx wY W s) = varsKerDExact wY W s := by
  rw [Fintype.card_coe, card_kerDIdxFinset wY W s hwY]

section ContactBasis

variable {A : Type*} [CommRing A]

/-- Embed a scalar `c : A` into `ContactPoly A = A[X][Y][R]`. -/
noncomputable def cC (a : A) : ContactPoly A := C (C (C a))
/-- Variable `X` in `ContactPoly A`. -/
noncomputable def cX : ContactPoly A := C (C X)
/-- Variable `Y` in `ContactPoly A`. -/
noncomputable def cY : ContactPoly A := C X
/-- Variable `R` in `ContactPoly A`. -/
noncomputable def cR : ContactPoly A := X

lemma coeff_cC (a : A) (k j i : ℕ) :
    (((cC a).coeff k).coeff j).coeff i = if k = 0 ∧ j = 0 ∧ i = 0 then a else 0 := by
  unfold cC
  by_cases hk : k = 0 <;> by_cases hj : j = 0 <;> by_cases hi : i = 0 <;>
    simp [hk, hj, hi, coeff_C]

lemma coeff_cX (k j i : ℕ) :
    (((cX : ContactPoly A).coeff k).coeff j).coeff i = if k = 0 ∧ j = 0 ∧ i = 1 then 1 else 0 := by
  unfold cX
  by_cases hk : k = 0 <;> by_cases hj : j = 0 <;> by_cases hi : i = 1 <;>
    simp [hk, hj, hi, coeff_C, coeff_X, eq_comm]

lemma coeff_cY (k j i : ℕ) :
    (((cY : ContactPoly A).coeff k).coeff j).coeff i = if k = 0 ∧ j = 1 ∧ i = 0 then 1 else 0 := by
  unfold cY
  by_cases hk : k = 0 <;> by_cases hj : j = 1 <;> by_cases hi : i = 0 <;>
    simp [hk, hj, hi, coeff_C, coeff_X, coeff_one, eq_comm]

lemma coeff_cR (k j i : ℕ) :
    (((cR : ContactPoly A).coeff k).coeff j).coeff i = if k = 1 ∧ j = 0 ∧ i = 0 then 1 else 0 := by
  unfold cR
  by_cases hk : k = 1 <;> by_cases hj : j = 0 <;> by_cases hi : i = 0 <;>
    simp [hk, hj, hi, coeff_C, coeff_X, coeff_one, eq_comm]

lemma contactDeriv_cC (a : A) : contactDeriv (cC a) = 0 := by
  ext k j i; rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative]
  have h1 : (((cC a).coeff k).coeff j).coeff (i + 1) = 0 := by rw [coeff_cC]; simp
  rw [h1, zero_mul, zero_add]
  cases k with
  | zero => simp only [↓reduceIte, coeff_zero]
  | succ k' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative]
      rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C]
      have h2 : (((cC a).coeff k').coeff (j + 1)).coeff i = 0 := by rw [coeff_cC]; simp
      rw [h2, zero_mul, coeff_zero, coeff_zero, coeff_zero]

lemma contactDeriv_cX : contactDeriv (cX : ContactPoly A) = 1 := by
  ext k j i
  rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative]
  have h2 : (if k = 0 then (0 : BiPoly A) else ((cX : ContactPoly A).coeff (k - 1)).derivative).coeff j = 0 := by
    cases k with
    | zero => simp
    | succ k' =>
        ext i'
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative, coeff_zero]
        rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C, coeff_cX]; simp
  rw [h2, coeff_zero, add_zero, coeff_cX]
  change (if k = 0 ∧ j = 0 ∧ i + 1 = 1 then (1 : A) else 0) * ((i : A) + 1) =
    (((cC (1 : A)).coeff k).coeff j).coeff i
  rw [coeff_cC]
  by_cases hk : k = 0 <;> by_cases hj : j = 0 <;> by_cases hi : i = 0 <;>
    simp [hk, hj, hi]

lemma contactDeriv_cY : contactDeriv (cY : ContactPoly A) = cR := by
  ext k j i
  rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative]
  have h1 : (((cY : ContactPoly A).coeff k).coeff j).coeff (i + 1) = 0 := by rw [coeff_cY]; simp
  rw [h1, zero_mul, zero_add, coeff_cR]
  cases k with
  | zero => simp
  | succ k' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative]
      rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C, coeff_cY]
      by_cases hk : k' = 0 <;> by_cases hj : j = 0 <;> by_cases hi : i = 0 <;>
        simp [hk, hj, hi]

lemma contactDeriv_cR : contactDeriv (cR : ContactPoly A) = 0 := by
  ext k j i
  rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative, coeff_zero]
  have h1 : (((cR : ContactPoly A).coeff k).coeff j).coeff (i + 1) = 0 := by rw [coeff_cR]; simp
  rw [h1, zero_mul, zero_add]
  cases k with
  | zero => simp
  | succ k' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative]
      rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C]
      have h2 : (((cR : ContactPoly A).coeff k').coeff (j + 1)).coeff i = 0 := by rw [coeff_cR]; simp
      rw [h2, zero_mul, coeff_zero, coeff_zero]

lemma contactDeriv_sq [CharP A 2] (P : ContactPoly A) : contactDeriv (P ^ 2) = 0 := by
  rw [sq, contactDeriv_mul]
  have h2 : (2 : ContactPoly A) = 0 := by
    ext k j i; rw [show (2 : ContactPoly A) = cC 2 by rfl, coeff_cC, coeff_zero]
    split_ifs <;> simp [CharTwo.two_eq_zero]
  calc contactDeriv P * P + P * contactDeriv P
      = (2 : ContactPoly A) * (P * contactDeriv P) := by ring
    _ = 0 := by rw [h2, zero_mul]

lemma contactDeriv_Y_add_XR [CharP A 2] :
    contactDeriv ((cY : ContactPoly A) + cX * cR) = 0 := by
  rw [contactDeriv_add, contactDeriv_mul, contactDeriv_cY, contactDeriv_cX, contactDeriv_cR]
  have h2 : (2 : ContactPoly A) = 0 := by
    ext k j i; rw [show (2 : ContactPoly A) = cC 2 by rfl, coeff_cC, coeff_zero]
    split_ifs <;> simp [CharTwo.two_eq_zero]
  calc cR + (1 * cR + cX * 0) = (2 : ContactPoly A) * cR := by ring
    _ = 0 := by rw [h2, zero_mul]

lemma contactDeriv_pow (P : ContactPoly A) (n : ℕ) (hP : contactDeriv P = 0) :
    contactDeriv (P ^ n) = 0 := by
  induction n with
  | zero =>
      rw [pow_zero]; exact contactDeriv_cC 1
  | succ n ih =>
      rw [pow_succ, contactDeriv_mul, ih, hP, zero_mul, mul_zero, add_zero]

/-- Basis polynomial of `K_W(s)` for tuple `(k, r, b, a)`: `R^k * (Y + X R)^r * X^(2a) * Y^(2b)`. -/
noncomputable def kerDBasisPoly (e : ℕ × ℕ × ℕ × ℕ) : ContactPoly A :=
  cR ^ e.1 * (cY + cX * cR) ^ e.2.1 * (cX ^ 2) ^ e.2.2.2 * (cY ^ 2) ^ e.2.2.1

lemma contactDeriv_kerDBasisPoly [CharP A 2] (e : ℕ × ℕ × ℕ × ℕ) :
    contactDeriv (kerDBasisPoly (A := A) e) = 0 := by
  unfold kerDBasisPoly
  have h1 : contactDeriv (cR (A := A) ^ e.1) = 0 := contactDeriv_pow _ _ contactDeriv_cR
  have h2 : contactDeriv ((cY (A := A) + cX * cR) ^ e.2.1) = 0 :=
    contactDeriv_pow _ _ contactDeriv_Y_add_XR
  have h3 : contactDeriv ((cX (A := A) ^ 2) ^ e.2.2.2) = 0 :=
    contactDeriv_pow _ _ (contactDeriv_sq cX)
  have h4 : contactDeriv ((cY (A := A) ^ 2) ^ e.2.2.1) = 0 :=
    contactDeriv_pow _ _ (contactDeriv_sq cY)
  simp [contactDeriv_mul, h1, h2, h3, h4]

/-- Explicit coefficient formula for `kerDBasisPoly (k, r, b, a)` with `r < 2`. -/
lemma coeff_kerDBasisPoly (k r b a : ℕ) (hr : r < 2) (k' j' i' : ℕ) :
    (((kerDBasisPoly (A := A) (k, r, b, a)).coeff k').coeff j').coeff i' =
      if r = 0 then
        (if k' = k ∧ j' = 2 * b ∧ i' = 2 * a then 1 else 0)
      else
        (if (k' = k ∧ j' = 2 * b + 1 ∧ i' = 2 * a) ∨
            (k' = k + 1 ∧ j' = 2 * b ∧ i' = 2 * a + 1) then 1 else 0) := by
  have hmon : ∀ (m n l : ℕ),
      (cR (A := A) ^ m * cY ^ n * cX ^ l) = monomial m (monomial n (monomial l 1)) := by
    intro m n l
    unfold cR cY cX
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      map_one, one_mul, map_mul, map_pow, map_pow, map_pow]
    ring
  have hr01 : r = 0 ∨ r = 1 := by omega
  rcases hr01 with rfl | rfl
  · have heq : kerDBasisPoly (A := A) (k, 0, b, a) =
        cR ^ k * cY ^ (2 * b) * cX ^ (2 * a) := by
      unfold kerDBasisPoly; rw [pow_zero, mul_one, ← pow_mul, ← pow_mul]; ring
    rw [heq, hmon]
    simp only [↓reduceIte, coeff_monomial]
    by_cases h1 : k' = k <;> by_cases h2 : j' = 2 * b <;> by_cases h3 : i' = 2 * a <;>
      simp [h1, h2, h3, eq_comm]
  · have heq : kerDBasisPoly (A := A) (k, 1, b, a) =
        cR ^ k * cY ^ (2 * b + 1) * cX ^ (2 * a) +
        cR ^ (k + 1) * cY ^ (2 * b) * cX ^ (2 * a + 1) := by
      unfold kerDBasisPoly; rw [pow_one, ← pow_mul, ← pow_mul]
      have h2a : (cX : ContactPoly A) ^ (2 * a + 1) = cX * cX ^ (2 * a) := by rw [pow_succ']
      have h2b : (cY : ContactPoly A) ^ (2 * b + 1) = cY * cY ^ (2 * b) := by rw [pow_succ']
      have hk1 : (cR : ContactPoly A) ^ (k + 1) = cR * cR ^ k := by rw [pow_succ']
      rw [h2a, h2b, hk1]; ring
    rw [heq, hmon, hmon, coeff_add, coeff_add, coeff_add]
    simp only [one_ne_zero, ↓reduceIte]
    by_cases hA : k' = k ∧ j' = 2 * b + 1 ∧ i' = 2 * a
    · rcases hA with ⟨rfl, rfl, rfl⟩
      have hne : ¬ (k' + 1 = k') := by omega
      simp [coeff_monomial, hne]
    · by_cases hB : k' = k + 1 ∧ j' = 2 * b ∧ i' = 2 * a + 1
      · rcases hB with ⟨rfl, rfl, rfl⟩
        have hne : ¬ (k = k + 1) := by omega
        simp [coeff_monomial, hne]
      · simp only [hA, hB, or_self, ↓reduceIte]
        have h1 : (((monomial k (monomial (2 * b + 1) (monomial (2 * a) (1 : A)))).coeff k').coeff j').coeff i' = 0 := by
          by_cases hk : k = k'
          · subst hk
            by_cases hj : 2 * b + 1 = j'
            · subst hj
              have hi : 2 * a ≠ i' := fun h => hA ⟨rfl, rfl, h.symm⟩
              simp [coeff_monomial, hi]
            · simp [coeff_monomial, hj]
          · simp [coeff_monomial, hk]
        have h2 : (((monomial (k + 1) (monomial (2 * b) (monomial (2 * a + 1) (1 : A)))).coeff k').coeff j').coeff i' = 0 := by
          by_cases hk : k + 1 = k'
          · subst hk
            by_cases hj : 2 * b = j'
            · subst hj
              have hi : 2 * a + 1 ≠ i' := fun h => hB ⟨rfl, rfl, h.symm⟩
              simp [coeff_monomial, hi]
            · simp [coeff_monomial, hj]
          · simp [coeff_monomial, hk]
        rw [h1, h2, add_zero]

/-- Exact linear-combination evaluation of `∑ e, c e • kerDBasisPoly e` at `(k', j', i')`:
every monomial `(k', 2b, 2a)` uniquely picks `e = (k', 0, b, a)`,
every `(k', 2b+1, 2a)` uniquely picks `e = (k', 1, b, a)`,
every `(k'+1, 2b, 2a+1)` uniquely picks `e = (k', 1, b, a)`,
and `(k', 2b+1, 2a+1)` and `(0, 2b, 2a+1)` are always `0`! -/
lemma coeff_sum_kerDBasisPoly {wY W s : ℕ} (hwY : 0 < wY) (c : KerDIdx wY W s → A) (k' j' i' : ℕ) :
    (((∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1).coeff k').coeff j').coeff i' =
      if j' % 2 = 0 ∧ i' % 2 = 0 then
        if h : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s then c ⟨_, h⟩ else 0
      else if j' % 2 = 1 ∧ i' % 2 = 0 then
        if h : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s then c ⟨_, h⟩ else 0
      else if j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k' then
        if h : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s then c ⟨_, h⟩ else 0
      else 0 := by
  classical
  have hmul : ∀ (a : A) (P : ContactPoly A) (k j i : ℕ),
      (((cC a * P).coeff k).coeff j).coeff i = a * (((P.coeff k).coeff j).coeff i) := by
    intro a P k j i; unfold cC; simp [coeff_C_mul]
  rw [finset_sum_coeff, finset_sum_coeff, finset_sum_coeff]
  simp_rw [hmul]
  have hterm : ∀ e : KerDIdx wY W s,
      c e * (((kerDBasisPoly (A := A) e.1).coeff k').coeff j').coeff i' =
      if (e.1.2.1 = 0 ∧ k' = e.1.1 ∧ j' = 2 * e.1.2.2.1 ∧ i' = 2 * e.1.2.2.2) ∨
         (e.1.2.1 = 1 ∧ ((k' = e.1.1 ∧ j' = 2 * e.1.2.2.1 + 1 ∧ i' = 2 * e.1.2.2.2) ∨
                         (k' = e.1.1 + 1 ∧ j' = 2 * e.1.2.2.1 ∧ i' = 2 * e.1.2.2.2 + 1))) then c e else 0 := by
    intro ⟨⟨k, r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W s hwY k r b a).mp he).1
    rw [coeff_kerDBasisPoly k r b a hr]
    have hr01 : r = 0 ∨ r = 1 := by omega
    rcases hr01 with rfl | rfl <;>
      simp only [↓reduceIte, one_ne_zero, zero_ne_one, false_and, true_and, false_or, or_false] <;>
      split_ifs <;> simp
  simp_rw [hterm]
  by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
  · simp only [h00, ↓reduceIte]
    rcases h00 with ⟨hj, hi⟩
    by_cases hmem : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
    · rw [dif_pos hmem, Finset.sum_eq_single ⟨(k', 0, j' / 2, i' / 2), hmem⟩]
      · simp; omega
      · intro ⟨⟨k, r, b, a⟩, he⟩ _ hne
        split_ifs with hcond
        · exfalso; apply hne; apply Subtype.ext
          rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ <;>
            [simp; omega; omega]
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hmem]
      apply Finset.sum_eq_zero
      intro ⟨⟨k, r, b, a⟩, he⟩ _
      split_ifs with hcond
      · exfalso; apply hmem
        rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
        · simpa using he
        · omega
        · omega
      · rfl
  · simp only [h00, ↓reduceIte]
    by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
    · simp only [h10, ↓reduceIte]
      rcases h10 with ⟨hj, hi⟩
      by_cases hmem : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
      · rw [dif_pos hmem, Finset.sum_eq_single ⟨(k', 1, j' / 2, i' / 2), hmem⟩]
        · simp; omega
        · intro ⟨⟨k, r, b, a⟩, he⟩ _ hne
          split_ifs with hcond
          · exfalso; apply hne; apply Subtype.ext
            rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ <;>
              [omega; (ext <;> dsimp <;> omega); omega]
          · rfl
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [dif_neg hmem]
        apply Finset.sum_eq_zero
        intro ⟨⟨k, r, b, a⟩, he⟩ _
        split_ifs with hcond
        · exfalso; apply hmem
          rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
          · omega
          · have : (2 * b + 1) / 2 = b := by omega
            have : (2 * a) / 2 = a := by omega
            simpa [*] using he
          · omega
        · rfl
    · simp only [h10, ↓reduceIte]
      by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
      · simp only [h01, ↓reduceIte]
        rcases h01 with ⟨hj, hi, hk⟩
        by_cases hmem : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
        · rw [dif_pos hmem, Finset.sum_eq_single ⟨(k' - 1, 1, j' / 2, i' / 2), hmem⟩]
          · simp; omega
          · intro ⟨⟨k, r, b, a⟩, he⟩ _ hne
            split_ifs with hcond
            · exfalso; apply hne; apply Subtype.ext
              rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ <;>
                [omega; omega; (ext <;> dsimp <;> omega)]
            · rfl
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [dif_neg hmem]
          apply Finset.sum_eq_zero
          intro ⟨⟨k, r, b, a⟩, he⟩ _
          split_ifs with hcond
          · exfalso; apply hmem
            rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
            · omega
            · omega
            · have h1 : k + 1 - 1 = k := by omega
              have h2 : (2 * b) / 2 = b := by omega
              have h3 : (2 * a + 1) / 2 = a := by omega
              simpa [h1, h2, h3] using he
          · rfl
      · simp only [h01, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro ⟨⟨k, r, b, a⟩, he⟩ _
        split_ifs with hcond
        · exfalso
          rcases hcond with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ <;>
            omega
        · rfl

/-- Exact `K_W(s)` characterization over ANY characteristic-2 commutative ring `A`:
`Q ∈ K_W(s)` iff `Q = ∑ e : KerDIdx wY W s, c e • kerDBasisPoly e`, AND the coefficients `c` are UNIQUE! -/
theorem mem_kerD_iff_exists_unique_coords [CharP A 2] {wY W s : ℕ} (hwY : 1 ≤ wY) (Q : ContactPoly A) :
    (contactDeriv Q = 0 ∧ Q.natDegree ≤ s ∧ wdeg wY Q ≤ W) ↔
      ∃! c : KerDIdx wY W s → A, Q = ∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1 := by
  have hwYpos : 0 < wY := by omega
  have huniq : ∀ c1 c2 : KerDIdx wY W s → A,
      (∑ e, cC (c1 e) * kerDBasisPoly (A := A) e.1) = (∑ e, cC (c2 e) * kerDBasisPoly e.1) → c1 = c2 := by
    intro c1 c2 heq
    funext ⟨⟨k, r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W s hwYpos k r b a).mp he).1
    have hr01 : r = 0 ∨ r = 1 := by omega
    rcases hr01 with rfl | rfl
    · have h := congrArg (fun P : ContactPoly A => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) heq
      rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
      simpa [he] using h
    · have h := congrArg (fun P : ContactPoly A => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) heq
      rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
      have hmod1 : (2 * b + 1) % 2 = 1 := by omega
      have hmod2 : (2 * a) % 2 = 0 := by omega
      have hdiv1 : (2 * b + 1) / 2 = b := by omega
      have hdiv2 : (2 * a) / 2 = a := by omega
      simpa [hmod1, hmod2, hdiv1, hdiv2, he] using h
  constructor
  · rintro ⟨hDQ, hdeg, hw⟩
    -- Extract the candidate coordinates directly from Q's coefficients!
    let c : KerDIdx wY W s → A := fun ⟨⟨k, r, b, a⟩, _⟩ =>
      if r = 0 then ((Q.coeff k).coeff (2 * b)).coeff (2 * a)
      else ((Q.coeff k).coeff (2 * b + 1)).coeff (2 * a)
    have hQeq : Q = ∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1 := by
      -- Prove Q = ∑ e, cC (c e) * kerDBasisPoly e.1 entry by entry using hDQ = 0!
      have hDentry : ∀ k j i,
          ((Q.coeff k).coeff j).coeff (i + 1) * ((i + 1 : ℕ) : A) +
          (if k = 0 then 0 else ((Q.coeff (k - 1)).coeff (j + 1)).coeff i * ((j + 1 : ℕ) : A)) = 0 := by
        intro k j i
        have h := congrArg (fun P : ContactPoly A => ((P.coeff k).coeff j).coeff i) hDQ
        rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative, coeff_zero] at h
        cases k with
        | zero => simpa using h
        | succ k' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative] at h
            rw [show ((j : Polynomial A) + 1) = C ((j : A) + 1) by simp, coeff_mul_C] at h
            simpa [Nat.cast_add, Nat.cast_one] using h
      have hmul_odd : ∀ (a : A) (n : ℕ), n % 2 = 1 → a * (n : A) = a := by
        intro a n hn
        have : (n : A) = 1 := by
          rw [show n = 2 * (n / 2) + 1 by omega]
          push_cast; simp [CharTwo.two_eq_zero]
        rw [this, mul_one]
      have hmul_even : ∀ (a : A) (n : ℕ), n % 2 = 0 → a * (n : A) = 0 := by
        intro a n hn
        have : (n : A) = 0 := by
          rw [show n = 2 * (n / 2) by omega]
          push_cast; simp [CharTwo.two_eq_zero]
        rw [this, mul_zero]
      -- From D(Q) = 0:
      -- (1) For j odd, i odd: ((Q.coeff k).coeff j).coeff i = 0 (take k+1, j-1, i: (i+1) even, j odd!)
      have h11 : ∀ k j i, j % 2 = 1 → i % 2 = 1 → ((Q.coeff k).coeff j).coeff i = 0 := by
        intro k j i hj hi
        have h := hDentry (k + 1) (j - 1) i
        have hi1 : (i + 1) % 2 = 0 := by omega
        have hj1 : j - 1 + 1 = j := by omega
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hj1] at h
        rw [hmul_even _ _ hi1, zero_add, hmul_odd _ _ hj] at h
        exact h
      -- (2) For k = 0, j even, i odd: ((Q.coeff 0).coeff j).coeff i = 0
      have h0_01 : ∀ j i, j % 2 = 0 → i % 2 = 1 → ((Q.coeff 0).coeff j).coeff i = 0 := by
        intro j i _ hi
        have h := hDentry 0 j (i - 1)
        have hi1 : i - 1 + 1 = i := by omega
        simp only [↓reduceIte, add_zero, hi1] at h
        rw [hmul_odd _ _ hi] at h
        exact h
      -- (3) For k > 0, j even, i odd: ((Q.coeff k).coeff j).coeff i = ((Q.coeff (k-1)).coeff (j+1)).coeff (i-1)
      have h_match' : ∀ k j i, 0 < k → j % 2 = 0 → i % 2 = 1 →
          ((Q.coeff k).coeff j).coeff i = ((Q.coeff (k - 1)).coeff (j + 1)).coeff (i - 1) := by
        intro k j i hk hj hi
        have h := hDentry k j (i - 1)
        have hi1 : i - 1 + 1 = i := by omega
        have hj1 : (j + 1) % 2 = 1 := by omega
        have hk0 : k ≠ 0 := by omega
        simp only [hk0, ↓reduceIte, hi1] at h
        rw [hmul_odd _ _ hi, hmul_odd _ _ hj1] at h
        have hadd := congrArg (· + ((Q.coeff (k - 1)).coeff (j + 1)).coeff (i - 1)) h
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hadd
        exact hadd
      -- (4) For k = s, j odd, i even: ((Q.coeff s).coeff j).coeff i = 0 (since Q.coeff (s+1) = 0!)
      have hs_10 : ∀ j i, j % 2 = 1 → i % 2 = 0 → ((Q.coeff s).coeff j).coeff i = 0 := by
        intro j i hj _
        have h := hDentry (s + 1) (j - 1) i
        have hj1 : j - 1 + 1 = j := by omega
        have hQsp : Q.coeff (s + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hj1, hQsp, coeff_zero, zero_mul, zero_add] at h
        rw [hmul_odd _ _ hj] at h
        exact h
      ext k' j' i'
      rw [coeff_sum_kerDBasisPoly hwYpos]
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, ↓reduceIte]
        rcases h00 with ⟨hj, hi⟩
        by_cases hmem : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
        · rw [dif_pos hmem]; dsimp [c]; simp [show 2 * (j' / 2) = j' by omega, show 2 * (i' / 2) = i' by omega]
        · rw [dif_neg hmem]
          by_contra hnz
          apply hmem
          rw [mem_kerDIdxFinset_iff wY W s hwYpos]
          have hk_le : k' ≤ s := le_trans (le_natDegree_of_ne_zero (fun h0 => hnz (by simp [h0]))) hdeg
          have hw_le := (wdeg_le_iff wY W Q).mp hw k' j' i' hnz
          refine ⟨by omega, by omega, ?_⟩
          have : 2 * (j' / 2) = j' := by omega
          have : 2 * (i' / 2) = i' := by omega
          nlinarith
      · simp only [h00, ↓reduceIte]
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, ↓reduceIte]
          rcases h10 with ⟨hj, hi⟩
          by_cases hmem : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
          · rw [dif_pos hmem]; dsimp [c]
            simp [show 2 * (j' / 2) + 1 = j' by omega, show 2 * (i' / 2) = i' by omega]
          · rw [dif_neg hmem]
            by_contra hnz
            apply hmem
            rw [mem_kerDIdxFinset_iff wY W s hwYpos]
            have hk_le : k' ≤ s := le_trans (le_natDegree_of_ne_zero (fun h0 => hnz (by simp [h0]))) hdeg
            have hk_lt : k' < s := by
              by_contra hge
              have hks : k' = s := by omega
              subst hks; exact hnz (hs_10 j' i' hj hi)
            have hw_le := (wdeg_le_iff wY W Q).mp hw k' j' i' hnz
            refine ⟨by omega, by omega, ?_⟩
            have : 2 * (j' / 2) + 1 = j' := by omega
            have : 2 * (i' / 2) = i' := by omega
            nlinarith
        · simp only [h10, ↓reduceIte]
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, ↓reduceIte]
            rcases h01 with ⟨hj, hi, hk⟩
            rw [h_match' k' j' i' hk hj hi]
            by_cases hmem : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
            · rw [dif_pos hmem]; dsimp [c]
              simp [show 2 * (j' / 2) + 1 = j' + 1 by omega, show 2 * (i' / 2) = i' - 1 by omega]
            · rw [dif_neg hmem]
              by_contra hnz
              apply hmem
              rw [mem_kerDIdxFinset_iff wY W s hwYpos]
              have hk_le : k' ≤ s := by
                rw [← h_match' k' j' i' hk hj hi] at hnz
                exact le_trans (le_natDegree_of_ne_zero (fun h0 => hnz (by simp [h0]))) hdeg
              have hw_le : (i' - 1) + (j' + 1) * wY + (k' - 1) * (wY - 1) ≤ W :=
                (wdeg_le_iff wY W Q).mp hw (k' - 1) (j' + 1) (i' - 1) hnz
              refine ⟨by omega, by omega, ?_⟩
              have : 2 * (j' / 2) = j' := by omega
              have : 2 * (i' / 2) = i' - 1 := by omega
              nlinarith
          · simp only [h01, ↓reduceIte]
            have hcases : (j' % 2 = 1 ∧ i' % 2 = 1) ∨ (k' = 0 ∧ j' % 2 = 0 ∧ i' % 2 = 1) := by omega
            rcases hcases with ⟨hj, hi⟩ | ⟨rfl, hj, hi⟩
            · exact h11 k' j' i' hj hi
            · exact h0_01 j' i' hj hi
    exact ⟨c, hQeq, fun c' hc' => huniq c' c (hc'.symm.trans hQeq)⟩
  · rintro ⟨c, rfl, _⟩
    refine ⟨?_, ?_, ?_⟩
    · -- D(∑ cC(c e) * kerDBasisPoly e) = 0
      have hlin : ∀ (s' : Finset (KerDIdx wY W s)) (f : KerDIdx wY W s → ContactPoly A),
          contactDeriv (∑ e ∈ s', f e) = ∑ e ∈ s', contactDeriv (f e) := by
        intro s' f; classical
        induction s' using Finset.induction_on with
        | empty => ext k j i; simp [coeff_contactDeriv, coeff_dXBi]
        | insert a s' ha ih => rw [Finset.sum_insert ha, contactDeriv_add, ih, Finset.sum_insert ha]
      rw [hlin]
      apply Finset.sum_eq_zero
      intro e _
      rw [contactDeriv_mul, contactDeriv_cC, contactDeriv_kerDBasisPoly, zero_mul, mul_zero, add_zero]
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k' hk'
      ext j' i'
      rw [coeff_sum_kerDBasisPoly hwYpos, coeff_zero, coeff_zero]
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, ↓reduceIte]
        by_cases hmem1 : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
        · exfalso; have := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem1).2.1; omega
        · simp [hmem1]
      · simp only [h00, ↓reduceIte]
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, ↓reduceIte]
          by_cases hmem2 : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
          · exfalso; have := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem2).2.1; omega
          · simp [hmem2]
        · simp only [h10, ↓reduceIte]
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, ↓reduceIte]
            by_cases hmem3 : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
            · exfalso; have := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem3).2.1; omega
            · simp [hmem3]
          · simp [h01]
    · rw [wdeg_le_iff]
      intro k' j' i' hne
      rw [coeff_sum_kerDBasisPoly hwYpos] at hne
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, ↓reduceIte] at hne
        by_cases hmem1 : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
        · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem1).2.2
          have : 2 * (j' / 2) = j' := by omega
          have : 2 * (i' / 2) = i' := by omega
          nlinarith
        · simp [hmem1] at hne
      · simp only [h00, ↓reduceIte] at hne
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, ↓reduceIte] at hne
          by_cases hmem2 : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
          · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem2).2.2
            have : 2 * (j' / 2) + 1 = j' := by omega
            have : 2 * (i' / 2) = i' := by omega
            nlinarith
          · simp [hmem2] at hne
        · simp only [h10, ↓reduceIte] at hne
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, ↓reduceIte] at hne
            by_cases hmem3 : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W s
            · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hmem3).2.2
              have h1 : 2 * (j' / 2) = j' := by omega
              have h2 : 2 * (i' / 2) + 1 = i' := by omega
              have hk1 : 1 ≤ k' := h01.2.2
              have h3 : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY, hk1]; ring
              nlinarith
            · simp [hmem3] at hne
          · simp [h01] at hne

end ContactBasis

/-! ### Part 2: Local shifted ring `LocalPoly A = A[R][w][t]` and exact free basis `B(m, s)` -/

/-- Local shifted polynomial ring `A[R][w][t]` (outer `t`, middle `w`, inner `R`). -/
abbrev LocalPoly (A : Type*) [CommRing A] := Polynomial (Polynomial (Polynomial A))

section LocalRing

variable {A : Type*} [CommRing A]

noncomputable def locC (a : A) : LocalPoly A := C (C (C a))
noncomputable def locR : LocalPoly A := C (C X)
noncomputable def locW : LocalPoly A := C X
noncomputable def locT : LocalPoly A := X
/-- Key char-2 contact invariant `u = w^2 + t R^2`. -/
noncomputable def localU : LocalPoly A := locW ^ 2 + locT * locR ^ 2

/-- Coefficient of `t^p w^q` in `A[R]`. -/
noncomputable def twCoeff (H : LocalPoly A) (p q : ℕ) : Polynomial A := (H.coeff p).coeff q

/-- `(t, w)`-valuation is at least `m`: every monomial `t^p w^q R^e` with `p + q < m` vanishes. -/
def twOrdGE (H : LocalPoly A) (m : ℕ) : Prop :=
  ∀ p q, p + q < m → twCoeff H p q = 0

lemma twOrdGE_zero (H : LocalPoly A) : twOrdGE H 0 := by
  intro p q hpq; omega

lemma twOrdGE_of_zero (m : ℕ) : twOrdGE (0 : LocalPoly A) m := by
  intro p q _; simp [twCoeff]

lemma twOrdGE_add {H1 H2 : LocalPoly A} {m : ℕ} (h1 : twOrdGE H1 m) (h2 : twOrdGE H2 m) :
    twOrdGE (H1 + H2) m := by
  intro p q hpq
  have ha := h1 p q hpq
  have hb := h2 p q hpq
  unfold twCoeff at ha hb ⊢
  simp [ha, hb]

lemma twOrdGE_sub {H1 H2 : LocalPoly A} {m : ℕ} (h1 : twOrdGE H1 m) (h2 : twOrdGE H2 m) :
    twOrdGE (H1 - H2) m := by
  intro p q hpq
  have ha := h1 p q hpq
  have hb := h2 p q hpq
  unfold twCoeff at ha hb ⊢
  simp [ha, hb]

lemma twOrdGE_sum {ι : Type*} (S : Finset ι) (f : ι → LocalPoly A) {m : ℕ}
    (hf : ∀ i ∈ S, twOrdGE (f i) m) : twOrdGE (∑ i ∈ S, f i) m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [twOrdGE_of_zero]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact twOrdGE_add (hf a (Finset.mem_insert_self _ _))
        (ih fun y hy => hf y (Finset.mem_insert_of_mem hy))

lemma twOrdGE_mono {H : LocalPoly A} {m1 m2 : ℕ} (hle : m1 ≤ m2) (h : twOrdGE H m2) :
    twOrdGE H m1 := fun p q hpq => h p q (lt_of_lt_of_le hpq hle)

lemma twOrdGE_mul {H1 H2 : LocalPoly A} {m1 m2 : ℕ} (h1 : twOrdGE H1 m1) (h2 : twOrdGE H2 m2) :
    twOrdGE (H1 * H2) (m1 + m2) := by
  intro p q hpq
  unfold twCoeff
  rw [coeff_mul, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro y hy
  have hpx := Finset.mem_antidiagonal.mp hx
  have hqy := Finset.mem_antidiagonal.mp hy
  by_cases hlt1 : x.1 + y.1 < m1
  · have hz := h1 x.1 y.1 hlt1; unfold twCoeff at hz; rw [hz, zero_mul]
  · have hlt2 : x.2 + y.2 < m2 := by omega
    have hz := h2 x.2 y.2 hlt2; unfold twCoeff at hz; rw [hz, mul_zero]

lemma twOrdGE_locW : twOrdGE (locW : LocalPoly A) 1 := by
  intro p q hpq
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst hp; subst hq; simp [twCoeff, locW]

lemma twOrdGE_locT : twOrdGE (locT : LocalPoly A) 1 := by
  intro p q hpq
  have hp : p = 0 := by omega
  have hq : q = 0 := by omega
  subst hp; subst hq; simp [twCoeff, locT]

lemma twOrdGE_localU : twOrdGE (localU : LocalPoly A) 1 := by
  unfold localU
  apply twOrdGE_add
  · rw [sq]; exact twOrdGE_mono (by omega) (twOrdGE_mul twOrdGE_locW twOrdGE_locW)
  · exact twOrdGE_mono (by omega) (twOrdGE_mul twOrdGE_locT (twOrdGE_zero _))

lemma twOrdGE_pow {H : LocalPoly A} {k : ℕ} (h : twOrdGE H k) (n : ℕ) :
    twOrdGE (H ^ n) (k * n) := by
  induction n with
  | zero => simp [twOrdGE_zero]
  | succ n ih =>
      rw [pow_succ, Nat.mul_succ]
      exact twOrdGE_mul ih h

/-- **Exact valuation multiplication theorem over any domain `A`:**
If `F` has exact `(t, w)`-order `k` (i.e. `twOrdGE F k` and some `p+q = k` has `twCoeff F p q ≠ 0`)
and `V` fails `twOrdGE V l`, then `F * V` fails `twOrdGE (F * V) (k + l)`! -/
theorem not_twOrdGE_mul_of_exact_ord [IsDomain A] {F V : LocalPoly A} {k l : ℕ}
    (hFk : twOrdGE F k) (hFex : ∃ p q, p + q = k ∧ twCoeff F p q ≠ 0)
    (hVnot : ¬ twOrdGE V l) : ¬ twOrdGE (F * V) (k + l) := by
  classical
  have hVex : ∃ d < l, ∃ p q, p + q = d ∧ twCoeff V p q ≠ 0 := by
    unfold twOrdGE at hVnot; push Not at hVnot
    rcases hVnot with ⟨p, q, hpq, hne⟩
    exact ⟨p + q, hpq, p, q, rfl, hne⟩
  obtain ⟨d, hd_lt, hd_ex, hVd⟩ :
      ∃ d < l, (∃ p q, p + q = d ∧ twCoeff V p q ≠ 0) ∧ twOrdGE V d := by
    refine ⟨Nat.find hVex, (Nat.find_spec hVex).1, (Nat.find_spec hVex).2, ?_⟩
    intro p q hpq
    by_contra hne
    exact Nat.find_min hVex hpq ⟨lt_trans hpq (Nat.find_spec hVex).1, p, q, rfl, hne⟩
  obtain ⟨pF, hpF_le, hpF_nz, hpF_max⟩ :
      ∃ pF ≤ k, twCoeff F pF (k - pF) ≠ 0 ∧ ∀ p ≤ k, pF < p → twCoeff F p (k - p) = 0 := by
    let sF := (Finset.range (k + 1)).filter fun p => twCoeff F p (k - p) ≠ 0
    have hsF_ne : sF.Nonempty := by
      rcases hFex with ⟨p, q, hpq, hne⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rwa [show k - p = q by omega]
    refine ⟨sF.max' hsF_ne,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem sF hsF_ne)).1),
      (Finset.mem_filter.mp (Finset.max'_mem sF hsF_ne)).2, ?_⟩
    intro p hp hgt
    by_contra hnz
    exact not_lt_of_ge (Finset.le_max' sF p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnz⟩)) hgt
  obtain ⟨pV, hpV_le, hpV_nz, hpV_max⟩ :
      ∃ pV ≤ d, twCoeff V pV (d - pV) ≠ 0 ∧ ∀ p ≤ d, pV < p → twCoeff V p (d - p) = 0 := by
    let sV := (Finset.range (d + 1)).filter fun p => twCoeff V p (d - p) ≠ 0
    have hsV_ne : sV.Nonempty := by
      rcases hd_ex with ⟨p, q, hpq, hne⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      rwa [show d - p = q by omega]
    refine ⟨sV.max' hsV_ne,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem sV hsV_ne)).1),
      (Finset.mem_filter.mp (Finset.max'_mem sV hsV_ne)).2, ?_⟩
    intro p hp hgt
    by_contra hnz
    exact not_lt_of_ge (Finset.le_max' sV p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnz⟩)) hgt
  intro hFV
  have hzero := hFV (pF + pV) ((k - pF) + (d - pV)) (by omega)
  unfold twCoeff at hzero
  rw [coeff_mul, finset_sum_coeff] at hzero
  have hsingle : (∑ x ∈ Finset.antidiagonal (pF + pV), (F.coeff x.1 * V.coeff x.2).coeff ((k - pF) + (d - pV))) =
      twCoeff F pF (k - pF) * twCoeff V pV (d - pV) := by
    rw [Finset.sum_eq_single (pF, pV)]
    · rw [coeff_mul]
      rw [Finset.sum_eq_single (k - pF, d - pV)]
      · rfl
      · intro y hy hne
        have hy_sum := Finset.mem_antidiagonal.mp hy
        have hne' : ¬ (y.1 = k - pF ∧ y.2 = d - pV) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
        by_cases hlt1 : pF + y.1 < k
        · have hz := hFk pF y.1 hlt1; unfold twCoeff at hz; rw [hz, zero_mul]
        · have hlt2 : pV + y.2 < d := by omega
          have hz := hVd pV y.2 hlt2; unfold twCoeff at hz; rw [hz, mul_zero]
      · intro hnot; exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim
    · intro x hx hne
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro y hy
      have hx_sum := Finset.mem_antidiagonal.mp hx
      have hy_sum := Finset.mem_antidiagonal.mp hy
      have hne' : ¬ (x.1 = pF ∧ x.2 = pV) := fun ⟨h1, h2⟩ => hne (Prod.ext h1 h2)
      by_cases hlt1 : x.1 + y.1 < k
      · have hz := hFk x.1 y.1 hlt1; unfold twCoeff at hz; rw [hz, zero_mul]
      · by_cases hlt2 : x.2 + y.2 < d
        · have hz := hVd x.2 y.2 hlt2; unfold twCoeff at hz; rw [hz, mul_zero]
        · have heq1 : x.1 + y.1 = k := by omega
          have heq2 : x.2 + y.2 = d := by omega
          by_cases hx1 : x.1 > pF
          · have hz := hpF_max x.1 (by omega) hx1
            unfold twCoeff at hz
            have : y.1 = k - x.1 := by omega
            rw [this, hz, zero_mul]
          · have hx2 : x.2 > pV := by omega
            have hz := hpV_max x.2 (by omega) hx2
            unfold twCoeff at hz
            have : y.2 = d - x.2 := by omega
            rw [this, hz, mul_zero]
    · intro hnot; exact (hnot (Finset.mem_antidiagonal.mpr rfl)).elim
  rw [hsingle] at hzero
  exact mul_ne_zero hpF_nz hpV_nz hzero

/-- Exact finite basis index set `B(m, s)` for `Φ_m(K(s)) ⊆ A[R][w][t] / (t, w)^m`:
tuples `(q, j, a, b)` with `q + j ≤ s`, `q + a + b < m`, and `j < 2 ∨ a = 0`. -/
def localBasisFinset (m s : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (min (s + 1) m)).biUnion fun q =>
    let mq := m - q
    let tri := (Finset.range mq).biUnion fun a => (Finset.range (mq - a)).image fun b => (a, b)
    (tri.image fun ab => (q, 0, ab.1, ab.2)) ∪
    (if q + 1 ≤ s then tri.image fun ab => (q, 1, ab.1, ab.2) else ∅) ∪
    (if q + 2 ≤ s then
      ((Finset.Ico 2 (s - q + 1)).biUnion fun j =>
        (Finset.range mq).image fun b => (q, j, 0, b))
    else ∅)

abbrev LocalBasisIdx (m s : ℕ) := { e : ℕ × ℕ × ℕ × ℕ // e ∈ localBasisFinset m s }

lemma mem_localBasisFinset_iff (m s q j a b : ℕ) :
    (q, j, a, b) ∈ localBasisFinset m s ↔
      q + j ≤ s ∧ q + a + b < m ∧ (j < 2 ∨ a = 0) := by
  unfold localBasisFinset
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq', hmem⟩
    rcases hmem with (⟨⟨a', b'⟩, ⟨a'', ha'', b'', hb'', rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ | h1) | h2
    · exact ⟨by omega, by omega, Or.inl (by omega)⟩
    · split_ifs at h1 with hqs
      · simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_range, Prod.mk.injEq] at h1
        rcases h1 with ⟨⟨a', b'⟩, ⟨a'', ha'', b'', hb'', rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
        exact ⟨by omega, by omega, Or.inl (by omega)⟩
      · simp at h1
    · split_ifs at h2 with hqs
      · simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image, Finset.mem_range,
          Prod.mk.injEq] at h2
        rcases h2 with ⟨j', hj', b', hb', rfl, rfl, rfl, rfl⟩
        exact ⟨by omega, by omega, Or.inr rfl⟩
      · simp at h2
  · rintro ⟨hqs, hlt, hja⟩
    refine ⟨q, by omega, ?_⟩
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
    · left; left
      exact ⟨(a, b), ⟨a, by omega, b, by omega, by simp⟩, by simp⟩
    · left; right
      have h1 : q + 1 ≤ s := by omega
      simp only [h1, ↓reduceIte, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range, Prod.mk.injEq]
      exact ⟨(a, b), ⟨a, by omega, b, by omega, by simp⟩, by simp⟩
    · right
      have ha0 : a = 0 := by omega
      subst ha0
      have h2 : q + 2 ≤ s := by omega
      simp only [h2, ↓reduceIte, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image,
        Finset.mem_range, Prod.mk.injEq]
      exact ⟨j, ⟨hj2, by omega⟩, b, by omega, by simp⟩

lemma card_tri (n : ℕ) :
    ((Finset.range n).biUnion fun a => (Finset.range (n - a)).image fun b => (a, b)).card =
      n * (n + 1) / 2 := by
  rw [Finset.card_biUnion]
  · trans ∑ a ∈ Finset.range n, (n - a)
    · apply Finset.sum_congr rfl
      intro a _
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_range]
    · induction n with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ']
          simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
          rw [ih]
          have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
          omega
  · intro a1 _ a2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h⟩
    exact hne (Prod.mk.inj h).1.symm

/-- **Exact cardinality theorem:** `|LocalBasisIdx m s| = rankKerD m s`! -/
theorem card_localBasisFinset (m s : ℕ) :
    (localBasisFinset m s).card = rankKerD m s := by
  unfold localBasisFinset rankKerD
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro q hq
    have hq_lt : q < min (s + 1) m := Finset.mem_range.mp hq
    let mq := m - q
    let tri := (Finset.range mq).biUnion fun a => (Finset.range (mq - a)).image fun b => (a, b)
    let S0 := tri.image fun ab => (q, 0, ab.1, ab.2)
    let S1 := if q + 1 ≤ s then tri.image fun ab => (q, 1, ab.1, ab.2) else ∅
    let S2 := if q + 2 ≤ s then
        (Finset.Ico 2 (s - q + 1)).biUnion fun j => (Finset.range mq).image fun b => (q, j, 0, b)
      else ∅
    have hd01 : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]; intro x hx0 hx1
      simp only [S0, Finset.mem_image] at hx0; rcases hx0 with ⟨_, _, rfl⟩
      dsimp [S1] at hx1; split_ifs at hx1 with h
      · simp only [Finset.mem_image] at hx1; rcases hx1 with ⟨_, _, h'⟩; simp at h'
      · simp at hx1
    have hd012 : Disjoint (S0 ∪ S1) S2 := by
      rw [Finset.disjoint_left]; intro x hx01 hx2
      dsimp [S2] at hx2; split_ifs at hx2 with h
      · simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image] at hx2
        rcases hx2 with ⟨j, hj, _, _, rfl⟩
        rcases Finset.mem_union.mp hx01 with hx0 | hx1
        · simp only [S0, Finset.mem_image] at hx0; rcases hx0 with ⟨_, _, h'⟩
          have : j = 0 := (Prod.mk.inj (Prod.mk.inj h').2).1.symm; omega
        · dsimp [S1] at hx1; split_ifs at hx1 with h1
          · simp only [Finset.mem_image] at hx1; rcases hx1 with ⟨_, _, h'⟩
            have : j = 1 := (Prod.mk.inj (Prod.mk.inj h').2).1.symm; omega
          · simp at hx1
      · simp at hx2
    change (S0 ∪ S1 ∪ S2).card = _
    rw [Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
    have hc0 : S0.card = mq * (mq + 1) / 2 := by
      rw [Finset.card_image_of_injective, card_tri]
      intro ab1 ab2 h
      have h1 := Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2
      exact Prod.ext h1.1 h1.2
    have hc1 : S1.card = if q + 1 ≤ s then mq * (mq + 1) / 2 else 0 := by
      dsimp [S1]; split_ifs with h
      · rw [Finset.card_image_of_injective, card_tri]
        intro ab1 ab2 h'
        have h1 := Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h').2).2
        exact Prod.ext h1.1 h1.2
      · simp
    have hc2 : S2.card = if q + 2 ≤ s then (s - 1 - q) * mq else 0 := by
      dsimp [S2]; split_ifs with h
      · rw [Finset.card_biUnion]
        · trans ∑ _j ∈ Finset.Ico 2 (s - q + 1), mq
          · apply Finset.sum_congr rfl; intro j _
            rw [Finset.card_image_of_injective _ (fun _ _ h' => (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h').2).2).2),
              Finset.card_range]
          · rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
            congr 1; omega
        · intro j1 _ j2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_image] at hx1 hx2
          rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h'⟩
          exact hne (Prod.mk.inj (Prod.mk.inj h').2).1.symm
      · simp
    rw [hc0, hc1, hc2]
  · intro q1 _ q2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have hq1 : x.1 = q1 := by
      rcases Finset.mem_union.mp hx1 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · simp only [Finset.mem_image] at h0; rcases h0 with ⟨_, _, rfl⟩; rfl
        · split_ifs at h1 <;> [skip; simp at h1]
          simp only [Finset.mem_image] at h1; rcases h1 with ⟨_, _, rfl⟩; rfl
      · split_ifs at h2 <;> [skip; simp at h2]
        simp only [Finset.mem_biUnion, Finset.mem_image] at h2; rcases h2 with ⟨_, _, _, _, rfl⟩; rfl
    have hq2 : x.1 = q2 := by
      rcases Finset.mem_union.mp hx2 with h01 | h2
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · simp only [Finset.mem_image] at h0; rcases h0 with ⟨_, _, rfl⟩; rfl
        · split_ifs at h1 <;> [skip; simp at h1]
          simp only [Finset.mem_image] at h1; rcases h1 with ⟨_, _, rfl⟩; rfl
      · split_ifs at h2 <;> [skip; simp at h2]
        simp only [Finset.mem_biUnion, Finset.mem_image] at h2; rcases h2 with ⟨_, _, _, _, rfl⟩; rfl
    exact hne (hq1.symm.trans hq2)

lemma card_localBasisIdx (m s : ℕ) :
    Fintype.card (LocalBasisIdx m s) = rankKerD m s := by
  rw [Fintype.card_coe, card_localBasisFinset]

/-- The basis element `w^q * R^j * t^a * u^b` in `LocalPoly A`. -/
noncomputable def localBasisElem (e : ℕ × ℕ × ℕ × ℕ) : LocalPoly A :=
  locW ^ e.1 * locR ^ e.2.1 * locT ^ e.2.2.1 * localU ^ e.2.2.2

/-- Lowest `(t, w)`-degree monomial of `localBasisElem (q, j, a, b)`:
every term has `(t, w)`-degree `≥ q + a + b`, and at exact `(t, w)`-degree `q + a + b`
the ONLY nonzero `twCoeff` is at `(p, q') = (a + b, q)` equal to `R^(j + 2b)`! -/
lemma twCoeff_localBasisElem_min (q j a b p q' : ℕ) (hle : p + q' ≤ q + a + b) :
    twCoeff (localBasisElem (A := A) (q, j, a, b)) p q' =
      if p = a + b ∧ q' = q then X ^ (j + 2 * b) else 0 := by
  -- Expand localU^b = (t R^2 + w^2)^b = (t R^2)^b + w^2 * rest, where w^2 * rest has twOrdGE (b + 1)!
  have hU : ∀ b : ℕ, ∃ rest : LocalPoly A, twOrdGE rest (b + 1) ∧
      localU (A := A) ^ b = locT ^ b * locR ^ (2 * b) + rest := by
    intro b'
    induction b' with
    | zero => exact ⟨0, twOrdGE_of_zero 1, by simp⟩
    | succ b ih =>
        rcases ih with ⟨rest, hrest, hEq⟩
        refine ⟨locW ^ 2 * (locT ^ b * locR ^ (2 * b)) + (locW ^ 2 + locT * locR ^ 2) * rest, ?_, ?_⟩
        · apply twOrdGE_add
          · have h1 : twOrdGE (locW (A := A) ^ 2) 2 := by
              rw [show (2 : ℕ) = 1 * 2 by rfl]; exact twOrdGE_pow twOrdGE_locW 2
            have h2 : twOrdGE (locT (A := A) ^ b * locR ^ (2 * b)) b := by
              simpa using twOrdGE_mul (twOrdGE_pow twOrdGE_locT b) (twOrdGE_zero (locR ^ (2 * b)))
            exact twOrdGE_mono (by omega) (twOrdGE_mul h1 h2)
          · have h1 : twOrdGE (localU (A := A)) 1 := twOrdGE_localU
            exact twOrdGE_mono (by omega) (twOrdGE_mul h1 hrest)
        · rw [pow_succ, hEq, localU]
          have : locT (A := A) ^ (b + 1) * locR ^ (2 * (b + 1)) =
              (locT ^ b * locR ^ (2 * b)) * (locT * locR ^ 2) := by
            rw [pow_succ, show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]; ring
          rw [this]; ring
  rcases hU b with ⟨rest, hrest, hUeq⟩
  have hElem : localBasisElem (A := A) (q, j, a, b) =
      locT ^ (a + b) * locW ^ q * locR ^ (j + 2 * b) +
      locW ^ q * locR ^ j * locT ^ a * rest := by
    unfold localBasisElem
    rw [hUeq, pow_add, pow_add]; ring
  have hrest_big : twOrdGE (locW (A := A) ^ q * locR ^ j * locT ^ a * rest) (q + a + b + 1) := by
    have h1 : twOrdGE (locW (A := A) ^ q) q := by
      simpa using twOrdGE_pow twOrdGE_locW q
    have h2 : twOrdGE (locT (A := A) ^ a) a := by
      simpa using twOrdGE_pow twOrdGE_locT a
    have h3 : twOrdGE (locW (A := A) ^ q * locR ^ j * locT ^ a) (q + a) := by
      have := twOrdGE_mul (twOrdGE_mul h1 (twOrdGE_zero (locR ^ j))) h2
      simpa [add_zero] using this
    exact twOrdGE_mono (by omega) (twOrdGE_mul h3 hrest)
  rw [hElem]
  have hrb := hrest_big p q' (by omega)
  unfold twCoeff at hrb ⊢
  rw [coeff_add, coeff_add, hrb, add_zero]
  -- Evaluate coeff (p, q') of locT^(a+b) * locW^q * locR^(j+2b)
  have hmon : (locT (A := A) ^ (a + b) * locW ^ q * locR ^ (j + 2 * b)) =
      monomial (a + b) (monomial q (X ^ (j + 2 * b))) := by
    unfold locT locW locR
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_pow, map_pow]
    ring
  rw [hmon]
  by_cases h1 : p = a + b <;> by_cases h2 : q' = q <;> simp [h1, h2, coeff_monomial, eq_comm]

/-- **Injectivity of lowest-degree monomials on `B(m, s)`:**
`(q, j, a, b) ↦ (a + b, q, j + 2b)` is injective on `localBasisFinset m s`! -/
lemma localBasis_min_monomial_inj {m s : ℕ} {e1 e2 : LocalBasisIdx m s}
    (hp : e1.1.2.2.1 + e1.1.2.2.2 = e2.1.2.2.1 + e2.1.2.2.2)
    (hq : e1.1.1 = e2.1.1)
    (hR : e1.1.2.1 + 2 * e1.1.2.2.2 = e2.1.2.1 + 2 * e2.1.2.2.2) :
    e1 = e2 := by
  rcases e1 with ⟨⟨q1, j1, a1, b1⟩, h1⟩
  rcases e2 with ⟨⟨q2, j2, a2, b2⟩, h2⟩
  dsimp at hp hq hR
  subst hq
  have hja1 := ((mem_localBasisFinset_iff m s q1 j1 a1 b1).mp h1).2.2
  have hja2 := ((mem_localBasisFinset_iff m s q1 j2 a2 b2).mp h2).2.2
  -- Note (j1 : ℤ) - 2*a1 = (j1 + 2*b1) - 2*(a1 + b1) = (j2 + 2*b2) - 2*(a2 + b2) = (j2 : ℤ) - 2*a2!
  have hdiff : (j1 : ℤ) - 2 * a1 = (j2 : ℤ) - 2 * a2 := by omega
  apply Subtype.ext
  have hj_eq : j1 = j2 ∧ a1 = a2 := by
    rcases hja1 with hj1 | rfl <;> rcases hja2 with hj2 | rfl <;> omega
  rcases hj_eq with ⟨rfl, rfl⟩
  have hb : b1 = b2 := by omega
  subst hb; rfl

/-- **LINEAR INDEPENDENCE OF `B(m, s)` MOD `(t, w)^m` OVER ANY COMMUTATIVE RING `A`!** -/
theorem localBasis_linearIndependent_mod (m s : ℕ) (c : LocalBasisIdx m s → A)
    (hvan : twOrdGE (∑ e : LocalBasisIdx m s, locC (c e) * localBasisElem e.1) m) :
    ∀ e : LocalBasisIdx m s, c e = 0 := by
  classical
  by_contra hnot
  push Not at hnot
  -- Pick minimum (t, w)-order d = q + a + b < m among e with c e ≠ 0!
  let nz := Finset.univ.filter fun e : LocalBasisIdx m s => c e ≠ 0
  have hnz_ne : nz.Nonempty := by
    rcases hnot with ⟨e, he⟩; exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  let degE (e : LocalBasisIdx m s) : ℕ := e.1.1 + e.1.2.2.1 + e.1.2.2.2
  obtain ⟨e0, he0_mem, he0_min⟩ := Finset.exists_min_image nz degE hnz_ne
  have he0_nz : c e0 ≠ 0 := (Finset.mem_filter.mp he0_mem).2
  have hd_lt : degE e0 < m :=
    ((mem_localBasisFinset_iff m s _ _ _ _).mp e0.2).2.1
  let p0 := e0.1.2.2.1 + e0.1.2.2.2
  let q0 := e0.1.1
  have hzero := hvan p0 q0 (by dsimp [p0, q0, degE] at *; omega)
  -- Extract coefficient of R^(e0.j + 2 * e0.b) in twCoeff (∑ ...) p0 q0!
  have hR0 := congrArg (fun P : Polynomial A => P.coeff (e0.1.2.1 + 2 * e0.1.2.2.2)) hzero
  rw [coeff_zero] at hR0
  have hmul : ∀ (a : A) (H : LocalPoly A),
      twCoeff (locC a * H) p0 q0 = C a * twCoeff H p0 q0 := by
    intro a H; unfold locC twCoeff; simp [coeff_C_mul]
  unfold twCoeff at hR0
  rw [finset_sum_coeff, finset_sum_coeff, finset_sum_coeff] at hR0
  have hsum_eq : (∑ e : LocalBasisIdx m s, (((locC (c e) * localBasisElem e.1).coeff p0).coeff q0).coeff
      (e0.1.2.1 + 2 * e0.1.2.2.2)) = c e0 := by
    rw [Finset.sum_eq_single e0]
    · have h := hmul (c e0) (localBasisElem e0.1)
      change (twCoeff (locC (c e0) * localBasisElem e0.1) p0 q0).coeff _ = c e0
      have hmin := twCoeff_localBasisElem_min (A := A) e0.1.1 e0.1.2.1 e0.1.2.2.1 e0.1.2.2.2 p0 q0
        (by dsimp [p0, q0]; omega)
      rw [h, show localBasisElem (A := A) e0.1 = localBasisElem (e0.1.1, e0.1.2.1, e0.1.2.2.1, e0.1.2.2.2) from rfl, hmin]
      simp [p0, q0, coeff_C_mul, coeff_X_pow]
    · intro e _ hne
      by_cases hce : c e = 0
      · simp [hce, locC]
      · have hle : degE e0 ≤ degE e := he0_min e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hce⟩)
        change (twCoeff (locC (c e) * localBasisElem e.1) p0 q0).coeff _ = 0
        have hmin := twCoeff_localBasisElem_min (A := A) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 p0 q0
          (by dsimp [p0, q0, degE] at hle ⊢; omega)
        rw [hmul, show localBasisElem (A := A) e.1 = localBasisElem (e.1.1, e.1.2.1, e.1.2.2.1, e.1.2.2.2) from rfl, hmin]
        split_ifs with hpq
        · rw [coeff_C_mul, coeff_X_pow]
          split_ifs with hR
          · exfalso; exact hne (localBasis_min_monomial_inj hpq.1.symm hpq.2.symm hR.symm)
          · ring
        · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum_eq] at hR0
  exact he0_nz hR0

/-- **3-line `GF(2)`-linear normal form `reduceToBasis`** sending ANY monomial `w^q R^j t^a u^b`
with `q + j ≤ s` into a `ℕ`-count (over `GF(2)`, i.e. `ZMod 2` or `A`-linear combination via `Nat`
reduction, ZERO `Z`-dependence!) of `LocalBasisIdx m s` modulo `(t, w)^m`! -/
def reduceMonomialCoords (m s : ℕ) : ℕ → ℕ → ℕ → ℕ → (LocalBasisIdx m s → ℕ)
  | q, j, 0, b => fun e => if e.1 = (q, j, 0, b) then 1 else 0
  | q, j, a + 1, b =>
      if q + (a + 1) + b ≥ m then fun _ => 0
      else if j < 2 then fun e => if e.1 = (q, j, a + 1, b) then 1 else 0
      else fun e =>
        reduceMonomialCoords m s q (j - 2) a (b + 1) e +
        reduceMonomialCoords m s (q + 2) (j - 2) a b e

/-- Correctness of `reduceMonomialCoords` over ANY char-2 commutative ring `A`:
`w^q R^j t^a u^b - ∑ e, (reduceMonomialCoords m s q j a b e : A) * localBasisElem e ∈ (t, w)^m`! -/
theorem twOrdGE_sub_reduceMonomialCoords [CharP A 2] (m s q j a b : ℕ) (hqs : q + j ≤ s) :
    twOrdGE (localBasisElem (A := A) (q, j, a, b) -
      ∑ e : LocalBasisIdx m s, locC ((reduceMonomialCoords m s q j a b e : ℕ) : A) * localBasisElem e.1) m := by
  induction a generalizing q j b with
  | zero =>
      by_cases hlt : q + 0 + b < m
      · have hmem : (q, j, 0, b) ∈ localBasisFinset m s :=
          (mem_localBasisFinset_iff m s q j 0 b).mpr ⟨hqs, hlt, Or.inr rfl⟩
        have hsum : (∑ e : LocalBasisIdx m s,
            locC ((reduceMonomialCoords m s q j 0 b e : ℕ) : A) * localBasisElem e.1) =
            localBasisElem (q, j, 0, b) := by
          rw [Finset.sum_eq_single ⟨(q, j, 0, b), hmem⟩]
          · simp [reduceMonomialCoords, locC]
          · intro e _ hne
            have hne' : e.1 ≠ (q, j, 0, b) := fun h => hne (Subtype.ext h)
            simp [reduceMonomialCoords, hne', locC]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, sub_self]; exact twOrdGE_of_zero m
      · have hsum : (∑ e : LocalBasisIdx m s,
            locC ((reduceMonomialCoords m s q j 0 b e : ℕ) : A) * localBasisElem e.1) = 0 := by
          apply Finset.sum_eq_zero; intro e _
          rcases e with ⟨⟨q', j', a', b'⟩, he⟩
          have hne' : (q', j', a', b') ≠ (q, j, 0, b) := by
            intro h
            simp only [Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            have := ((mem_localBasisFinset_iff m s q' j' 0 b').mp he).2.1
            omega
          simp [reduceMonomialCoords, hne', locC]
        rw [hsum, sub_zero (G := LocalPoly A)]
        unfold localBasisElem
        have h1 : twOrdGE (locW (A := A) ^ q) q := by simpa using twOrdGE_pow twOrdGE_locW q
        have h2 : twOrdGE (localU (A := A) ^ b) b := by simpa using twOrdGE_pow twOrdGE_localU b
        have h3 := twOrdGE_mul (twOrdGE_mul (twOrdGE_mul h1 (twOrdGE_zero (locR ^ j))) (twOrdGE_zero (locT (A := A) ^ 0))) h2
        exact twOrdGE_mono (by omega) h3
  | succ a ih =>
      unfold reduceMonomialCoords
      split_ifs with hge hj2
      · simp only [Nat.cast_zero, locC, map_zero, zero_mul, Finset.sum_const_zero]
        rw [sub_zero (G := LocalPoly A)]
        unfold localBasisElem
        have h1 : twOrdGE (locW (A := A) ^ q) q := by simpa using twOrdGE_pow twOrdGE_locW q
        have h2 : twOrdGE (locT (A := A) ^ (a + 1)) (a + 1) := by simpa using twOrdGE_pow twOrdGE_locT (a + 1)
        have h3 : twOrdGE (localU (A := A) ^ b) b := by simpa using twOrdGE_pow twOrdGE_localU b
        have h4 := twOrdGE_mul (twOrdGE_mul (twOrdGE_mul h1 (twOrdGE_zero (locR ^ j))) h2) h3
        exact twOrdGE_mono (by omega) h4
      · have hmem : (q, j, a + 1, b) ∈ localBasisFinset m s :=
          (mem_localBasisFinset_iff m s q j (a + 1) b).mpr ⟨hqs, by omega, Or.inl hj2⟩
        have hsum : (∑ e : LocalBasisIdx m s,
            locC (((if e.1 = (q, j, a + 1, b) then 1 else 0 : ℕ) : A)) * localBasisElem e.1) =
            localBasisElem (q, j, a + 1, b) := by
          rw [Finset.sum_eq_single ⟨(q, j, a + 1, b), hmem⟩]
          · simp [locC]
          · intro e _ hne
            have hne' : e.1 ≠ (q, j, a + 1, b) := fun h => hne (Subtype.ext h)
            simp [hne', locC]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, sub_self]; exact twOrdGE_of_zero m
      · -- Key char-2 identity: t * R^2 = localU + w^2!
        have hstep : localBasisElem (A := A) (q, j, a + 1, b) =
            localBasisElem (q, j - 2, a, b + 1) + localBasisElem (q + 2, j - 2, a, b) := by
          unfold localBasisElem; dsimp only
          have hj_eq : j = (j - 2) + 2 := by omega
          have htR2 : locT (A := A) * locR ^ 2 = localU + locW ^ 2 := by
            unfold localU
            have h2w : locW (A := A) ^ 2 + locW ^ 2 = 0 := by
              have h2 : (2 : LocalPoly A) = 0 := by
                ext p q' e; rw [show (2 : LocalPoly A) = locC 2 by rfl, locC]
                simp [CharTwo.two_eq_zero]
              calc locW ^ 2 + locW ^ 2 = (2 : LocalPoly A) * locW ^ 2 := by ring
                _ = 0 := by rw [h2, zero_mul]
            calc locT * locR ^ 2 = (locW ^ 2 + locW ^ 2) + locT * locR ^ 2 := by rw [h2w, zero_add]
              _ = (locW ^ 2 + locT * locR ^ 2) + locW ^ 2 := by ring
          have hR : locR (A := A) ^ j = locR ^ (j - 2) * locR ^ 2 := by
            rw [← pow_add, ← hj_eq]
          calc locW ^ q * locR ^ j * locT ^ (a + 1) * localU ^ b
              = locW ^ q * (locR ^ (j - 2) * locR ^ 2) * (locT ^ a * locT) * localU ^ b := by
                  rw [hR, pow_succ locT a]
            _ = locW ^ q * locR ^ (j - 2) * locT ^ a * localU ^ b * (locT * locR ^ 2) := by ring
            _ = locW ^ q * locR ^ (j - 2) * locT ^ a * localU ^ b * (localU + locW ^ 2) := by rw [htR2]
            _ = locW ^ q * locR ^ (j - 2) * locT ^ a * localU ^ (b + 1) +
                locW ^ (q + 2) * locR ^ (j - 2) * locT ^ a * localU ^ b := by rw [pow_add, pow_succ]; ring
        have hsum_add : (∑ e : LocalBasisIdx m s,
            locC (((reduceMonomialCoords m s q (j - 2) a (b + 1) e +
                   reduceMonomialCoords m s (q + 2) (j - 2) a b e : ℕ) : A)) * localBasisElem e.1) =
            (∑ e : LocalBasisIdx m s,
              locC ((reduceMonomialCoords m s q (j - 2) a (b + 1) e : ℕ) : A) * localBasisElem e.1) +
            (∑ e : LocalBasisIdx m s,
              locC ((reduceMonomialCoords m s (q + 2) (j - 2) a b e : ℕ) : A) * localBasisElem e.1) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e _
          simp only [Nat.cast_add, locC, map_add, add_mul]
        rw [hstep, hsum_add, show ∀ x1 x2 y1 y2 : LocalPoly A, (x1 + x2) - (y1 + y2) = (x1 - y1) + (x2 - y2) by
          intros; ring]
        exact twOrdGE_add (ih q (j - 2) (b + 1) (by omega)) (ih (q + 2) (j - 2) b (by omega))

/-- Local shift of a `KerDIdx` basis element `R^k (Y + X R)^r X^(2a) Y^(2b)` at `(x0, y0)`:
`R^k * (y0 + x0 R + w)^r * (x0^2 + t)^a * (y0^2 + u)^b`! -/
noncomputable def kerDLocalPoly (x0 y0 : A) (e : ℕ × ℕ × ℕ × ℕ) : LocalPoly A :=
  locR ^ e.1 * (locC y0 + locC x0 * locR + locW) ^ e.2.1 *
    (locC (x0 ^ 2) + locT) ^ e.2.2.2 * (locC (y0 ^ 2) + localU) ^ e.2.2.1

/-- Explicit expansion of `kerDLocalPoly x0 y0 (k, r, b, a)` in `(w^q R^j t^a' u^b')` with `q + j ≤ k + r`,
projected onto `LocalBasisIdx m s` via `reduceMonomialCoords`! -/
noncomputable def kerDLocalNF (m s : ℕ) (x0 y0 : A) (e : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) : A :=
  let (k, r, b, a) := e
  ∑ a' ∈ Finset.range (a + 1),
    ∑ b' ∈ Finset.range (b + 1),
      (Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
      ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')) *
      (if r = 0 then
        ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A)
       else
        y0 * ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A) +
        x0 * ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : A) +
        ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : A))

/-- Exact equivalence: `kerDLocalPoly x0 y0 e ≡ ∑ idx, kerDLocalNF m s x0 y0 e idx • localBasisElem idx mod (t, w)^m`! -/
theorem twOrdGE_kerDLocalPoly_sub_NF [CharP A 2] (m s : ℕ) (x0 y0 : A) (k r b a : ℕ)
    (hr : r < 2) (hks : k + r ≤ s) :
    twOrdGE (kerDLocalPoly x0 y0 (k, r, b, a) -
      ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s x0 y0 (k, r, b, a) idx) * localBasisElem idx.1) m := by
  -- Expand (x0^2 + t)^a and (y0^2 + u)^b via Commute.add_pow
  have hpow_a : (locC (x0 ^ 2) + locT) ^ a =
      ∑ a' ∈ Finset.range (a + 1), locC ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a')) * locT ^ a' := by
    rw [add_comm, add_pow (R := LocalPoly A)]
    apply Finset.sum_congr rfl; intro a' _
    have hc : locC (x0 ^ 2) ^ (a - a') * (Nat.choose a a' : LocalPoly A) =
        locC ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a')) := by
      unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
    rw [mul_assoc, hc]; ring
  have hpow_b : (locC (y0 ^ 2) + localU) ^ b =
      ∑ b' ∈ Finset.range (b + 1), locC ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')) * localU ^ b' := by
    rw [add_comm, add_pow (R := LocalPoly A)]
    apply Finset.sum_congr rfl; intro b' _
    have hc : locC (y0 ^ 2) ^ (b - b') * (Nat.choose b b' : LocalPoly A) =
        locC ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')) := by
      unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
    rw [mul_assoc, hc]; ring
  have hscale : ∀ (c : A) (H : LocalPoly A), twOrdGE H m → twOrdGE (locC c * H) m := fun c H hH => by
    simpa using twOrdGE_mul (twOrdGE_zero (locC c)) hH
  have hr01 : r = 0 ∨ r = 1 := by omega
  have hdiff : kerDLocalPoly x0 y0 (k, r, b, a) -
      ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s x0 y0 (k, r, b, a) idx) * localBasisElem idx.1 =
      ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
        locC ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
          ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b'))) *
        (if r = 0 then
          (localBasisElem (0, k, a', b') -
            ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A) * localBasisElem idx.1)
         else
          locC y0 * (localBasisElem (0, k, a', b') -
            ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A) * localBasisElem idx.1) +
          locC x0 * (localBasisElem (0, k + 1, a', b') -
            ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : A) * localBasisElem idx.1) +
          (localBasisElem (1, k, a', b') -
            ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : A) * localBasisElem idx.1)) := by
    unfold kerDLocalPoly kerDLocalNF
    rw [hpow_a, hpow_b]
    simp_rw [locC]
    have hcomm : ∀ (f : ℕ → ℕ → LocalBasisIdx m s → LocalPoly A),
        (∑ idx : LocalBasisIdx m s, ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1), f a' b' idx) =
        ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1), ∑ idx : LocalBasisIdx m s, f a' b' idx := by
      intro f
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a' _; rw [Finset.sum_comm]
    rcases hr01 with rfl | rfl
    · simp only [pow_zero, mul_one, ↓reduceIte]
      have hlhs : locR (A := A) ^ k *
          (∑ a' ∈ Finset.range (a + 1), C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a')))) * locT ^ a') *
          (∑ b' ∈ Finset.range (b + 1), C (C (C ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')))) * localU ^ b') =
          ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b'))))) * localBasisElem (0, k, a', b') := by
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem; simp only [pow_zero, one_mul, map_mul]; ring
      rw [hlhs]
      have hrhs : (∑ idx : LocalBasisIdx m s,
          C (C (C (∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            (Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')) *
              ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A)))) * localBasisElem idx.1) =
          ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b'))))) *
            ∑ idx : LocalBasisIdx m s,
              C (C (C ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A))) * localBasisElem idx.1 := by
        simp_rw [map_sum, Finset.sum_mul]
        rw [hcomm]
        apply Finset.sum_congr rfl; intro a' _
        apply Finset.sum_congr rfl; intro b' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro idx _
        simp only [map_mul]; ring
      rw [hrhs, ← Finset.sum_sub_distrib (G := LocalPoly A)]
      apply Finset.sum_congr rfl; intro a' _
      rw [← Finset.sum_sub_distrib (G := LocalPoly A)]
      apply Finset.sum_congr rfl; intro b' _
      ring
    · simp only [pow_one, one_ne_zero, ↓reduceIte]
      have hlhs : locR (A := A) ^ k * (C (C (C y0)) + C (C (C x0)) * locR + locW) *
          (∑ a' ∈ Finset.range (a + 1), C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a')))) * locT ^ a') *
          (∑ b' ∈ Finset.range (b + 1), C (C (C ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')))) * localU ^ b') =
          ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b'))))) *
            (C (C (C y0)) * localBasisElem (0, k, a', b') +
             C (C (C x0)) * localBasisElem (0, k + 1, a', b') +
             localBasisElem (1, k, a', b')) := by
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem; simp only [pow_zero, pow_one, one_mul, map_mul, pow_succ]; ring
      rw [hlhs]
      have hrhs : (∑ idx : LocalBasisIdx m s,
          C (C (C (∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            (Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b')) *
              (y0 * ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A) +
               x0 * ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : A) +
               ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : A))))) * localBasisElem idx.1) =
          ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1),
            C (C (C ((Nat.choose a a' : A) * (x0 ^ 2) ^ (a - a') *
              ((Nat.choose b b' : A) * (y0 ^ 2) ^ (b - b'))))) *
            (C (C (C y0)) * (∑ idx : LocalBasisIdx m s,
                C (C (C ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : A))) * localBasisElem idx.1) +
             C (C (C x0)) * (∑ idx : LocalBasisIdx m s,
                C (C (C ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : A))) * localBasisElem idx.1) +
             (∑ idx : LocalBasisIdx m s,
                C (C (C ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : A))) * localBasisElem idx.1)) := by
        simp_rw [map_sum, Finset.sum_mul]
        rw [hcomm]
        apply Finset.sum_congr rfl; intro a' _
        apply Finset.sum_congr rfl; intro b' _
        simp_rw [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro idx _
        simp only [map_mul, map_add]; ring
      rw [hrhs, ← Finset.sum_sub_distrib (G := LocalPoly A)]
      apply Finset.sum_congr rfl; intro a' _
      rw [← Finset.sum_sub_distrib (G := LocalPoly A)]
      apply Finset.sum_congr rfl; intro b' _
      ring
  rw [hdiff]
  apply twOrdGE_sum; intro a' _
  apply twOrdGE_sum; intro b' _
  apply hscale
  split_ifs with hr0
  · exact twOrdGE_sub_reduceMonomialCoords m s 0 k a' b' (by omega)
  · apply twOrdGE_add
    · apply twOrdGE_add
      · exact hscale _ _ (twOrdGE_sub_reduceMonomialCoords m s 0 k a' b' (by omega))
      · exact hscale _ _ (twOrdGE_sub_reduceMonomialCoords m s 0 (k + 1) a' b' (by omega))
    · exact twOrdGE_sub_reduceMonomialCoords m s 1 k a' b' (by omega)

/-- **Z-degree bound for `kerDLocalNF` when `A = F[Z]`:**
If `deg_Z(x0) = 0` and `deg_Z(y0) ≤ dy`, then for `e = (k, r, b, a) ∈ KerDIdx wY W s`:
`deg_Z(kerDLocalNF m s x0 y0 e idx) ≤ dy * (2 * b + r) ≤ dy * (W / wY)`! -/
lemma natDegree_kerDLocalNF_le {F : Type*} [Field F] {wY W s m dy : ℕ} (hwY : 1 ≤ wY)
    (x0 : F) (y0 : Polynomial F) (hy0 : y0.natDegree ≤ dy)
    (e : KerDIdx wY W s) (idx : LocalBasisIdx m s) :
    (kerDLocalNF m s (C x0) y0 e.1 idx).natDegree ≤ dy * (W / wY) := by
  rcases e with ⟨⟨k, r, b, a⟩, he⟩
  have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) k r b a).mp he
  have hbr : 2 * b + r ≤ W / wY := by
    have : (2 * b + r) * wY ≤ W := by nlinarith [hmem.2.2]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < wY)).mpr this
  unfold kerDLocalNF
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a' _ => ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b' hb' => ?_)
  have hb'_le : b' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
  have hC1 : (((Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a'))).natDegree = 0 := by
    have : (Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a') =
        C ((Nat.choose a a' : F) * (x0 ^ 2) ^ (a - a')) := by simp
    rw [this, natDegree_C]
  have hY : ((Nat.choose b b' : Polynomial F) * (y0 ^ 2) ^ (b - b')).natDegree ≤ 2 * dy * (b - b') := by
    calc _ ≤ (Nat.choose b b' : Polynomial F).natDegree + ((y0 ^ 2) ^ (b - b')).natDegree :=
            natDegree_mul_le
      _ ≤ 0 + (b - b') * (y0 ^ 2).natDegree := by
            have h0 : (Nat.choose b b' : Polynomial F).natDegree = 0 := natDegree_natCast _
            rw [h0]; exact Nat.add_le_add_left (natDegree_pow_le) 0
      _ ≤ (b - b') * (2 * dy) := by
            rw [zero_add]
            exact Nat.mul_le_mul_left _ (natDegree_pow_le.trans (by omega))
      _ = 2 * dy * (b - b') := by ring
  have hTail : (if r = 0 then
        ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F)
       else
        y0 * ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F) +
        C x0 * ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : Polynomial F) +
        ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : Polynomial F)).natDegree ≤ dy * r := by
    split_ifs with hr0
    · simp [natDegree_natCast]
    · have hr1 : r = 1 := by omega
      subst hr1; rw [mul_one]
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp [natDegree_natCast]))
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (by simp [natDegree_natCast, hy0])
      · exact natDegree_mul_le.trans (by simp [natDegree_C, natDegree_natCast])
  calc _ ≤ ((Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a') *
            ((Nat.choose b b' : Polynomial F) * (y0 ^ 2) ^ (b - b'))).natDegree + dy * r :=
          natDegree_mul_le.trans (Nat.add_le_add_left hTail _)
    _ ≤ (0 + 2 * dy * (b - b')) + dy * r := by
          exact Nat.add_le_add_right (natDegree_mul_le.trans (by rw [hC1]; exact Nat.add_le_add_left hY 0)) _
    _ ≤ dy * (2 * b + r) := by have : b - b' ≤ b := Nat.sub_le b b'; nlinarith
    _ ≤ dy * (W / wY) := Nat.mul_le_mul_left dy hbr

/-! ### Part 3: Contact evaluation `evalContact Q P` and `(X - x0)^(2m)` divisibility -/

/-- Evaluate `Q ∈ ContactPoly F = F[X][Y][R]` at `(X, P(X), P'(X))`. -/
noncomputable def evalContact {F : Type*} [CommRing F] (Q : ContactPoly F) (P : Polynomial F) :
    Polynomial F :=
  (Q.map (evalRingHom P)).eval P.derivative

lemma evalContact_add {F : Type*} [CommRing F] (Q1 Q2 : ContactPoly F) (P : Polynomial F) :
    evalContact (Q1 + Q2) P = evalContact Q1 P + evalContact Q2 P := by
  unfold evalContact; simp [Polynomial.map_add, eval_add]

lemma evalContact_mul {F : Type*} [CommRing F] (Q1 Q2 : ContactPoly F) (P : Polynomial F) :
    evalContact (Q1 * Q2) P = evalContact Q1 P * evalContact Q2 P := by
  unfold evalContact; simp [Polynomial.map_mul, eval_mul]

lemma evalContact_cC {F : Type*} [CommRing F] (a : F) (P : Polynomial F) :
    evalContact (cC a) P = C a := by
  unfold evalContact cC; simp

lemma evalContact_cX {F : Type*} [CommRing F] (P : Polynomial F) :
    evalContact cX P = X := by
  unfold evalContact cX; simp

lemma evalContact_cY {F : Type*} [CommRing F] (P : Polynomial F) :
    evalContact cY P = P := by
  unfold evalContact cY; simp

lemma evalContact_cR {F : Type*} [CommRing F] (P : Polynomial F) :
    evalContact cR P = P.derivative := by
  unfold evalContact cR; simp

lemma evalContact_sum {F ι : Type*} [CommRing F] (S : Finset ι) (f : ι → ContactPoly F) (P : Polynomial F) :
    evalContact (∑ i ∈ S, f i) P = ∑ i ∈ S, evalContact (f i) P := by
  classical
  induction S using Finset.induction_on with
  | empty => unfold evalContact; simp
  | insert a s ha ih => rw [Finset.sum_insert ha, evalContact_add, ih, Finset.sum_insert ha]

/-- Weighted degree controls `natDegree (evalContact Q P)`:
if `P.natDegree ≤ D` and `wdeg D Q ≤ W`, then `(evalContact Q P).natDegree ≤ W`! -/
theorem natDegree_evalContact_le {F : Type*} [CommRing F] (D W : ℕ) (hD : 1 ≤ D)
    (Q : ContactPoly F) (P : Polynomial F) (hP : P.natDegree ≤ D) (hw : wdeg D Q ≤ W) :
    (evalContact Q P).natDegree ≤ W := by
  have hPd : P.derivative.natDegree ≤ D - 1 := by
    exact (natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
  unfold evalContact
  rw [eval_eq_sum_range]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
  dsimp only [Function.comp_apply]
  rw [coeff_map]
  by_cases hqk : Q.coeff k = 0
  · simp [hqk]
  · rw [coe_evalRingHom, eval_eq_sum_range, Finset.sum_mul]
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
    by_cases hqj : (Q.coeff k).coeff j = 0
    · simp [hqj]
    · have hi_deg : ((Q.coeff k).coeff j).natDegree + j * D + k * (D - 1) ≤ W := by
        have hnz : ((Q.coeff k).coeff j).coeff ((Q.coeff k).coeff j).natDegree ≠ 0 :=
          leadingCoeff_ne_zero.mpr hqj
        exact (wdeg_le_iff D W Q).mp hw k j _ hnz
      calc (((Q.coeff k).coeff j) * P ^ j * P.derivative ^ k).natDegree
          ≤ (((Q.coeff k).coeff j) * P ^ j).natDegree + (P.derivative ^ k).natDegree := natDegree_mul_le
        _ ≤ (((Q.coeff k).coeff j).natDegree + (P ^ j).natDegree) + k * P.derivative.natDegree :=
            Nat.add_le_add natDegree_mul_le natDegree_pow_le
        _ ≤ ((Q.coeff k).coeff j).natDegree + j * P.natDegree + k * (D - 1) := by
            have := natDegree_pow_le (p := P) (n := j)
            nlinarith
        _ ≤ W := by nlinarith

/-- Evaluate `LocalPoly F = F[R][w][t]` at `t = (X - x0)^2`, `w = P - y0 - (X - x0)*P'`, `R = P'`. -/
noncomputable def evalLocal {F : Type*} [CommRing F] (x0 y0 : F) (P : Polynomial F) :
    LocalPoly F →+* Polynomial F :=
  eval₂RingHom
    (eval₂RingHom
      (eval₂RingHom C P.derivative)
      (P - C y0 - (X - C x0) * P.derivative))
    ((X - C x0) ^ 2)

lemma evalLocal_locC {F : Type*} [CommRing F] (x0 y0 a : F) (P : Polynomial F) :
    evalLocal x0 y0 P (locC a) = C a := by
  unfold evalLocal locC; simp

lemma evalLocal_locR {F : Type*} [CommRing F] (x0 y0 : F) (P : Polynomial F) :
    evalLocal x0 y0 P locR = P.derivative := by
  unfold evalLocal locR; simp

lemma evalLocal_locW {F : Type*} [CommRing F] (x0 y0 : F) (P : Polynomial F) :
    evalLocal x0 y0 P locW = P - C y0 - (X - C x0) * P.derivative := by
  unfold evalLocal locW; simp

lemma evalLocal_locT {F : Type*} [CommRing F] (x0 y0 : F) (P : Polynomial F) :
    evalLocal x0 y0 P locT = (X - C x0) ^ 2 := by
  unfold evalLocal locT; simp

lemma evalLocal_localU {F : Type*} [CommRing F] [CharP F 2] (x0 y0 : F) (P : Polynomial F) :
    evalLocal x0 y0 P localU = P ^ 2 + C (y0 ^ 2) := by
  unfold localU
  rw [map_add, map_pow, map_mul, map_pow, evalLocal_locW, evalLocal_locT, evalLocal_locR]
  have h2 : (2 : Polynomial F) = 0 := by simp [CharTwo.two_eq_zero]
  have hsq : ∀ a b : Polynomial F, (a - b) ^ 2 = a ^ 2 + b ^ 2 := fun a b => by
    calc (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by ring
      _ = a ^ 2 + b ^ 2 := by rw [h2]; ring
  rw [hsq, hsq, mul_pow, map_pow]
  have hadd : ∀ a : Polynomial F, a + a = 0 := fun a => by
    calc a + a = 2 * a := by ring
      _ = 0 := by rw [h2, zero_mul]
  calc P ^ 2 + C y0 ^ 2 + (X - C x0) ^ 2 * P.derivative ^ 2 + (X - C x0) ^ 2 * P.derivative ^ 2
      = P ^ 2 + C y0 ^ 2 + ((X - C x0) ^ 2 * P.derivative ^ 2 + (X - C x0) ^ 2 * P.derivative ^ 2) := by ring
    _ = P ^ 2 + C y0 ^ 2 := by rw [hadd, add_zero]

/-- Exact match on every `kerDBasisPoly` element:
`evalLocal x0 y0 P (kerDLocalPoly x0 y0 e) = evalContact (kerDBasisPoly e) P`! -/
theorem evalLocal_kerDLocalPoly {F : Type*} [CommRing F] [CharP F 2]
    (x0 y0 : F) (P : Polynomial F) (e : ℕ × ℕ × ℕ × ℕ) :
    evalLocal x0 y0 P (kerDLocalPoly x0 y0 e) = evalContact (kerDBasisPoly e) P := by
  unfold kerDLocalPoly kerDBasisPoly
  have h2 : (2 : Polynomial F) = 0 := by simp [CharTwo.two_eq_zero]
  have hadd : ∀ a : Polynomial F, a + a = 0 := fun a => by
    calc a + a = 2 * a := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hsub_eq_add : ∀ a b : Polynomial F, a - b = a + b := fun a b => by
    calc a - b = a + b - 2 * b := by ring
      _ = a + b := by rw [h2]; ring
  have hX2 : evalLocal x0 y0 P (locC (x0 ^ 2) + locT) = X ^ 2 := by
    rw [map_add, evalLocal_locC, evalLocal_locT, map_pow, hsub_eq_add]
    calc C x0 ^ 2 + (X + C x0) ^ 2 = (C x0 ^ 2 + C x0 ^ 2) + 2 * X * C x0 + X ^ 2 := by ring
      _ = X ^ 2 := by rw [hadd, h2]; ring
  have hY2 : evalLocal x0 y0 P (locC (y0 ^ 2) + localU) = P ^ 2 := by
    rw [map_add, evalLocal_locC, evalLocal_localU]
    calc C (y0 ^ 2) + (P ^ 2 + C (y0 ^ 2)) = P ^ 2 + (C (y0 ^ 2) + C (y0 ^ 2)) := by ring
      _ = P ^ 2 := by rw [hadd, add_zero]
  have hYXR : evalLocal x0 y0 P (locC y0 + locC x0 * locR + locW) = P + X * P.derivative := by
    rw [map_add, map_add, map_mul, evalLocal_locC, evalLocal_locC, evalLocal_locR, evalLocal_locW]
    rw [hsub_eq_add, hsub_eq_add, hsub_eq_add]
    calc C y0 + C x0 * P.derivative + (P + C y0 + (X + C x0) * P.derivative)
        = (C y0 + C y0) + (C x0 * P.derivative + C x0 * P.derivative) + (P + X * P.derivative) := by ring
      _ = P + X * P.derivative := by rw [hadd, hadd, zero_add, zero_add]
  simp only [map_mul, map_pow, evalLocal_locR, hX2, hY2, hYXR,
    evalContact_mul, evalContact_add, evalContact_cR, evalContact_cY, evalContact_cX,
    show ∀ (Q : ContactPoly F) (n : ℕ), evalContact (Q ^ n) P = (evalContact Q P) ^ n from
      fun Q n => by induction n with
        | zero => unfold evalContact; simp
        | succ n ih => rw [pow_succ, pow_succ, evalContact_mul, ih]]

/-- **2-line char-2 Taylor divisibility:**
If `P(x0) = y0` in char 2, then `(X - C x0)^2 ∣ P - C y0 - (X - C x0) * P'`! -/
theorem sq_dvd_contact_w {F : Type*} [CommRing F] [CharP F 2] (x0 : F) (P : Polynomial F) :
    (X - C x0) ^ 2 ∣ P - C (P.eval x0) - (X - C x0) * P.derivative := by
  let W : Polynomial F := P - C (P.eval x0) - (X - C x0) * P.derivative
  have hW0 : W.eval x0 = 0 := by simp [W]
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hW0
  -- Differentiate W = (X - C x0) * Q! In char 2, P'' = 0, so W' = 0!
  have hPdd : P.derivative.derivative = 0 := by
    ext n
    rw [coeff_derivative, coeff_derivative, coeff_zero]
    have h2 : (((n + 1 : ℕ) : F) + 1) * ((n : F) + 1) = 0 := by
      have hev : 2 ∣ (n + 2) * (n + 1) := by
        rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
        · exact ⟨(2 * k + 3) * (k + 1), by ring⟩
      obtain ⟨t, ht⟩ := hev
      have hcast : (((n + 1 : ℕ) : F) + 1) * ((n : F) + 1) = (((n + 2) * (n + 1) : ℕ) : F) := by
        push_cast; ring
      rw [hcast, ht, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
    calc P.coeff (n + 1 + 1) * (((n + 1 : ℕ) : F) + 1) * ((n : F) + 1)
        = P.coeff (n + 1 + 1) * ((((n + 1 : ℕ) : F) + 1) * ((n : F) + 1)) := by ring
      _ = 0 := by rw [h2, mul_zero]
  have hWd : W.derivative = 0 := by
    dsimp [W]
    rw [derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_mul,
      derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, hPdd, mul_zero, add_zero, sub_self]
  have hQ0 : Q.eval x0 = 0 := by
    rw [hQ, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hWd
    have h := congrArg (fun R : Polynomial F => R.eval x0) hWd
    simpa using h
  obtain ⟨R, hR⟩ := dvd_iff_isRoot.mpr hQ0
  refine ⟨R, ?_⟩
  change W = _
  rw [hQ, hR, sq, mul_assoc]

/-- **`twOrdGE H m` gives `(X - C x0)^(2m) ∣ evalLocal x0 y0 P H` whenever `P(x0) = y0`!** -/
theorem pow_two_mul_dvd_evalLocal_of_twOrdGE {F : Type*} [CommRing F] [CharP F 2]
    (x0 y0 : F) (P : Polynomial F) (hPy : P.eval x0 = y0) {H : LocalPoly F} {m : ℕ}
    (hord : twOrdGE H m) :
    (X - C x0) ^ (2 * m) ∣ evalLocal x0 y0 P H := by
  have hw_dvd : (X - C x0) ^ 2 ∣ (P - C y0 - (X - C x0) * P.derivative) := by
    rw [← hPy]; exact sq_dvd_contact_w x0 P
  rw [evalLocal]
  change (X - C x0) ^ (2 * m) ∣ eval₂ _ _ H
  rw [eval₂_eq_sum_range]
  apply Finset.dvd_sum; intro p _
  change (X - C x0) ^ (2 * m) ∣ eval₂ _ _ (H.coeff p) * _
  rw [eval₂_eq_sum_range, Finset.sum_mul]
  apply Finset.dvd_sum; intro q _
  by_cases hlt : p + q < m
  · have hz : (H.coeff p).coeff q = 0 := hord p q hlt
    simp [hz]
  · have hge : m ≤ p + q := by omega
    have h1 : (X - C x0) ^ (2 * q) ∣ (P - C y0 - (X - C x0) * P.derivative) ^ q := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd hw_dvd q
    have h2 : (X - C x0) ^ (2 * p) = ((X - C x0) ^ 2) ^ p := by rw [pow_mul]
    have h3 : (X - C x0) ^ (2 * m) ∣ (X - C x0) ^ (2 * q) * (X - C x0) ^ (2 * p) := by
      rw [← pow_add]; exact pow_dvd_pow _ (by omega)
    rw [← h2, mul_assoc]
    exact h3.trans (dvd_mul_of_dvd_right (mul_dvd_mul h1 dvd_rfl) _)

/-! ### Part 4: Specialized 4-variable contact polynomials `Q ∈ K_W(s)[Z]_{≤ D_Z}` -/

/-- Specialize `Z ↦ z` on `ContactPoly (Polynomial F)`. -/
noncomputable def evalZContact {F : Type*} [CommRing F] (Q : ContactPoly (Polynomial F)) (z : F) :
    ContactPoly F :=
  Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (evalRingHom z)))

/-- Specialize `Z ↦ z` on `LocalPoly (Polynomial F)`. -/
noncomputable def evalZLocal {F : Type*} [CommRing F] (H : LocalPoly (Polynomial F)) (z : F) :
    LocalPoly F :=
  H.map (Polynomial.mapRingHom (Polynomial.mapRingHom (evalRingHom z)))

lemma evalZLocal_add {F : Type*} [CommRing F] (H1 H2 : LocalPoly (Polynomial F)) (z : F) :
    evalZLocal (H1 + H2) z = evalZLocal H1 z + evalZLocal H2 z := by
  unfold evalZLocal; simp [Polynomial.map_add]

lemma evalZLocal_mul {F : Type*} [CommRing F] (H1 H2 : LocalPoly (Polynomial F)) (z : F) :
    evalZLocal (H1 * H2) z = evalZLocal H1 z * evalZLocal H2 z := by
  unfold evalZLocal; simp [Polynomial.map_mul]

lemma evalZLocal_locC {F : Type*} [CommRing F] (a : Polynomial F) (z : F) :
    evalZLocal (locC a) z = locC (a.eval z) := by
  unfold evalZLocal locC; simp

lemma evalZLocal_locR {F : Type*} [CommRing F] (z : F) :
    evalZLocal (locR : LocalPoly (Polynomial F)) z = locR := by
  unfold evalZLocal locR; simp

lemma evalZLocal_locW {F : Type*} [CommRing F] (z : F) :
    evalZLocal (locW : LocalPoly (Polynomial F)) z = locW := by
  unfold evalZLocal locW; simp

lemma evalZLocal_locT {F : Type*} [CommRing F] (z : F) :
    evalZLocal (locT : LocalPoly (Polynomial F)) z = locT := by
  unfold evalZLocal locT; simp

lemma evalZLocal_localU {F : Type*} [CommRing F] (z : F) :
    evalZLocal (localU : LocalPoly (Polynomial F)) z = localU := by
  unfold localU; rw [evalZLocal_add, evalZLocal_mul]
  simp [evalZLocal, locW, locT, locR]

lemma evalZLocal_kerDLocalPoly {F : Type*} [CommRing F] (x0 : F) (y0 : Polynomial F)
    (e : ℕ × ℕ × ℕ × ℕ) (z : F) :
    evalZLocal (kerDLocalPoly (C x0) y0 e) z = kerDLocalPoly x0 (y0.eval z) e := by
  unfold kerDLocalPoly
  have hpow : ∀ (H : LocalPoly (Polynomial F)) (n : ℕ),
      evalZLocal (H ^ n) z = (evalZLocal H z) ^ n := fun H n => by
    unfold evalZLocal; rw [Polynomial.map_pow]
  simp [evalZLocal_mul, evalZLocal_add, hpow, evalZLocal_locR, evalZLocal_locW,
    evalZLocal_locT, evalZLocal_localU, evalZLocal_locC]

lemma evalZContact_kerDBasisPoly {F : Type*} [CommRing F] (e : ℕ × ℕ × ℕ × ℕ) (z : F) :
    evalZContact (kerDBasisPoly e) z = kerDBasisPoly e := by
  unfold kerDBasisPoly evalZContact cR cY cX
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add]

lemma evalZContact_cC {F : Type*} [CommRing F] (a : Polynomial F) (z : F) :
    evalZContact (cC a) z = cC (a.eval z) := by
  unfold evalZContact cC; simp

lemma twOrdGE_evalZLocal {F : Type*} [CommRing F] {H : LocalPoly (Polynomial F)} {m : ℕ}
    (h : twOrdGE H m) (z : F) : twOrdGE (evalZLocal H z) m := by
  intro p q hpq
  unfold evalZLocal twCoeff
  rw [coeff_map, coe_mapRingHom, coeff_map, show (H.coeff p).coeff q = 0 from h p q hpq, map_zero]

/-- Linear algebra pigeonhole over a field `F`: if `|I| > |J|`, any linear map `(I → F) →ₗ[F] (J → F)`
has a nonzero vector in its kernel! -/
lemma exists_ne_zero_ker_linearMap {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (L : (I → F) →ₗ[F] (J → F)) (hlt : Fintype.card J < Fintype.card I) :
    ∃ v : I → F, v ≠ 0 ∧ L v = 0 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hne
    exact h v hne hv
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi, Module.finrank_pi] at hle
  omega

/-- Reconstruct a `ContactPoly (Polynomial F)` from its `KerDIdx` coordinates of `Z`-degree `≤ D_Z`. -/
noncomputable def buildContactPoly {F : Type*} [CommRing F] {wY W s D_Z : ℕ}
    (v : KerDIdx wY W s × Fin (D_Z + 1) → F) : ContactPoly (Polynomial F) :=
  ∑ e : KerDIdx wY W s,
    cC (∑ t : Fin (D_Z + 1), C (v (e, t)) * X ^ t.val) * kerDBasisPoly e.1

lemma buildContactPoly_eq_zero_iff {F : Type*} [CommRing F] {wY W s D_Z : ℕ}
    (hwY : 0 < wY) (v : KerDIdx wY W s × Fin (D_Z + 1) → F) :
    buildContactPoly v = 0 ↔ v = 0 := by
  constructor
  · intro h0
    funext ⟨e, t⟩
    have hc : (∑ t' : Fin (D_Z + 1), C (v (e, t')) * X ^ t'.val) = 0 := by
      rcases e with ⟨⟨k, r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s hwY k r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) h0
        unfold buildContactPoly at h
        rw [coeff_sum_kerDBasisPoly hwY, coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) h0
        unfold buildContactPoly at h
        rw [coeff_sum_kerDBasisPoly hwY, coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
    rw [finset_sum_coeff, coeff_zero] at ht
    rw [Finset.sum_eq_single t] at ht
    · simpa [coeff_C_mul, coeff_X_pow] using ht
    · intro t' _ hne
      have : t.val ≠ t'.val := fun h => hne (Fin.ext h.symm)
      simp [coeff_C_mul, coeff_X_pow, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rintro rfl; unfold buildContactPoly; simp [cC]

/-- Local shift of `buildContactPoly v` at `(x0, y0)`. -/
noncomputable def buildLocalShift {F : Type*} [CommRing F] {wY W s D_Z : ℕ}
    (x0 : F) (y0 : Polynomial F) (v : KerDIdx wY W s × Fin (D_Z + 1) → F) :
    LocalPoly (Polynomial F) :=
  ∑ e : KerDIdx wY W s,
    locC (∑ t : Fin (D_Z + 1), C (v (e, t)) * X ^ t.val) * kerDLocalPoly (C x0) y0 e.1

/-- **Global 4-variable contact interpolation theorem!**
Works for BOTH MCA (`dy = 1, D_ZF = 13000, m0 = 8, s0 = 2`) AND ScalarList (`dy = 0, D_ZF = 0`)! -/
theorem exists_global_contact_interpolant {F ι : Type*} [Field F] [CharP F 2] [Fintype ι]
    (x : ι → F) (y : ι → Polynomial F) {dy wY W0 s0 m0 D_ZF : ℕ}
    (hwY : 1 ≤ wY) (hy : ∀ i, (y i).natDegree ≤ dy)
    (hsurplus : Fintype.card ι * rankKerD m0 s0 * (D_ZF + dy * (W0 / wY) + 1) <
      varsKerDExact wY W0 s0 * (D_ZF + 1)) :
    ∃ (Q : ContactPoly (Polynomial F)) (v : KerDIdx wY W0 s0 × Fin (D_ZF + 1) → F),
      Q = buildContactPoly v ∧ Q ≠ 0 ∧
      contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 ∧
      (∀ k j i, (((Q.coeff k).coeff j).coeff i).natDegree ≤ D_ZF) ∧
      ∀ i : ι, twOrdGE (buildLocalShift (x i) (y i) v) m0 := by
  classical
  let D_eq := D_ZF + dy * (W0 / wY)
  let I := KerDIdx wY W0 s0 × Fin (D_ZF + 1)
  let J := ι × LocalBasisIdx m0 s0 × Fin (D_eq + 1)
  -- Linear map extracting Z-coefficients of local NF at every (i, idx)
  let L : (I → F) →ₗ[F] (J → F) :=
    { toFun := fun v j =>
        let (i, idx, t) := j
        (∑ e : KerDIdx wY W0 s0,
          (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).coeff t.val
      map_add' := by
        intro v1 v2; funext ⟨i, idx, t⟩
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, coeff_add, finset_sum_coeff]
      map_smul' := by
        intro c v; funext ⟨i, idx, t⟩
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, mul_assoc,
          ← Finset.mul_sum, finset_sum_coeff, coeff_C_mul] }
  have hcard : Fintype.card J < Fintype.card I := by
    simp only [I, J, Fintype.card_prod, Fintype.card_fin, card_kerDIdx wY W0 s0 (by omega),
      card_localBasisIdx m0 s0]
    simpa [D_eq, mul_assoc] using hsurplus
  obtain ⟨v, hv_ne, hLv⟩ := exists_ne_zero_ker_linearMap L hcard
  let Q := buildContactPoly v
  have hQne : Q ≠ 0 := mt (buildContactPoly_eq_zero_iff (by omega) v).mp hv_ne
  have hQmem : contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 := by
    refine (mem_kerD_iff_exists_unique_coords hwY Q).mpr ⟨fun e => ∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val, rfl, ?_⟩
    intro c' hc'
    -- uniqueness already proved inside mem_kerD_iff_exists_unique_coords; reuse via ext!
    funext ⟨⟨k, r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [Q] at h; unfold buildContactPoly at h
      rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [Q] at h; unfold buildContactPoly at h
      rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  refine ⟨Q, v, rfl, hQne, hQmem.1, hQmem.2.1, hQmem.2.2, ?_, ?_⟩
  · -- deg_Z of every coefficient ≤ D_ZF
    intro k j i
    dsimp only [Q]; unfold buildContactPoly
    rw [coeff_sum_kerDBasisPoly (by omega)]
    have hpoly : ∀ e : KerDIdx wY W0 s0,
        (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val).natDegree ≤ D_ZF := fun e => by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ => ?_)
      exact natDegree_C_mul_X_pow_le _ _ |>.trans (Nat.lt_succ_iff.mp t.isLt)
    by_cases h00 : j % 2 = 0 ∧ i % 2 = 0
    · simp only [h00, ↓reduceIte]
      by_cases hm1 : (k, 0, j / 2, i / 2) ∈ kerDIdxFinset wY W0 s0
      · simp only [hm1, ↓reduceIte]; exact hpoly _
      · simp [hm1]
    · simp only [h00, ↓reduceIte]
      by_cases h10 : j % 2 = 1 ∧ i % 2 = 0
      · simp only [h10, ↓reduceIte]
        by_cases hm2 : (k, 1, j / 2, i / 2) ∈ kerDIdxFinset wY W0 s0
        · simp only [hm2, ↓reduceIte]; exact hpoly _
        · simp [hm2]
      · simp only [h10, ↓reduceIte]
        by_cases h01 : j % 2 = 0 ∧ i % 2 = 1 ∧ 0 < k
        · simp only [h01, ↓reduceIte]
          by_cases hm3 : (k - 1, 1, j / 2, i / 2) ∈ kerDIdxFinset wY W0 s0
          · simp only [hm3, ↓reduceIte]; exact hpoly _
          · simp [hm3]
        · simp [h01]
  · -- Local vanishing twOrdGE (buildLocalShift (x i) (y i) v) m0
    intro i
    -- For every idx : LocalBasisIdx m0 s0, the NF polynomial P_idx(Z) has natDegree ≤ D_eq and vanishes for all t ≤ D_eq, so P_idx = 0!
    have hNF0 : ∀ idx : LocalBasisIdx m0 s0,
        (∑ e : KerDIdx wY W0 s0,
          (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) = 0 := by
      intro idx
      have hdeg : (∑ e : KerDIdx wY W0 s0,
          (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).natDegree ≤ D_eq := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
        refine natDegree_mul_le.trans ?_
        have h1 : (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val).natDegree ≤ D_ZF :=
          (natDegree_sum_le _ _).trans (Finset.sup_le fun u _ =>
            (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp u.isLt))
        have h2 := natDegree_kerDLocalNF_le hwY (x i) (y i) (hy i) e idx
        dsimp [D_eq]; omega
      ext t
      rw [coeff_zero]
      by_cases ht : t < D_eq + 1
      · exact congrFun hLv (i, idx, ⟨t, ht⟩)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    -- Therefore buildLocalShift = ∑ e, c_e * (kerDLocalPoly e - ∑ idx, NF e idx * basis idx) ∈ (t, w)^m0!
    have hEq : buildLocalShift (x i) (y i) v =
        ∑ e : KerDIdx wY W0 s0,
          locC (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
          (kerDLocalPoly (C (x i)) (y i) e.1 -
            ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
      unfold buildLocalShift
      have hzero : (∑ e : KerDIdx wY W0 s0,
          locC (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
          ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) = 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero; intro idx _
        have hsum : (∑ e : KerDIdx wY W0 s0,
            locC (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
            (locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1)) =
            locC (∑ e : KerDIdx wY W0 s0,
              (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
              kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1 := by
          rw [show locC (∑ e : KerDIdx wY W0 s0,
              (∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
              kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) =
              ∑ e : KerDIdx wY W0 s0, locC ((∑ u : Fin (D_ZF + 1), C (v (e, u)) * X ^ u.val) *
              kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) from by unfold locC; simp [map_sum]]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro e _
          unfold locC; simp [map_mul, mul_assoc]
        rw [hsum, hNF0 idx]; simp [locC]
      rw [← sub_zero (G := LocalPoly (Polynomial F)) (∑ e : KerDIdx wY W0 s0, _), ← hzero,
        ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
      apply Finset.sum_congr rfl; intro e _
      have hms : ∀ x y z : LocalPoly (Polynomial F), x * (y - z) = x * y - x * z := fun x y z =>
        eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
      exact (hms _ _ _).symm
    rw [hEq]
    apply twOrdGE_sum; intro e _
    have hmem := (mem_kerDIdxFinset_iff wY W0 s0 (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    simpa using twOrdGE_mul (twOrdGE_zero _)
      (twOrdGE_kerDLocalPoly_sub_NF m0 s0 (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)

/-- **Vanishing of `evalContact (evalZContact Q z) P` when `W0 < 2 * A * m0`!** -/
theorem evalContact_eq_zero_of_global_interpolant {F ι : Type*} [Field F] [CharP F 2] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {wY W0 s0 m0 D_ZF A : ℕ}
    (hwY : 1 ≤ wY) (hW0 : W0 < 2 * A * m0)
    (v : KerDIdx wY W0 s0 × Fin (D_ZF + 1) → F)
    (hvan : ∀ i : ι, twOrdGE (buildLocalShift (x i) (y i) v) m0)
    (z : F) (P : Polynomial F) (hP : P.natDegree ≤ wY)
    (Az : Finset ι) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (x i) = (y i).eval z) :
    evalContact (evalZContact (buildContactPoly v) z) P = 0 := by
  by_contra hne
  let E := evalContact (evalZContact (buildContactPoly v) z) P
  -- At every i ∈ Az, (X - C (x i))^(2 * m0) ∣ E!
  have hdvd_each : ∀ i ∈ Az, (X - C (x i)) ^ (2 * m0) ∣ E := by
    intro i hi
    have hEqE : E = evalLocal (x i) ((y i).eval z) P (evalZLocal (buildLocalShift (x i) (y i) v) z) := by
      dsimp only [E]
      unfold buildContactPoly buildLocalShift
      rw [show evalZContact (∑ e : KerDIdx wY W0 s0,
            cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDBasisPoly e.1) z =
          ∑ e : KerDIdx wY W0 s0, evalZContact (cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDBasisPoly e.1) z
          from by unfold evalZContact; rw [Polynomial.map_sum]]
      rw [show evalZLocal (∑ e : KerDIdx wY W0 s0,
            locC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDLocalPoly (C (x i)) (y i) e.1) z =
          ∑ e : KerDIdx wY W0 s0, evalZLocal (locC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDLocalPoly (C (x i)) (y i) e.1) z
          from by unfold evalZLocal; rw [Polynomial.map_sum]]
      rw [evalContact_sum, map_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [show evalZContact (cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDBasisPoly e.1) z =
            evalZContact (cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val)) z * evalZContact (kerDBasisPoly e.1) z from by
            unfold evalZContact; rw [Polynomial.map_mul],
          evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC,
          evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul,
          evalLocal_locC, evalLocal_kerDLocalPoly]
    rw [hEqE]
    exact pow_two_mul_dvd_evalLocal_of_twOrdGE (x i) ((y i).eval z) P (hagree i hi)
      (twOrdGE_evalZLocal (hvan i) z)
  -- Product of pairwise coprime (X - C (x i))^(2 * m0) divides E!
  have hdvd_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m0)) ∣ E := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      apply IsCoprime.pow
      have hne_x : x i ≠ x j := fun h => hij (x.injective h)
      refine ⟨C (x j - x i)⁻¹, -C (x j - x i)⁻¹, ?_⟩
      have hne' : x j - x i ≠ 0 := sub_ne_zero.mpr hne_x.symm
      calc C (x j - x i)⁻¹ * (X - C (x i)) + -C (x j - x i)⁻¹ * (X - C (x j))
          = C (x j - x i)⁻¹ * C (x j - x i) := by rw [map_sub]; ring
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne', map_one]
    · exact hdvd_each
  have hdeg_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m0)).natDegree = Az.card * (2 * m0) := by
    rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
    simp [natDegree_pow, natDegree_X_sub_C]
  have hle_deg : Az.card * (2 * m0) ≤ E.natDegree := by
    rw [← hdeg_prod]
    exact natDegree_le_of_dvd hdvd_prod hne
  have hE_deg : E.natDegree ≤ W0 := by
    apply natDegree_evalContact_le wY W0 hwY _ P hP
    rw [wdeg_le_iff]
    intro k' j' i' hnz
    have hmem : (evalZContact (buildContactPoly v) z) =
        ∑ e : KerDIdx wY W0 s0,
          cC ((∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val).eval z) * kerDBasisPoly e.1 := by
      unfold buildContactPoly
      rw [show evalZContact (∑ e : KerDIdx wY W0 s0,
            cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val) * kerDBasisPoly e.1) z =
          ∑ e : KerDIdx wY W0 s0,
            evalZContact (cC (∑ t : Fin (D_ZF + 1), C (v (e, t)) * X ^ t.val)) z * evalZContact (kerDBasisPoly e.1) z
          from by unfold evalZContact; rw [Polynomial.map_sum]; apply Finset.sum_congr rfl; intro e _; rw [Polynomial.map_mul]]
      apply Finset.sum_congr rfl; intro e _
      rw [evalZContact_cC, evalZContact_kerDBasisPoly]
    rw [hmem, coeff_sum_kerDBasisPoly (by omega)] at hnz
    by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
    · simp only [h00, ↓reduceIte] at hnz
      by_cases hm1 : (k', 0, j' / 2, i' / 2) ∈ kerDIdxFinset wY W0 s0
      · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm1).2.2
        have : 2 * (j' / 2) = j' := by omega
        have : 2 * (i' / 2) = i' := by omega
        nlinarith
      · simp [hm1] at hnz
    · simp only [h00, ↓reduceIte] at hnz
      by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
      · simp only [h10, ↓reduceIte] at hnz
        by_cases hm2 : (k', 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W0 s0
        · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm2).2.2
          have : 2 * (j' / 2) + 1 = j' := by omega
          have : 2 * (i' / 2) = i' := by omega
          nlinarith
        · simp [hm2] at hnz
      · simp only [h10, ↓reduceIte] at hnz
        by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
        · simp only [h01, ↓reduceIte] at hnz
          by_cases hm3 : (k' - 1, 1, j' / 2, i' / 2) ∈ kerDIdxFinset wY W0 s0
          · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm3).2.2
            have : 2 * (j' / 2) = j' := by omega
            have : 2 * (i' / 2) + 1 = i' := by omega
            have hk1 : 1 ≤ k' := h01.2.2
            have : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY, hk1]; ring
            nlinarith
          · simp [hm3] at hnz
        · simp [h01] at hnz
  nlinarith

/-! ### Part 5: Denominator-free 4-variable quotient interpolation -/

/-- Exact basis-extension lemma over any field `K`: given a finite index set `B0` and an injective
linear map `T : (B1 → K) →ₗ[K] (B0 → K)`, there exists a subset `I0 ⊆ Finset.univ` of cardinality
`|B0| - |B1|` whose coordinate subspace intersects `LinearMap.range T` trivially! -/
lemma exists_complement_subset_of_injective {K B0 B1 : Type*} [Field K]
    [Fintype B0] [Fintype B1] [DecidableEq B0]
    (T : (B1 → K) →ₗ[K] (B0 → K)) (hT : Function.Injective T) :
    ∃ I0 : Finset B0,
      I0.card + Fintype.card B1 = Fintype.card B0 ∧
      ∀ v : B0 → K, (∀ b ∉ I0, v b = 0) → v ∈ LinearMap.range T → v = 0 := by
  classical
  -- Standard Steinitz exchange: pick maximal I0 ⊆ univ such that {Pi.single b 1 | b ∈ I0} is independent mod range T!
  let P (S : Finset B0) : Prop :=
    ∀ v : B0 → K, (∀ b ∉ S, v b = 0) → v ∈ LinearMap.range T → v = 0
  have hP0 : P ∅ := fun v hv _ => by funext b; exact hv b (Finset.notMem_empty b)
  let valid := Finset.univ.filter P
  have hvalid_ne : valid.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP0⟩⟩
  obtain ⟨I0, hI0_mem, hI0_max⟩ := Finset.exists_max_image valid Finset.card hvalid_ne
  have hPI0 : P I0 := (Finset.mem_filter.mp hI0_mem).2
  -- Maximality implies every basis vector Pi.single b 1 lies in range T + span(I0)!
  let spanI0 : Submodule K (B0 → K) :=
    { carrier := { v | ∀ b ∉ I0, v b = 0 }
      add_mem' := fun ha hb b h => by simp [ha b h, hb b h]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c _ ha b h => by simp [ha b h] }
  have hdisj : Disjoint spanI0 (LinearMap.range T) := by
    rw [Submodule.disjoint_def]; exact hPI0
  have hsup : spanI0 ⊔ LinearMap.range T = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [show v = ∑ b : B0, v b • Pi.single b 1 from by
      funext b'; simp [Finset.sum_apply, Pi.single_apply]]
    apply Submodule.sum_mem
    intro b _
    apply Submodule.smul_mem
    by_cases hb : b ∈ I0
    · exact Submodule.mem_sup_left (fun b' hb' => by
        have hne : b' ≠ b := fun h => hb' (h ▸ hb)
        simp [Pi.single_apply, hne])
    · -- Since insert b I0 has larger card, ¬ P (insert b I0)!
      have hnotP : ¬ P (insert b I0) := by
        intro hP'
        have hmem' : insert b I0 ∈ valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩
        have hle := hI0_max (insert b I0) hmem'
        rw [Finset.card_insert_of_notMem hb] at hle
        omega
      unfold P at hnotP; push Not at hnotP
      rcases hnotP with ⟨w, hw_supp, hw_rng, hw_ne⟩
      have hwb : w b ≠ 0 := by
        intro h0
        apply hw_ne
        exact hPI0 w (fun b' hb' => by
          by_cases hbb' : b' = b
          · subst hbb'; exact h0
          · exact hw_supp b' (by simp [hb', hbb'])) hw_rng
      -- Write Pi.single b 1 = (w b)⁻¹ • w - (w b)⁻¹ • (w - w b • Pi.single b 1) ∈ range T + spanI0!
      let u : B0 → K := w - w b • Pi.single b (1 : K)
      have hu : u ∈ spanI0 := by
        intro b' hb'
        by_cases hbb' : b' = b
        · subst hbb'; simp [u]
        · have h0 := hw_supp b' (by simp [hb', hbb'])
          simp [u, h0, hbb']
      have heq : Pi.single b (1 : K) = (-(w b)⁻¹ • u) + (w b)⁻¹ • w := by
        funext b'
        simp only [u, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        by_cases hbb' : b' = b
        · subst hbb'; simp [inv_mul_cancel₀ hwb]
        · simp [hbb']
      rw [heq]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hw_rng)
  -- Compute dimensions via finrank_sup_add_finrank_inf_eq!
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq spanI0 (LinearMap.range T)
  rw [hsup, hdisj.eq_bot, finrank_top, finrank_bot, add_zero, Module.finrank_pi] at hdim
  have hdimT : Module.finrank K (LinearMap.range T) = Fintype.card B1 := by
    rw [LinearMap.finrank_range_of_inj hT, Module.finrank_pi]
  have hdimI0 : Module.finrank K spanI0 = I0.card := by
    let e : spanI0 ≃ₗ[K] (I0 → K) :=
      { toFun := fun v i => v.1 i.1
        invFun := fun f => ⟨fun b => if h : b ∈ I0 then f ⟨b, h⟩ else 0,
          fun b hb => dif_neg hb⟩
        left_inv := fun ⟨v, hv⟩ => Subtype.ext (funext fun b => by
          by_cases h : b ∈ I0
          · simp [h]
          · simp [h, (hv b h).symm])
        right_inv := fun f => funext fun ⟨b, hb⟩ => by simp [hb]
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [LinearEquiv.finrank_eq e, Module.finrank_pi, Fintype.card_coe]
  rw [hdimT, hdimI0] at hdim
  exact ⟨I0, hdim.symm, hPI0⟩

/-- Local product `localShift(F) * localBasisElem(e2)` projected to `LocalBasisIdx m s` via
`reduceMonomialCoords`, for any `F` expressed via `KerDIdx wY W_F d` coordinates `f_coord`. -/
noncomputable def prodLocalNF {F : Type*} [CommRing F] {wY W_F d m s : ℕ}
    (x0 y0 : F) (f_coord : KerDIdx wY W_F d → F) (e2 : ℕ × ℕ × ℕ × ℕ)
    (idx : LocalBasisIdx m s) : F :=
  let (q2, j2, a2, b2) := e2
  ∑ e1 : KerDIdx wY W_F d,
    let (k1, r1, b1, a1) := e1.1
    f_coord e1 *
    ∑ a' ∈ Finset.range (a1 + 1),
      ∑ b' ∈ Finset.range (b1 + 1),
        (Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
        ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) *
        (if r1 = 0 then
          ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F)
         else
          y0 * ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
          x0 * ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
          ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F))

lemma natDegree_prodLocalNF_le {F : Type*} [Field F] {wY W_F d m s dy D_ZF : ℕ} (hwY : 1 ≤ wY)
    (x0 : F) (y0 : Polynomial F) (hy0 : y0.natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hfdeg : ∀ e1, (f_coord e1).natDegree ≤ D_ZF)
    (e2 : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) :
    (prodLocalNF (C x0) y0 f_coord e2 idx).natDegree ≤ D_ZF + dy * (W_F / wY) := by
  unfold prodLocalNF
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e1 _ => ?_)
  rcases e1 with ⟨⟨k1, r1, b1, a1⟩, he1⟩
  have hmem := (mem_kerDIdxFinset_iff wY W_F d (by omega) k1 r1 b1 a1).mp he1
  have hbr : 2 * b1 + r1 ≤ W_F / wY := by
    have : (2 * b1 + r1) * wY ≤ W_F := by nlinarith [hmem.2.2]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < wY)).mpr this
  refine natDegree_mul_le.trans (Nat.add_le_add (hfdeg ⟨_, he1⟩) ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a' _ => ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b' hb' => ?_)
  have hb'_le : b' ≤ b1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
  have hC1 : (((Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a'))).natDegree = 0 := by
    have : (Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a') =
        C ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) := by simp
    rw [this, natDegree_C]
  have hY : ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')).natDegree ≤ 2 * dy * (b1 - b') := by
    calc _ ≤ (Nat.choose b1 b' : Polynomial F).natDegree + ((y0 ^ 2) ^ (b1 - b')).natDegree :=
            natDegree_mul_le
      _ ≤ 0 + (b1 - b') * (y0 ^ 2).natDegree := by
            rw [natDegree_natCast]; exact Nat.add_le_add_left natDegree_pow_le 0
      _ ≤ (b1 - b') * (2 * dy) := by
            rw [zero_add]; exact Nat.mul_le_mul_left _ (natDegree_pow_le.trans (by omega))
      _ = 2 * dy * (b1 - b') := by ring
  have hTail : (if r1 = 0 then
        ((reduceMonomialCoords m s e2.1 (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F)
       else
        y0 * ((reduceMonomialCoords m s e2.1 (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F) +
        C x0 * ((reduceMonomialCoords m s e2.1 (k1 + 1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F) +
        ((reduceMonomialCoords m s (e2.1 + 1) (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F)).natDegree
        ≤ dy * r1 := by
    split_ifs with hr0
    · simp [natDegree_natCast]
    · have hr1 : r1 = 1 := by omega
      subst hr1; rw [mul_one]
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp [natDegree_natCast]))
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (by simp [natDegree_natCast, hy0])
      · exact natDegree_mul_le.trans (by simp [natDegree_C, natDegree_natCast])
  calc _ ≤ ((Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b'))).natDegree + dy * r1 :=
          natDegree_mul_le.trans (Nat.add_le_add_left hTail _)
    _ ≤ (0 + 2 * dy * (b1 - b')) + dy * r1 :=
          Nat.add_le_add_right (natDegree_mul_le.trans (by rw [hC1]; exact Nat.add_le_add_left hY 0)) _
    _ ≤ dy * (2 * b1 + r1) := by have : b1 - b' ≤ b1 := Nat.sub_le b1 b'; nlinarith
    _ ≤ dy * (W_F / wY) := Nat.mul_le_mul_left dy hbr

/-- Correctness of `prodLocalNF`: `(∑ e1, f_coord e1 * kerDLocalPoly e1) * localBasisElem e2`
is congruent to `∑ idx, prodLocalNF ... idx • localBasisElem idx` modulo `(t, w)^m`! -/
theorem twOrdGE_prodLocal_sub_NF {F : Type*} [CommRing F] [CharP F 2] {wY W_F d m s : ℕ}
    (hwY : 0 < wY) (hd : d ≤ s) (x0 y0 : F) (f_coord : KerDIdx wY W_F d → F)
    (e2 : ℕ × ℕ × ℕ × ℕ) (he2 : e2.1 + e2.2.1 ≤ s - d) :
    twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly x0 y0 e1.1) * localBasisElem e2 -
      ∑ idx : LocalBasisIdx m s, locC (prodLocalNF x0 y0 f_coord e2 idx) * localBasisElem idx.1) m := by
  have hscale : ∀ (c : F) (H : LocalPoly F), twOrdGE H m → twOrdGE (locC c * H) m := fun c H hH => by
    simpa using twOrdGE_mul (twOrdGE_zero (locC c)) hH
  -- Factor out ∑ e1, locC (f_coord e1) * (...)
  have houter : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly x0 y0 e1.1) * localBasisElem e2 -
      ∑ idx : LocalBasisIdx m s, locC (prodLocalNF x0 y0 f_coord e2 idx) * localBasisElem idx.1 =
      ∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) *
        (kerDLocalPoly x0 y0 e1.1 * localBasisElem e2 -
          ∑ idx : LocalBasisIdx m s, locC (
            let (k1, r1, b1, a1) := e1.1
            let (q2, j2, a2, b2) := e2
            ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
              (Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) *
              (if r1 = 0 then
                ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F)
               else
                y0 * ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
                x0 * ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
                ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F))) *
            localBasisElem idx.1) := by
    rw [Finset.sum_mul]
    unfold prodLocalNF
    simp_rw [locC, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly F)]
    apply Finset.sum_congr rfl; intro e1 _
    have hms : ∀ x y z : LocalPoly F, x * (y - z) = x * y - x * z := fun x y z =>
      eq_sub_of_add_eq (G := LocalPoly F) (by rw [← mul_add, sub_add_cancel (G := LocalPoly F)])
    rw [mul_assoc, hms]; congr 1
    refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
    simp only [map_mul, map_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [houter]
  apply twOrdGE_sum; intro e1 _
  apply hscale
  rcases e1 with ⟨⟨k1, r1, b1, a1⟩, he1⟩
  rcases e2 with ⟨q2, j2, a2, b2⟩
  dsimp only at he2 ⊢
  have hmem := (mem_kerDIdxFinset_iff wY W_F d hwY k1 r1 b1 a1).mp he1
  -- Expand (x0^2 + t)^a1 and (y0^2 + u)^b1 exactly as in twOrdGE_kerDLocalPoly_sub_NF!
  have hpow_a : (locC (x0 ^ 2) + locT) ^ a1 =
      ∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) * locT ^ a' := by
    rw [add_comm, add_pow (R := LocalPoly F)]; apply Finset.sum_congr rfl; intro a' _
    have hc : locC (x0 ^ 2) ^ (a1 - a') * (Nat.choose a1 a' : LocalPoly F) =
        locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) := by
      unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
    rw [mul_assoc, hc]; ring
  have hpow_b : (locC (y0 ^ 2) + localU) ^ b1 =
      ∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b' := by
    rw [add_comm, add_pow (R := LocalPoly F)]; apply Finset.sum_congr rfl; intro b' _
    have hc : locC (y0 ^ 2) ^ (b1 - b') * (Nat.choose b1 b' : LocalPoly F) =
        locC ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) := by
      unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
    rw [mul_assoc, hc]; ring
  have hcomm : ∀ (f : ℕ → ℕ → LocalBasisIdx m s → LocalPoly F),
      (∑ idx : LocalBasisIdx m s, ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1), f a' b' idx) =
      ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1), ∑ idx : LocalBasisIdx m s, f a' b' idx := by
    intro f; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a' _; rw [Finset.sum_comm]
  have hr01 : r1 = 0 ∨ r1 = 1 := by omega
  rcases hr01 with rfl | rfl
  · have hEq : kerDLocalPoly x0 y0 (k1, 0, b1, a1) * localBasisElem (q2, j2, a2, b2) -
        ∑ idx : LocalBasisIdx m s, locC (
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            (Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) *
            ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F)) * localBasisElem idx.1 =
        ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
          locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b'))) *
          (localBasisElem (q2, k1 + j2, a' + a2, b' + b2) -
            ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) *
              localBasisElem idx.1) := by
      unfold kerDLocalPoly; rw [pow_zero, mul_one, hpow_a, hpow_b]
      have hlhs : locR ^ k1 *
          (∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) * locT ^ a') *
          (∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b') *
          localBasisElem (q2, j2, a2, b2) =
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b'))) *
            localBasisElem (q2, k1 + j2, a' + a2, b' + b2) := by
        conv_lhs => arg 1; arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem locC; simp only [map_mul, pow_add]; ring
      rw [hlhs]
      simp_rw [locC, map_sum, Finset.sum_mul]
      rw [hcomm, ← Finset.sum_sub_distrib (G := LocalPoly F)]
      apply Finset.sum_congr rfl; intro a' _
      rw [← Finset.sum_sub_distrib (G := LocalPoly F)]
      apply Finset.sum_congr rfl; intro b' _
      have hms : ∀ x y z : LocalPoly F, x * (y - z) = x * y - x * z := fun x y z =>
      eq_sub_of_add_eq (G := LocalPoly F) (by rw [← mul_add, sub_add_cancel (G := LocalPoly F)])
      rw [hms]; congr 1
      refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
      simp only [map_mul]; ring
    simp only [↓reduceIte]
    rw [hEq]
    apply twOrdGE_sum; intro a' _; apply twOrdGE_sum; intro b' _; apply hscale
    exact twOrdGE_sub_reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) (by omega)
  · have hEq : kerDLocalPoly x0 y0 (k1, 1, b1, a1) * localBasisElem (q2, j2, a2, b2) -
        ∑ idx : LocalBasisIdx m s, locC (
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            (Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) *
            (y0 * ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
             x0 * ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) +
             ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F))) *
          localBasisElem idx.1 =
        ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
          locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b'))) *
          (locC y0 * (localBasisElem (q2, k1 + j2, a' + a2, b' + b2) -
              ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) * localBasisElem idx.1) +
           locC x0 * (localBasisElem (q2, k1 + 1 + j2, a' + a2, b' + b2) -
              ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) * localBasisElem idx.1) +
           (localBasisElem (q2 + 1, k1 + j2, a' + a2, b' + b2) -
              ∑ idx : LocalBasisIdx m s, locC ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : F) * localBasisElem idx.1)) := by
      unfold kerDLocalPoly; rw [pow_one, hpow_a, hpow_b]
      have hlhs : locR ^ k1 * (locC y0 + locC x0 * locR + locW) *
          (∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) * locT ^ a') *
          (∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b') *
          localBasisElem (q2, j2, a2, b2) =
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            locC ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b'))) *
            (locC y0 * localBasisElem (q2, k1 + j2, a' + a2, b' + b2) +
             locC x0 * localBasisElem (q2, k1 + 1 + j2, a' + a2, b' + b2) +
             localBasisElem (q2 + 1, k1 + j2, a' + a2, b' + b2)) := by
        conv_lhs => arg 1; arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem locC; simp only [map_mul, pow_add, pow_succ]; ring
      rw [hlhs]
      simp_rw [locC, map_sum, Finset.sum_mul]
      rw [hcomm, ← Finset.sum_sub_distrib (G := LocalPoly F)]
      apply Finset.sum_congr rfl; intro a' _
      rw [← Finset.sum_sub_distrib (G := LocalPoly F)]
      apply Finset.sum_congr rfl; intro b' _
      have hms : ∀ x y z : LocalPoly F, x * (y - z) = x * y - x * z := fun x y z =>
        eq_sub_of_add_eq (G := LocalPoly F) (by rw [← mul_add, sub_add_cancel (G := LocalPoly F)])
      simp_rw [mul_add, hms, Finset.mul_sum]
      -- Combine the 3 sums on RHS into one sum
      have h3 : ∀ (f1 f2 f3 : LocalBasisIdx m s → LocalPoly F),
          (∑ i, f1 i) + (∑ i, f2 i) + (∑ i, f3 i) = ∑ i, (f1 i + f2 i + f3 i) := by
        intro f1 f2 f3; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [show ∀ a b c d e f : LocalPoly F, (a - d) + (b - e) + (c - f) = (a + b + c) - (d + e + f) by intros; ring]
      refine congrArg₂ (· - ·) rfl ?_
      rw [h3]; apply Finset.sum_congr rfl; intro idx _
      simp only [map_mul, map_add]; ring
    simp only [one_ne_zero, ↓reduceIte]
    rw [hEq]
    apply twOrdGE_sum; intro a' _; apply twOrdGE_sum; intro b' _; apply hscale
    apply twOrdGE_add
    · apply twOrdGE_add
      · exact hscale _ _ (twOrdGE_sub_reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) (by omega))
      · exact hscale _ _ (twOrdGE_sub_reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) (by omega))
    · exact twOrdGE_sub_reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) (by omega)

/-- **MAIN DENOMINATOR-FREE 4-VARIABLE QUOTIENT INTERPOLATION THEOREM!**
Given nonzero `F ∈ K_{W_F}(d)[Z]_{≤ D_ZF}` (represented by coordinates `f_coord : KerDIdx wY W_F d → F[Z]`)
whose exact local `(t, w)`-order at point `i` is `k_i ≤ m`, and ANY `(m, s, W, D_Z')` satisfying the
exact integer surplus inequality, there exists a nonzero `G ∈ K_W(s)[Z]_{≤ D_Z'}` such that:
1. `F ∤ G` in `ContactPoly (RatFunc F)` (hence `Res_R(F, G) ≠ 0` when `F` is irreducible!),
2. `G` vanishes on EVERY `(z, P)` with `P.natDegree ≤ wY`, `A` agreements with `y_i(z)`, and `evalContact F_z P = 0`
   (whenever `W < 2 * A * m`)! -/
theorem exists_quotient_contact_interpolant {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {dy wY W_F d D_ZF m s W D_Z' : ℕ}
    (hwY : 1 ≤ wY) (hd : d ≤ s) (hW : W_F ≤ W) (hDZ : D_ZF ≤ D_Z')
    (hy : ∀ i, (y i).natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hfdeg : ∀ e, (f_coord e).natDegree ≤ D_ZF)
    (hFne : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≠ 0)
    (hFdeg : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).natDegree = d)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (k : ι → ℕ)
    (hk_exact : ∀ i,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1
      k i ≤ m ∧ (k i < m → twOrdGE Fi (k i) ∧ ∃ p q, p + q = k i ∧ twCoeff Fi p q ≠ 0))
    (hsurplus :
      Fintype.card ι * rankKerD m s * (D_Z' + dy * max (W / wY) (W_F / wY) + 1) <
      (varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)) * (D_Z' + 1) +
      (∑ i : ι, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1)) :
    ∃ G : ContactPoly (Polynomial F),
      G ≠ 0 ∧ contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W ∧
      (∀ k' j' i', (((G.coeff k').coeff j').coeff i').natDegree ≤ D_Z') ∧
      (¬ ∃ Q' : ContactPoly (RatFunc F),
        G.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) =
        (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).map
          (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) * Q') ∧
      (∀ (A : ℕ), W < 2 * A * m → ∀ (z : F) (P : Polynomial F),
        P.natDegree ≤ wY →
        ∀ (Az : Finset ι), A ≤ Az.card →
        (∀ i ∈ Az, P.eval (x i) = (y i).eval z) →
        evalContact (evalZContact (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) z) P = 0 →
        evalContact (evalZContact G z) P = 0) := by
  classical
  let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1
  let alg : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let liftC : ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom alg))
  have hFne_rat : liftC Fpoly ≠ 0 := by
    intro h0
    apply hFne
    apply Polynomial.ext; intro k'
    apply Polynomial.ext; intro j'
    apply Polynomial.ext; intro i'
    have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
    simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
    have h0' : ((Fpoly.coeff k').coeff j').coeff i' = 0 :=
      (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by rw [map_zero]; exact h)
    simpa only [Fpoly, coeff_zero] using h0'
  -- Step 1: Build the injective linear map `· Fpoly : K_{W-W_F}(s-d) → K_W(s)` over RatFunc F!
  have hFkerD : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ d ∧ wdeg wY Fpoly ≤ W_F := by
    refine (mem_kerD_iff_exists_unique_coords hwY Fpoly).mpr ⟨f_coord, rfl, ?_⟩
    intro c' hc'
    funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W_F d (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  -- Embed KerDIdx wY (W - W_F) (s - d) → RatFunc F into KerDIdx wY W s → RatFunc F via multiplication by liftC Fpoly!
  have hRatChar2 : CharP (RatFunc F) 2 := charP_of_injective_ringHom (IsFractionRing.injective (Polynomial F) (RatFunc F)) 2
  have hF_rat_mem : contactDeriv (liftC Fpoly) = 0 ∧ (liftC Fpoly).natDegree ≤ d ∧ wdeg wY (liftC Fpoly) ≤ W_F := by
    refine ⟨?_, ?_, ?_⟩
    · ext k' j' i'
      have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff j').coeff i') hFkerD.1
      rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative] at h ⊢
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h ⊢
      have h1 : alg ((((Fpoly.coeff k').coeff j').coeff (i' + 1)) * ((i' + 1 : ℕ) : Polynomial F)) =
          alg (((Fpoly.coeff k').coeff j').coeff (i' + 1)) * ((i' + 1 : ℕ) : RatFunc F) := by simp
      cases k' with
      | zero => simpa [h1] using congrArg alg h
      | succ k'' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative,
            coe_mapRingHom, coeff_map] at h ⊢
          rw [show ((j' : Polynomial (Polynomial F)) + 1) = C ((j' : Polynomial F) + 1) by simp, coeff_mul_C] at h
          rw [show ((j' : Polynomial (RatFunc F)) + 1) = C ((j' : RatFunc F) + 1) by simp, coeff_mul_C]
          have := congrArg alg h; simpa using this
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k' hk'
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hFkerD.2.1 hk'), map_zero]
    · rw [wdeg_le_iff]
      intro k' j' i' hnz
      simp only [liftC, coe_mapRingHom, coeff_map] at hnz
      have hnz' : ((Fpoly.coeff k').coeff j').coeff i' ≠ 0 := fun h0 => hnz (by rw [h0, map_zero])
      exact (wdeg_le_iff wY W_F Fpoly).mp hFkerD.2.2 k' j' i' hnz'
  -- Coordinate extraction map on K_W(s) over RatFunc F
  let toPolyRat (W' s' : ℕ) (c : KerDIdx wY W' s' → RatFunc F) : ContactPoly (RatFunc F) :=
    ∑ e : KerDIdx wY W' s', cC (c e) * kerDBasisPoly e.1
  let coordRat (Q : ContactPoly (RatFunc F)) (e : KerDIdx wY W s) : RatFunc F :=
    if e.1.2.1 = 0 then ((Q.coeff e.1.1).coeff (2 * e.1.2.2.1)).coeff (2 * e.1.2.2.2)
    else ((Q.coeff e.1.1).coeff (2 * e.1.2.2.1 + 1)).coeff (2 * e.1.2.2.2)
  let T : (KerDIdx wY (W - W_F) (s - d) → RatFunc F) →ₗ[RatFunc F] (KerDIdx wY W s → RatFunc F) :=
    { toFun := fun c => coordRat (liftC Fpoly * toPolyRat (W - W_F) (s - d) c)
      map_add' := fun c1 c2 => by
        funext e
        have hadd : toPolyRat (W - W_F) (s - d) (c1 + c2) =
            toPolyRat (W - W_F) (s - d) c1 + toPolyRat (W - W_F) (s - d) c2 := by
          dsimp [toPolyRat]; rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e' _; simp [cC, add_mul]
        dsimp [coordRat]; rw [hadd, mul_add]; split_ifs <;> simp
      map_smul' := fun a c => by
        funext e
        have hsmul : toPolyRat (W - W_F) (s - d) (a • c) =
            cC a * toPolyRat (W - W_F) (s - d) c := by
          dsimp [toPolyRat]; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro e' _; simp [cC, mul_assoc]
        have hmul : ∀ P : ContactPoly (RatFunc F), liftC Fpoly * (cC a * P) = cC a * (liftC Fpoly * P) := by
          intro P; ring
        dsimp [coordRat]; rw [hsmul, hmul]; split_ifs <;> simp [cC, coeff_C_mul] }
  have hT_reconstruct : ∀ c, toPolyRat W s (T c) = liftC Fpoly * toPolyRat (W - W_F) (s - d) c := by
    intro c
    let Q := liftC Fpoly * toPolyRat (W - W_F) (s - d) c
    have hQ1 : contactDeriv (toPolyRat (W - W_F) (s - d) c) = 0 ∧
        (toPolyRat (W - W_F) (s - d) c).natDegree ≤ s - d ∧
        wdeg wY (toPolyRat (W - W_F) (s - d) c) ≤ W - W_F := by
      refine (mem_kerD_iff_exists_unique_coords hwY _).mpr ⟨c, rfl, ?_⟩
      intro c' hc'
      funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY (W - W_F) (s - d) (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [he] using h.symm
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h.symm
    have hQmem : contactDeriv Q = 0 ∧ Q.natDegree ≤ s ∧ wdeg wY Q ≤ W := by
      refine ⟨?_, ?_, ?_⟩
      · dsimp [Q]; rw [contactDeriv_mul, hF_rat_mem.1, hQ1.1, zero_mul, mul_zero, add_zero]
      · dsimp [Q]; exact natDegree_mul_le.trans (by omega)
      · by_cases h0 : toPolyRat (W - W_F) (s - d) c = 0
        · simp [Q, h0, wdeg]
        · dsimp [Q]; rw [wdeg_mul wY hFne_rat h0]; omega
    obtain ⟨c', hQc', _⟩ := (mem_kerD_iff_exists_unique_coords hwY Q).mp hQmem
    have hc'eq : c' = T c := by
      funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hQc'
        rw [coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [T, coordRat, Q, he] using h.symm
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hQc'
        rw [coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [T, coordRat, Q, h1, h2, h3, h4, he] using h.symm
    rw [← hc'eq]; exact hQc'.symm
  have hT_inj : Function.Injective T := by
    intro c1 c2 h
    have hprod : liftC Fpoly * toPolyRat (W - W_F) (s - d) c1 = liftC Fpoly * toPolyRat (W - W_F) (s - d) c2 := by
      rw [← hT_reconstruct, ← hT_reconstruct, h]
    have hpoly := mul_left_cancel₀ hFne_rat hprod
    funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY (W - W_F) (s - d) (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h' := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hpoly
      dsimp only [toPolyRat] at h'; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h'
      simpa [he] using h'
    · have h' := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hpoly
      dsimp only [toPolyRat] at h'; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h'
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h'
  -- Step 2: Obtain complement index subset I0 ⊆ KerDIdx wY W s of size |B0| - |B1|!
  obtain ⟨I0, hI0_card, hI0_disj⟩ := exists_complement_subset_of_injective T hT_inj
  -- Step 3: Set up homogeneous F-linear system for (g_coeff on I0 × Fin(D_Z'+1), v_coeff on Σ i, B(m-k_i, s-d) × Fin(D_Z'-D_ZF+1))!
  let D_eq := D_Z' + dy * max (W / wY) (W_F / wY)
  let I_G := { e : KerDIdx wY W s // e ∈ I0 } × Fin (D_Z' + 1)
  let I_V := (Σ i : ι, LocalBasisIdx (m - k i) (s - d)) × Fin (D_Z' - D_ZF + 1)
  let I_all := I_G ⊕ I_V
  let J_all := ι × LocalBasisIdx m s × Fin (D_eq + 1)
  let gPoly (u : I_all → F) (e : KerDIdx wY W s) : Polynomial F :=
    if h : e ∈ I0 then ∑ t : Fin (D_Z' + 1), C (u (Sum.inl (⟨e, h⟩, t))) * X ^ t.val else 0
  let vPoly (u : I_all → F) (i : ι) (b : LocalBasisIdx (m - k i) (s - d)) : Polynomial F :=
    ∑ t : Fin (D_Z' - D_ZF + 1), C (u (Sum.inr (⟨i, b⟩, t))) * X ^ t.val
  let L : (I_all → F) →ₗ[F] (J_all → F) :=
    { toFun := fun u j =>
        let (i, idx, t) := j
        ((∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
         (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx)).coeff t.val
      map_add' := by
        intro u1 u2; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (u1 + u2) e = gPoly u1 e + gPoly u2 e := fun e => by
          dsimp [gPoly]; split_ifs <;> [simp [add_mul, Finset.sum_add_distrib]; simp]
        have hv : ∀ b, vPoly (u1 + u2) i b = vPoly u1 i b + vPoly u2 i b := fun b => by
          dsimp [vPoly]; simp [add_mul, Finset.sum_add_distrib]
        simp only [hg, hv, add_mul, Finset.sum_add_distrib, coeff_sub, coeff_add, Pi.add_apply]; ring
      map_smul' := by
        intro a u; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (a • u) e = C a * gPoly u e := fun e => by
          dsimp [gPoly]; split_ifs <;> [simp [Finset.mul_sum, mul_assoc]; simp]
        have hv : ∀ b, vPoly (a • u) i b = C a * vPoly u i b := fun b => by
          dsimp [vPoly]; simp [Finset.mul_sum, mul_assoc]
        simp only [hg, hv, mul_assoc, ← Finset.mul_sum, ← mul_sub, coeff_C_mul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] }
  have hcard : Fintype.card J_all < Fintype.card I_all := by
    have hI0_eq : I0.card = varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d) := by
      rw [card_kerDIdx wY W s (by omega), card_kerDIdx wY (W - W_F) (s - d) (by omega)] at hI0_card
      omega
    simp only [I_all, I_G, I_V, J_all, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_coe, Fintype.card_fin, card_localBasisFinset, hI0_eq]
    simpa [D_eq, mul_assoc] using hsurplus
  obtain ⟨u, hu_ne, hLu⟩ := exists_ne_zero_ker_linearMap L hcard
  let G : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (gPoly u e) * kerDBasisPoly e.1
  -- Show for every i, localShift(G) - Fi * V_i ∈ (t, w)^m!
  have hlocal_van : ∀ i : ι,
      twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
    intro i
    -- First show the NF difference vanishes identically in Polynomial F!
    have hNF_zero : ∀ idx : LocalBasisIdx m s,
        (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
        (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) = 0 := by
      intro idx
      have hdeg1 : (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx).natDegree ≤ D_eq := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => natDegree_mul_le.trans ?_)
        have hg : (gPoly u e).natDegree ≤ D_Z' := by
          dsimp [gPoly]; split_ifs
          · exact (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
              (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp t.isLt))
          · simp
        have hnf := natDegree_kerDLocalNF_le hwY (x i) (y i) (hy i) e idx
        have hle : dy * (W / wY) ≤ dy * max (W / wY) (W_F / wY) := Nat.mul_le_mul_left dy (le_max_left _ _)
        dsimp [D_eq]; omega
      have hdeg2 : (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx).natDegree ≤ D_eq := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b _ => natDegree_mul_le.trans ?_)
        have hv : (vPoly u i b).natDegree ≤ D_Z' - D_ZF :=
          (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
            (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp t.isLt))
        have hnf := natDegree_prodLocalNF_le hwY (x i) (y i) (hy i) f_coord hfdeg b.1 idx
        have hle : dy * (W_F / wY) ≤ dy * max (W / wY) (W_F / wY) := Nat.mul_le_mul_left dy (le_max_right _ _)
        dsimp [D_eq]; omega
      have hdeg : ((∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
          (∑ b : LocalBasisIdx (m - k i) (s - d),
            vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx)).natDegree ≤ D_eq :=
        (natDegree_sub_le _ _).trans (max_le hdeg1 hdeg2)
      ext t; rw [coeff_zero]
      by_cases ht : t < D_eq + 1
      · exact congrFun hLu (i, idx, ⟨t, ht⟩)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    -- Rewrite LHS as (G_i - NF(G_i)) - (Fi*V_i - NF(Fi*V_i)) since NF(G_i) = NF(Fi*V_i)!
    have h1 : twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
          localBasisElem idx.1) m := by
      have hrew : (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
            localBasisElem idx.1 =
          ∑ e : KerDIdx wY W s, locC (gPoly u e) *
            (kerDLocalPoly (C (x i)) (y i) e.1 -
              ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro e _
        have hms : ∀ x y z : LocalPoly (Polynomial F), x * (y - z) = x * y - x * z := fun x y z =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]; congr 1
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF m s (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have h2 : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) m := by
      have hrew : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
          (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
            vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 =
          ∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) *
            ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) * localBasisElem b.1 -
              ∑ idx : LocalBasisIdx m s, locC (prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) := by
        have h2a : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d),
              (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
              (locC (vPoly u i b) * localBasisElem b.1) := Finset.mul_sum _ _ _
        have h2b : (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
              vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d), ∑ idx : LocalBasisIdx m s,
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
          trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k i) (s - d),
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1
          · apply Finset.sum_congr rfl; intro idx _
            unfold locC; simp only [map_sum, Finset.sum_mul]
          · exact Finset.sum_comm
        rw [h2a, h2b, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro b _
        have hms : ∀ x y z : LocalPoly (Polynomial F), x * (y - z) = x * y - x * z := fun x y z =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]
        refine congrArg₂ (· - ·) (by rw [← mul_assoc, mul_comm _ (locC (vPoly u i b)), mul_assoc]) ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        unfold locC; simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro b _
      have hb := ((mem_localBasisFinset_iff (m - k i) (s - d) _ _ _ _).mp b.2).1
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_prodLocal_sub_NF (by omega) hd (C (x i)) (y i) f_coord b.1 hb)
    have hNF_eq : (∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
        gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) =
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
      apply Finset.sum_congr rfl; intro idx _
      rw [sub_eq_zero.mp (hNF_zero idx)]
    have hcomb := twOrdGE_sub h1 h2
    rwa [hNF_eq, sub_sub_sub_cancel_right] at hcomb
  -- Step 4: Prove G ≠ 0 by exact (t, w)-valuation + localBasis_linearIndependent_mod!
  have hGne : G ≠ 0 := by
    intro hG0
    have hg0 : ∀ e : KerDIdx wY W s, gPoly u e = 0 := by
      intro ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have hv0 : ∀ i : ι, ∀ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b = 0 := by
      intro i
      by_cases hkm : k i < m
      · have hloc := hlocal_van i
        simp only [hg0, locC, map_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hloc
        have hneg : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
          intro p q hpq; have := hloc p q hpq
          unfold twCoeff at this ⊢
          rw [coeff_sub, coeff_sub, coeff_zero, coeff_zero] at this
          exact (sub_eq_zero.mp this).symm
        have hVvan : twOrdGE (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) (m - k i) := by
          by_contra hnot
          have hSpec := (hk_exact i).2 hkm
          have hfail := not_twOrdGE_mul_of_exact_ord hSpec.1 hSpec.2 hnot
          rw [Nat.add_sub_cancel' (le_of_lt hkm)] at hfail
          exact hfail hneg
        exact localBasis_linearIndependent_mod (m - k i) (s - d) (vPoly u i) hVvan
      · intro b
        exfalso
        have hle := (hk_exact i).1
        have h0 : m - k i = 0 := by omega
        have hlt := ((mem_localBasisFinset_iff (m - k i) (s - d) _ _ _ _).mp b.2).2.1
        omega
    apply hu_ne
    funext x'
    rcases x' with ⟨⟨e, he⟩, t⟩ | ⟨⟨i, b⟩, t⟩
    · have hc := hg0 e
      dsimp only [gPoly] at hc; rw [dif_pos he] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hc := hv0 i b
      dsimp only [vPoly] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
  -- Step 5: Verify G ∈ K_W(s)[Z]_{≤ D_Z'}, F ∤ G over RatFunc F, and evaluation vanishing!
  have hGmem : contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W := by
    refine (mem_kerD_iff_exists_unique_coords hwY G).mpr ⟨gPoly u, rfl, ?_⟩
    intro c' hc'
    funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  refine ⟨G, hGne, hGmem.1, hGmem.2.1, hGmem.2.2, ?_, ?_, ?_⟩
  · -- deg_Z ≤ D_Z'
    intro k' j' i'
    dsimp only [G]; rw [coeff_sum_kerDBasisPoly (by omega)]
    have hg : ∀ e : KerDIdx wY W s, (gPoly u e).natDegree ≤ D_Z' := fun e => by
      dsimp only [gPoly]; split_ifs
      · exact (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
          (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp t.isLt))
      · simp
    split_ifs <;> first | exact hg _ | simp
  · -- F ∤ G over RatFunc F!
    rintro ⟨Q', hQ'0⟩
    have hQ' : liftC G = liftC Fpoly * Q' := hQ'0
    have hGne_rat : liftC G ≠ 0 := by
      intro h0; apply hGne
      refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
      have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
      exact (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by simp only [coeff_zero, map_zero]; exact h)
    have hQ'ne : Q' ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hQ'; exact hGne_rat hQ'
    -- Since D(G) = 0 and D(F) = 0, D(F * Q') = F * D(Q') = 0 => D(Q') = 0, deg_R(Q') ≤ s - d, wdeg(Q') ≤ W - W_F!
    have hG_rat_mem : contactDeriv (liftC G) = 0 ∧ (liftC G).natDegree ≤ s ∧ wdeg wY (liftC G) ≤ W := by
      refine ⟨?_, ?_, ?_⟩
      · refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
        have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff j').coeff i') hGmem.1
        rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative] at h ⊢
        simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h ⊢
        cases k' with
        | zero => simpa using congrArg alg h
        | succ k'' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative,
              coe_mapRingHom, coeff_map] at h ⊢
            rw [show ((j' : Polynomial (Polynomial F)) + 1) = C ((j' : Polynomial F) + 1) by simp, coeff_mul_C] at h
            rw [show ((j' : Polynomial (RatFunc F)) + 1) = C ((j' : RatFunc F) + 1) by simp, coeff_mul_C]
            have := congrArg alg h; simpa using this
      · rw [natDegree_le_iff_coeff_eq_zero]; intro k' hk'
        simp only [liftC, coe_mapRingHom, coeff_map, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hGmem.2.1 hk'), map_zero]
      · rw [wdeg_le_iff]; intro k' j' i' hnz
        simp only [liftC, coe_mapRingHom, coeff_map] at hnz
        have hnz' : ((G.coeff k').coeff j').coeff i' ≠ 0 := fun h0 => hnz (by rw [h0, map_zero])
        exact (wdeg_le_iff wY W G).mp hGmem.2.2 k' j' i' hnz'
    -- Wait: exact deg_R(liftC Fpoly) = d and wdeg(liftC Fpoly) = W_F since alg is injective!
    have hF_rat_deg : (liftC Fpoly).natDegree = d := by
      have hinj := IsFractionRing.injective (Polynomial F) (RatFunc F)
      have hne_c : ∀ k', (liftC Fpoly).coeff k' ≠ 0 ↔ Fpoly.coeff k' ≠ 0 := by
        intro k'
        simp only [liftC, coe_mapRingHom, coeff_map, ne_eq]
        constructor
        · intro h h0; apply h; rw [h0, Polynomial.map_zero]
        · intro h h0; apply h
          refine Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
          have := congrArg (fun p : BiPoly (RatFunc F) => (p.coeff j').coeff i') h0
          simp only [coe_mapRingHom, coeff_map, coeff_zero] at this
          exact hinj (by simp only [coeff_zero, map_zero]; exact this)
      apply le_antisymm hF_rat_mem.2.1
      by_cases hd0 : d = 0
      · omega
      · apply le_natDegree_of_ne_zero
        rw [hne_c, ← hFdeg]
        exact leadingCoeff_ne_zero.mpr hFne
    have hF_rat_wdeg : wdeg wY (liftC Fpoly) = W_F := by
      have hinj := IsFractionRing.injective (Polynomial F) (RatFunc F)
      apply le_antisymm hF_rat_mem.2.2
      rw [← hFwdeg]
      rw [wdeg_le_iff]
      intro k' j' i' hnz
      have hnz' : (((liftC Fpoly).coeff k').coeff j').coeff i' ≠ 0 := by
        simp only [liftC, coe_mapRingHom, coeff_map]
        intro h0; exact hnz (hinj (by rw [map_zero]; exact h0))
      exact (wdeg_le_iff wY (wdeg wY (liftC Fpoly)) (liftC Fpoly)).mp le_rfl k' j' i' hnz'
    -- Since liftC G = liftC Fpoly * Q', D(Q') = 0, deg_R(Q') ≤ s - d, wdeg(Q') ≤ W - W_F!
    have hQ'mem : contactDeriv Q' = 0 ∧ Q'.natDegree ≤ s - d ∧ wdeg wY Q' ≤ W - W_F := by
      refine ⟨?_, ?_, ?_⟩
      · have hD := congrArg contactDeriv hQ'
        rw [hG_rat_mem.1, contactDeriv_mul, hF_rat_mem.1, zero_mul, zero_add] at hD
        exact (mul_eq_zero.mp hD.symm).resolve_left hFne_rat
      · have hdeg_mul := natDegree_mul hFne_rat hQ'ne
        rw [← hQ', hF_rat_deg] at hdeg_mul
        omega
      · have hw_mul := wdeg_mul wY hFne_rat hQ'ne
        rw [← hQ', hF_rat_wdeg] at hw_mul
        omega
    -- Hence Q' = toPolyRat (W - W_F) (s - d) c1, so coordRat (liftC G) = T c1 ∈ range T!
    obtain ⟨c1, hc1, _⟩ := (mem_kerD_iff_exists_unique_coords hwY Q').mp hQ'mem
    have hc1' : Q' = toPolyRat (W - W_F) (s - d) c1 := hc1
    have hG_eq : toPolyRat W s (fun e => alg (gPoly u e)) = liftC G := by
      dsimp only [toPolyRat, G, liftC]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [map_mul]
      congr 1
      · unfold cC; simp [alg, coe_mapRingHom]
      · unfold kerDBasisPoly cR cY cX; simp [map_mul, map_pow, map_add, coe_mapRingHom]
    have hT_eq : T c1 = fun e => alg (gPoly u e) := by
      have hprod : toPolyRat W s (T c1) = toPolyRat W s (fun e => alg (gPoly u e)) := by
        rw [hT_reconstruct, ← hc1', ← hQ', hG_eq]
      funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hprod
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hprod
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have hv_zero : (fun e => alg (gPoly u e)) = 0 :=
      hI0_disj (fun e => alg (gPoly u e))
        (fun e he => by dsimp only [gPoly]; rw [dif_neg he, map_zero])
        ⟨c1, hT_eq⟩
    apply hGne_rat
    rw [← hG_eq]
    dsimp only [toPolyRat]
    apply Finset.sum_eq_zero; intro e _
    have h0 := congrFun hv_zero e
    rw [h0]; simp [cC]
  · -- Evaluation vanishing: if F_z(X, P, P') = 0 and P agrees with y_i(z) at A points, then G_z(X, P, P') = 0!
    intro A hWlt z P hP Az hAz hagree hFvan
    by_contra hGvan
    let E := evalContact (evalZContact G z) P
    have hdvd_each : ∀ i ∈ Az, (X - C (x i)) ^ (2 * m) ∣ E := by
      intro i hi
      -- Specialize hlocal_van i at Z = z and apply evalLocal (x i) ((y i).eval z) P!
      have hloc_z := twOrdGE_evalZLocal (hlocal_van i) z
      have hdvd := pow_two_mul_dvd_evalLocal_of_twOrdGE (x i) ((y i).eval z) P (hagree i hi) hloc_z
      have hEv : evalLocal (x i) ((y i).eval z) P
          (evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z) = E := by
        have hsub : evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z =
            evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z -
            evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z *
            evalZLocal (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) z := by
          rw [← evalZLocal_mul]
          exact eq_sub_of_add_eq (G := LocalPoly F)
            (by rw [← evalZLocal_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hsub, map_sub, map_mul]
        have hEvG : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z) = E := by
          dsimp only [E, G]
          rw [show evalZLocal (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZLocal (locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z from by
                unfold evalZLocal; simp [Polynomial.map_sum],
              show evalZContact (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZContact (cC (gPoly u e) * kerDBasisPoly e.1) z from by
                unfold evalZContact; simp [Polynomial.map_sum],
              map_sum, evalContact_sum]
          apply Finset.sum_congr rfl; intro e _
          rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
            evalLocal_kerDLocalPoly,
            show evalZContact (_ * _) z = evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z from by
              unfold evalZContact; simp [Polynomial.map_mul],
            evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
        have hEvF : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z) = 0 := by
          rw [show evalZLocal (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                evalZLocal (locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z from by
                unfold evalZLocal; simp [Polynomial.map_sum],
              map_sum]
          trans evalContact (evalZContact Fpoly z) P
          · dsimp only [Fpoly]
            rw [show evalZContact (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                  evalZContact (cC (f_coord e1) * kerDBasisPoly e1.1) z from by
                  unfold evalZContact; simp [Polynomial.map_sum],
                evalContact_sum]
            apply Finset.sum_congr rfl; intro e1 _
            rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
              evalLocal_kerDLocalPoly,
              show evalZContact (_ * _) z = evalZContact (cC (f_coord e1)) z * evalZContact (kerDBasisPoly e1.1) z from by
                unfold evalZContact; simp [Polynomial.map_mul],
              evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
          · exact hFvan
        rw [hEvG, hEvF, zero_mul, sub_zero]
      rwa [hEv] at hdvd
    have hdvd_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m)) ∣ E := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        apply IsCoprime.pow
        have hne_x : x i ≠ x j := fun h => hij (x.injective h)
        refine ⟨C (x j - x i)⁻¹, -C (x j - x i)⁻¹, ?_⟩
        have hne' : x j - x i ≠ 0 := sub_ne_zero.mpr hne_x.symm
        calc C (x j - x i)⁻¹ * (X - C (x i)) + -C (x j - x i)⁻¹ * (X - C (x j))
            = C (x j - x i)⁻¹ * C (x j - x i) := by rw [map_sub]; ring
          _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne', map_one]
      · exact hdvd_each
    have hdeg_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m)).natDegree = Az.card * (2 * m) := by
      rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
      simp [natDegree_pow, natDegree_X_sub_C]
    have hle_deg : Az.card * (2 * m) ≤ E.natDegree := by
      rw [← hdeg_prod]; exact natDegree_le_of_dvd hdvd_prod hGvan
    have hE_deg : E.natDegree ≤ W := by
      apply natDegree_evalContact_le wY W hwY _ P hP
      rw [wdeg_le_iff]; intro k' j' i' hnz
      have hmem : evalZContact G z = ∑ e : KerDIdx wY W s, cC ((gPoly u e).eval z) * kerDBasisPoly e.1 := by
        dsimp only [G]; unfold evalZContact; simp only [Polynomial.map_sum, Polynomial.map_mul]
        apply Finset.sum_congr rfl; intro e _
        change evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z = _
        rw [evalZContact_cC, evalZContact_kerDBasisPoly]
      rw [hmem, coeff_sum_kerDBasisPoly (by omega)] at hnz
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, and_self, ↓reduceIte] at hnz
        split_ifs at hnz with hm1
        · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm1).2.2
          have hj2 : 2 * (j' / 2) = j' := by omega
          have hi2 : 2 * (i' / 2) = i' := by omega
          nlinarith only [hw, hj2, hi2]
        · exact absurd rfl hnz
      · simp only [h00, ↓reduceIte] at hnz
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, and_self, ↓reduceIte] at hnz
          split_ifs at hnz with hm2
          · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm2).2.2
            have hj2 : 2 * (j' / 2) + 1 = j' := by omega
            have hi2 : 2 * (i' / 2) = i' := by omega
            nlinarith only [hw, hj2, hi2]
          · exact absurd rfl hnz
        · simp only [h10, ↓reduceIte] at hnz
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, and_self, ↓reduceIte] at hnz
            split_ifs at hnz with hm3
            · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm3).2.2
              have hj2 : 2 * (j' / 2) = j' := by omega
              have hi2 : 2 * (i' / 2) + 1 = i' := by omega
              have hk1 : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY, h01.2.2]; ring
              nlinarith only [hw, hj2, hi2, hk1]
            · exact absurd rfl hnz
          · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz
    nlinarith only [hWlt, hAz, hle_deg, hE_deg]

end LocalRing

/-! ### Part 6: `(Y, Z)`-weighted degree `wYZ`, `yWeightSum`, and weighted global/quotient interpolation -/

/-- Sum of `Y`-degrees `2*b + r` over all basis indices `e = (k, r, b, a) ∈ KerDIdx wY W s`. -/
def yWeightSum (wY W s : ℕ) : ℕ :=
  ∑ e ∈ kerDIdxFinset wY W s, (2 * e.2.2.1 + e.2.1)

/-- Closed-form arithmetic evaluation of `yWeightSum` for one `(k, r)` parity block. -/
def yWeightSumBlock (wY rem r : ℕ) : ℕ :=
  let bmax := rem / (2 * wY)
  let c0 := rem / 2 + 1
  r * ((bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2) +
    (bmax * (bmax + 1) * c0 - wY * bmax * (bmax + 1) * (2 * bmax + 1) / 3)

/-- Fast 6-term closed-form evaluation of `yWeightSum wY W s`. -/
def yWeightSumClosed (wY W s : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (s + 1),
    ∑ r ∈ Finset.range 2,
      if k + r ≤ s then
        let cost := k * (wY - 1) + r * wY
        if cost ≤ W then yWeightSumBlock wY (W - cost) r
        else 0
      else 0

private lemma sum_yWeight_block_eq (wY rem r : ℕ) (hwY : 0 < wY) :
    let bmax := rem / (2 * wY)
    ∑ b ∈ Finset.range (bmax + 1), (2 * b + r) * ((rem - 2 * b * wY) / 2 + 1) =
      yWeightSumBlock wY rem r := by
  intro bmax
  let c0 := rem / 2 + 1
  have hterm : ∀ b ∈ Finset.range (bmax + 1),
      (2 * b + r) * ((rem - 2 * b * wY) / 2 + 1) = (2 * b + r) * (c0 - b * wY) := by
    intro b hb
    have hble : b ≤ bmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hmul : 2 * (b * wY) ≤ rem := by
      have h1 : b * (2 * wY) ≤ rem / (2 * wY) * (2 * wY) := Nat.mul_le_mul_right _ hble
      have h2 : rem / (2 * wY) * (2 * wY) ≤ rem := Nat.div_mul_le_self rem (2 * wY)
      linarith
    have hsub : (rem - 2 * b * wY) / 2 = rem / 2 - b * wY := by
      rw [show 2 * b * wY = 2 * (b * wY) by ring]; omega
    have hle2 : b * wY ≤ rem / 2 := by omega
    congr 1; dsimp [c0]; omega
  rw [Finset.sum_congr rfl hterm]
  have hsplit : (∑ b ∈ Finset.range (bmax + 1), (2 * b + r) * (c0 - b * wY)) =
      r * (∑ b ∈ Finset.range (bmax + 1), (c0 - b * wY)) +
      (∑ b ∈ Finset.range (bmax + 1), 2 * b * (c0 - b * wY)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [hsplit]
  have hpart1 : ∑ b ∈ Finset.range (bmax + 1), (c0 - b * wY) =
      (bmax + 1) * c0 - wY * bmax * (bmax + 1) / 2 := by
    have hEq := sum_parity_block_eq wY rem hwY
    dsimp only at hEq
    rw [← hEq]; apply Finset.sum_congr rfl; intro b hb
    have hble : b ≤ bmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hmul : 2 * (b * wY) ≤ rem := by
      have h1 : b * (2 * wY) ≤ rem / (2 * wY) * (2 * wY) := Nat.mul_le_mul_right _ hble
      have h2 : rem / (2 * wY) * (2 * wY) ≤ rem := Nat.div_mul_le_self rem (2 * wY)
      linarith
    have hsub : (rem - 2 * b * wY) / 2 = rem / 2 - b * wY := by
      rw [show 2 * b * wY = 2 * (b * wY) by ring]; omega
    dsimp [c0]; omega
  have hbw_le : bmax * wY ≤ c0 := by
    have h0 : 2 * (bmax * wY) ≤ rem := by
      have := Nat.div_mul_le_self rem (2 * wY); dsimp [bmax] at *; linarith
    dsimp [c0]; omega
  have hpart2 : ∑ b ∈ Finset.range (bmax + 1), 2 * b * (c0 - b * wY) =
      bmax * (bmax + 1) * c0 - wY * bmax * (bmax + 1) * (2 * bmax + 1) / 3 := by
    have hdiv3 : ∀ n : ℕ, 3 ∣ n * (n + 1) * (2 * n + 1) := by
      intro n
      have hm : n % 3 < 3 := Nat.mod_lt n (by norm_num)
      set q := n / 3; set t := n % 3
      have hn : n = 3 * q + t := by omega
      rw [hn]; interval_cases t
      · exact ⟨q * (3 * q + 1) * (6 * q + 1), by ring⟩
      · exact ⟨(3 * q + 1) * (3 * q + 2) * (2 * q + 1), by ring⟩
      · exact ⟨(3 * q + 2) * (q + 1) * (6 * q + 5), by ring⟩
    have hsumZ : ∀ n : ℕ, n ≤ bmax + 1 →
        (∑ b ∈ Finset.range n, ((2 * b * (c0 - b * wY) : ℕ) : ℤ)) =
          (((n - 1) * n * c0 : ℕ) : ℤ) - (wY : ℤ) * (((n - 1) * n * (2 * (n - 1) + 1) / 3 : ℕ) : ℤ) := by
      intro n hn
      induction n with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, ih (by omega)]
          have hmle : m * wY ≤ c0 := (Nat.mul_le_mul_right wY (by omega : m ≤ bmax)).trans hbw_le
          have hstep3 : m * (m + 1) * (2 * m + 1) / 3 =
              (m - 1) * m * (2 * (m - 1) + 1) / 3 + 2 * m * m := by
            cases m with
            | zero => simp
            | succ k =>
                simp only [Nat.add_sub_cancel]
                obtain ⟨u, hu⟩ := hdiv3 k
                obtain ⟨v, hv⟩ := hdiv3 (k + 1)
                rw [hu, hv, Nat.mul_div_right _ (by norm_num), Nat.mul_div_right _ (by norm_num)]
                have hrel : 3 * v = 3 * u + 6 * ((k + 1) * (k + 1)) := by
                  rw [← hu, ← hv]; ring
                have h2 : 2 * (k + 1) * (k + 1) = 2 * ((k + 1) * (k + 1)) := by ring
                rw [h2]; omega
          rw [Nat.add_sub_cancel, hstep3]
          have hsubZ : ((2 * m * (c0 - m * wY) : ℕ) : ℤ) = 2 * (m : ℤ) * ((c0 : ℤ) - (m : ℤ) * (wY : ℤ)) := by
            rw [Nat.cast_mul, Nat.cast_sub hmle]; push_cast; ring
          rw [hsubZ]
          cases m with
          | zero => simp
          | succ k => simp only [Nat.add_sub_cancel]; push_cast; ring
    have hle_tot : wY * bmax * (bmax + 1) * (2 * bmax + 1) / 3 ≤ bmax * (bmax + 1) * c0 := by
      cases hb : bmax with
      | zero => simp
      | succ k =>
          have hbw_le' : (k + 1) * wY ≤ c0 := by rwa [← hb]
          have h3 : 2 * (k + 1) + 1 ≤ 3 * (k + 1) := by omega
          have h1 : wY * (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) ≤
              3 * ((k + 1) * (k + 1 + 1) * c0) := by
            calc wY * (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1)
                ≤ wY * (k + 1) * (k + 1 + 1) * (3 * (k + 1)) := Nat.mul_le_mul_left _ h3
              _ = 3 * ((k + 1) * (k + 1 + 1) * ((k + 1) * wY)) := by ring
              _ ≤ 3 * ((k + 1) * (k + 1 + 1) * c0) := by
                  exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ hbw_le')
          omega
    have hmul3 : wY * bmax * (bmax + 1) * (2 * bmax + 1) / 3 =
        wY * (bmax * (bmax + 1) * (2 * bmax + 1) / 3) := by
      rw [show wY * bmax * (bmax + 1) * (2 * bmax + 1) = wY * (bmax * (bmax + 1) * (2 * bmax + 1)) by ring]
      exact Nat.mul_div_assoc wY (hdiv3 bmax)
    have hZ : ((∑ b ∈ Finset.range (bmax + 1), 2 * b * (c0 - b * wY) : ℕ) : ℤ) =
        ((bmax * (bmax + 1) * c0 - wY * bmax * (bmax + 1) * (2 * bmax + 1) / 3 : ℕ) : ℤ) := by
      rw [Nat.cast_sum, hsumZ (bmax + 1) le_rfl, Nat.add_sub_cancel, Nat.cast_sub hle_tot, hmul3]
      push_cast; ring
    exact_mod_cast hZ
  rw [hpart1, hpart2]; rfl

/-- `yWeightSum wY W s = yWeightSumClosed wY W s` for all `0 < wY`! -/
theorem yWeightSum_eq_closed (wY W s : ℕ) (hwY : 0 < wY) :
    yWeightSum wY W s = yWeightSumClosed wY W s := by
  unfold yWeightSum kerDIdxFinset yWeightSumClosed
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl; intro r _
      by_cases hkr : k + r ≤ s
      · simp only [hkr, ↓reduceIte]
        by_cases hcost : k * (wY - 1) + r * wY ≤ W
        · simp only [hcost, ↓reduceIte]
          rw [Finset.sum_biUnion]
          · trans ∑ b ∈ Finset.range ((W - (k * (wY - 1) + r * wY)) / (2 * wY) + 1),
                (2 * b + r) * ((W - (k * (wY - 1) + r * wY) - 2 * b * wY) / 2 + 1)
            · apply Finset.sum_congr rfl; intro b _
              rw [Finset.sum_image]
              · simp [Finset.sum_const, smul_eq_mul, mul_comm]
              · intro a1 _ a2 _ h; exact (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2
            · exact sum_yWeight_block_eq wY (W - (k * (wY - 1) + r * wY)) r hwY
          · intro b1 _ b2 _ hne
            dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
            simp only [Finset.mem_image] at hx1 hx2
            rcases hx1 with ⟨_, _, rfl⟩; rcases hx2 with ⟨_, _, h⟩
            exact hne (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1.symm
        · simp [hcost]
      · simp [hkr]
    · intro r1 _ r2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
      split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
      split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
      simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨_, _, _, _, rfl⟩; rcases hx2 with ⟨_, _, _, _, h⟩
      exact hne (Prod.mk.inj (Prod.mk.inj h).2).1.symm
  · intro k1 _ k2 _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_biUnion] at hx1 hx2
    rcases hx1 with ⟨r1, _, hx1⟩; rcases hx2 with ⟨r2, _, hx2⟩
    split_ifs at hx1 <;> [skip; simp at hx1; simp at hx1]
    split_ifs at hx2 <;> [skip; simp at hx2; simp at hx2]
    simp only [Finset.mem_biUnion, Finset.mem_image] at hx1 hx2
    rcases hx1 with ⟨_, _, _, _, rfl⟩; rcases hx2 with ⟨_, _, _, _, h⟩
    exact hne (Prod.mk.inj h).1.symm

/-- Concrete global interpolation surplus for `64.01` (`m0 = 9, s0 = 2, D_ZF = 3850, dy = 1`):
`2097152 * rankKerD 9 2 * 3851 + yWeightSum 1048575 26690957 2 < varsKerDExact 1048575 26690957 2 * 3851`! -/
theorem global_surplus_6401_wtd :
    2097152 * rankKerD 9 2 * (3850 + 1) + 1 * yWeightSum 1048575 (2 * 1482831 * 9 - 1) 2 <
      varsKerDExact 1048575 (2 * 1482831 * 9 - 1) 2 * (3850 + 1) := by
  rw [yWeightSum_eq_closed 1048575 (2 * 1482831 * 9 - 1) 2 (by norm_num)]
  norm_num [rankKerD, varsKerDExact, yWeightSumClosed, yWeightSumBlock,
    Finset.sum_range_succ, Finset.sum_range_zero]

/-- `(Y, Z)`-weighted degree of `P ∈ ContactPoly (Polynomial F)`:
maximum of `deg_Z(c_{k, j, i}) + dy * j` over all nonzero coefficients `c_{k, j, i} ∈ F[Z]`. -/
noncomputable def wYZ {F : Type*} [CommRing F] (dy : ℕ) (P : ContactPoly (Polynomial F)) : ℕ :=
  P.support.sup fun k =>
    (P.coeff k).support.sup fun j =>
      ((P.coeff k).coeff j).support.sup fun i =>
        (((P.coeff k).coeff j).coeff i).natDegree + dy * j

lemma wYZ_le_iff {F : Type*} [CommRing F] (dy D : ℕ) (P : ContactPoly (Polynomial F)) :
    wYZ dy P ≤ D ↔
      ∀ k j i, ((P.coeff k).coeff j).coeff i ≠ 0 →
        (((P.coeff k).coeff j).coeff i).natDegree + dy * j ≤ D := by
  unfold wYZ
  simp only [Finset.sup_le_iff, mem_support_iff]
  constructor
  · intro h k j i hi
    have hj : (P.coeff k).coeff j ≠ 0 := fun h0 => hi (by simp [h0])
    have hk : P.coeff k ≠ 0 := fun h0 => hj (by simp [h0])
    exact h k hk j hj i hi
  · intro h k _ j _ i hi
    exact h k j i hi

lemma natDegree_Z_le_of_wYZ {F : Type*} [CommRing F] {dy D : ℕ} {P : ContactPoly (Polynomial F)}
    (h : wYZ dy P ≤ D) (k j i : ℕ) :
    (((P.coeff k).coeff j).coeff i).natDegree ≤ D := by
  by_cases h0 : ((P.coeff k).coeff j).coeff i = 0
  · simp [h0]
  · have := (wYZ_le_iff dy D P).mp h k j i h0; omega

/-- Over any integral domain `F`, `wYZ dy` is additive on nonzero products! -/
theorem wYZ_mul {F : Type*} [CommRing F] [IsDomain F] (dy : ℕ) {P Q : ContactPoly (Polynomial F)}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    wYZ dy (P * Q) = wYZ dy P + wYZ dy Q := by
  classical
  apply le_antisymm
  · rw [wYZ_le_iff]
    intro k j i hne
    rw [coeff_mul, coeff_finset_sum, coeff_finset_sum] at hne
    -- Bound natDegree of the sum by max over nonzero terms
    have hdeg_le : ((((P * Q).coeff k).coeff j).coeff i).natDegree + dy * j ≤ wYZ dy P + wYZ dy Q := by
      rw [coeff_mul, coeff_finset_sum, coeff_finset_sum]
      have hsub : (∑ x ∈ Finset.antidiagonal k, ((P.coeff x.1 * Q.coeff x.2).coeff j).coeff i).natDegree ≤
          wYZ dy P + wYZ dy Q - dy * j := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun x hx => ?_)
        dsimp only [Function.comp_apply]
        rw [coeff_mul, coeff_finset_sum]
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun y hy => ?_)
        dsimp only [Function.comp_apply]
        rw [coeff_mul]
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun z hz => ?_)
        dsimp only [Function.comp_apply]
        by_cases hprod : ((P.coeff x.1).coeff y.1).coeff z.1 * ((Q.coeff x.2).coeff y.2).coeff z.2 = 0
        · simp [hprod]
        · have hp1 := (wYZ_le_iff dy (wYZ dy P) P).mp le_rfl x.1 y.1 z.1 (left_ne_zero_of_mul hprod)
          have hq2 := (wYZ_le_iff dy (wYZ dy Q) Q).mp le_rfl x.2 y.2 z.2 (right_ne_zero_of_mul hprod)
          have hj : y.1 + y.2 = j := Finset.mem_antidiagonal.mp hy
          have hmul : (((P.coeff x.1).coeff y.1).coeff z.1 * ((Q.coeff x.2).coeff y.2).coeff z.2).natDegree ≤
              (((P.coeff x.1).coeff y.1).coeff z.1).natDegree + (((Q.coeff x.2).coeff y.2).coeff z.2).natDegree :=
            natDegree_mul_le
          have : dy * j = dy * y.1 + dy * y.2 := by rw [← hj]; ring
          omega
      -- Also verify dy * j ≤ wYZ dy P + wYZ dy Q from hne!
      obtain ⟨x, _, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [coeff_mul, coeff_finset_sum] at hne1
      obtain ⟨y, hy, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
      rw [coeff_mul] at hne2
      obtain ⟨z, _, hne3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne2
      have hp1 := (wYZ_le_iff dy (wYZ dy P) P).mp le_rfl x.1 y.1 z.1 (left_ne_zero_of_mul hne3)
      have hq2 := (wYZ_le_iff dy (wYZ dy Q) Q).mp le_rfl x.2 y.2 z.2 (right_ne_zero_of_mul hne3)
      have hj : y.1 + y.2 = j := Finset.mem_antidiagonal.mp hy
      have : dy * j = dy * y.1 + dy * y.2 := by rw [← hj]; ring
      omega
    exact hdeg_le
  · -- Lower bound: pick the unique lex-maximal `(t + dy * j, k, j, i)` 4-tuple in P and Q!
    let supp4 (R : ContactPoly (Polynomial F)) : Finset (ℕ × ℕ × ℕ × ℕ) :=
      R.support.biUnion fun k =>
        (R.coeff k).support.biUnion fun j =>
          ((R.coeff k).coeff j).support.biUnion fun i =>
            (((R.coeff k).coeff j).coeff i).support.image fun t => (k, j, i, t)
    have hmem4 : ∀ (R : ContactPoly (Polynomial F)) (k j i t : ℕ),
        (k, j, i, t) ∈ supp4 R ↔ (((R.coeff k).coeff j).coeff i).coeff t ≠ 0 := by
      intro R k j i t
      simp only [supp4, Finset.mem_biUnion, Finset.mem_image, mem_support_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨k', _, j', _, i', _, t', ht', rfl, rfl, rfl, rfl⟩; exact ht'
      · intro ht
        have hi : ((R.coeff k).coeff j).coeff i ≠ 0 := fun h => ht (by simp [h])
        have hj : (R.coeff k).coeff j ≠ 0 := fun h => hi (by simp [h])
        have hk : R.coeff k ≠ 0 := fun h => hj (by simp [h])
        exact ⟨k, hk, j, hj, i, hi, t, ht, rfl, rfl, rfl, rfl⟩
    have hne4 : ∀ (R : ContactPoly (Polynomial F)), R ≠ 0 → (supp4 R).Nonempty := by
      intro R hR
      obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hR
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr (mem_support_iff.mp hk)
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (mem_support_iff.mp hj)
      obtain ⟨t, ht⟩ := Polynomial.support_nonempty.mpr (mem_support_iff.mp hi)
      exact ⟨(k, j, i, t), (hmem4 R k j i t).mpr (mem_support_iff.mp ht)⟩
    let score (p : ℕ × ℕ × ℕ × ℕ) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
      toLex (p.2.2.2 + dy * p.2.1, toLex (p.1, toLex (p.2.1, p.2.2.1)))
    obtain ⟨pM, hpM_mem, hpM_max⟩ := Finset.exists_max_image (supp4 P) score (hne4 P hP)
    obtain ⟨qM, hqM_mem, hqM_max⟩ := Finset.exists_max_image (supp4 Q) score (hne4 Q hQ)
    have hwtP : wYZ dy P = pM.2.2.2 + dy * pM.2.1 := by
      apply le_antisymm
      · rw [wYZ_le_iff]; intro k j i hi
        have hlt := leadingCoeff_ne_zero.mpr hi
        have hle := hpM_max (k, j, i, (((P.coeff k).coeff j).coeff i).natDegree) ((hmem4 P _ _ _ _).mpr hlt)
        exact (Prod.Lex.le_iff.mp hle).elim le_of_lt (fun h => h.1.le)
      · have hpM_nz := (hmem4 P _ _ _ _).mp hpM_mem
        have hi_nz : ((P.coeff pM.1).coeff pM.2.1).coeff pM.2.2.1 ≠ 0 := fun h => hpM_nz (by simp [h])
        have hle1 := le_natDegree_of_ne_zero hpM_nz
        have hle2 := (wYZ_le_iff dy (wYZ dy P) P).mp le_rfl pM.1 pM.2.1 pM.2.2.1 hi_nz
        exact (Nat.add_le_add_right hle1 _).trans hle2
    have hwtQ : wYZ dy Q = qM.2.2.2 + dy * qM.2.1 := by
      apply le_antisymm
      · rw [wYZ_le_iff]; intro k j i hi
        have hlt := leadingCoeff_ne_zero.mpr hi
        have hle := hqM_max (k, j, i, (((Q.coeff k).coeff j).coeff i).natDegree) ((hmem4 Q _ _ _ _).mpr hlt)
        exact (Prod.Lex.le_iff.mp hle).elim le_of_lt (fun h => h.1.le)
      · have hqM_nz := (hmem4 Q _ _ _ _).mp hqM_mem
        have hi_nz : ((Q.coeff qM.1).coeff qM.2.1).coeff qM.2.2.1 ≠ 0 := fun h => hqM_nz (by simp [h])
        have hle1 := le_natDegree_of_ne_zero hqM_nz
        have hle2 := (wYZ_le_iff dy (wYZ dy Q) Q).mp le_rfl qM.1 qM.2.1 qM.2.2.1 hi_nz
        exact (Nat.add_le_add_right hle1 _).trans hle2
    have huniq : ∀ k1 k2 j1 j2 i1 i2 t1 t2,
        k1 + k2 = pM.1 + qM.1 → j1 + j2 = pM.2.1 + qM.2.1 →
        i1 + i2 = pM.2.2.1 + qM.2.2.1 → t1 + t2 = pM.2.2.2 + qM.2.2.2 →
        (((P.coeff k1).coeff j1).coeff i1).coeff t1 * (((Q.coeff k2).coeff j2).coeff i2).coeff t2 ≠ 0 →
        (k1, j1, i1, t1) = pM ∧ (k2, j2, i2, t2) = qM := by
      intro k1 k2 j1 j2 i1 i2 t1 t2 hk hj hi ht hprod
      have hleP := hpM_max (k1, j1, i1, t1) ((hmem4 P _ _ _ _).mpr (left_ne_zero_of_mul hprod))
      have hleQ := hqM_max (k2, j2, i2, t2) ((hmem4 Q _ _ _ _).mpr (right_ne_zero_of_mul hprod))
      have hw1 : t1 + dy * j1 ≤ pM.2.2.2 + dy * pM.2.1 :=
        (Prod.Lex.le_iff.mp hleP).elim le_of_lt (fun h => h.1.le)
      have hw2 : t2 + dy * j2 ≤ qM.2.2.2 + dy * qM.2.1 :=
        (Prod.Lex.le_iff.mp hleQ).elim le_of_lt (fun h => h.1.le)
      have hweq : (t1 + dy * j1) + (t2 + dy * j2) = (pM.2.2.2 + dy * pM.2.1) + (qM.2.2.2 + dy * qM.2.1) := by
        have : (t1 + t2) + dy * (j1 + j2) = (pM.2.2.2 + qM.2.2.2) + dy * (pM.2.1 + qM.2.1) := by rw [ht, hj]
        linarith
      have hweq1 : t1 + dy * j1 = pM.2.2.2 + dy * pM.2.1 := by omega
      have hweq2 : t2 + dy * j2 = qM.2.2.2 + dy * qM.2.1 := by omega
      have hleP2 : toLex (k1, toLex (j1, i1)) ≤ toLex (pM.1, toLex (pM.2.1, pM.2.2.1)) := by
        rcases Prod.Lex.le_iff.mp hleP with hlt | ⟨_, h2⟩
        · exfalso; dsimp [score] at hlt; omega
        · exact h2
      have hleQ2 : toLex (k2, toLex (j2, i2)) ≤ toLex (qM.1, toLex (qM.2.1, qM.2.2.1)) := by
        rcases Prod.Lex.le_iff.mp hleQ with hlt | ⟨_, h2⟩
        · exfalso; dsimp [score] at hlt; omega
        · exact h2
      have hk1le : k1 ≤ pM.1 := (Prod.Lex.le_iff.mp hleP2).elim le_of_lt (fun h => h.1.le)
      have hk2le : k2 ≤ qM.1 := (Prod.Lex.le_iff.mp hleQ2).elim le_of_lt (fun h => h.1.le)
      have hk1eq : k1 = pM.1 := by omega
      have hk2eq : k2 = qM.1 := by omega
      have hleP3 : toLex (j1, i1) ≤ toLex (pM.2.1, pM.2.2.1) := by
        rcases Prod.Lex.le_iff.mp hleP2 with hlt | ⟨_, h2⟩
        · exfalso; simp at hlt; omega
        · exact h2
      have hleQ3 : toLex (j2, i2) ≤ toLex (qM.2.1, qM.2.2.1) := by
        rcases Prod.Lex.le_iff.mp hleQ2 with hlt | ⟨_, h2⟩
        · exfalso; simp at hlt; omega
        · exact h2
      have hj1le : j1 ≤ pM.2.1 := (Prod.Lex.le_iff.mp hleP3).elim le_of_lt (fun h => h.1.le)
      have hj2le : j2 ≤ qM.2.1 := (Prod.Lex.le_iff.mp hleQ3).elim le_of_lt (fun h => h.1.le)
      have hj1eq : j1 = pM.2.1 := by omega
      have hj2eq : j2 = qM.2.1 := by omega
      have hi1le : i1 ≤ pM.2.2.1 := by
        rcases Prod.Lex.le_iff.mp hleP3 with hlt | ⟨_, h2⟩
        · exfalso; simp at hlt; omega
        · exact h2
      have hi2le : i2 ≤ qM.2.2.1 := by
        rcases Prod.Lex.le_iff.mp hleQ3 with hlt | ⟨_, h2⟩
        · exfalso; simp at hlt; omega
        · exact h2
      have hi1eq : i1 = pM.2.2.1 := by omega
      have hi2eq : i2 = qM.2.2.1 := by omega
      have ht1eq : t1 = pM.2.2.2 := by rw [hj1eq] at hweq1; omega
      have ht2eq : t2 = qM.2.2.2 := by rw [hj2eq] at hweq2; omega
      exact ⟨Prod.ext hk1eq (Prod.ext hj1eq (Prod.ext hi1eq ht1eq)),
        Prod.ext hk2eq (Prod.ext hj2eq (Prod.ext hi2eq ht2eq))⟩
    have hcoeff_ne :
        ((((P * Q).coeff (pM.1 + qM.1)).coeff (pM.2.1 + qM.2.1)).coeff (pM.2.2.1 + qM.2.2.1)).coeff
          (pM.2.2.2 + qM.2.2.2) ≠ 0 := by
      rw [coeff_mul, coeff_finset_sum, coeff_finset_sum, coeff_finset_sum]
      rw [Finset.sum_eq_single (pM.1, qM.1)]
      · rw [coeff_mul, coeff_finset_sum, coeff_finset_sum]
        rw [Finset.sum_eq_single (pM.2.1, qM.2.1)]
        · rw [coeff_mul, coeff_finset_sum]
          rw [Finset.sum_eq_single (pM.2.2.1, qM.2.2.1)]
          · rw [coeff_mul]
            rw [Finset.sum_eq_single (pM.2.2.2, qM.2.2.2)]
            · exact mul_ne_zero ((hmem4 P _ _ _ _).mp hpM_mem) ((hmem4 Q _ _ _ _).mp hqM_mem)
            · intro w hw hne
              by_contra hnz
              have := huniq pM.1 qM.1 pM.2.1 qM.2.1 pM.2.2.1 qM.2.2.1 w.1 w.2
                rfl rfl rfl (Finset.mem_antidiagonal.mp hw) hnz
              exact hne (Prod.ext (congrArg (fun t => t.2.2.2) this.1) (congrArg (fun t => t.2.2.2) this.2))
            · intro hnot; simp at hnot
          · intro x hx hne
            rw [coeff_mul]; apply Finset.sum_eq_zero; intro w hw
            by_contra hnz
            have := huniq pM.1 qM.1 pM.2.1 qM.2.1 x.1 x.2 w.1 w.2
              rfl rfl (Finset.mem_antidiagonal.mp hx) (Finset.mem_antidiagonal.mp hw) hnz
            exact hne (Prod.ext (congrArg (fun t => t.2.2.1) this.1) (congrArg (fun t => t.2.2.1) this.2))
          · intro hnot; simp at hnot
        · intro y hy hne
          rw [coeff_mul, coeff_finset_sum]; apply Finset.sum_eq_zero; intro x hx
          rw [coeff_mul]; apply Finset.sum_eq_zero; intro w hw
          by_contra hnz
          have := huniq pM.1 qM.1 y.1 y.2 x.1 x.2 w.1 w.2
            rfl (Finset.mem_antidiagonal.mp hy) (Finset.mem_antidiagonal.mp hx) (Finset.mem_antidiagonal.mp hw) hnz
          exact hne (Prod.ext (congrArg (fun t => t.2.1) this.1) (congrArg (fun t => t.2.1) this.2))
        · intro hnot; simp at hnot
      · intro z hz hne
        rw [coeff_mul, coeff_finset_sum, coeff_finset_sum]; apply Finset.sum_eq_zero; intro y hy
        rw [coeff_mul, coeff_finset_sum]; apply Finset.sum_eq_zero; intro x hx
        rw [coeff_mul]; apply Finset.sum_eq_zero; intro w hw
        by_contra hnz
        have := huniq z.1 z.2 y.1 y.2 x.1 x.2 w.1 w.2
          (Finset.mem_antidiagonal.mp hz) (Finset.mem_antidiagonal.mp hy)
          (Finset.mem_antidiagonal.mp hx) (Finset.mem_antidiagonal.mp hw) hnz
        exact hne (Prod.ext (congrArg (fun t => t.1) this.1) (congrArg (fun t => t.1) this.2))
      · intro hnot; simp at hnot
    have hi_ne : (((P * Q).coeff (pM.1 + qM.1)).coeff (pM.2.1 + qM.2.1)).coeff (pM.2.2.1 + qM.2.2.1) ≠ 0 :=
      fun h0 => hcoeff_ne (by simp [h0])
    have hdeg_ge : pM.2.2.2 + qM.2.2.2 ≤
        ((((P * Q).coeff (pM.1 + qM.1)).coeff (pM.2.1 + qM.2.1)).coeff (pM.2.2.1 + qM.2.2.1)).natDegree :=
      le_natDegree_of_ne_zero hcoeff_ne
    have hlb := (wYZ_le_iff dy (wYZ dy (P * Q)) (P * Q)).mp le_rfl
      (pM.1 + qM.1) (pM.2.1 + qM.2.1) (pM.2.2.1 + qM.2.2.1) hi_ne
    rw [hwtP, hwtQ]
    have : dy * (pM.2.1 + qM.2.1) = dy * pM.2.1 + dy * qM.2.1 := by ring
    omega

/-- **10-line Frobenius descent `wYZ` preservation:**
If `Q(X, Y, R, w^2) = H(X, Y, R, w)^2` over an integral domain `F` and `wYZ 1 Q ≤ D_ZF`,
then `wYZ 2 H ≤ D_ZF`! -/
theorem wYZ_frobenius_descent {F : Type*} [CommRing F] [IsDomain F] {D_ZF : ℕ}
    {Q H : ContactPoly (Polynomial F)}
    (hsq : Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2)))) = H ^ 2)
    (hw : wYZ 1 Q ≤ D_ZF) :
    wYZ 2 H ≤ D_ZF := by
  by_cases hH : H = 0
  · subst hH; simp [wYZ]
  · have h2H : wYZ 2 (H ^ 2) = 2 * wYZ 2 H := by
      rw [sq, wYZ_mul 2 hH hH]; omega
    have hQ2 : wYZ 2 (Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2))))) ≤ 2 * D_ZF := by
      rw [wYZ_le_iff]
      intro k j i hnz
      simp only [coe_mapRingHom, coeff_map, coe_compRingHom] at hnz ⊢
      have hp_nz : ((Q.coeff k).coeff j).coeff i ≠ 0 := by
        intro h0; exact hnz (by rw [h0, zero_comp])
      have h1 := (wYZ_le_iff 1 D_ZF Q).mp hw k j i hp_nz
      have hcomp : (((Q.coeff k).coeff j).coeff i |>.comp (X ^ 2)).natDegree ≤
          2 * (((Q.coeff k).coeff j).coeff i).natDegree :=
        natDegree_comp_le.trans ((Nat.mul_le_mul_left _ (natDegree_X_pow_le 2)).trans (by omega))
      omega
    rw [hsq, h2H] at hQ2
    omega

/-- Exact `Z`-degree bound on `kerDLocalNF` in terms of `2 * b + r` (without coarsening to `W / wY`). -/
lemma natDegree_kerDLocalNF_le_exact {F : Type*} [Field F] {wY W s m dy : ℕ} (hwY : 1 ≤ wY)
    (x0 : F) (y0 : Polynomial F) (hy0 : y0.natDegree ≤ dy)
    (e : KerDIdx wY W s) (idx : LocalBasisIdx m s) :
    (kerDLocalNF m s (C x0) y0 e.1 idx).natDegree ≤ dy * (2 * e.1.2.2.1 + e.1.2.1) := by
  rcases e with ⟨⟨k, r, b, a⟩, he⟩
  have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) k r b a).mp he
  unfold kerDLocalNF
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a' _ => ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b' hb' => ?_)
  have hb'_le : b' ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
  have hC1 : (((Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a'))).natDegree = 0 := by
    have : (Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a') =
        C ((Nat.choose a a' : F) * (x0 ^ 2) ^ (a - a')) := by simp
    rw [this, natDegree_C]
  have hY : ((Nat.choose b b' : Polynomial F) * (y0 ^ 2) ^ (b - b')).natDegree ≤ 2 * dy * (b - b') := by
    calc _ ≤ (Nat.choose b b' : Polynomial F).natDegree + ((y0 ^ 2) ^ (b - b')).natDegree :=
            natDegree_mul_le
      _ ≤ 0 + (b - b') * (y0 ^ 2).natDegree := by
            rw [natDegree_natCast]; exact Nat.add_le_add_left natDegree_pow_le 0
      _ ≤ (b - b') * (2 * dy) := by
            rw [zero_add]; exact Nat.mul_le_mul_left _ (natDegree_pow_le.trans (by omega))
      _ = 2 * dy * (b - b') := by ring
  have hTail : (if r = 0 then
        ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F)
       else
        y0 * ((reduceMonomialCoords m s 0 k a' b' idx : ℕ) : Polynomial F) +
        C x0 * ((reduceMonomialCoords m s 0 (k + 1) a' b' idx : ℕ) : Polynomial F) +
        ((reduceMonomialCoords m s 1 k a' b' idx : ℕ) : Polynomial F)).natDegree ≤ dy * r := by
    split_ifs with hr0
    · simp [natDegree_natCast]
    · have hr1 : r = 1 := by omega
      subst hr1; rw [mul_one]
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp [natDegree_natCast]))
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (by simp [natDegree_natCast, hy0])
      · exact natDegree_mul_le.trans (by simp [natDegree_C, natDegree_natCast])
  calc _ ≤ ((Nat.choose a a' : Polynomial F) * (C x0 ^ 2) ^ (a - a') *
            ((Nat.choose b b' : Polynomial F) * (y0 ^ 2) ^ (b - b'))).natDegree + dy * r :=
          natDegree_mul_le.trans (Nat.add_le_add_left hTail _)
    _ ≤ (0 + 2 * dy * (b - b')) + dy * r :=
          Nat.add_le_add_right (natDegree_mul_le.trans (by rw [hC1]; exact Nat.add_le_add_left hY 0)) _
    _ ≤ dy * (2 * b + r) := by have : b - b' ≤ b := Nat.sub_le b b'; nlinarith

/-- Extract coordinate-level `(Y, Z)`-weighted degree bounds for nonzero coordinates from `wYZ dy P ≤ D`. -/
lemma coord_wYZ_le_of_wYZ_ne {F : Type*} [CommRing F] [CharP F 2] {wY W s dy D : ℕ} (hwY : 0 < wY)
    (c : KerDIdx wY W s → Polynomial F)
    (hw : wYZ dy (∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1) ≤ D) :
    ∀ e : KerDIdx wY W s, c e ≠ 0 → (c e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D := by
  intro ⟨⟨k, r, b, a⟩, he⟩ hne
  have hr := ((mem_kerDIdxFinset_iff wY W s hwY k r b a).mp he).1
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · have hcoeff : (((∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1).coeff k).coeff (2 * b)).coeff (2 * a) =
        c ⟨(k, 0, b, a), he⟩ := by
      rw [coeff_sum_kerDBasisPoly hwY]; simp [he]
    have hle := (wYZ_le_iff dy D _).mp hw k (2 * b) (2 * a) (hcoeff.symm ▸ hne)
    rw [hcoeff] at hle; simpa using hle
  · have hcoeff : (((∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1).coeff k).coeff (2 * b + 1)).coeff (2 * a) =
        c ⟨(k, 1, b, a), he⟩ := by
      rw [coeff_sum_kerDBasisPoly hwY]
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simp [h1, h2, h3, h4, he]
    have hle := (wYZ_le_iff dy D _).mp hw k (2 * b + 1) (2 * a) (hcoeff.symm ▸ hne)
    rw [hcoeff] at hle; simpa using hle

/-- Sharp `Z`-degree bound on `prodLocalNF` directly from `wYZ dy Fpoly ≤ D_ZF` (even if some `f_coord e = 0`!). -/
lemma natDegree_prodLocalNF_le_of_wYZ {F : Type*} [Field F] {wY W_F d m s dy D_ZF : ℕ} (hwY : 1 ≤ wY)
    (x0 : F) (y0 : Polynomial F) (hy0 : y0.natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hf_wtd : ∀ e1, f_coord e1 ≠ 0 → (f_coord e1).natDegree + dy * (2 * e1.1.2.2.1 + e1.1.2.1) ≤ D_ZF)
    (e2 : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) :
    (prodLocalNF (C x0) y0 f_coord e2 idx).natDegree ≤ D_ZF := by
  unfold prodLocalNF
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e1 _ => ?_)
  by_cases h0 : f_coord e1 = 0
  · simp [h0]
  · rcases e1 with ⟨⟨k1, r1, b1, a1⟩, he1⟩
    have hmem := (mem_kerDIdxFinset_iff wY W_F d (by omega) k1 r1 b1 a1).mp he1
    have hfw := hf_wtd ⟨(k1, r1, b1, a1), he1⟩ h0
    dsimp only at hfw
    refine natDegree_mul_le.trans ((Nat.add_le_add_left ?_ _).trans hfw)
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a' _ => ?_)
    refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b' hb' => ?_)
    have hb'_le : b' ≤ b1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    have hC1 : (((Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a'))).natDegree = 0 := by
      have : (Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a') =
          C ((Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a')) := by simp
      rw [this, natDegree_C]
    have hY : ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')).natDegree ≤ 2 * dy * (b1 - b') := by
      calc _ ≤ (Nat.choose b1 b' : Polynomial F).natDegree + ((y0 ^ 2) ^ (b1 - b')).natDegree := natDegree_mul_le
        _ ≤ 0 + (b1 - b') * (y0 ^ 2).natDegree := by rw [natDegree_natCast]; exact Nat.add_le_add_left natDegree_pow_le 0
        _ ≤ (b1 - b') * (2 * dy) := by rw [zero_add]; exact Nat.mul_le_mul_left _ (natDegree_pow_le.trans (by omega))
        _ = 2 * dy * (b1 - b') := by ring
    have hTail : (if r1 = 0 then
          ((reduceMonomialCoords m s e2.1 (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F)
         else
          y0 * ((reduceMonomialCoords m s e2.1 (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F) +
          C x0 * ((reduceMonomialCoords m s e2.1 (k1 + 1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F) +
          ((reduceMonomialCoords m s (e2.1 + 1) (k1 + e2.2.1) (a' + e2.2.2.1) (b' + e2.2.2.2) idx : ℕ) : Polynomial F)).natDegree
          ≤ dy * r1 := by
      split_ifs with hr0
      · simp [natDegree_natCast]
      · have hr1 : r1 = 1 := by omega
        subst hr1; rw [mul_one]
        refine (natDegree_add_le _ _).trans (max_le ?_ (by simp [natDegree_natCast]))
        refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_mul_le.trans (by simp [natDegree_natCast, hy0])
        · exact natDegree_mul_le.trans (by simp [natDegree_C, natDegree_natCast])
    calc _ ≤ ((Nat.choose a1 a' : Polynomial F) * (C x0 ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b'))).natDegree + dy * r1 :=
            natDegree_mul_le.trans (Nat.add_le_add_left hTail _)
      _ ≤ (0 + 2 * dy * (b1 - b')) + dy * r1 :=
            Nat.add_le_add_right (natDegree_mul_le.trans (by rw [hC1]; exact Nat.add_le_add_left hY 0)) _
      _ ≤ dy * (2 * b1 + r1) := by have : b1 - b' ≤ b1 := Nat.sub_le b1 b'; nlinarith

/-- Helper: `wYZ dy (∑ e, cC (c e) * kerDBasisPoly e.1) ≤ D` whenever every nonzero coordinate `c e` satisfies
`(c e).natDegree + dy * (2 * b + r) ≤ D`! -/
lemma wYZ_sum_kerDBasisPoly_le {F : Type*} [CommRing F] [CharP F 2] {wY W s dy D : ℕ} (hwY : 0 < wY)
    (c : KerDIdx wY W s → Polynomial F)
    (hc : ∀ e : KerDIdx wY W s, c e ≠ 0 → (c e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D) :
    wYZ dy (∑ e : KerDIdx wY W s, cC (c e) * kerDBasisPoly e.1) ≤ D := by
  rw [wYZ_le_iff]
  intro k j i hnz
  rw [coeff_sum_kerDBasisPoly hwY] at hnz ⊢
  by_cases h00 : j % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte] at hnz ⊢
    split_ifs at hnz ⊢ with hm1
    · have hle := hc ⟨(k, 0, j / 2, i / 2), hm1⟩ hnz
      dsimp only at hle
      have hj : 2 * (j / 2) + 0 = j := by omega
      rw [hj] at hle; exact hle
    · exact absurd rfl hnz
  · simp only [h00, ↓reduceIte] at hnz ⊢
    by_cases h10 : j % 2 = 1 ∧ i % 2 = 0
    · simp only [h10, and_self, ↓reduceIte] at hnz ⊢
      split_ifs at hnz ⊢ with hm2
      · have hle := hc ⟨(k, 1, j / 2, i / 2), hm2⟩ hnz
        dsimp only at hle
        have hj : 2 * (j / 2) + 1 = j := by omega
        rw [hj] at hle; exact hle
      · exact absurd rfl hnz
    · simp only [h10, ↓reduceIte] at hnz ⊢
      by_cases h01 : j % 2 = 0 ∧ i % 2 = 1 ∧ 0 < k
      · simp only [h01, and_self, ↓reduceIte] at hnz ⊢
        split_ifs at hnz ⊢ with hm3
        · have hle := hc ⟨(k - 1, 1, j / 2, i / 2), hm3⟩ hnz
          dsimp only at hle
          have hj : j ≤ 2 * (j / 2) + 1 := by omega
          nlinarith
        · exact absurd rfl hnz
      · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz

/-- **Weighted global 4-variable contact interpolation theorem!**
Produces nonzero `Q ∈ K_{W0}(s0)[Z]` with `wYZ dy Q ≤ D_ZF` and `twOrdGE (localShift Q) m0` at every point,
using ONLY the exact `yWeightSum` budget `N * rankKerD m0 s0 * (D_ZF + 1) + dy * yWeightSum wY W0 s0 < varsKerDExact wY W0 s0 * (D_ZF + 1)`! -/
theorem exists_global_contact_interpolant_wtd {F ι : Type*} [Field F] [CharP F 2] [Fintype ι]
    (x : ι → F) (y : ι → Polynomial F) {dy wY W0 s0 m0 D_ZF : ℕ}
    (hwY : 1 ≤ wY) (hy : ∀ i, (y i).natDegree ≤ dy)
    (hD_ge : dy * (W0 / wY) ≤ D_ZF)
    (hsurplus : Fintype.card ι * rankKerD m0 s0 * (D_ZF + 1) + dy * yWeightSum wY W0 s0 <
      varsKerDExact wY W0 s0 * (D_ZF + 1)) :
    ∃ (Q : ContactPoly (Polynomial F)) (f_coord : KerDIdx wY W0 s0 → Polynomial F),
      Q = ∑ e : KerDIdx wY W0 s0, cC (f_coord e) * kerDBasisPoly e.1 ∧
      Q ≠ 0 ∧ contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 ∧
      wYZ dy Q ≤ D_ZF ∧
      (∀ e : KerDIdx wY W0 s0, (f_coord e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF) ∧
      ∀ i : ι, twOrdGE (∑ e : KerDIdx wY W0 s0, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) m0 := by
  classical
  let cap (e : KerDIdx wY W0 s0) : ℕ := D_ZF + 1 - dy * (2 * e.1.2.2.1 + e.1.2.1)
  have hbr_le : ∀ e : KerDIdx wY W0 s0, dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF := by
    intro ⟨⟨k, r, b, a⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he
    have h1 : (2 * b + r) * wY ≤ W0 := by nlinarith [hmem.2.2]
    have h2 : 2 * b + r ≤ W0 / wY := (Nat.le_div_iff_mul_le (by omega : 0 < wY)).mpr h1
    exact (Nat.mul_le_mul_left dy h2).trans hD_ge
  let I := Σ e : KerDIdx wY W0 s0, Fin (cap e)
  let J := ι × LocalBasisIdx m0 s0 × Fin (D_ZF + 1)
  let cPoly (v : I → F) (e : KerDIdx wY W0 s0) : Polynomial F :=
    ∑ t : Fin (cap e), C (v ⟨e, t⟩) * X ^ t.val
  let L : (I → F) →ₗ[F] (J → F) :=
    { toFun := fun v j =>
        let (i, idx, t) := j
        (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).coeff t.val
      map_add' := by
        intro v1 v2; funext ⟨i, idx, t⟩
        have hc : ∀ e, cPoly (v1 + v2) e = cPoly v1 e + cPoly v2 e := fun e => by
          dsimp [cPoly]; simp [add_mul, Finset.sum_add_distrib]
        simp only [hc, add_mul, Finset.sum_add_distrib, coeff_add, finset_sum_coeff, Pi.add_apply]
      map_smul' := by
        intro a v; funext ⟨i, idx, t⟩
        have hc : ∀ e, cPoly (a • v) e = C a * cPoly v e := fun e => by
          dsimp [cPoly]; simp [Finset.mul_sum, mul_assoc]
        simp only [hc, mul_assoc, ← Finset.mul_sum, finset_sum_coeff, coeff_C_mul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] }
  have hcard : Fintype.card J < Fintype.card I := by
    have hI_eq : Fintype.card I + dy * yWeightSum wY W0 s0 = varsKerDExact wY W0 s0 * (D_ZF + 1) := by
      simp only [I, Fintype.card_sigma, Fintype.card_fin]
      have hsum_y : dy * yWeightSum wY W0 s0 = ∑ e : KerDIdx wY W0 s0, dy * (2 * e.1.2.2.1 + e.1.2.1) := by
        unfold yWeightSum; rw [Finset.mul_sum, ← Finset.sum_coe_sort]
      rw [hsum_y, ← Finset.sum_add_distrib]
      trans ∑ _e : KerDIdx wY W0 s0, (D_ZF + 1)
      · apply Finset.sum_congr rfl; intro e _
        have hle := hbr_le e
        dsimp [cap]; omega
      · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_kerDIdx wY W0 s0 (by omega)]
    simp only [J, Fintype.card_prod, Fintype.card_fin, card_localBasisIdx m0 s0, ← mul_assoc]
    omega
  obtain ⟨v, hv_ne, hLv⟩ := exists_ne_zero_ker_linearMap L hcard
  let Q : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W0 s0, cC (cPoly v e) * kerDBasisPoly e.1
  have hQne : Q ≠ 0 := by
    intro hQ0; apply hv_ne; funext ⟨e, t⟩
    have hc0 : cPoly v e = 0 := by
      rcases e with ⟨⟨k, r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) hQ0
        dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) hQ0
        dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc0
    dsimp only [cPoly] at ht; rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
    · simpa [coeff_C_mul, coeff_X_pow] using ht
    · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
      simp [coeff_C_mul, coeff_X_pow, this.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQmem : contactDeriv Q = 0 ∧ Q.natDegree ≤ s0 ∧ wdeg wY Q ≤ W0 := by
    refine (mem_kerD_iff_exists_unique_coords hwY Q).mpr ⟨cPoly v, rfl, ?_⟩
    intro c' hc'; funext ⟨⟨k, r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) k r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k).coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [Q] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  have hc_wtd : ∀ e : KerDIdx wY W0 s0, (cPoly v e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D_ZF := by
    intro e
    have hle := hbr_le e
    have hdeg : (cPoly v e).natDegree ≤ D_ZF - dy * (2 * e.1.2.2.1 + e.1.2.1) := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ => ?_)
      have ht := t.isLt; dsimp [cap] at ht
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  have hwQ : wYZ dy Q ≤ D_ZF := wYZ_sum_kerDBasisPoly_le (by omega) (cPoly v) (fun e _ => hc_wtd e)
  refine ⟨Q, cPoly v, rfl, hQne, hQmem.1, hQmem.2.1, hQmem.2.2, hwQ, hc_wtd, ?_⟩
  intro i
  have hNF0 : ∀ idx : LocalBasisIdx m0 s0,
      (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) = 0 := by
    intro idx
    have hdeg : (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx).natDegree ≤ D_ZF := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => natDegree_mul_le.trans ?_)
      have h1 := hc_wtd e
      have h2 := natDegree_kerDLocalNF_le_exact hwY (x i) (y i) (hy i) e idx
      omega
    ext t; rw [coeff_zero]
    by_cases ht : t < D_ZF + 1
    · exact congrFun hLv (i, idx, ⟨t, ht⟩)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hEq : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) * kerDLocalPoly (C (x i)) (y i) e.1) =
      ∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
        (kerDLocalPoly (C (x i)) (y i) e.1 -
          ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
    have hzero : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
        ∑ idx : LocalBasisIdx m0 s0, locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) = 0 := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro idx _
      have hsum : (∑ e : KerDIdx wY W0 s0, locC (cPoly v e) *
            (locC (kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) * localBasisElem idx.1)) =
          locC (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) *
            localBasisElem idx.1 := by
        rw [show locC (∑ e : KerDIdx wY W0 s0, cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx) =
              ∑ e : KerDIdx wY W0 s0, locC (cPoly v e * kerDLocalNF m0 s0 (C (x i)) (y i) e.1 idx)
              from by unfold locC; simp [map_sum], Finset.sum_mul]
        apply Finset.sum_congr rfl; intro e _; unfold locC; simp [map_mul, mul_assoc]
      rw [hsum, hNF0 idx]; simp [locC]
    rw [← sub_zero (G := LocalPoly (Polynomial F)) (∑ e : KerDIdx wY W0 s0, _), ← hzero,
      ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro e _
    have hms : ∀ a b c : LocalPoly (Polynomial F), a * (b - c) = a * b - a * c := fun a b c =>
      eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
    exact (hms _ _ _).symm
  rw [hEq]; apply twOrdGE_sum; intro e _
  have hmem := (mem_kerDIdxFinset_iff wY W0 s0 (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  simpa using twOrdGE_mul (twOrdGE_zero _)
    (twOrdGE_kerDLocalPoly_sub_NF m0 s0 (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)

/-- Evaluation vanishing corollary for `exists_global_contact_interpolant_wtd` (arbitrary `f_coord`). -/
theorem evalContact_eq_zero_of_global_coords {F ι : Type*} [Field F] [CharP F 2] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {wY W0 s0 m0 A : ℕ}
    (hwY : 1 ≤ wY) (hW0 : W0 < 2 * A * m0)
    (f_coord : KerDIdx wY W0 s0 → Polynomial F)
    (hvan : ∀ i : ι, twOrdGE (∑ e : KerDIdx wY W0 s0, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) m0)
    (z : F) (P : Polynomial F) (hP : P.natDegree ≤ wY)
    (Az : Finset ι) (hAz : A ≤ Az.card)
    (hagree : ∀ i ∈ Az, P.eval (x i) = (y i).eval z) :
    evalContact (evalZContact (∑ e : KerDIdx wY W0 s0, cC (f_coord e) * kerDBasisPoly e.1) z) P = 0 := by
  by_contra hne
  let Q := ∑ e : KerDIdx wY W0 s0, cC (f_coord e) * kerDBasisPoly e.1
  let E := evalContact (evalZContact Q z) P
  have hdvd_each : ∀ i ∈ Az, (X - C (x i)) ^ (2 * m0) ∣ E := by
    intro i hi
    have hEqE : E = evalLocal (x i) ((y i).eval z) P
        (evalZLocal (∑ e : KerDIdx wY W0 s0, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) z) := by
      dsimp only [E, Q]
      rw [show evalZContact (∑ e : KerDIdx wY W0 s0, cC (f_coord e) * kerDBasisPoly e.1) z =
            ∑ e : KerDIdx wY W0 s0, evalZContact (cC (f_coord e) * kerDBasisPoly e.1) z
            from by unfold evalZContact; rw [Polynomial.map_sum],
          show evalZLocal (∑ e : KerDIdx wY W0 s0, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) z =
            ∑ e : KerDIdx wY W0 s0, evalZLocal (locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) z
            from by unfold evalZLocal; rw [Polynomial.map_sum],
          evalContact_sum, map_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [show evalZContact (cC (f_coord e) * kerDBasisPoly e.1) z =
            evalZContact (cC (f_coord e)) z * evalZContact (kerDBasisPoly e.1) z
            from by unfold evalZContact; rw [Polynomial.map_mul],
          evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC,
          evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul,
          evalLocal_locC, evalLocal_kerDLocalPoly]
    rw [hEqE]
    exact pow_two_mul_dvd_evalLocal_of_twOrdGE (x i) ((y i).eval z) P (hagree i hi) (twOrdGE_evalZLocal (hvan i) z)
  have hdvd_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m0)) ∣ E := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      apply IsCoprime.pow
      have hne_x : x i ≠ x j := fun h => hij (x.injective h)
      refine ⟨C (x j - x i)⁻¹, -C (x j - x i)⁻¹, ?_⟩
      have hne' : x j - x i ≠ 0 := sub_ne_zero.mpr hne_x.symm
      calc C (x j - x i)⁻¹ * (X - C (x i)) + -C (x j - x i)⁻¹ * (X - C (x j))
          = C (x j - x i)⁻¹ * C (x j - x i) := by rw [map_sub]; ring
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne', map_one]
    · exact hdvd_each
  have hdeg_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m0)).natDegree = Az.card * (2 * m0) := by
    rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
    simp [natDegree_pow, natDegree_X_sub_C]
  have hle_deg : Az.card * (2 * m0) ≤ E.natDegree := by
    rw [← hdeg_prod]; exact natDegree_le_of_dvd hdvd_prod hne
  have hE_deg : E.natDegree ≤ W0 := by
    apply natDegree_evalContact_le wY W0 hwY _ P hP
    have hmem : evalZContact Q z = ∑ e : KerDIdx wY W0 s0, cC ((f_coord e).eval z) * kerDBasisPoly e.1 := by
      dsimp only [Q]; unfold evalZContact; simp only [Polynomial.map_sum, Polynomial.map_mul]
      apply Finset.sum_congr rfl; intro e _
      change evalZContact (cC (f_coord e)) z * evalZContact (kerDBasisPoly e.1) z = _
      rw [evalZContact_cC, evalZContact_kerDBasisPoly]
    rw [hmem, wdeg_le_iff]; intro k' j' i' hnz
    rw [coeff_sum_kerDBasisPoly (by omega)] at hnz
    by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
    · simp only [h00, and_self, ↓reduceIte] at hnz
      split_ifs at hnz with hm1
      · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm1).2.2
        have hj2 : 2 * (j' / 2) = j' := by omega
        have hi2 : 2 * (i' / 2) = i' := by omega
        nlinarith only [hw, hj2, hi2]
      · exact absurd rfl hnz
    · simp only [h00, ↓reduceIte] at hnz
      by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
      · simp only [h10, and_self, ↓reduceIte] at hnz
        split_ifs at hnz with hm2
        · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm2).2.2
          have hj2 : 2 * (j' / 2) + 1 = j' := by omega
          have hi2 : 2 * (i' / 2) = i' := by omega
          nlinarith only [hw, hj2, hi2]
        · exact absurd rfl hnz
      · simp only [h10, ↓reduceIte] at hnz
        by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
        · simp only [h01, and_self, ↓reduceIte] at hnz
          split_ifs at hnz with hm3
          · have hw := ((mem_kerDIdxFinset_iff wY W0 s0 (by omega) _ _ _ _).mp hm3).2.2
            have hj2 : 2 * (j' / 2) = j' := by omega
            have hi2 : 2 * (i' / 2) + 1 = i' := by omega
            have hk1 : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY, h01.2.2]; ring
            nlinarith only [hw, hj2, hi2, hk1]
          · exact absurd rfl hnz
        · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz
  nlinarith only [hW0, hAz, hle_deg, hE_deg]

/-- **Weighted denominator-free 4-variable quotient interpolation theorem!**
Given nonzero `F ∈ K_{W_F}(d)[Z]` with `wYZ dy F ≤ D_ZF` and exact local orders `k_i ≤ m`,
under the sharp weighted surplus inequality (NO `+ dy * max(W/wY, W_F/wY)` overhead on equations!),
produces nonzero `G ∈ K_W(s)[Z]` with `wYZ dy G ≤ D_Z'`, `F ∤ G` over `F(Z)`, and vanishing on all
agreeing pairs `(z, P)` where `F_z(X, P, P') = 0`! -/
theorem exists_quotient_contact_interpolant_wtd {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {dy wY W_F d D_ZF m s W D_Z' : ℕ}
    (hwY : 1 ≤ wY) (hd : d ≤ s) (hW : W_F ≤ W) (hDZ : D_ZF ≤ D_Z')
    (hD_ge : dy * (W / wY) ≤ D_Z')
    (hy : ∀ i, (y i).natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hf_wYZ : wYZ dy (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (hFne : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≠ 0)
    (hFdeg : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).natDegree = d)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (k : ι → ℕ)
    (hk_exact : ∀ i,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1
      k i ≤ m ∧ (k i < m → twOrdGE Fi (k i) ∧ ∃ p q, p + q = k i ∧ twCoeff Fi p q ≠ 0))
    (hsurplus :
      Fintype.card ι * rankKerD m s * (D_Z' + 1) +
        dy * (varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)) * (W / wY) <
      (varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)) * (D_Z' + 1) +
      (∑ i : ι, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1)) :
    ∃ G : ContactPoly (Polynomial F),
      G ≠ 0 ∧ contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W ∧
      wYZ dy G ≤ D_Z' ∧
      (∀ k' j' i', (((G.coeff k').coeff j').coeff i').natDegree ≤ D_Z') ∧
      (¬ ∃ Q' : ContactPoly (RatFunc F),
        G.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) =
        (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).map
          (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) * Q') ∧
      (∀ (A : ℕ), W < 2 * A * m → ∀ (z : F) (P : Polynomial F),
        P.natDegree ≤ wY →
        ∀ (Az : Finset ι), A ≤ Az.card →
        (∀ i ∈ Az, P.eval (x i) = (y i).eval z) →
        evalContact (evalZContact (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) z) P = 0 →
        evalContact (evalZContact G z) P = 0) ∧
      (∃ (g_coord : KerDIdx wY W s → Polynomial F)
         (v_coord : ∀ i : ι, LocalBasisIdx (m - k i) (s - d) → Polynomial F),
        G = ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1 ∧
        ∀ i : ι, twOrdGE
          ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (v_coord i b) * localBasisElem b.1)) m) := by
  classical
  let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1
  let alg : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let liftC : ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom alg))
  have hFne_rat : liftC Fpoly ≠ 0 := by
    intro h0; apply hFne
    apply Polynomial.ext; intro k'; apply Polynomial.ext; intro j'; apply Polynomial.ext; intro i'
    have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
    simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
    have h0' : ((Fpoly.coeff k').coeff j').coeff i' = 0 :=
      (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by rw [map_zero]; exact h)
    simpa only [Fpoly, coeff_zero] using h0'
  have hFkerD : contactDeriv Fpoly = 0 ∧ Fpoly.natDegree ≤ d ∧ wdeg wY Fpoly ≤ W_F := by
    refine (mem_kerD_iff_exists_unique_coords hwY Fpoly).mpr ⟨f_coord, rfl, ?_⟩
    intro c' hc'; funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W_F d (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [Fpoly] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  have hRatChar2 : CharP (RatFunc F) 2 := charP_of_injective_ringHom (IsFractionRing.injective (Polynomial F) (RatFunc F)) 2
  have hF_rat_mem : contactDeriv (liftC Fpoly) = 0 ∧ (liftC Fpoly).natDegree ≤ d ∧ wdeg wY (liftC Fpoly) ≤ W_F := by
    refine ⟨?_, ?_, ?_⟩
    · ext k' j' i'
      have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff j').coeff i') hFkerD.1
      rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative] at h ⊢
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h ⊢
      have h1 : alg ((((Fpoly.coeff k').coeff j').coeff (i' + 1)) * ((i' + 1 : ℕ) : Polynomial F)) =
          alg (((Fpoly.coeff k').coeff j').coeff (i' + 1)) * ((i' + 1 : ℕ) : RatFunc F) := by simp
      cases k' with
      | zero => simpa [h1] using congrArg alg h
      | succ k'' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative,
            coe_mapRingHom, coeff_map] at h ⊢
          rw [show ((j' : Polynomial (Polynomial F)) + 1) = C ((j' : Polynomial F) + 1) by simp, coeff_mul_C] at h
          rw [show ((j' : Polynomial (RatFunc F)) + 1) = C ((j' : RatFunc F) + 1) by simp, coeff_mul_C]
          have := congrArg alg h; simpa using this
    · rw [natDegree_le_iff_coeff_eq_zero]; intro k' hk'
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hFkerD.2.1 hk'), map_zero]
    · rw [wdeg_le_iff]; intro k' j' i' hnz
      simp only [liftC, coe_mapRingHom, coeff_map] at hnz
      have hnz' : ((Fpoly.coeff k').coeff j').coeff i' ≠ 0 := fun h0 => hnz (by rw [h0, map_zero])
      exact (wdeg_le_iff wY W_F Fpoly).mp hFkerD.2.2 k' j' i' hnz'
  let toPolyRat (W' s' : ℕ) (c : KerDIdx wY W' s' → RatFunc F) : ContactPoly (RatFunc F) :=
    ∑ e : KerDIdx wY W' s', cC (c e) * kerDBasisPoly e.1
  let coordRat (Q : ContactPoly (RatFunc F)) (e : KerDIdx wY W s) : RatFunc F :=
    if e.1.2.1 = 0 then ((Q.coeff e.1.1).coeff (2 * e.1.2.2.1)).coeff (2 * e.1.2.2.2)
    else ((Q.coeff e.1.1).coeff (2 * e.1.2.2.1 + 1)).coeff (2 * e.1.2.2.2)
  let T : (KerDIdx wY (W - W_F) (s - d) → RatFunc F) →ₗ[RatFunc F] (KerDIdx wY W s → RatFunc F) :=
    { toFun := fun c => coordRat (liftC Fpoly * toPolyRat (W - W_F) (s - d) c)
      map_add' := fun c1 c2 => by
        funext e
        have hadd : toPolyRat (W - W_F) (s - d) (c1 + c2) =
            toPolyRat (W - W_F) (s - d) c1 + toPolyRat (W - W_F) (s - d) c2 := by
          dsimp [toPolyRat]; rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro e' _; simp [cC, add_mul]
        dsimp [coordRat]; rw [hadd, mul_add]; split_ifs <;> simp
      map_smul' := fun a c => by
        funext e
        have hsmul : toPolyRat (W - W_F) (s - d) (a • c) =
            cC a * toPolyRat (W - W_F) (s - d) c := by
          dsimp [toPolyRat]; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro e' _; simp [cC, mul_assoc]
        have hmul : ∀ P : ContactPoly (RatFunc F), liftC Fpoly * (cC a * P) = cC a * (liftC Fpoly * P) := fun P => by ring
        dsimp [coordRat]; rw [hsmul, hmul]; split_ifs <;> simp [cC, coeff_C_mul] }
  have hT_reconstruct : ∀ c, toPolyRat W s (T c) = liftC Fpoly * toPolyRat (W - W_F) (s - d) c := by
    intro c
    let Q := liftC Fpoly * toPolyRat (W - W_F) (s - d) c
    have hQ1 : contactDeriv (toPolyRat (W - W_F) (s - d) c) = 0 ∧
        (toPolyRat (W - W_F) (s - d) c).natDegree ≤ s - d ∧
        wdeg wY (toPolyRat (W - W_F) (s - d) c) ≤ W - W_F := by
      refine (mem_kerD_iff_exists_unique_coords hwY _).mpr ⟨c, rfl, ?_⟩
      intro c' hc'; funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY (W - W_F) (s - d) (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [he] using h.symm
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h.symm
    have hQmem : contactDeriv Q = 0 ∧ Q.natDegree ≤ s ∧ wdeg wY Q ≤ W := by
      refine ⟨?_, ?_, ?_⟩
      · dsimp [Q]; rw [contactDeriv_mul, hF_rat_mem.1, hQ1.1, zero_mul, mul_zero, add_zero]
      · dsimp [Q]; exact natDegree_mul_le.trans (by omega)
      · by_cases h0 : toPolyRat (W - W_F) (s - d) c = 0
        · simp [Q, h0, wdeg]
        · dsimp [Q]; rw [wdeg_mul wY hFne_rat h0]; omega
    obtain ⟨c', hQc', _⟩ := (mem_kerD_iff_exists_unique_coords hwY Q).mp hQmem
    have hc'eq : c' = T c := by
      funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hQc'
        rw [coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [T, coordRat, Q, he] using h.symm
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hQc'
        rw [coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [T, coordRat, Q, h1, h2, h3, h4, he] using h.symm
    rw [← hc'eq]; exact hQc'.symm
  have hT_inj : Function.Injective T := by
    intro c1 c2 h
    have hprod : liftC Fpoly * toPolyRat (W - W_F) (s - d) c1 = liftC Fpoly * toPolyRat (W - W_F) (s - d) c2 := by
      rw [← hT_reconstruct, ← hT_reconstruct, h]
    have hpoly := mul_left_cancel₀ hFne_rat hprod
    funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY (W - W_F) (s - d) (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h' := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hpoly
      dsimp only [toPolyRat] at h'; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h'
      simpa [he] using h'
    · have h' := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hpoly
      dsimp only [toPolyRat] at h'; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h'
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h'
  obtain ⟨I0, hI0_card, hI0_disj⟩ := exists_complement_subset_of_injective T hT_inj
  -- Weighted variable capacities: deg_Z(g_e) ≤ D_Z' - dy * (2*b + r)!
  let cap (e : KerDIdx wY W s) : ℕ := D_Z' + 1 - dy * (2 * e.1.2.2.1 + e.1.2.1)
  have hbr_le : ∀ e : KerDIdx wY W s, dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ dy * (W / wY) := by
    intro ⟨⟨k', r, b, a⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he
    have h1 : (2 * b + r) * wY ≤ W := by nlinarith [hmem.2.2]
    exact Nat.mul_le_mul_left dy ((Nat.le_div_iff_mul_le (by omega : 0 < wY)).mpr h1)
  let I_G := Σ e : { e : KerDIdx wY W s // e ∈ I0 }, Fin (cap e.1)
  let I_V := (Σ i : ι, LocalBasisIdx (m - k i) (s - d)) × Fin (D_Z' - D_ZF + 1)
  let I_all := I_G ⊕ I_V
  let J_all := ι × LocalBasisIdx m s × Fin (D_Z' + 1)
  let gPoly (u : I_all → F) (e : KerDIdx wY W s) : Polynomial F :=
    if h : e ∈ I0 then ∑ t : Fin (cap e), C (u (Sum.inl ⟨⟨e, h⟩, t⟩)) * X ^ t.val else 0
  let vPoly (u : I_all → F) (i : ι) (b : LocalBasisIdx (m - k i) (s - d)) : Polynomial F :=
    ∑ t : Fin (D_Z' - D_ZF + 1), C (u (Sum.inr (⟨i, b⟩, t))) * X ^ t.val
  let L : (I_all → F) →ₗ[F] (J_all → F) :=
    { toFun := fun u j =>
        let (i, idx, t) := j
        ((∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
         (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx)).coeff t.val
      map_add' := by
        intro u1 u2; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (u1 + u2) e = gPoly u1 e + gPoly u2 e := fun e => by
          dsimp [gPoly]; split_ifs <;> [simp [add_mul, Finset.sum_add_distrib]; simp]
        have hv : ∀ b, vPoly (u1 + u2) i b = vPoly u1 i b + vPoly u2 i b := fun b => by
          dsimp [vPoly]; simp [add_mul, Finset.sum_add_distrib]
        simp only [hg, hv, add_mul, Finset.sum_add_distrib, coeff_sub, coeff_add, Pi.add_apply]; ring
      map_smul' := by
        intro a u; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (a • u) e = C a * gPoly u e := fun e => by
          dsimp [gPoly]; split_ifs <;> [simp [Finset.mul_sum, mul_assoc]; simp]
        have hv : ∀ b, vPoly (a • u) i b = C a * vPoly u i b := fun b => by
          dsimp [vPoly]; simp [Finset.mul_sum, mul_assoc]
        simp only [hg, hv, mul_assoc, ← Finset.mul_sum, ← mul_sub, coeff_C_mul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] }
  have hcard : Fintype.card J_all < Fintype.card I_all := by
    have hI0_eq : I0.card = varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d) := by
      rw [card_kerDIdx wY W s (by omega), card_kerDIdx wY (W - W_F) (s - d) (by omega)] at hI0_card
      omega
    have hIG_ge : I0.card * (D_Z' + 1) ≤ Fintype.card I_G + dy * I0.card * (W / wY) := by
      have h1 : I0.card * (D_Z' + 1 - dy * (W / wY)) ≤ Fintype.card I_G := by
        simp only [I_G, Fintype.card_sigma, Fintype.card_fin]
        calc I0.card * (D_Z' + 1 - dy * (W / wY))
            = ∑ _e : { e : KerDIdx wY W s // e ∈ I0 }, (D_Z' + 1 - dy * (W / wY)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
          _ ≤ ∑ e : { e : KerDIdx wY W s // e ∈ I0 }, cap e.1 := by
                apply Finset.sum_le_sum; intro e _
                have := hbr_le e.1; dsimp [cap]; omega
      have hsub : I0.card * (D_Z' + 1) - dy * I0.card * (W / wY) = I0.card * (D_Z' + 1 - dy * (W / wY)) := by
        rw [Nat.mul_sub_left_distrib]; congr 1; ring
      have hle_mul : dy * I0.card * (W / wY) ≤ I0.card * (D_Z' + 1) := by
        calc dy * I0.card * (W / wY) = I0.card * (dy * (W / wY)) := by ring
          _ ≤ I0.card * (D_Z' + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    simp only [I_all, I_V, J_all, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_fin, card_localBasisIdx]
    rw [hI0_eq] at hIG_ge
    have hJ : Fintype.card ι * (rankKerD m s * (D_Z' + 1)) = Fintype.card ι * rankKerD m s * (D_Z' + 1) := by ring
    omega
  obtain ⟨u, hu_ne, hLu⟩ := exists_ne_zero_ker_linearMap L hcard
  let G : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (gPoly u e) * kerDBasisPoly e.1
  have hg_wtd : ∀ e : KerDIdx wY W s, (gPoly u e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D_Z' := by
    intro e
    have hle := (hbr_le e).trans hD_ge
    have hdeg : (gPoly u e).natDegree ≤ D_Z' - dy * (2 * e.1.2.2.1 + e.1.2.1) := by
      dsimp [gPoly]; split_ifs
      · refine (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ => ?_)
        have ht := t.isLt; dsimp [cap] at ht
        exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · simp
    omega
  have hf_wtd_ne := coord_wYZ_le_of_wYZ_ne (by omega) f_coord hf_wYZ
  have hlocal_van : ∀ i : ι,
      twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
    intro i
    have hNF_zero : ∀ idx : LocalBasisIdx m s,
        (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
        (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) = 0 := by
      intro idx
      have hdeg1 : (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx).natDegree ≤ D_Z' := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => natDegree_mul_le.trans ?_)
        have h1 := hg_wtd e
        have h2 := natDegree_kerDLocalNF_le_exact hwY (x i) (y i) (hy i) e idx
        omega
      have hdeg2 : (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx).natDegree ≤ D_Z' := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b _ => natDegree_mul_le.trans ?_)
        have hv : (vPoly u i b).natDegree ≤ D_Z' - D_ZF :=
          (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
            (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp t.isLt))
        have hnf := natDegree_prodLocalNF_le_of_wYZ hwY (x i) (y i) (hy i) f_coord hf_wtd_ne b.1 idx
        omega
      have hdeg := (natDegree_sub_le _ _).trans (max_le hdeg1 hdeg2)
      ext t; rw [coeff_zero]
      by_cases ht : t < D_Z' + 1
      · exact congrFun hLu (i, idx, ⟨t, ht⟩)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have h1 : twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
          localBasisElem idx.1) m := by
      have hrew : (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
            localBasisElem idx.1 =
          ∑ e : KerDIdx wY W s, locC (gPoly u e) *
            (kerDLocalPoly (C (x i)) (y i) e.1 -
              ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro e _
        have hms : ∀ a b c : LocalPoly (Polynomial F), a * (b - c) = a * b - a * c := fun a b c =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]; congr 1
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W s (by omega) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF m s (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have h2 : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) m := by
      have hrew : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
          (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
            vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 =
          ∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) *
            ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) * localBasisElem b.1 -
              ∑ idx : LocalBasisIdx m s, locC (prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) := by
        have h2a : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d),
              (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
              (locC (vPoly u i b) * localBasisElem b.1) := Finset.mul_sum _ _ _
        have h2b : (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
              vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d), ∑ idx : LocalBasisIdx m s,
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
          trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k i) (s - d),
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1
          · apply Finset.sum_congr rfl; intro idx _; unfold locC; simp only [map_sum, Finset.sum_mul]
          · exact Finset.sum_comm
        rw [h2a, h2b, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro b _
        have hms : ∀ a b' c : LocalPoly (Polynomial F), a * (b' - c) = a * b' - a * c := fun a b' c =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]
        refine congrArg₂ (· - ·) (by rw [← mul_assoc, mul_comm _ (locC (vPoly u i b)), mul_assoc]) ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        unfold locC; simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro b _
      have hb := ((mem_localBasisFinset_iff (m - k i) (s - d) _ _ _ _).mp b.2).1
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_prodLocal_sub_NF (by omega) hd (C (x i)) (y i) f_coord b.1 hb)
    have hNF_eq : (∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
        gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) =
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
      apply Finset.sum_congr rfl; intro idx _; rw [sub_eq_zero.mp (hNF_zero idx)]
    have hcomb := twOrdGE_sub h1 h2
    rwa [hNF_eq, sub_sub_sub_cancel_right] at hcomb
  have hGne : G ≠ 0 := by
    intro hG0
    have hg0 : ∀ e : KerDIdx wY W s, gPoly u e = 0 := by
      intro ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have hv0 : ∀ i : ι, ∀ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b = 0 := by
      intro i
      by_cases hkm : k i < m
      · have hloc := hlocal_van i
        simp only [hg0, locC, map_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hloc
        have hneg : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
          intro p q hpq; have := hloc p q hpq
          unfold twCoeff at this ⊢; rw [coeff_sub, coeff_sub, coeff_zero, coeff_zero] at this
          exact (sub_eq_zero.mp this).symm
        have hVvan : twOrdGE (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) (m - k i) := by
          by_contra hnot
          have hSpec := (hk_exact i).2 hkm
          have hfail := not_twOrdGE_mul_of_exact_ord hSpec.1 hSpec.2 hnot
          rw [Nat.add_sub_cancel' (le_of_lt hkm)] at hfail
          exact hfail hneg
        exact localBasis_linearIndependent_mod (m - k i) (s - d) (vPoly u i) hVvan
      · intro b; exfalso
        have hle := (hk_exact i).1
        have h0 : m - k i = 0 := by omega
        have hlt := ((mem_localBasisFinset_iff (m - k i) (s - d) _ _ _ _).mp b.2).2.1
        omega
    apply hu_ne; funext x'
    rcases x' with ⟨⟨e, he⟩, t⟩ | ⟨⟨i, b⟩, t⟩
    · have hc := hg0 e; dsimp only [gPoly] at hc; rw [dif_pos he] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hc := hv0 i b; dsimp only [vPoly] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hGmem : contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W := by
    refine (mem_kerD_iff_exists_unique_coords hwY G).mpr ⟨gPoly u, rfl, ?_⟩
    intro c' hc'; funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  have hwG : wYZ dy G ≤ D_Z' := wYZ_sum_kerDBasisPoly_le (by omega) (gPoly u) (fun e _ => hg_wtd e)
  refine ⟨G, hGne, hGmem.1, hGmem.2.1, hGmem.2.2, hwG, natDegree_Z_le_of_wYZ hwG, ?_, ?_, ⟨gPoly u, vPoly u, rfl, hlocal_van⟩⟩
  · -- F ∤ G over RatFunc F
    rintro ⟨Q', hQ'0⟩
    have hQ' : liftC G = liftC Fpoly * Q' := hQ'0
    have hGne_rat : liftC G ≠ 0 := by
      intro h0; apply hGne
      refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
      have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
      exact (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by simp only [coeff_zero, map_zero]; exact h)
    have hQ'ne : Q' ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ'; exact hGne_rat hQ'
    have hG_rat_mem : contactDeriv (liftC G) = 0 ∧ (liftC G).natDegree ≤ s ∧ wdeg wY (liftC G) ≤ W := by
      refine ⟨?_, ?_, ?_⟩
      · refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
        have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff j').coeff i') hGmem.1
        rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative] at h ⊢
        simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h ⊢
        cases k' with
        | zero => simpa using congrArg alg h
        | succ k'' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative,
              coe_mapRingHom, coeff_map] at h ⊢
            rw [show ((j' : Polynomial (Polynomial F)) + 1) = C ((j' : Polynomial F) + 1) by simp, coeff_mul_C] at h
            rw [show ((j' : Polynomial (RatFunc F)) + 1) = C ((j' : RatFunc F) + 1) by simp, coeff_mul_C]
            have := congrArg alg h; simpa using this
      · rw [natDegree_le_iff_coeff_eq_zero]; intro k' hk'
        simp only [liftC, coe_mapRingHom, coeff_map, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hGmem.2.1 hk'), map_zero]
      · rw [wdeg_le_iff]; intro k' j' i' hnz
        simp only [liftC, coe_mapRingHom, coeff_map] at hnz
        have hnz' : ((G.coeff k').coeff j').coeff i' ≠ 0 := fun h0 => hnz (by rw [h0, map_zero])
        exact (wdeg_le_iff wY W G).mp hGmem.2.2 k' j' i' hnz'
    have hF_rat_deg : (liftC Fpoly).natDegree = d := by
      have hinj := IsFractionRing.injective (Polynomial F) (RatFunc F)
      have hne_c : ∀ k', (liftC Fpoly).coeff k' ≠ 0 ↔ Fpoly.coeff k' ≠ 0 := by
        intro k'; simp only [liftC, coe_mapRingHom, coeff_map, ne_eq]
        constructor
        · intro h h0; apply h; rw [h0, Polynomial.map_zero]
        · intro h h0; apply h
          refine Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
          have := congrArg (fun p : BiPoly (RatFunc F) => (p.coeff j').coeff i') h0
          simp only [coe_mapRingHom, coeff_map, coeff_zero] at this
          exact hinj (by simp only [coeff_zero, map_zero]; exact this)
      apply le_antisymm hF_rat_mem.2.1
      by_cases hd0 : d = 0
      · omega
      · apply le_natDegree_of_ne_zero; rw [hne_c, ← hFdeg]; exact leadingCoeff_ne_zero.mpr hFne
    have hF_rat_wdeg : wdeg wY (liftC Fpoly) = W_F := by
      have hinj := IsFractionRing.injective (Polynomial F) (RatFunc F)
      apply le_antisymm hF_rat_mem.2.2
      rw [← hFwdeg, wdeg_le_iff]; intro k' j' i' hnz
      have hnz' : (((liftC Fpoly).coeff k').coeff j').coeff i' ≠ 0 := by
        simp only [liftC, coe_mapRingHom, coeff_map]; intro h0; exact hnz (hinj (by rw [map_zero]; exact h0))
      exact (wdeg_le_iff wY (wdeg wY (liftC Fpoly)) (liftC Fpoly)).mp le_rfl k' j' i' hnz'
    have hQ'mem : contactDeriv Q' = 0 ∧ Q'.natDegree ≤ s - d ∧ wdeg wY Q' ≤ W - W_F := by
      refine ⟨?_, ?_, ?_⟩
      · have hD := congrArg contactDeriv hQ'
        rw [hG_rat_mem.1, contactDeriv_mul, hF_rat_mem.1, zero_mul, zero_add] at hD
        exact (mul_eq_zero.mp hD.symm).resolve_left hFne_rat
      · have hdeg_mul := natDegree_mul hFne_rat hQ'ne; rw [← hQ', hF_rat_deg] at hdeg_mul; omega
      · have hw_mul := wdeg_mul wY hFne_rat hQ'ne; rw [← hQ', hF_rat_wdeg] at hw_mul; omega
    obtain ⟨c1, hc1, _⟩ := (mem_kerD_iff_exists_unique_coords hwY Q').mp hQ'mem
    have hc1' : Q' = toPolyRat (W - W_F) (s - d) c1 := hc1
    have hG_eq : toPolyRat W s (fun e => alg (gPoly u e)) = liftC G := by
      dsimp only [toPolyRat, G, liftC]; rw [map_sum]
      apply Finset.sum_congr rfl; intro e _; rw [map_mul]; congr 1
      · unfold cC; simp [alg, coe_mapRingHom]
      · unfold kerDBasisPoly cR cY cX; simp [map_mul, map_pow, map_add, coe_mapRingHom]
    have hT_eq : T c1 = fun e => alg (gPoly u e) := by
      have hprod : toPolyRat W s (T c1) = toPolyRat W s (fun e => alg (gPoly u e)) := by
        rw [hT_reconstruct, ← hc1', ← hQ', hG_eq]
      funext ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s (by omega) k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hprod
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hprod
        dsimp only [toPolyRat] at h; rw [coeff_sum_kerDBasisPoly (by omega), coeff_sum_kerDBasisPoly (by omega)] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have hv_zero : (fun e => alg (gPoly u e)) = 0 :=
      hI0_disj (fun e => alg (gPoly u e)) (fun e he => by dsimp only [gPoly]; rw [dif_neg he, map_zero]) ⟨c1, hT_eq⟩
    apply hGne_rat; rw [← hG_eq]; dsimp only [toPolyRat]
    apply Finset.sum_eq_zero; intro e _; rw [congrFun hv_zero e]; simp [cC]
  · -- Evaluation vanishing
    intro A hWlt z P hP Az hAz hagree hFvan
    by_contra hGvan
    let E := evalContact (evalZContact G z) P
    have hdvd_each : ∀ i ∈ Az, (X - C (x i)) ^ (2 * m) ∣ E := by
      intro i hi
      have hloc_z := twOrdGE_evalZLocal (hlocal_van i) z
      have hdvd := pow_two_mul_dvd_evalLocal_of_twOrdGE (x i) ((y i).eval z) P (hagree i hi) hloc_z
      have hEv : evalLocal (x i) ((y i).eval z) P
          (evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z) = E := by
        have hsub : evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z =
            evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z -
            evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z *
            evalZLocal (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) z := by
          rw [← evalZLocal_mul]
          exact eq_sub_of_add_eq (G := LocalPoly F)
            (by rw [← evalZLocal_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hsub, map_sub, map_mul]
        have hEvG : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z) = E := by
          dsimp only [E, G]
          rw [show evalZLocal (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZLocal (locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z
                from by unfold evalZLocal; simp [Polynomial.map_sum],
              show evalZContact (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZContact (cC (gPoly u e) * kerDBasisPoly e.1) z
                from by unfold evalZContact; simp [Polynomial.map_sum],
              map_sum, evalContact_sum]
          apply Finset.sum_congr rfl; intro e _
          rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
            evalLocal_kerDLocalPoly,
            show evalZContact (_ * _) z = evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z
              from by unfold evalZContact; simp [Polynomial.map_mul],
            evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
        have hEvF : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z) = 0 := by
          rw [show evalZLocal (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                evalZLocal (locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z
                from by unfold evalZLocal; simp [Polynomial.map_sum], map_sum]
          trans evalContact (evalZContact Fpoly z) P
          · dsimp only [Fpoly]
            rw [show evalZContact (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                  evalZContact (cC (f_coord e1) * kerDBasisPoly e1.1) z
                  from by unfold evalZContact; simp [Polynomial.map_sum], evalContact_sum]
            apply Finset.sum_congr rfl; intro e1 _
            rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
              evalLocal_kerDLocalPoly,
              show evalZContact (_ * _) z = evalZContact (cC (f_coord e1)) z * evalZContact (kerDBasisPoly e1.1) z
                from by unfold evalZContact; simp [Polynomial.map_mul],
              evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
          · exact hFvan
        rw [hEvG, hEvF, zero_mul, sub_zero]
      rwa [hEv] at hdvd
    have hdvd_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m)) ∣ E := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        apply IsCoprime.pow
        have hne_x : x i ≠ x j := fun h => hij (x.injective h)
        refine ⟨C (x j - x i)⁻¹, -C (x j - x i)⁻¹, ?_⟩
        have hne' : x j - x i ≠ 0 := sub_ne_zero.mpr hne_x.symm
        calc C (x j - x i)⁻¹ * (X - C (x i)) + -C (x j - x i)⁻¹ * (X - C (x j))
            = C (x j - x i)⁻¹ * C (x j - x i) := by rw [map_sub]; ring
          _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne', map_one]
      · exact hdvd_each
    have hdeg_prod : (∏ i ∈ Az, (X - C (x i)) ^ (2 * m)).natDegree = Az.card * (2 * m) := by
      rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
      simp [natDegree_pow, natDegree_X_sub_C]
    have hle_deg : Az.card * (2 * m) ≤ E.natDegree := by
      rw [← hdeg_prod]; exact natDegree_le_of_dvd hdvd_prod hGvan
    have hE_deg : E.natDegree ≤ W := by
      apply natDegree_evalContact_le wY W hwY _ P hP
      rw [wdeg_le_iff]; intro k' j' i' hnz
      have hmem : evalZContact G z = ∑ e : KerDIdx wY W s, cC ((gPoly u e).eval z) * kerDBasisPoly e.1 := by
        dsimp only [G]; unfold evalZContact; simp only [Polynomial.map_sum, Polynomial.map_mul]
        apply Finset.sum_congr rfl; intro e _
        change evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z = _
        rw [evalZContact_cC, evalZContact_kerDBasisPoly]
      rw [hmem, coeff_sum_kerDBasisPoly (by omega)] at hnz
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, and_self, ↓reduceIte] at hnz
        split_ifs at hnz with hm1
        · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm1).2.2
          have hj2 : 2 * (j' / 2) = j' := by omega
          have hi2 : 2 * (i' / 2) = i' := by omega
          nlinarith only [hw, hj2, hi2]
        · exact absurd rfl hnz
      · simp only [h00, ↓reduceIte] at hnz
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, and_self, ↓reduceIte] at hnz
          split_ifs at hnz with hm2
          · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm2).2.2
            have hj2 : 2 * (j' / 2) + 1 = j' := by omega
            have hi2 : 2 * (i' / 2) = i' := by omega
            nlinarith only [hw, hj2, hi2]
          · exact absurd rfl hnz
        · simp only [h10, ↓reduceIte] at hnz
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, and_self, ↓reduceIte] at hnz
            split_ifs at hnz with hm3
            · have hw := ((mem_kerDIdxFinset_iff wY W s (by omega) _ _ _ _).mp hm3).2.2
              have hj2 : 2 * (j' / 2) = j' := by omega
              have hi2 : 2 * (i' / 2) + 1 = i' := by omega
              have hk1 : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY, h01.2.2]; ring
              nlinarith only [hw, hj2, hi2, hk1]
            · exact absurd rfl hnz
          · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz
    nlinarith only [hWlt, hAz, hle_deg, hE_deg]

end B6401QuotInterp
end ProximityPrize.SubmissionBinaryLower

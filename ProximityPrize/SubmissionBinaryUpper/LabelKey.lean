/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.SubspacePoly

/-!
# A 35-bit key for the three top coefficients of a label polynomial

The coset labels are `y h = ∑ᵢ bitᵢ(h) bᵢ` for seven basis labels `bᵢ`.  For a
label set `U` write `nᵢ = #{h ∈ U | bitᵢ h}` and `nᵢⱼ = #{h ∈ U | bitᵢ h ∧ bitⱼ h}`.
In characteristic two

* `e₁ = ∑ nᵢ bᵢ`,
* `e₂ = ∑ C(nᵢ, 2) bᵢ² + ∑_{j<i} (nᵢ nⱼ + nᵢⱼ) bᵢ bⱼ`,
* `p₃ = ∑ y³ = ∑_{i,j} nᵢⱼ bᵢ bⱼ²`,
* `e₃ = p₃ + e₁ e₂ + e₁³` (Newton's identity, which in characteristic two
  needs no division).

So `(e₁, e₂, e₃)` only depends on `nᵢ mod 4` and on `nᵢⱼ mod 2` for `j < i`:
`14 + 21 = 35` bits.
-/

namespace ProximityPrize.SubmissionBinaryUpper.LabelKey

open Polynomial
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly

/-- The `i`-th bit of a label, as a natural number. -/
def bit (i h : ℕ) : ℕ := if h.testBit i then 1 else 0

theorem bit_le_one (i h : ℕ) : bit i h ≤ 1 := by
  unfold bit; split_ifs <;> norm_num

theorem bit_mul_self (i h : ℕ) : bit i h * bit i h = bit i h := by
  unfold bit; split_ifs <;> norm_num

theorem cast_bit_sq (i h : ℕ) : ((bit i h : ℕ) : K) ^ 2 = (bit i h : K) := by
  rw [sq, ← Nat.cast_mul, bit_mul_self]

theorem y_bits (n : ℕ) : ∀ h < 2 ^ n, y h = ∑ i ∈ Finset.range n, (bit i h : K) * b i := by
  induction n with
  | zero =>
      intro h hh
      have : h = 0 := by simpa using hh
      subst this
      simp [y_zero]
  | succ n ih =>
      intro h hh
      rw [Finset.sum_range_succ]
      by_cases hlow : h < 2 ^ n
      · rw [ih h hlow]
        simp [bit, Nat.testBit_lt_two_pow hlow]
      · obtain ⟨h', hh', rfl⟩ : ∃ h', h' < 2 ^ n ∧ h = 2 ^ n * 1 + h' :=
          ⟨h - 2 ^ n, by rw [pow_succ] at hh; omega, by omega⟩
        have hbits : ∀ i < n, bit i (2 ^ n * 1 + h') = bit i h' := by
          intro i hi
          unfold bit
          rw [Nat.testBit_two_pow_mul_add 1 hh' i, if_pos hi]
        have htop : bit n (2 ^ n * 1 + h') = 1 := by
          unfold bit
          rw [Nat.testBit_two_pow_mul_add 1 hh' n, if_neg (lt_irrefl n)]
          simp
        conv_lhs => rw [two_pow_mul_add_eq_xor hh', y_xor, Nat.mul_one, ih _ hh']
        rw [htop]
        have hsum : ∑ i ∈ Finset.range n, (bit i (2 ^ n * 1 + h') : K) * b i =
            ∑ i ∈ Finset.range n, (bit i h' : K) * b i :=
          Finset.sum_congr rfl (fun i hi => by rw [hbits i (Finset.mem_range.mp hi)])
        rw [hsum]
        simp [b, add_comm]

theorem y_bits7 {h : ℕ} (hh : h < 128) : y h = ∑ i ∈ Finset.range 7, (bit i h : K) * b i :=
  y_bits 7 h (by norm_num; exact hh)

/-! ## Counts -/

def cnt (i : ℕ) (U : Finset ℕ) : ℕ := ∑ h ∈ U, bit i h

def cnt2 (i j : ℕ) (U : Finset ℕ) : ℕ := ∑ h ∈ U, bit i h * bit j h

theorem cnt_insert {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) (i : ℕ) :
    cnt i (insert a U) = cnt i U + bit i a := by
  rw [cnt, cnt, Finset.sum_insert ha, add_comm]

theorem cnt2_insert {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) (i j : ℕ) :
    cnt2 i j (insert a U) = cnt2 i j U + bit i a * bit j a := by
  rw [cnt2, cnt2, Finset.sum_insert ha, add_comm]

theorem cnt2_self (i : ℕ) (U : Finset ℕ) : cnt2 i i U = cnt i U := by
  simp only [cnt2, cnt, bit_mul_self]

theorem cnt2_comm (i j : ℕ) (U : Finset ℕ) : cnt2 i j U = cnt2 j i U := by
  simp only [cnt2, Nat.mul_comm]

/-! ## Symmetric functions of the labels -/

noncomputable def ys (U : Finset ℕ) : Multiset K := U.val.map y

theorem ys_insert {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) : ys (insert a U) = y a ::ₘ ys U := by
  rw [ys, ys, Finset.insert_val_of_notMem ha, Multiset.map_cons]

noncomputable def e (k : ℕ) (U : Finset ℕ) : K := (ys U).esymm k

theorem e_zero (U : Finset ℕ) : e 0 U = 1 := Multiset.esymm_zero _

theorem e_insert {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) (k : ℕ) :
    e (k + 1) (insert a U) = e (k + 1) U + y a * e k U := by
  rw [e, e, e, ys_insert ha, esymm_cons]

theorem e_empty (k : ℕ) : e (k + 1) ∅ = 0 := by
  rw [e, Multiset.esymm_of_card_lt]
  simp [ys]

noncomputable def p3 (U : Finset ℕ) : K := ∑ h ∈ U, y h ^ 3

/-- Newton's identity for `e₃` in characteristic two. -/
theorem newton3 (U : Finset ℕ) : e 3 U = p3 U + e 1 U * e 2 U + e 1 U ^ 3 := by
  induction U using Finset.induction_on with
  | empty => simp [e_empty, p3]
  | insert a U ha ih =>
      rw [e_insert ha 2, e_insert ha 1, e_insert ha 0, e_zero, p3, Finset.sum_insert ha,
        ← p3, ih]
      linear_combination
        (-(y a ^ 3 + 2 * e 1 U ^ 2 * y a + 2 * e 1 U * y a ^ 2)) * two_eq_zero

/-! ## Closed forms -/

noncomputable def E1 (U : Finset ℕ) : K := ∑ i ∈ Finset.range 7, (cnt i U : K) * b i

noncomputable def E2 (U : Finset ℕ) : K :=
  ∑ i ∈ Finset.range 7, ((cnt i U).choose 2 : K) * b i ^ 2 +
    ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range i,
      ((cnt i U * cnt j U + cnt2 i j U : ℕ) : K) * (b i * b j)

noncomputable def P3 (U : Finset ℕ) : K :=
  ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7, (cnt2 i j U : K) * (b i * b j ^ 2)

/-- Splitting a square sum into its diagonal and the strictly lower triangle. -/
theorem sum_square_split (f : ℕ → ℕ → K) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f i j =
      ∑ i ∈ Finset.range n, f i i +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (f i j + f j i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      rw [ih]
      simp only [Finset.sum_add_distrib]
      ring

theorem labels_lt {U : Finset ℕ} (hU : U ⊆ Finset.range 128) {h : ℕ} (hh : h ∈ U) : h < 128 := by
  simpa using hU hh

theorem e1_eq {U : Finset ℕ} (hU : U ⊆ Finset.range 128) : e 1 U = E1 U := by
  induction U using Finset.induction_on with
  | empty => simp [e_empty, E1, cnt]
  | insert a U ha ih =>
      have hU' : U ⊆ Finset.range 128 := (Finset.subset_insert a U).trans hU
      have haR : a < 128 := labels_lt hU (Finset.mem_insert_self a U)
      rw [e_insert ha 0, e_zero, mul_one, ih hU', y_bits7 haR, E1, E1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [cnt_insert ha]
      push_cast
      ring

theorem choose_two_add_bit (n i a : ℕ) :
    ((n + bit i a).choose 2 : K) = (n.choose 2 : K) + (bit i a : K) * n := by
  unfold bit
  split_ifs
  · rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    ring
  · simp

theorem e2_eq {U : Finset ℕ} (hU : U ⊆ Finset.range 128) : e 2 U = E2 U := by
  induction U using Finset.induction_on with
  | empty => simp [e_empty, E2, cnt, cnt2]
  | insert a U ha ih =>
      have hU' : U ⊆ Finset.range 128 := (Finset.subset_insert a U).trans hU
      have haR : a < 128 := labels_lt hU (Finset.mem_insert_self a U)
      rw [e_insert ha 1, ih hU', e1_eq hU', y_bits7 haR, E1, Finset.sum_mul_sum,
        sum_square_split]
      simp only [E2, cnt_insert ha, cnt2_insert ha, choose_two_add_bit]
      have hdiag : ∀ i ∈ Finset.range 7,
          ((cnt i U).choose 2 + (bit i a : K) * (cnt i U) : K) * b i ^ 2 =
            ((cnt i U).choose 2 : K) * b i ^ 2 + (bit i a : K) * b i * ((cnt i U : K) * b i) := by
        intro i _; ring
      have hoff : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range i,
          (((cnt i U + bit i a) * (cnt j U + bit j a) + (cnt2 i j U + bit i a * bit j a) : ℕ) : K) *
              (b i * b j) =
            ((cnt i U * cnt j U + cnt2 i j U : ℕ) : K) * (b i * b j) +
              ((bit i a : K) * b i * ((cnt j U : K) * b j) +
                (bit j a : K) * b j * ((cnt i U : K) * b i)) := by
        intro i _ j _
        push_cast
        linear_combination ((bit i a : K) * (bit j a : K) * (b i * b j)) * two_eq_zero
      rw [Finset.sum_congr rfl hdiag,
        Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (hoff i hi))]
      simp only [Finset.sum_add_distrib]
      ring

theorem y_sq_bits {h : ℕ} (hh : h < 128) :
    y h ^ 2 = ∑ j ∈ Finset.range 7, (bit j h : K) * b j ^ 2 := by
  rw [y_bits7 hh, sum_pow_char]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_pow, cast_bit_sq]

theorem y_cube_bits {h : ℕ} (hh : h < 128) :
    y h ^ 3 = ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
      ((bit i h * bit j h : ℕ) : K) * (b i * b j ^ 2) := by
  rw [show y h ^ 3 = y h * y h ^ 2 by ring, y_sq_bits hh]
  conv_lhs => rw [y_bits7 hh]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  push_cast
  ring

theorem p3_eq {U : Finset ℕ} (hU : U ⊆ Finset.range 128) : p3 U = P3 U := by
  rw [p3, Finset.sum_congr rfl (fun h hh => y_cube_bits (labels_lt hU hh)), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, cnt2]
  push_cast
  rfl

/-! ## The key -/

/-- The 21 strictly lower-triangular index pairs `(i, j)`, `j < i < 7`. -/
def pairA : Fin 21 → ℕ := ![1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6]
def pairB : Fin 21 → ℕ := ![0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5]

set_option maxRecDepth 100000 in
theorem pair_surj : ∀ i < 7, ∀ j < i, ∃ r : Fin 21, pairA r = i ∧ pairB r = j := by
  decide

/-- The 35-bit key: `nᵢ mod 4` and the lower-triangular `nᵢⱼ mod 2`. -/
noncomputable def kappa (U : Finset ℕ) : (Fin 7 → ZMod 4) × (Fin 21 → ZMod 2) :=
  (fun i => ((cnt i.val U : ℕ) : ZMod 4), fun r => ((cnt2 (pairA r) (pairB r) U : ℕ) : ZMod 2))

theorem card_kappa_type : Fintype.card ((Fin 7 → ZMod 4) × (Fin 21 → ZMod 2)) = 2 ^ 35 := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

theorem cast_eq_of_modEq_two {m n : ℕ} (h : m ≡ n [MOD 2]) : (m : K) = (n : K) :=
  (CharP.natCast_eq_natCast K 2).mpr h

theorem choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem choose_two_add_four (k : ℕ) : (k + 4).choose 2 = k.choose 2 + 2 * (2 * k + 3) := by
  rw [show k + 4 = (k + 3) + 1 by rfl, choose_two_succ, show k + 3 = (k + 2) + 1 by rfl,
    choose_two_succ, show k + 2 = (k + 1) + 1 by rfl, choose_two_succ, choose_two_succ]
  ring

theorem choose_two_mod_four (k : ℕ) : k.choose 2 ≡ (k % 4).choose 2 [MOD 2] := by
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
      rcases Nat.lt_or_ge k 4 with hk | hk
      · rw [Nat.mod_eq_of_lt hk]
      · obtain ⟨l, rfl⟩ : ∃ l, k = l + 4 := ⟨k - 4, by omega⟩
        rw [choose_two_add_four, show (l + 4) % 4 = l % 4 by omega]
        refine Nat.ModEq.trans ?_ (ihk l (by omega))
        unfold Nat.ModEq
        omega

theorem choose_two_modEq {m n : ℕ} (h : m ≡ n [MOD 4]) : m.choose 2 ≡ n.choose 2 [MOD 2] := by
  have hmn : m % 4 = n % 4 := h
  refine (choose_two_mod_four m).trans ?_
  rw [hmn]
  exact (choose_two_mod_four n).symm

theorem mod2_of_mod4 {a c : ℕ} (h : a ≡ c [MOD 4]) : a ≡ c [MOD 2] :=
  Nat.ModEq.of_mul_left 2 (show a ≡ c [MOD 2 * 2] from h)

theorem kappa_cnt {U W : Finset ℕ} (hk : kappa U = kappa W) {i : ℕ} (hi : i < 7) :
    cnt i U ≡ cnt i W [MOD 4] := by
  have h := congrFun (congrArg Prod.fst hk) ⟨i, hi⟩
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

theorem kappa_cnt2 {U W : Finset ℕ} (hk : kappa U = kappa W) {i j : ℕ} (hi : i < 7) (hj : j < i) :
    cnt2 i j U ≡ cnt2 i j W [MOD 2] := by
  obtain ⟨r, hrA, hrB⟩ := pair_surj i hi j hj
  have h := congrFun (congrArg Prod.snd hk) r
  simp only [kappa, hrA, hrB] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

theorem kappa_cnt2_all {U W : Finset ℕ} (hk : kappa U = kappa W) {i j : ℕ}
    (hi : i < 7) (hj : j < 7) : cnt2 i j U ≡ cnt2 i j W [MOD 2] := by
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact kappa_cnt2 hk hi hlt
  · subst heq
    rw [cnt2_self, cnt2_self]
    exact mod2_of_mod4 (kappa_cnt hk hi)
  · rw [cnt2_comm, cnt2_comm i j W]
    exact kappa_cnt2 hk hj hgt

theorem E1_congr {U W : Finset ℕ} (hk : kappa U = kappa W) : E1 U = E1 W := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  rw [cast_eq_of_modEq_two (mod2_of_mod4 (kappa_cnt hk hi'))]

theorem E2_congr {U W : Finset ℕ} (hk : kappa U = kappa W) : E2 U = E2 W := by
  unfold E2
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [cast_eq_of_modEq_two (choose_two_modEq (kappa_cnt hk (Finset.mem_range.mp hi)))]
  · refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have h1 := mod2_of_mod4 (kappa_cnt hk hi')
    have h2 := mod2_of_mod4 (kappa_cnt hk (lt_trans hj' hi'))
    have h3 := kappa_cnt2 hk hi' hj'
    rw [cast_eq_of_modEq_two ((h1.mul h2).add h3)]

theorem P3_congr {U W : Finset ℕ} (hk : kappa U = kappa W) : P3 U = P3 W := by
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
  rw [cast_eq_of_modEq_two (kappa_cnt2_all hk (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))]

theorem e_congr {U W : Finset ℕ} (hU : U ⊆ Finset.range 128) (hW : W ⊆ Finset.range 128)
    (hk : kappa U = kappa W) :
    e 1 U = e 1 W ∧ e 2 U = e 2 W ∧ e 3 U = e 3 W := by
  have h1 : e 1 U = e 1 W := by rw [e1_eq hU, e1_eq hW, E1_congr hk]
  have h2 : e 2 U = e 2 W := by rw [e2_eq hU, e2_eq hW, E2_congr hk]
  refine ⟨h1, h2, ?_⟩
  rw [newton3, newton3, p3_eq hU, p3_eq hW, P3_congr hk, h1, h2]

end ProximityPrize.SubmissionBinaryUpper.LabelKey

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.FlatPoly

/-!
# A family of unions of four flats avoiding a fixed subspace

Write a domain index as `y + 2^18 (g + 2 t + 4 b)` with `y < 2^18` and bits
`g, t, b`.  A family member is the graph `g = G p y t b`: for each pair `(t, b)`
and each `y` exactly one `g`, so it has `2^20` points.  On every slice it is
one of four affine flats of size `2^18`, each a graph over `y`:

* `b = 0, t = 0`: `g = 1`;
* `b = 0, t = 1`: `g = l(y) + c`;
* `b = 1`: with `ε = t + m(y)`, `g = l₀(y) + ε D(y)`, so the two flats are
  `t = m(y) + ε`, `g = (l₀ + ε D)(y)`.

Normalising `D 0 = 1` and `m 0 = 0` makes the parameters readable from the set,
so the `2^71` parameters give `2^71` distinct sets.  Every member avoids the
subspace `W` of the first `2^17` words.  The product of the four flat locators
vanishes on the member and is `X^(2^20)` plus terms of degree at most
`2^20 - 2^17` (`FlatPoly`), which is the input of the pole pair of TR26-237,
Lemma 6.1.
-/

namespace ProximityPrize.SubmissionBinaryUpper.PoleFamily

set_option linter.constructorNameAsVariable false

attribute [local irreducible] SubspacePoly.nodeN FlatPoly.P SubspacePoly.L

open Polynomial
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open ProximityPrize.SubmissionBinaryUpper.FlatPoly

abbrev Idx := BinaryIRSProfile.Index

/-! ## Linear functionals on `y` -/

def fe (f : Fin 18 → ZMod 2) (i : ℕ) : ZMod 2 := if h : i < 18 then f ⟨i, h⟩ else 0

def lin (f : Fin 18 → ZMod 2) (z : ℕ) : ZMod 2 := ∑ i ∈ Finset.range 18, fe f i * bit z i

theorem lin_xor (f : Fin 18 → ZMod 2) (a c : ℕ) : lin f (a ^^^ c) = lin f a + lin f c := by
  simp only [lin, bit_xor, mul_add, Finset.sum_add_distrib]

theorem lin_add (f h : Fin 18 → ZMod 2) (z : ℕ) : lin (f + h) z = lin f z + lin h z := by
  simp only [lin, ← Finset.sum_add_distrib, ← add_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold fe
  split_ifs <;> simp

theorem lin_zero_fun (z : ℕ) : lin 0 z = 0 := by
  simp only [lin, fe]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

theorem lin_zero (f : Fin 18 → ZMod 2) : lin f 0 = 0 := by
  simp [lin, bit]

theorem bit_two_pow (k i : ℕ) : bit (2 ^ k) i = if i = k then 1 else 0 := by
  unfold bit
  rw [Nat.testBit_two_pow]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem lin_two_pow (f : Fin 18 → ZMod 2) (i : Fin 18) : lin f (2 ^ i.val) = f i := by
  rw [lin, Finset.sum_eq_single i.val]
  · simp [fe, bit_two_pow, i.isLt]
  · intro k _ hk
    simp [bit_two_pow, hk]
  · intro h
    exact absurd (Finset.mem_range.mpr i.isLt) h

theorem lin_one (f : Fin 18 → ZMod 2) : lin f 1 = f 0 := by
  simpa using lin_two_pow f 0

/-! ## Coordinates of domain words -/

irreducible_def idx (z : ℕ) (g t b : ZMod 2) : ℕ := z + 2 ^ 18 * (g.val + 2 * t.val + 4 * b.val)

theorem val_lt_two (a : ZMod 2) : a.val < 2 := ZMod.val_lt a

theorem idx_lt {z : ℕ} (hz : z < 2 ^ 18) (g t b : ZMod 2) : idx z g t b < 2 ^ 21 := by
  have := val_lt_two g
  have := val_lt_two t
  have := val_lt_two b
  rw [idx_def]
  omega

theorem bits_s (g t b : ZMod 2) :
    bit (g.val + 2 * t.val + 4 * b.val) 0 = g ∧ bit (g.val + 2 * t.val + 4 * b.val) 1 = t ∧
      bit (g.val + 2 * t.val + 4 * b.val) 2 = b := by
  revert g t b
  decide

theorem nodeN_idx {z : ℕ} (hz : z < 2 ^ 18) (g t b : ZMod 2) :
    nodeN (idx z g t b) =
      nodeN z + ψ g * nodeN (2 ^ 18) + ψ t * nodeN (2 ^ 19) + ψ b * nodeN (2 ^ 20) := by
  have hs : idx z g t b = 2 ^ 18 * (g.val + 2 * t.val + 4 * b.val) + z := by rw [idx_def]; ring
  have hlow : ∀ i ∈ Finset.range 18, bit (idx z g t b) i = bit z i := by
    intro i hi
    unfold bit
    rw [hs, Nat.testBit_two_pow_mul_add _ hz, if_pos (Finset.mem_range.mp hi)]
  have hhigh : ∀ r, bit (idx z g t b) (18 + r) = bit (g.val + 2 * t.val + 4 * b.val) r := by
    intro r
    unfold bit
    rw [hs, Nat.testBit_two_pow_mul_add _ hz, if_neg (show ¬ (18 + r < 18) by omega),
      Nat.add_sub_cancel_left]
  obtain ⟨h0, h1, h2⟩ := bits_s g t b
  have h18 : bit (idx z g t b) 18 = g := by have := hhigh 0; rw [h0] at this; exact this
  have h19 : bit (idx z g t b) 19 = t := by have := hhigh 1; rw [h1] at this; exact this
  have h20 : bit (idx z g t b) 20 = b := by have := hhigh 2; rw [h2] at this; exact this
  have hsplit : ∀ F : ℕ → K, ∑ i ∈ Finset.range 21, F i =
      ∑ i ∈ Finset.range 18, F i + F 18 + F 19 + F 20 := by
    intro F
    simp [Finset.sum_range_succ]
  rw [nodeN_bits 21 _ (idx_lt hz g t b), hsplit,
    Finset.sum_congr rfl (fun i hi => by rw [hlow i hi]), h18, h19, h20, ← nodeN_bits 18 z hz]

/-! ## The four flats -/

/-- Direction vectors of the flat `g = L(y) + _`, `t = M(y) + _`. -/
noncomputable def dirv (L M : Fin 18 → ZMod 2) (i : ℕ) : K :=
  nodeN (2 ^ i) + ψ (fe L i) * nodeN (2 ^ 18) + ψ (fe M i) * nodeN (2 ^ 19)

noncomputable def base (cg ct cb : ZMod 2) : K :=
  ψ cg * nodeN (2 ^ 18) + ψ ct * nodeN (2 ^ 19) + ψ cb * nodeN (2 ^ 20)

theorem span_eq (L M : Fin 18 → ZMod 2) {z : ℕ} (hz : z < 2 ^ 18) :
    ∑ i ∈ Finset.range 18, ψ (bit z i) * dirv L M i =
      nodeN z + ψ (lin L z) * nodeN (2 ^ 18) + ψ (lin M z) * nodeN (2 ^ 19) := by
  rw [nodeN_bits 18 z hz]
  simp only [lin, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dirv]
  ring

noncomputable irreducible_def Fl (L M : Fin 18 → ZMod 2) (cg ct cb : ZMod 2) : Polynomial K :=
  flatPoly (dirv L M) 18 (base cg ct cb)

theorem Fl_eval (L M : Fin 18 → ZMod 2) (cg ct cb : ZMod 2) {z : ℕ} (hz : z < 2 ^ 18) :
    (Fl L M cg ct cb).eval (nodeN (idx z (lin L z + cg) (lin M z + ct) cb)) = 0 := by
  have h : nodeN (idx z (lin L z + cg) (lin M z + ct) cb) =
      base cg ct cb + ∑ i ∈ Finset.range 18, ψ (bit z i) * dirv L M i := by
    rw [nodeN_idx hz, span_eq L M hz, base]
    simp only [map_add]
    ring
  rw [h, Fl_def]
  exact flatPoly_eval _ _ _ _

theorem Fl_gap (L M : Fin 18 → ZMod 2) (cg ct cb : ZMod 2) :
    (Fl L M cg ct cb - Xp (2 ^ 18)).natDegree ≤ 2 ^ 18 - 2 ^ 17 := by
  rw [Fl_def]
  exact (flatPoly_gapX (dirv L M) 18 (by norm_num) (base cg ct cb)).trans (by norm_num)

/-! ## Parameters and members -/

abbrev Param :=
  (Fin 18 → ZMod 2) × ZMod 2 × (Fin 18 → ZMod 2) × (Fin 17 → ZMod 2) × (Fin 17 → ZMod 2)

def Dv (p : Param) : Fin 18 → ZMod 2 := Fin.cons 1 p.2.2.2.1

def mv (p : Param) : Fin 18 → ZMod 2 := Fin.cons 0 p.2.2.2.2

def G (p : Param) (z : ℕ) (t b : ZMod 2) : ZMod 2 :=
  if b = 0 then (if t = 0 then 1 else lin p.1 z + p.2.1)
  else lin p.2.2.1 z + (t + lin (mv p) z) * lin (Dv p) z

def toIdx (i : ℕ) : Idx := ⟨i % 2097152, Nat.mod_lt _ (by norm_num)⟩

theorem toIdx_val {i : ℕ} (hi : i < 2097152) : (toIdx i).val = i := Nat.mod_eq_of_lt hi

def pt (p : Param) (q : ℕ × ZMod 2 × ZMod 2) : Idx :=
  toIdx (idx q.1 (G p q.1 q.2.1 q.2.2) q.2.1 q.2.2)

irreducible_def Dom : Finset (ℕ × ZMod 2 × ZMod 2) := Finset.range (2 ^ 18) ×ˢ Finset.univ

theorem mem_Dom_iff {q : ℕ × ZMod 2 × ZMod 2} : q ∈ Dom ↔ q.1 < 2 ^ 18 := by
  rw [Dom_def, Finset.mem_product, Finset.mem_range]
  simp

theorem Dom_card : Dom.card = 2 ^ 20 := by
  rw [Dom_def, Finset.card_product, Finset.card_range, Finset.card_univ]
  simp [ZMod.card]

theorem pt_val (p : Param) {q : ℕ × ZMod 2 × ZMod 2} (hq : q.1 < 2 ^ 18) :
    (pt p q).val = idx q.1 (G p q.1 q.2.1 q.2.2) q.2.1 q.2.2 :=
  toIdx_val (by have := idx_lt hq (G p q.1 q.2.1 q.2.2) q.2.1 q.2.2; omega)

theorem mem_Dom {q : ℕ × ZMod 2 × ZMod 2} (hq : q ∈ Dom) : q.1 < 2 ^ 18 := mem_Dom_iff.mp hq

/-- The family member with parameters `p`. -/
def Aset (p : Param) : Finset Idx := Dom.image (pt p)

theorem idx_eq_iff {z z' : ℕ} (hz : z < 2 ^ 18) (hz' : z' < 2 ^ 18) {g t b g' t' b' : ZMod 2}
    (h : idx z g t b = idx z' g' t' b') : z = z' ∧ g = g' ∧ t = t' ∧ b = b' := by
  have := val_lt_two g
  have := val_lt_two t
  have := val_lt_two b
  have := val_lt_two g'
  have := val_lt_two t'
  have := val_lt_two b'
  rw [idx_def, idx_def] at h
  refine ⟨by omega, ZMod.val_injective _ (by omega), ZMod.val_injective _ (by omega),
    ZMod.val_injective _ (by omega)⟩

theorem Aset_card (p : Param) : (Aset p).card = 2 ^ 20 := by
  rw [Aset, Finset.card_image_of_injOn, Dom_card]
  · intro q hq q' hq' h
    have hq1 := mem_Dom (Finset.mem_coe.mp hq)
    have hq1' := mem_Dom (Finset.mem_coe.mp hq')
    have h' := congrArg Fin.val h
    rw [pt_val p hq1, pt_val p hq1'] at h'
    obtain ⟨h1, -, h3, h4⟩ := idx_eq_iff hq1 hq1' h'
    exact Prod.ext h1 (Prod.ext h3 h4)

theorem G_val_pos (p : Param) (z : ℕ) (t b : ZMod 2) :
    1 ≤ (G p z t b).val + 2 * t.val + 4 * b.val := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rcases zmod2_cases t with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [G, h1]
  · simp only [h1]; omega
  · simp only [h1]; omega
  · simp only [h1]; omega

theorem Aset_val_ge (p : Param) {j : Idx} (hj : j ∈ Aset p) : 2 ^ 18 ≤ j.val := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
  rw [pt_val p (mem_Dom hq)]
  have := G_val_pos p q.1 q.2.1 q.2.2
  rw [idx_def]
  nlinarith

/-! ## Parameters are readable from the set -/

theorem G_eq_of_Aset_eq {p p' : Param} (h : Aset p = Aset p') {z : ℕ} (hz : z < 2 ^ 18)
    (t b : ZMod 2) : G p z t b = G p' z t b := by
  have hq : (z, t, b) ∈ Dom := mem_Dom_iff.mpr hz
  have hmem : pt p (z, t, b) ∈ Aset p' := h ▸ Finset.mem_image_of_mem _ hq
  obtain ⟨q', hq', he⟩ := Finset.mem_image.mp hmem
  have h' := congrArg Fin.val he
  rw [pt_val p' (mem_Dom hq'), pt_val p (mem_Dom hq)] at h'
  obtain ⟨h1, h2, h3, h4⟩ := idx_eq_iff (mem_Dom hq') hz h'
  obtain ⟨z', t', b'⟩ := q'
  simp only at h1 h2 h3 h4
  subst h1 h3 h4
  exact h2.symm

theorem two_zmod : (2 : ZMod 2) = 0 := by decide

theorem read_D (p : Param) (z : ℕ) : lin (Dv p) z = G p z 1 1 + G p z 0 1 := by
  simp only [G, one_ne_zero, if_false]
  linear_combination (-(lin p.2.2.1 z) - lin (mv p) z * lin (Dv p) z) * two_zmod

theorem read_m (p : Param) (i : Fin 18) (_hi : i ≠ 0) :
    mv p i = G p (1 ^^^ 2 ^ i.val) 0 1 + G p 1 0 1 + G p (2 ^ i.val) 0 1 := by
  simp only [G, one_ne_zero, if_false, lin_xor, lin_one, lin_two_pow]
  have hm0 : mv p 0 = 0 := rfl
  have hD0 : Dv p 0 = 1 := rfl
  rw [hm0, hD0]
  linear_combination (-(p.2.2.1 0) - p.2.2.1 i - mv p i * Dv p i) * two_zmod

theorem read_l0 (p : Param) (i : Fin 18) : p.2.2.1 i = G p (2 ^ i.val) 0 1 + mv p i * Dv p i := by
  simp only [G, one_ne_zero, if_false, lin_two_pow, zero_add]
  linear_combination (-(mv p i * Dv p i)) * two_zmod

theorem read_c (p : Param) : p.2.1 = G p 0 1 0 := by
  simp [G, lin_zero]

theorem read_l (p : Param) (i : Fin 18) : p.1 i = G p (2 ^ i.val) 1 0 + p.2.1 := by
  simp only [G, one_ne_zero, if_true, if_false, lin_two_pow]
  linear_combination (-(p.2.1)) * two_zmod

theorem two_pow_lt (i : Fin 18) : 2 ^ i.val < 2 ^ 18 := Nat.pow_lt_pow_right (by norm_num) i.isLt

theorem Aset_injective {p p' : Param} (h : Aset p = Aset p') : p = p' := by
  have hG := fun {z : ℕ} (hz : z < 2 ^ 18) (t b : ZMod 2) => G_eq_of_Aset_eq h hz t b
  have hc : p.2.1 = p'.2.1 := by rw [read_c, read_c, hG (by norm_num)]
  have hl : p.1 = p'.1 := by
    funext i
    rw [read_l, read_l, hG (two_pow_lt i), hc]
  have hD : Dv p = Dv p' := by
    funext i
    rw [← lin_two_pow (Dv p) i, ← lin_two_pow (Dv p') i, read_D, read_D,
      hG (two_pow_lt i), hG (two_pow_lt i)]
  have hm : mv p = mv p' := by
    funext i
    by_cases hi : i = 0
    · subst hi; rfl
    · have hx : 1 ^^^ 2 ^ i.val < 2 ^ 18 := Nat.xor_lt_two_pow (by norm_num) (two_pow_lt i)
      rw [read_m p i hi, read_m p' i hi, hG hx, hG (by norm_num), hG (two_pow_lt i)]
  have hl0 : p.2.2.1 = p'.2.2.1 := by
    funext i
    rw [read_l0, read_l0, hG (two_pow_lt i), hm, hD]
  have hD' : p.2.2.2.1 = p'.2.2.2.1 := by
    funext i
    have := congrFun hD i.succ
    simpa [Dv] using this
  have hm' : p.2.2.2.2 = p'.2.2.2.2 := by
    funext i
    have := congrFun hm i.succ
    simpa [mv] using this
  exact Prod.ext hl (Prod.ext hc (Prod.ext hl0 (Prod.ext hD' hm')))

/-! ## The locator of a member -/

noncomputable irreducible_def Lam (p : Param) : Polynomial K :=
  (Fl 0 0 1 0 0 * Fl p.1 0 p.2.1 1 0) *
    (Fl p.2.2.1 (mv p) 0 0 1 * Fl (p.2.2.1 + Dv p) (mv p) 0 1 1)

theorem Lam_eval_of (p : Param) {z : ℕ} (hz : z < 2 ^ 18) {g t b : ZMod 2}
    (h : (g = lin 0 z + 1 ∧ t = lin 0 z + 0 ∧ b = 0) ∨
      (g = lin p.1 z + p.2.1 ∧ t = lin 0 z + 1 ∧ b = 0) ∨
      (g = lin p.2.2.1 z + 0 ∧ t = lin (mv p) z + 0 ∧ b = 1) ∨
      (g = lin (p.2.2.1 + Dv p) z + 0 ∧ t = lin (mv p) z + 1 ∧ b = 1)) :
    (Lam p).eval (nodeN (idx z g t b)) = 0 := by
  rw [Lam_def]
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [eval_mul, Fl_eval _ _ _ _ _ hz, zero_mul, mul_zero]

theorem case_b1 (a e d t : ZMod 2) :
    (a + (t + e) * d = a + 0 ∧ t = e + 0) ∨ (a + (t + e) * d = (a + d) + 0 ∧ t = e + 1) := by
  revert a e d t
  decide

theorem Lam_eval (p : Param) {j : Idx} (hj : j ∈ Aset p) : (Lam p).eval (nodeN j.val) = 0 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
  rw [pt_val p (mem_Dom hq)]
  refine Lam_eval_of p (mem_Dom hq) ?_
  obtain ⟨z, t, b⟩ := q
  dsimp only
  rcases zmod2_cases b with rfl | rfl
  · rcases zmod2_cases t with rfl | rfl
    · left
      refine ⟨?_, ?_, rfl⟩ <;> simp [G, lin_zero_fun]
    · right; left
      refine ⟨?_, ?_, rfl⟩ <;> simp [G, lin_zero_fun]
  · right; right
    have hG : G p z t 1 = lin p.2.2.1 z + (t + lin (mv p) z) * lin (Dv p) z := by
      simp only [G, one_ne_zero, if_false]
    rw [hG, lin_add]
    rcases case_b1 (lin p.2.2.1 z) (lin (mv p) z) (lin (Dv p) z) t with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, rfl⟩
    · exact Or.inr ⟨h1, h2, rfl⟩

theorem Lam_gap (p : Param) : (Lam p - Xp (2 ^ 20)).natDegree ≤ 2 ^ 20 - 2 ^ 17 := by
  have hpair : ∀ f h : Polynomial K, (f - Xp (2 ^ 18)).natDegree ≤ 2 ^ 18 - 2 ^ 17 →
      (h - Xp (2 ^ 18)).natDegree ≤ 2 ^ 18 - 2 ^ 17 →
      (f * h - Xp (2 ^ 19)).natDegree ≤ 2 ^ 19 - 2 ^ 17 := fun f h hf hh =>
    gap_mulX (a := 2 ^ 18) (b := 2 ^ 18) (c := 2 ^ 19) (w := 2 ^ 17) (by norm_num) (by norm_num)
      (by norm_num) hf hh
  have h1 := hpair _ _ (Fl_gap 0 0 1 0 0) (Fl_gap p.1 0 p.2.1 1 0)
  have h2 := hpair _ _ (Fl_gap p.2.2.1 (mv p) 0 0 1) (Fl_gap (p.2.2.1 + Dv p) (mv p) 0 1 1)
  rw [Lam_def]
  exact gap_mulX (a := 2 ^ 19) (b := 2 ^ 19) (c := 2 ^ 20) (w := 2 ^ 17) (by norm_num) (by norm_num)
    (by norm_num) h1 h2

theorem Lam_coeff_top (p : Param) : (Lam p).coeff (2 ^ 20) = 1 := by
  have h := coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (Lam_gap p) (by norm_num : 2 ^ 20 - 2 ^ 17 < 2 ^ 20))
  rw [coeff_sub, Xp_coeff_self, sub_eq_zero] at h
  exact h

theorem Lam_ne_zero (p : Param) : Lam p ≠ 0 := by
  intro h0
  have h := Lam_coeff_top p
  rw [h0, coeff_zero] at h
  exact zero_ne_one h

theorem Lam_natDegree_le (p : Param) : (Lam p).natDegree ≤ 2 ^ 20 := by
  conv_lhs => rw [← sub_add_cancel (Lam p) (Xp (2 ^ 20))]
  refine (natDegree_add_le _ _).trans (max_le ((Lam_gap p).trans (by norm_num)) ?_)
  rw [Xp_natDegree]

theorem subset_of_vanish {Λ : Polynomial K} (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree ≤ 2 ^ 20)
    {S T : Finset Idx} (hS : S.card = 2 ^ 20) (hvS : ∀ j ∈ S, Λ.eval (nodeN j.val) = 0)
    (hvT : ∀ j ∈ T, Λ.eval (nodeN j.val) = 0) : T ⊆ S := by
  classical
  intro j hj
  by_contra hjS
  have hsub : (insert j S).image (fun i : Idx => nodeN i.val) ⊆ Λ.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hΛ]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hvT _ hj
    · exact hvS _ hi
  have hinj : Set.InjOn (fun i : Idx => nodeN i.val) ↑(insert j S) := by
    intro a _ c _ hac
    have ha := a.isLt
    have hc := c.isLt
    change a.val < 2 ^ 21 at ha
    change c.val < 2 ^ 21 at hc
    exact Fin.ext (nodeN_injective (by omega) (by omega) hac)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_insert_of_notMem hjS, hS] at hcard
  have h2 := (Multiset.toFinset_card_le Λ.roots).trans (card_roots' Λ)
  omega

theorem Lam_injective {p p' : Param} (h : Lam p = Lam p') : p = p' := by
  apply Aset_injective
  have hsub : Aset p' ⊆ Aset p :=
    subset_of_vanish (Lam_ne_zero p) (Lam_natDegree_le p) (Aset_card p) (fun j hj => Lam_eval p hj)
      (fun j hj => h ▸ Lam_eval p' hj)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [Aset_card, Aset_card])).symm

/-! ## The reserved subspace and the agreement sets -/

irreducible_def Wset : Finset Idx := (Finset.range (2 ^ 17)).image toIdx

theorem Wset_card : Wset.card = 2 ^ 17 := by
  rw [Wset_def, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha c hc hac
  have ha' : a < 2 ^ 17 := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hc' : c < 2 ^ 17 := Finset.mem_range.mp (Finset.mem_coe.mp hc)
  have := congrArg Fin.val hac
  rwa [toIdx_val (by omega), toIdx_val (by omega)] at this

theorem Wset_val_lt {j : Idx} (hj : j ∈ Wset) : j.val < 2 ^ 17 := by
  rw [Wset_def] at hj
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
  have hl' := Finset.mem_range.mp hl
  rw [toIdx_val (by omega)]
  exact hl'

noncomputable irreducible_def LamW : Polynomial K := L 17

theorem LamW_monic : LamW.Monic := by rw [LamW_def]; exact (L_monic_natDegree 17).1

theorem LamW_natDegree : LamW.natDegree = 2 ^ 17 := by rw [LamW_def]; exact (L_monic_natDegree 17).2

theorem LamW_eval {j : Idx} (hj : j ∈ Wset) : LamW.eval (nodeN j.val) = 0 := by
  rw [LamW_def]
  exact L_eval_low 17 _ (Wset_val_lt hj)

/-- The agreement set of a member: the member together with `W`. -/
def Sset (p : Param) : Finset Idx := Wset ∪ Aset p

theorem Sset_card (p : Param) : (Sset p).card = 2 ^ 17 + 2 ^ 20 := by
  rw [Sset, Finset.card_union_of_disjoint, Wset_card, Aset_card]
  rw [Finset.disjoint_left]
  intro j hj hj'
  have h1 := Wset_val_lt hj
  have h2 := Aset_val_ge p hj'
  omega

theorem vanish_Sset (p : Param) {j : Idx} (hj : j ∈ Sset p) :
    (LamW * Lam p).eval (nodeN j.val) = 0 := by
  rw [eval_mul]
  rcases Finset.mem_union.mp hj with hw | ha
  · rw [LamW_eval hw, zero_mul]
  · rw [Lam_eval p ha, mul_zero]

/-- The correction polynomial `C_A = L_W (L_A - X^(2^20))`, of degree at most `2^20`. -/
noncomputable irreducible_def Cp (p : Param) : Polynomial K := LamW * (Lam p - Xp (2 ^ 20))

theorem Cp_natDegree_le (p : Param) : (Cp p).natDegree ≤ 2 ^ 20 := by
  rw [Cp_def]
  refine natDegree_mul_le.trans ?_
  rw [LamW_natDegree]
  have := Lam_gap p
  have h : (2 : ℕ) ^ 17 ≤ 2 ^ 20 := by norm_num
  omega

theorem Cp_injective {p p' : Param} (h : Cp p = Cp p') : p = p' := by
  apply Lam_injective
  rw [Cp_def, Cp_def] at h
  exact sub_left_inj.mp (mul_left_cancel₀ LamW_monic.ne_zero h)

theorem Cp_split (p : Param) : LamW * Lam p = LamW * Xp (2 ^ 20) + Cp p := by
  rw [Cp_def, ← mul_add, add_sub_cancel]

end ProximityPrize.SubmissionBinaryUpper.PoleFamily

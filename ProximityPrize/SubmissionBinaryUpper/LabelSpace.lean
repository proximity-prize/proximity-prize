/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.FlatPoly

/-!
# Labels of the cosets of the first 64 words

The subspace polynomial `Ys = L 6` of the first `64` domain words is additive and
constant on each coset `64 h + {0, …, 63}`.  Its value there is the *label* of the
coset.  Labels are additive in `h`, so they are the image of an injective additive
map `lab` on the label space `V = 𝔽₂^11 × 𝔽₂^4`: the first factor holds the
low eleven bits of `h`, the second the top four.

`LW = P ell 11` is the subspace polynomial of the labels with zero top part.  It is
additive and constant on the sixteen cosets of that subspace.
-/

namespace ProximityPrize.SubmissionBinaryUpper.LabelSpace

open Polynomial
open ProximityPrize.SubmissionBinaryUpper.SubspacePoly
open ProximityPrize.SubmissionBinaryUpper.FlatPoly

/-! ## The subspace polynomial of the first 64 words -/

noncomputable def Ys : Polynomial K := L 6

theorem Ys_add (a b : K) : Ys.eval (a + b) = Ys.eval a + Ys.eval b := L_add 6 a b

theorem Ys_monic : Ys.Monic := (L_monic_natDegree 6).1

theorem Ys_natDegree : Ys.natDegree = 64 := by rw [Ys, (L_monic_natDegree 6).2]; norm_num

theorem Ys_eval_low (l : ℕ) (hl : l < 64) : Ys.eval (nodeN l) = 0 :=
  L_eval_low 6 l (by norm_num; exact hl)

theorem Ys_zero : Ys.eval 0 = 0 := by
  have h := Ys_add 0 0
  rw [add_zero] at h
  linear_combination -h

theorem Ys_smul (c : ZMod 2) (a : K) : Ys.eval (ψ c * a) = ψ c * Ys.eval a := by
  rcases zmod2_cases c with rfl | rfl
  · simp [Ys_zero]
  · simp

theorem Ys_eval_ne {i : ℕ} (hi : i < 2 ^ 64) (hlow : 64 ≤ i) : Ys.eval (nodeN i) ≠ 0 := by
  classical
  intro h
  let Zs : Finset K := (Finset.range 64).image nodeN
  have hZcard : Zs.card = 64 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact nodeN_injective (by omega) (by omega) hab
  have hnot : nodeN i ∉ Zs := by
    intro hm
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hm
    have := nodeN_injective (by simp at ha; omega) hi hab
    simp at ha
    omega
  have hsub : insert (nodeN i) Zs ⊆ Ys.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots Ys_monic.ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Ys_eval_low a (by simpa using ha)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hZcard] at hcard
  have h2 := (Multiset.toFinset_card_le Ys.roots).trans (card_roots' Ys)
  rw [Ys_natDegree] at h2
  omega

theorem Ys_fibre (a l : ℕ) (hl : l < 64) :
    Ys.eval (nodeN (64 * a + l)) = Ys.eval (nodeN (64 * a)) := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, two_pow_mul_add_eq_xor (by norm_num; exact hl), nodeN_xor,
    Ys_add, Ys_eval_low l hl, add_zero]

/-- `Ys` as an additive map, for sums. -/
noncomputable def YsHom : K →+ K := AddMonoidHom.mk' (fun a => Ys.eval a) Ys_add

theorem Ys_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    Ys.eval (∑ i ∈ s, f i) = ∑ i ∈ s, Ys.eval (f i) :=
  map_sum YsHom f s

/-! ## Words of the domain from binary digits -/

theorem nodeN_digits (b : ℕ → ZMod 2) (c : ℕ) : ∀ m : ℕ,
    nodeN (∑ i ∈ Finset.range m, (b i).val * 2 ^ (c + i)) =
        ∑ i ∈ Finset.range m, ψ (b i) * nodeN (2 ^ (c + i)) ∧
      ∑ i ∈ Finset.range m, (b i).val * 2 ^ (c + i) < 2 ^ (c + m) := by
  intro m
  induction m with
  | zero => simp [nodeN_zero]
  | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      have hb : (b m).val < 2 := ZMod.val_lt (b m)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      constructor
      · rw [show (∑ i ∈ Finset.range m, (b i).val * 2 ^ (c + i)) + (b m).val * 2 ^ (c + m) =
            2 ^ (c + m) * (b m).val + ∑ i ∈ Finset.range m, (b i).val * 2 ^ (c + i) by ring,
          two_pow_mul_add_eq_xor h2, nodeN_xor, h1, add_comm]
        congr 1
        rcases zmod2_cases (b m) with h | h <;> rw [h]
        · simp [nodeN_zero]
        · rw [show (1 : ZMod 2).val = 1 from rfl, mul_one, map_one, one_mul]
      · rw [show c + (m + 1) = c + m + 1 by ring, pow_succ]
        have : (b m).val * 2 ^ (c + m) ≤ 2 ^ (c + m) := by
          calc (b m).val * 2 ^ (c + m) ≤ 1 * 2 ^ (c + m) := Nat.mul_le_mul_right _ (by omega)
            _ = 2 ^ (c + m) := one_mul _
        omega

/-! ## Label vectors -/

abbrev Z4 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
abbrev Yv := Fin 11 → ZMod 2
abbrev V := Yv × Z4

theorem add_self_V (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eq_of_add_eq_zero_V {v w : V} (h : v + w = 0) : v = w := by
  calc v = v + (w + w) := by rw [add_self_V, add_zero]
    _ = (v + w) + w := by rw [add_assoc]
    _ = w := by rw [h, zero_add]

/-- Coordinate `i` of a label vector: the `y`-part is `0 … 10`, the `z`-part `11 … 14`. -/
def coord (v : V) (i : ℕ) : ZMod 2 :=
  if h : i < 11 then v.1 ⟨i, h⟩
  else if i = 11 then v.2.1 else if i = 12 then v.2.2.1 else if i = 13 then v.2.2.2.1
  else if i = 14 then v.2.2.2.2 else 0

theorem coord_add (v w : V) (i : ℕ) : coord (v + w) i = coord v i + coord w i := by
  unfold coord
  split_ifs <;> simp

theorem coord_smul (c : ZMod 2) (v : V) (i : ℕ) : coord (c • v) i = c * coord v i := by
  unfold coord
  split_ifs <;> simp

/-- The basis labels. -/
noncomputable def ell (i : ℕ) : K := Ys.eval (nodeN (2 ^ (6 + i)))

/-- The label of a label vector. -/
noncomputable def lab (v : V) : K := ∑ i ∈ Finset.range 15, ψ (coord v i) * ell i

theorem lab_add (v w : V) : lab (v + w) = lab v + lab w := by
  simp only [lab, coord_add, map_add, add_mul, Finset.sum_add_distrib]

theorem lab_smul (c : ZMod 2) (v : V) : lab (c • v) = ψ c * lab v := by
  simp only [lab, coord_smul, map_mul, Finset.mul_sum, mul_assoc]

theorem lab_zero : lab 0 = 0 := by
  have h := lab_add 0 0
  rw [add_zero] at h
  linear_combination -h

/-- The index of the coset with a given label vector. -/
def hidx (v : V) : ℕ := ∑ i ∈ Finset.range 15, (coord v i).val * 2 ^ i

theorem hidx_lt (v : V) : hidx v < 2 ^ 15 := by
  have := (nodeN_digits (coord v) 0 15).2
  simpa [hidx] using this

theorem lab_eq (v : V) : Ys.eval (nodeN (64 * hidx v)) = lab v := by
  have h64 : 64 * hidx v = ∑ i ∈ Finset.range 15, (coord v i).val * 2 ^ (6 + i) := by
    rw [hidx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
    ring
  rw [h64, (nodeN_digits (coord v) 6 15).1, Ys_sum, lab]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ys_smul, ell]

theorem Ys_label (v : V) (l : ℕ) (hl : l < 64) : Ys.eval (nodeN (64 * hidx v + l)) = lab v := by
  rw [Ys_fibre _ _ hl, lab_eq]

theorem coord_eq_zero_of_hidx {v : V} (h : hidx v = 0) (i : ℕ) (hi : i < 15) : coord v i = 0 := by
  have hterm := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_range.mpr hi)
  have hpos : 0 < 2 ^ i := by positivity
  have hval : (coord v i).val = 0 := by
    rcases Nat.mul_eq_zero.mp hterm with h' | h'
    · exact h'
    · omega
  exact (ZMod.val_eq_zero _).mp hval

theorem eq_zero_of_hidx {v : V} (h : hidx v = 0) : v = 0 := by
  have hc := coord_eq_zero_of_hidx h
  obtain ⟨y, z0, z1, z2, z3⟩ := v
  have hy : y = 0 := by
    funext j
    have := hc j.val (by omega)
    simpa [coord, j.isLt] using this
  have h0 : z0 = 0 := by simpa [coord] using hc 11 (by norm_num)
  have h1 : z1 = 0 := by simpa [coord] using hc 12 (by norm_num)
  have h2 : z2 = 0 := by simpa [coord] using hc 13 (by norm_num)
  have h3 : z3 = 0 := by simpa [coord] using hc 14 (by norm_num)
  subst hy h0 h1 h2 h3
  rfl

theorem lab_eq_zero {v : V} (h : lab v = 0) : v = 0 := by
  by_contra hv
  have hne : hidx v ≠ 0 := fun h0 => hv (eq_zero_of_hidx h0)
  have hlt := hidx_lt v
  rw [← lab_eq] at h
  exact Ys_eval_ne (by omega) (by omega) h

theorem lab_injective : Function.Injective lab := by
  intro v w h
  apply eq_of_add_eq_zero_V
  apply lab_eq_zero
  rw [lab_add, h]
  exact CharTwo.add_self_eq_zero _

theorem hidx_injective {v w : V} (h : hidx v = hidx w) : v = w := by
  apply lab_injective
  rw [← lab_eq, ← lab_eq, h]

theorem hidx_pos {v : V} (hv : v ≠ 0) : 1 ≤ hidx v := by
  by_contra h
  exact hv (eq_zero_of_hidx (by omega))

/-! ## The subspace polynomial of the labels with zero top part -/

noncomputable def LW : Polynomial K := P ell 11

theorem LW_monic : LW.Monic := (P_monic_natDegree ell 11).1

theorem LW_natDegree : LW.natDegree = 2048 := by
  rw [LW, (P_monic_natDegree ell 11).2]; norm_num

theorem LW_add (a b : K) : LW.eval (a + b) = LW.eval a + LW.eval b := P_add ell 11 a b

theorem lab_split (v : V) : lab v = lab (v.1, 0) + lab (0, v.2) := by
  rw [← lab_add]
  congr 1
  ext <;> simp

theorem lab_low (y : Yv) : lab (y, 0) = ∑ i ∈ Finset.range 11, ψ (coord (y, 0) i) * ell i := by
  rw [lab]
  simp [Finset.sum_range_succ, coord]

theorem LW_eval_low (y : Yv) : LW.eval (lab (y, 0)) = 0 := by
  rw [lab_low, LW]
  exact P_eval_span ell _ 11

theorem LW_eval (v : V) : LW.eval (lab v) = LW.eval (lab (0, v.2)) := by
  rw [lab_split, LW_add, LW_eval_low, zero_add]

end ProximityPrize.SubmissionBinaryUpper.LabelSpace

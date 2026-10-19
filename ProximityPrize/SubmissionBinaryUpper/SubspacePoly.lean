/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.PrescribedTop

/-!
# The subspace polynomial of the first `2^14` domain points

The binary evaluation domain is the set of the first `2^21` polynomial-basis
words of `BF64`, so it is an `𝔽₂`-subspace, and addition is `xor` of the
indices.  The words below `2^14` form a subspace `W`, and its vanishing
polynomial `Ysub` is additive (an `𝔽₂`-linearised polynomial) of degree `2^14`.

`Ysub` is built by the usual recursion `L₀ = X`, `L_{k+1} = L_k (L_k - L_k(2^k))`,
which makes additivity a one-line induction in characteristic two.  Then `Ysub`
is constant on each coset `2^14 h + W`, and its value `y h` there is additive
in the coset label `h`.
-/

namespace ProximityPrize.SubmissionBinaryUpper.SubspacePoly

open Polynomial

abbrev K := _root_.BF64

/-- Polynomial-basis words indexed by naturals. -/
def nodeN (i : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 i)

theorem nodeN_xor (i j : ℕ) : nodeN (i ^^^ j) = nodeN i + nodeN j := by
  simp only [nodeN, BF64.add_def, BF64.toBitVec_ofBitVec, BitVec.ofNat_xor]

theorem nodeN_zero : nodeN 0 = 0 := rfl

theorem nodeN_injective {i j : ℕ} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : nodeN i = nodeN j) : i = j := by
  have h1 := congrArg (fun z : K => (BF64.toBitVec z).toNat) h
  simp only [nodeN, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at h1
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1

theorem two_pow_mul_add_eq_xor {i a b : ℕ} (hb : b < 2 ^ i) :
    2 ^ i * a + b = (2 ^ i * a) ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add a hb, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : j < i
  · simp [hj, Nat.not_le_of_lt hj]
  · have hb' : b < 2 ^ j := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hj, Nat.le_of_not_lt hj, Nat.testBit_lt_two_pow hb']

theorem mul_two_pow_xor (a b i : ℕ) : 2 ^ i * (a ^^^ b) = (2 ^ i * a) ^^^ (2 ^ i * b) := by
  rw [Nat.mul_comm, Nat.mul_comm _ a, Nat.mul_comm _ b, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]

/-! ## The recursive subspace polynomials -/

/-- `L k` vanishes exactly on the words below `2^k`. -/
noncomputable def L : ℕ → Polynomial K
  | 0 => Polynomial.X
  | k + 1 => L k * (L k - C ((L k).eval (nodeN (2 ^ k))))

theorem two_eq_zero : (2 : K) = 0 := by
  have h := CharTwo.add_self_eq_zero (1 : K)
  rwa [one_add_one_eq_two] at h

theorem L_add (k : ℕ) (a b : K) : (L k).eval (a + b) = (L k).eval a + (L k).eval b := by
  induction k with
  | zero => simp [L]
  | succ k ih =>
      simp only [L, eval_mul, eval_sub, eval_C, ih]
      linear_combination (L k).eval a * (L k).eval b * two_eq_zero

theorem L_monic_natDegree (k : ℕ) : (L k).Monic ∧ (L k).natDegree = 2 ^ k := by
  induction k with
  | zero => exact ⟨monic_X, by simp [L, natDegree_X]⟩
  | succ k ih =>
      obtain ⟨hm, hd⟩ := ih
      have hpos : 0 < (L k).natDegree := by rw [hd]; positivity
      have hq : (L k - C ((L k).eval (nodeN (2 ^ k)))).Monic := by
        apply hm.sub_of_left
        calc (C ((L k).eval (nodeN (2 ^ k)))).degree ≤ 0 := degree_C_le
          _ < (L k).degree := by
            rw [degree_eq_natDegree hm.ne_zero]
            exact_mod_cast hpos
      refine ⟨hm.mul hq, ?_⟩
      rw [L, hm.natDegree_mul hq, natDegree_sub_C, hd, pow_succ]
      ring

theorem L_eval_low (k : ℕ) : ∀ l < 2 ^ k, (L k).eval (nodeN l) = 0 := by
  induction k with
  | zero =>
      intro l hl
      have : l = 0 := by omega
      subst this
      simp [L, nodeN_zero]
  | succ k ih =>
      intro l hl
      by_cases hlow : l < 2 ^ k
      · simp [L, ih l hlow]
      · have hsub : l - 2 ^ k < 2 ^ k := by rw [pow_succ] at hl; omega
        have hl' : l = (2 ^ k * 1) ^^^ (l - 2 ^ k) := by
          rw [← two_pow_mul_add_eq_xor hsub]; omega
        have hx : nodeN l = nodeN (2 ^ k) + nodeN (l - 2 ^ k) := by
          conv_lhs => rw [hl']
          rw [nodeN_xor, Nat.mul_one]
        simp only [L, eval_mul, eval_sub, eval_C]
        rw [hx, L_add, ih _ hsub, add_zero, sub_self, mul_zero]

/-- The subspace polynomial of the first `2^14` words. -/
noncomputable def Ysub : Polynomial K := L 14

theorem Y_monic : Ysub.Monic := (L_monic_natDegree 14).1

theorem Y_natDegree : Ysub.natDegree = 16384 := by
  rw [Ysub, (L_monic_natDegree 14).2]; norm_num

theorem Y_add (a b : K) : Ysub.eval (a + b) = Ysub.eval a + Ysub.eval b := L_add 14 a b

theorem Y_eval_low (l : ℕ) (hl : l < 16384) : Ysub.eval (nodeN l) = 0 :=
  L_eval_low 14 l (by norm_num; exact hl)

theorem Y_eval_ne {i : ℕ} (hi : i < 2 ^ 64) (hlow : 16384 ≤ i) : Ysub.eval (nodeN i) ≠ 0 := by
  classical
  intro h
  let Zs : Finset K := (Finset.range 16384).image nodeN
  have hZcard : Zs.card = 16384 := by
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
  have hsub : insert (nodeN i) Zs ⊆ Ysub.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots Y_monic.ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Y_eval_low a (by simpa using ha)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hZcard] at hcard
  have h2 := (Multiset.toFinset_card_le Ysub.roots).trans (card_roots' Ysub)
  rw [Y_natDegree] at h2
  omega

/-! ## Coset labels -/

/-- The value of `Ysub` on the coset `2^14 h + W`. -/
noncomputable def y (h : ℕ) : K := Ysub.eval (nodeN (16384 * h))

theorem Y_fibre (h l : ℕ) (hl : l < 16384) : Ysub.eval (nodeN (16384 * h + l)) = y h := by
  have hl' : l < 2 ^ 14 := by norm_num; exact hl
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, two_pow_mul_add_eq_xor hl', nodeN_xor, Y_add,
    Y_eval_low l hl, add_zero, y]
  norm_num

theorem y_xor (h h' : ℕ) : y (h ^^^ h') = y h + y h' := by
  unfold y
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, mul_two_pow_xor, nodeN_xor, Y_add]

theorem y_zero : y 0 = 0 := by
  simpa [y] using Y_eval_low 0 (by norm_num)

theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun z => Nat.testBit z i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem y_injective {h h' : ℕ} (hh : h < 128) (hh' : h' < 128) (e : y h = y h') : h = h' := by
  by_contra hne
  have hx : h ^^^ h' ≠ 0 := fun hz => hne (eq_of_xor_eq_zero hz)
  have hlt : h ^^^ h' < 2 ^ 7 := Nat.xor_lt_two_pow (by norm_num; exact hh) (by norm_num; exact hh')
  have hzero : y (h ^^^ h') = 0 := by
    rw [y_xor, e]
    exact CharTwo.add_self_eq_zero _
  apply Y_eval_ne (i := 16384 * (h ^^^ h')) (by norm_num at hlt ⊢; omega) (by omega)
  exact hzero

/-! ## Labels as subset sums of a seven-element basis -/

/-- The basis labels `y (2^k)`. -/
noncomputable def b (k : ℕ) : K := y (2 ^ k)

theorem y_decomp (n : ℕ) : ∀ h < 2 ^ n, ∃ A ⊆ Finset.range n, y h = ∑ k ∈ A, b k := by
  induction n with
  | zero =>
      intro h hh
      have : h = 0 := by simpa using hh
      subst this
      exact ⟨∅, by simp, by simp [y_zero]⟩
  | succ n ih =>
      intro h hh
      by_cases hlow : h < 2 ^ n
      · obtain ⟨A, hA, hy⟩ := ih h hlow
        exact ⟨A, hA.trans (Finset.range_subset_range.mpr (Nat.le_succ n)), hy⟩
      · have hsub : h - 2 ^ n < 2 ^ n := by rw [pow_succ] at hh; omega
        obtain ⟨A, hA, hy⟩ := ih (h - 2 ^ n) hsub
        have hnA : n ∉ A := fun hn => by simpa using hA hn
        refine ⟨insert n A, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · simp
          · exact Finset.range_subset_range.mpr (Nat.le_succ n) (hA hk)
        · have hx : h = (2 ^ n * 1) ^^^ (h - 2 ^ n) := by
            rw [← two_pow_mul_add_eq_xor hsub]; omega
          rw [Finset.sum_insert hnA, ← hy]
          conv_lhs => rw [hx]
          rw [y_xor, Nat.mul_one, b]

theorem sum_add_sum_eq_symmDiff {ι : Type*} [DecidableEq ι] (f : ι → K) (A B : Finset ι) :
    ∑ k ∈ A, f k + ∑ k ∈ B, f k = ∑ k ∈ (A \ B) ∪ (B \ A), f k := by
  rw [Finset.sum_union (disjoint_sdiff_sdiff), ← Finset.sum_inter_add_sum_sdiff A B,
    ← Finset.sum_inter_add_sum_sdiff B A, Finset.inter_comm B A]
  have h2 := CharTwo.add_self_eq_zero (∑ k ∈ A ∩ B, f k)
  linear_combination h2

/-- All subset sums of the basis labels. -/
noncomputable def S1 : Finset K :=
  (Finset.range 7).powerset.image (fun A => ∑ k ∈ A, b k)

/-- All subset sums of pairwise basis products. -/
noncomputable def S2 : Finset K :=
  (Finset.range 7 ×ˢ Finset.range 7).powerset.image (fun T => ∑ p ∈ T, b p.1 * b p.2)

theorem S1_card : S1.card ≤ 2 ^ 7 := by
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_powerset]

theorem S2_card : S2.card ≤ 2 ^ 49 := by
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_powerset]

theorem y_mem_S1 {h : ℕ} (hh : h < 128) : y h ∈ S1 := by
  obtain ⟨A, hA, hy⟩ := y_decomp 7 h (by norm_num; exact hh)
  exact Finset.mem_image.mpr ⟨A, Finset.mem_powerset.mpr hA, hy.symm⟩

theorem zero_mem_S1 : (0 : K) ∈ S1 :=
  Finset.mem_image.mpr ⟨∅, by simp, by simp⟩

theorem zero_mem_S2 : (0 : K) ∈ S2 :=
  Finset.mem_image.mpr ⟨∅, by simp, by simp⟩

theorem S1_add {a c : K} (ha : a ∈ S1) (hc : c ∈ S1) : a + c ∈ S1 := by
  classical
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hc
  refine Finset.mem_image.mpr ⟨(A \ B) ∪ (B \ A), ?_, (sum_add_sum_eq_symmDiff _ A B).symm⟩
  rw [Finset.mem_powerset] at hA hB ⊢
  exact Finset.union_subset (Finset.sdiff_subset.trans hA) (Finset.sdiff_subset.trans hB)

theorem S2_add {a c : K} (ha : a ∈ S2) (hc : c ∈ S2) : a + c ∈ S2 := by
  classical
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hc
  refine Finset.mem_image.mpr ⟨(A \ B) ∪ (B \ A), ?_,
    (sum_add_sum_eq_symmDiff (fun p : ℕ × ℕ => b p.1 * b p.2) A B).symm⟩
  rw [Finset.mem_powerset] at hA hB ⊢
  exact Finset.union_subset (Finset.sdiff_subset.trans hA) (Finset.sdiff_subset.trans hB)

theorem S1_mul {a c : K} (ha : a ∈ S1) (hc : c ∈ S1) : a * c ∈ S2 := by
  classical
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hc
  refine Finset.mem_image.mpr ⟨A ×ˢ B, ?_, ?_⟩
  · rw [Finset.mem_powerset] at hA hB ⊢
    exact Finset.product_subset_product hA hB
  · rw [Finset.sum_mul_sum, Finset.sum_product]

/-! ## Elementary symmetric functions of labels -/

theorem esymm_cons (a : K) (s : Multiset K) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem esymm_one_mem (s : Multiset K) (hs : ∀ a ∈ s, a ∈ S1) : s.esymm 1 ∈ S1 := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.esymm_of_card_lt (by simp)]; exact zero_mem_S1
  | cons a s ih =>
      rw [esymm_cons, Multiset.esymm_zero, mul_one]
      exact S1_add (ih fun x hx => hs x (Multiset.mem_cons_of_mem hx))
        (hs a (Multiset.mem_cons_self a s))

theorem esymm_two_mem (s : Multiset K) (hs : ∀ a ∈ s, a ∈ S1) : s.esymm 2 ∈ S2 := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.esymm_of_card_lt (by simp)]; exact zero_mem_S2
  | cons a s ih =>
      have hs' : ∀ x ∈ s, x ∈ S1 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      rw [esymm_cons]
      exact S2_add (ih hs') (S1_mul (hs a (Multiset.mem_cons_self a s)) (esymm_one_mem s hs'))

end ProximityPrize.SubmissionBinaryUpper.SubspacePoly

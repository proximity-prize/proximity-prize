import ProximityPrize.SubmissionLower.Z6970GateLeadingBase

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

open Gate6966Cell
open scoped BigOperators

private def rise (P : ℕ → ℤ → ℤ) (a : ℕ) (c : ℤ) (n : ℕ) : ℤ :=
  P a (a * (n : ℤ) + c - a) - P a (c - a)

private def fall (P : ℕ → ℤ → ℤ) (a : ℕ) (c : ℤ) (n : ℕ) : ℤ :=
  P a c - P a (c - a * (n : ℤ))

private theorem rise_eq (P : ℕ → ℤ → ℤ) (h : StepRule P)
    (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 3) (c : ℤ) (n : ℕ)
    (bound : ∀ q : ℕ, q < n → (a : ℤ) * q + c ≤ 1679) :
    rise P a c n = ∑ q ∈ Finset.range n, den ((a : ℤ) * q + c) := by
  induction n with
  | zero => simp [rise]
  | succ n ih =>
    have ih' := ih (fun q hq => bound q (Nat.lt_succ_of_lt hq))
    have step := h a ((a : ℤ) * n + c) ha ha' (bound n (Nat.lt_succ_self n))
    rw [Finset.sum_range_succ, ← ih']
    have shift : (a : ℤ) * ((n + 1 : ℕ) : ℤ) + c - a = (a : ℤ) * n + c := by
      push_cast
      ring
    unfold rise
    rw [shift]
    omega

private theorem fall_eq (P : ℕ → ℤ → ℤ) (h : StepRule P)
    (a : ℕ) (ha : 1 ≤ a) (ha' : a ≤ 3) (c : ℤ) (hc : c ≤ 1679) (n : ℕ) :
    fall P a c n = ∑ q ∈ Finset.range n, den (c - (a : ℤ) * q) := by
  induction n with
  | zero => simp [fall]
  | succ n ih =>
    have hb : c - (a : ℤ) * n ≤ 1679 := by
      have nonnegative : (0 : ℤ) ≤ (a : ℤ) * n := mul_nonneg (by positivity) (by positivity)
      omega
    have step := h a (c - (a : ℤ) * n) ha ha' hb
    rw [Finset.sum_range_succ, ← ih]
    have shift : c - (a : ℤ) * ((n + 1 : ℕ) : ℤ) = c - (a : ℤ) * n - a := by
      push_cast
      ring
    unfold fall
    rw [shift]
    omega

private theorem cast_dg (v c : ℕ) : (dg v c : ℤ) = den ((v : ℤ) - c) := by
  by_cases h : c ≤ v
  · have hn : ¬ (v : ℤ) - c < 0 := by omega
    have ht : ((v : ℤ) - c).toNat = v - c := by omega
    simp [dg, den, h, hn, ht]
  · have hn : (v : ℤ) - c < 0 := by omega
    simp [dg, den, h, hn]

private def lowTerm (q : ℕ) : ℤ :=
  den (3 * (q : ℤ)) - den (2 * (q : ℤ) - 1) - den (2 * (q : ℤ) - 2) -
    den (2 * (q : ℤ) - 3) + den ((q : ℤ) - 3) + den ((q : ℤ) - 4) +
    den ((q : ℤ) - 5)

private def highTerm (u q : ℕ) : ℤ :=
  den u + den ((u : ℤ) - 2 * (q : ℤ) - 3) + den ((u : ℤ) - 2 * (q : ℤ) - 4) +
    den ((u : ℤ) - 2 * (q : ℤ) - 5) - den ((u : ℤ) - (q : ℤ) - 1) -
    den ((u : ℤ) - (q : ℤ) - 2) - den ((u : ℤ) - (q : ℤ) - 3) -
    den ((u : ℤ) - 3 * (q : ℤ) - 6)

private theorem lowTerm_eq (q u : ℕ) (h : 3 * q ≤ u) :
    (cumP q u : ℤ) - cumQ q u = lowTerm q := by
  simp only [cumP, cumQ, min_eq_right h, cumPV, cumQV, Nat.cast_add, cast_dg,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, sub_zero, lowTerm]
  have z : den (-6) = 0 := by simp [den]
  ring_nf
  simp only [z, sub_zero]

private theorem highTerm_eq (q u : ℕ) (h : u ≤ 3 * q) :
    (cumP q u : ℤ) - cumQ q u = highTerm u q := by
  simp only [cumP, cumQ, min_eq_left h, cumPV, cumQV, Nat.cast_add, cast_dg,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, sub_zero, highTerm]
  ring_nf

private def lowPrefix (P : ℕ → ℤ → ℤ) (n : ℕ) : ℤ :=
  rise P 3 0 n - rise P 2 (-1) n - rise P 2 (-2) n - rise P 2 (-3) n +
    rise P 1 (-3) n + rise P 1 (-4) n + rise P 1 (-5) n

private def highPrefix (P : ℕ → ℤ → ℤ) (n u : ℕ) : ℤ :=
  (n : ℤ) * den u + fall P 2 ((u : ℤ) - 3) n + fall P 2 ((u : ℤ) - 4) n +
    fall P 2 ((u : ℤ) - 5) n - fall P 1 ((u : ℤ) - 1) n - fall P 1 ((u : ℤ) - 2) n -
    fall P 1 ((u : ℤ) - 3) n - fall P 3 ((u : ℤ) - 6) n

/-- Sum the gate leading coefficients by evaluating the arithmetic progression endpoints. -/
def «prefix» (P : ℕ → ℤ → ℤ) (n u : ℕ) : ℤ :=
  let ell := min n (u / 3 + 1)
  lowPrefix P ell + highPrefix P n u - highPrefix P ell u

private theorem lowPrefix_eq (P : ℕ → ℤ → ℤ) (h : StepRule P) (n u : ℕ)
    (hn : n ≤ u / 3 + 1) (hu : u ≤ 1679) :
    lowPrefix P n = ∑ q ∈ Finset.range n, lowTerm q := by
  have b (a : ℕ) (ha : a ≤ 3) (c : ℤ) (hc : c ≤ 0)
      (q : ℕ) (hq : q < n) : (a : ℤ) * q + c ≤ 1679 := by
    have le : (a : ℤ) * q ≤ 3 * (q : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    omega
  unfold lowPrefix
  rw [rise_eq P h 3 (by decide) (by decide) 0 n (b 3 (by decide) 0 (by decide)),
      rise_eq P h 2 (by decide) (by decide) (-1) n (b 2 (by decide) (-1) (by decide)),
      rise_eq P h 2 (by decide) (by decide) (-2) n (b 2 (by decide) (-2) (by decide)),
      rise_eq P h 2 (by decide) (by decide) (-3) n (b 2 (by decide) (-3) (by decide)),
      rise_eq P h 1 (by decide) (by decide) (-3) n (b 1 (by decide) (-3) (by decide)),
      rise_eq P h 1 (by decide) (by decide) (-4) n (b 1 (by decide) (-4) (by decide)),
      rise_eq P h 1 (by decide) (by decide) (-5) n (b 1 (by decide) (-5) (by decide))]
  simp only [lowTerm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Nat.cast_ofNat,
    Nat.cast_one, one_mul, add_zero]
  simp only [sub_eq_add_neg]

private theorem highPrefix_eq (P : ℕ → ℤ → ℤ) (h : StepRule P) (n u : ℕ)
    (hu : u ≤ 1679) :
    highPrefix P n u = ∑ q ∈ Finset.range n, highTerm u q := by
  unfold highPrefix
  rw [fall_eq P h 2 (by decide) (by decide) _ (by omega),
      fall_eq P h 2 (by decide) (by decide) _ (by omega),
      fall_eq P h 2 (by decide) (by decide) _ (by omega),
      fall_eq P h 1 (by decide) (by decide) _ (by omega),
      fall_eq P h 1 (by decide) (by decide) _ (by omega),
      fall_eq P h 1 (by decide) (by decide) _ (by omega),
      fall_eq P h 3 (by decide) (by decide) _ (by omega)]
  simp only [highTerm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one, one_mul]
  ring_nf

private theorem sum_split (f : ℕ → ℤ) (k m : ℕ) :
    (∑ q ∈ Finset.range (k + m), f q) =
      (∑ q ∈ Finset.range k, f q) + ∑ q ∈ Finset.range m, f (k + q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, Finset.sum_range_succ (f := fun q => f (k + q)),
      ih, add_assoc]

theorem prefix_eq (P : ℕ → ℤ → ℤ) (h : StepRule P) (n u : ℕ) (hu : u ≤ 1679) :
    «prefix» P n u = Gate6966Cell.sumUpTo
      (fun q => (Gate6966Cell.cumP q u : ℤ) - Gate6966Cell.cumQ q u) n := by
  let ell := min n (u / 3 + 1)
  have he : ell ≤ n := min_le_left _ _
  have hb : ell ≤ u / 3 + 1 := min_le_right _ _
  change lowPrefix P ell + highPrefix P n u - highPrefix P ell u = _
  rw [lowPrefix_eq P h ell u hb hu, highPrefix_eq P h n u hu, highPrefix_eq P h ell u hu,
    sumUpTo_eq]
  have spl (f : ℕ → ℤ) :
      (∑ q ∈ Finset.range n, f q) =
        (∑ q ∈ Finset.range ell, f q) +
          ∑ q ∈ Finset.range (n - ell), f (ell + q) := by
    have hn : ell + (n - ell) = n := by omega
    simpa only [hn] using sum_split f ell (n - ell)
  rw [spl (highTerm u), spl (fun q => (cumP q u : ℤ) - cumQ q u)]
  have left : (∑ q ∈ Finset.range ell, (↑(cumP q u) - ↑(cumQ q u) : ℤ)) =
      ∑ q ∈ Finset.range ell, lowTerm q := by
    apply Finset.sum_congr rfl
    intro q hq
    exact lowTerm_eq q u (by have := Finset.mem_range.mp hq; omega)
  have right :
      (∑ q ∈ Finset.range (n - ell), (↑(cumP (ell + q) u) - ↑(cumQ (ell + q) u) : ℤ)) =
        ∑ q ∈ Finset.range (n - ell), highTerm u (ell + q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have bound := Finset.mem_range.mp hq
    have cut : ell = u / 3 + 1 := by
      dsimp only [ell] at *
      omega
    exact highTerm_eq _ _ (by omega)
  rw [left, right]
  ring

end Gate6970Leading

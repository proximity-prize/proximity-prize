import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Gate61Shape

-- merged module Gate61FreeArith
section Merged_Gate61FreeArith

set_option autoImplicit false

namespace Gate61FreeArith

def Vn (m c : ℕ) : ℕ :=
  bif Nat.beq (m % 2) 0 then (c - m / 2) * (m / 2 + 1) ^ 2
  else (m / 2 + 1) * (m / 2 + 2) * (2 * c - 2 * (m / 2) - 1) / 2

def freeSum (b j t : ℕ) : ℕ := ∑ e ∈ Finset.range (t + 1), Vn (j - 3 * e) (b + 1 - e)

def Ppos (b j t : ℕ) : ℕ :=
  bif Nat.beq (t % 2) 0 then
    bif Nat.beq (j % 2) 0 then 8*b*j*j*t + 8*b*j*j + 8*b*j*t + 32*b*j + 24*b*t*t*t + 32*b + 14*j*j*t*t + 6*j*j*t + 16*j*t + 16*j + 9*t*t*t*t + 26*t*t*t + 32 else 8*b*j*j*t + 8*b*j*j + 8*b*j*t + 32*b*j + 24*b*t*t*t + 24*b + 14*j*j*t*t + 6*j*j*t + 16*j*t + 20*j + 9*t*t*t*t + 26*t*t*t + 24
  else
    bif Nat.beq (j % 2) 0 then 8*b*j*j*t + 8*b*j*j + 8*b*j*t + 32*b*j + 24*b*t*t*t + 28*b + 14*j*j*t*t + 6*j*j*t + 16*j*t + 18*j + 9*t*t*t*t + 26*t*t*t + 27 else 8*b*j*j*t + 8*b*j*j + 8*b*j*t + 32*b*j + 24*b*t*t*t + 28*b + 14*j*j*t*t + 6*j*j*t + 16*j*t + 18*j + 9*t*t*t*t + 26*t*t*t + 29

def Pneg (b j t : ℕ) : ℕ :=
  bif Nat.beq (t % 2) 0 then
    bif Nat.beq (j % 2) 0 then 24*b*j*t*t + 12*b*t*t + 8*b*t + 4*j*j*j*t + 4*j*j*j + 8*j*j + 20*j*t*t*t + 22*j*t*t + 20*t*t + 8*t else 24*b*j*t*t + 12*b*t*t + 8*b*t + 4*j*j*j*t + 4*j*j*j + 8*j*j + 20*j*t*t*t + 22*j*t*t + 20*t*t + 10*t
  else
    bif Nat.beq (j % 2) 0 then 24*b*j*t*t + 12*b*t*t + 8*b*t + 4*j*j*j*t + 4*j*j*j + 8*j*j + 20*j*t*t*t + 22*j*t*t + 20*t*t + 10*t else 24*b*j*t*t + 12*b*t*t + 8*b*t + 4*j*j*j*t + 4*j*j*j + 8*j*j + 20*j*t*t*t + 22*j*t*t + 20*t*t + 8*t

theorem Vn_even (h c : ℕ) : Vn (2 * h) c = (c - h) * (h + 1) ^ 2 := by
  have h1 : (2 * h) % 2 = 0 := by omega
  have h2 : (2 * h) / 2 = h := by omega
  simp [Vn, h1, h2]

theorem Vn_odd (h c : ℕ) : Vn (2 * h + 1) c = (h + 1) * (h + 2) * (2 * c - 2 * h - 1) / 2 := by
  have h1 : (2 * h + 1) % 2 = 1 := by omega
  have h2 : (2 * h + 1) / 2 = h := by omega
  simp [Vn, h1, h2]

theorem beq_mod_true {x : ℕ} (h : x % 2 = 0) : Nat.beq (x % 2) 0 = true := by simp [h]
theorem beq_mod_false {x : ℕ} (h : x % 2 = 1) : Nat.beq (x % 2) 0 = false := by rw [h]; rfl

theorem Vn_odd_cast (h c : ℕ) (hc : h + 1 ≤ c) :
    2 * (Vn (2 * h + 1) c : ℤ) = ((h + 1) * (h + 2) * (2 * (c : ℤ) - 2 * h - 1) : ℤ) := by
  rw [Vn_odd]
  have hd : 2 ∣ (h + 1) * (h + 2) * (2 * c - 2 * h - 1) := by
    have : 2 ∣ (h + 1) * (h + 2) := by
      have := Nat.even_mul_succ_self (h + 1)
      exact even_iff_two_dvd.mp this
    exact Dvd.dvd.mul_right this _
  have h2 := Nat.mul_div_cancel' hd
  have e : ((2 * c - 2 * h - 1 : ℕ) : ℤ) = 2 * (c : ℤ) - 2 * h - 1 := by
    have : 2 * h + 1 ≤ 2 * c := by omega
    push_cast [Nat.sub_sub, Nat.cast_sub this]
    ring
  have h3 : (2 : ℤ) * (((h + 1) * (h + 2) * (2 * c - 2 * h - 1) / 2 : ℕ) : ℤ) =
      (((h + 1) * (h + 2) * (2 * c - 2 * h - 1) : ℕ) : ℤ) := by exact_mod_cast h2
  rw [h3]
  push_cast [e]
  ring

theorem step_closed (t m d : ℕ) :
    ((Ppos (3*t+3+m+d) (3*t+3+m) (t+1) : ℕ) : ℤ) - (Pneg (3*t+3+m+d) (3*t+3+m) (t+1) : ℕ) -
      ((Ppos (3*t+3+m+d) (3*t+3+m) t : ℕ) - (Pneg (3*t+3+m+d) (3*t+3+m) t : ℕ)) =
    32 * (Vn m (3*t+3+m+d - t) : ℤ) := by
  rcases Nat.even_or_odd' t with ⟨q, rfl | rfl⟩ <;> rcases Nat.even_or_odd' m with ⟨h, rfl | rfl⟩
  · -- t = 2q, m = 2h
    have a1 := beq_mod_false (x := 2*q+1) (by omega)
    have a2 := beq_mod_true (x := 2*q) (by omega)
    have a3 := beq_mod_false (x := 3*(2*q)+3+2*h) (by omega)
    have e5 : (3*(2*q)+3+2*h+d - 2*q) = 4*q+3+2*h+d := by omega
    have e6 : 4*q+3+2*h+d - h = 4*q+3+h+d := by omega
    simp only [Ppos, Pneg, Vn_even, a1, a2, a3, e5, e6, Bool.cond_true, Bool.cond_false]
    push_cast
    ring
  · -- t = 2q, m = 2h+1
    have a1 := beq_mod_false (x := 2*q+1) (by omega)
    have a2 := beq_mod_true (x := 2*q) (by omega)
    have a3 := beq_mod_true (x := 3*(2*q)+3+(2*h+1)) (by omega)
    have e5 : (3*(2*q)+3+(2*h+1)+d - 2*q) = 4*q+4+2*h+d := by omega
    have hX := Vn_odd_cast h (3*(2*q)+3+(2*h+1)+d - 2*q) (by omega)
    rw [e5] at hX ⊢
    simp only [Ppos, Pneg, a1, a2, a3, Bool.cond_true, Bool.cond_false]
    push_cast at hX ⊢
    linear_combination (-16) * hX
  · -- t = 2q+1, m = 2h
    have a1 := beq_mod_true (x := 2*q+1+1) (by omega)
    have a2 := beq_mod_false (x := 2*q+1) (by omega)
    have a3 := beq_mod_true (x := 3*(2*q+1)+3+2*h) (by omega)
    have e5 : (3*(2*q+1)+3+2*h+d - (2*q+1)) = 4*q+5+2*h+d := by omega
    have e6 : 4*q+5+2*h+d - h = 4*q+5+h+d := by omega
    simp only [Ppos, Pneg, Vn_even, a1, a2, a3, e5, e6, Bool.cond_true, Bool.cond_false]
    push_cast
    ring
  · -- t = 2q+1, m = 2h+1
    have a1 := beq_mod_true (x := 2*q+1+1) (by omega)
    have a2 := beq_mod_false (x := 2*q+1) (by omega)
    have a3 := beq_mod_false (x := 3*(2*q+1)+3+(2*h+1)) (by omega)
    have e5 : (3*(2*q+1)+3+(2*h+1)+d - (2*q+1)) = 4*q+6+2*h+d := by omega
    have hX := Vn_odd_cast h (3*(2*q+1)+3+(2*h+1)+d - (2*q+1)) (by omega)
    rw [e5] at hX ⊢
    simp only [Ppos, Pneg, a1, a2, a3, Bool.cond_true, Bool.cond_false]
    push_cast at hX ⊢
    linear_combination (-16) * hX

theorem base_closed (j d : ℕ) :
    ((Ppos (j+d) j 0 : ℕ) : ℤ) - (Pneg (j+d) j 0 : ℕ) = 32 * (Vn j (j+d+1) : ℤ) := by
  rcases Nat.even_or_odd' j with ⟨h, rfl | rfl⟩
  · have a2 := beq_mod_true (x := 0) (by omega)
    have a3 := beq_mod_true (x := 2*h) (by omega)
    have e6 : 2*h+d+1 - h = h+d+1 := by omega
    simp only [Ppos, Pneg, Vn_even, a2, a3, Nat.zero_mod, e6, Bool.cond_true, Bool.cond_false, Nat.beq]
    push_cast
    ring
  · have a2 := beq_mod_true (x := 0) (by omega)
    have a3 := beq_mod_false (x := 2*h+1) (by omega)
    have hX := Vn_odd_cast h (2*h+1+d+1) (by omega)
    simp only [Ppos, Pneg, a2, a3, Nat.zero_mod, Bool.cond_true, Bool.cond_false, Nat.beq]
    push_cast at hX ⊢
    linear_combination (-16) * hX

theorem freeSum_closed (b j : ℕ) (hb : j ≤ b) :
    ∀ t, 3 * t ≤ j → 32 * freeSum b j t + Pneg b j t = Ppos b j t := by
  intro t
  induction t with
  | zero =>
    intro _
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have := base_closed j d
    have h0 : freeSum (j+d) j 0 = Vn j (j+d+1) := by simp [freeSum]
    rw [h0]
    zify
    linarith
  | succ t ih =>
    intro h3
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 3 * t + 3 ≤ j by omega)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have ih' := ih (by omega)
    have st := step_closed t m d
    have e1 : 3 * t + 3 + m - 3 * (t + 1) = m := by omega
    have e2 : 3 * t + 3 + m + d + 1 - (t + 1) = 3 * t + 3 + m + d - t := by omega
    have hs : freeSum (3*t+3+m+d) (3*t+3+m) (t+1) =
        freeSum (3*t+3+m+d) (3*t+3+m) t + Vn m (3*t+3+m+d - t) := by
      unfold freeSum
      rw [Finset.sum_range_succ _ (t+1), e1, e2]
    rw [hs]
    zify at ih' ⊢
    push_cast at st
    linarith

end Gate61FreeArith

end Merged_Gate61FreeArith

-- merged module Gate61FreeCard
section Merged_Gate61FreeCard

set_option autoImplicit false

namespace Gate61FreeCard
open Gate61FreeArith Gate61Shape Finset

theorem tri (k c : ℕ) (h : k ≤ c) :
    2 * (∑ e ∈ range (k + 1), ((c - e : ℕ) : ℤ)) = (k + 1) * (2 * c - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih (by omega)]
    have : ((c - (k + 1) : ℕ) : ℤ) = c - (k + 1) := by push_cast [Nat.cast_sub h]; ring
    rw [this]; push_cast; ring

theorem inner (m c : ℕ) (h : m ≤ c) :
    ((∑ e2 ∈ range (m / 2 + 1), ∑ e1 ∈ range (m - 2 * e2 + 1), (c - e2 - e1) : ℕ) : ℤ) * 2 =
      (2 * c - m) * ((m / 2 + 1) * (m + 1 - m / 2) : ℕ) := by
  have key : ∀ H : ℕ, H ≤ m / 2 + 1 →
      ((∑ e2 ∈ range H, ∑ e1 ∈ range (m - 2 * e2 + 1), (c - e2 - e1) : ℕ) : ℤ) * 2 =
        (2 * c - m) * ((H : ℤ) * (m + 1) - H * (H - 1)) := by
    intro H
    induction H with
    | zero => intro _; simp
    | succ H ih =>
      intro hH
      rw [sum_range_succ, Nat.cast_add, add_mul, ih (by omega)]
      have h2 := tri (m - 2 * H) (c - H) (by omega)
      have h3 : ((∑ e1 ∈ range (m - 2 * H + 1), (c - H - e1) : ℕ) : ℤ) =
          ∑ e1 ∈ range (m - 2 * H + 1), (((c - H) - e1 : ℕ) : ℤ) := by push_cast; rfl
      rw [h3, mul_comm _ (2:ℤ), h2]
      have hH2 : 2 * H ≤ m := by omega
      have e1 : ((m - 2 * H : ℕ) : ℤ) = m - 2 * H := by push_cast [Nat.cast_sub hH2]; ring
      have e2 : ((c - H : ℕ) : ℤ) = c - H := by push_cast [Nat.cast_sub (show H ≤ c by omega)]; ring
      rw [e1, e2]
      push_cast
      ring
  have := key (m / 2 + 1) le_rfl
  rw [this]
  have hle : m / 2 ≤ m + 1 := by omega
  push_cast [Nat.cast_sub hle]
  ring

theorem Vn_inner (m c : ℕ) (h : m ≤ c) :
    (∑ e2 ∈ range (m / 2 + 1), ∑ e1 ∈ range (m - 2 * e2 + 1), (c - e2 - e1)) = Vn m c := by
  have h1 := inner m c h
  rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
  · have hq : 2 * q / 2 = q := by omega
    rw [hq] at h1 ⊢
    rw [Vn_even]
    have e : 2 * q + 1 - q = q + 1 := by omega
    rw [e] at h1
    have e2 : ((c - q : ℕ) : ℤ) = c - q := by push_cast [Nat.cast_sub (show q ≤ c by omega)]; ring
    have : (((∑ e2 ∈ range (q + 1), ∑ e1 ∈ range (2 * q - 2 * e2 + 1), (c - e2 - e1) : ℕ) : ℤ)) =
        (((c - q) * (q + 1) ^ 2 : ℕ) : ℤ) := by
      push_cast [e2]
      push_cast at h1
      linarith
    exact_mod_cast this
  · have hq : (2 * q + 1) / 2 = q := by omega
    rw [hq] at h1 ⊢
    rw [Vn_odd]
    have hX := Vn_odd_cast q c (by omega)
    rw [Vn_odd] at hX
    have e : 2 * q + 1 + 1 - q = q + 2 := by omega
    rw [e] at h1
    have : (((∑ e2 ∈ range (q + 1), ∑ e1 ∈ range (2 * q + 1 - 2 * e2 + 1), (c - e2 - e1) : ℕ) : ℤ)) =
        (((q + 1) * (q + 2) * (2 * c - 2 * q - 1) / 2 : ℕ) : ℤ) := by
      push_cast at h1 hX ⊢
      push_cast at hX
      linarith
    exact_mod_cast this

theorem free_le_sum (b j t : ℕ) (h3 : 3 * t ≤ j) (hb : j ≤ b) :
    free ![b, j, t] ≤ freeSum b j t := by
  classical
  let S : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (range (t + 1)).sigma fun e3 => (range ((j - 3 * e3) / 2 + 1)).sigma fun e2 =>
      (range (j - 3 * e3 - 2 * e2 + 1)).sigma fun e1 => range (b + 1 - (e1 + e2 + e3))
  have hcard : S.card = freeSum b j t := by
    simp only [S, card_sigma, card_range]
    unfold freeSum
    apply sum_congr rfl
    intro e3 he3
    have he := mem_range.mp he3
    rw [← Vn_inner _ _ (by omega)]
    apply sum_congr rfl
    intro e2 he2
    have := mem_range.mp he2
    apply sum_congr rfl
    intro e1 he1
    have := mem_range.mp he1
    omega
  rw [← hcard]
  unfold free
  apply card_le_card_of_injOn (fun m : Fin 4 →₀ ℕ => (⟨m 3, m 2, m 1, m 0⟩ : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ))
  · intro m hm
    have hm' := (freeSet_finite ![b, j, t]).mem_toFinset.mp (by simpa using hm)
    have w0 := hm' 0
    have w1 := hm' 1
    have w2 := hm' 2
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, wv, Fin.sum_univ_four, Pi.single_apply] at w0 w1 w2
    simp only [Finset.mem_coe, S, mem_sigma, mem_range]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · intro m _ m' _ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true] at h
    obtain ⟨h3, h2, h1, h0⟩ := h
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]

def mn (a b : ℕ) : ℕ := bif Nat.ble a b then a else b
def mx (a b : ℕ) : ℕ := bif Nat.ble a b then b else a

theorem mn_eq (a b : ℕ) : mn a b = min a b := by
  unfold mn
  cases h : Nat.ble a b with
  | true => simp [Nat.le_of_ble_eq_true h]
  | false =>
    have : ¬ a ≤ b := fun hh => by simp [Nat.ble_eq_true_of_le hh] at h
    simp only [Bool.cond_false]; omega
theorem mx_eq (a b : ℕ) : mx a b = max a b := by
  unfold mx
  cases h : Nat.ble a b with
  | true => simp [Nat.le_of_ble_eq_true h]
  | false =>
    have : ¬ a ≤ b := fun hh => by simp [Nat.ble_eq_true_of_le hh] at h
    simp only [Bool.cond_false]; omega

def freeC (b j t : ℕ) : ℕ := (Ppos (mx b j) j (mn t (j / 3)) - Pneg (mx b j) j (mn t (j / 3))) / 32

theorem free_mono {Y Y' : Fin 3 → ℕ} (h : ∀ i, Y i ≤ Y' i) : free Y ≤ free Y' := by
  unfold free
  apply card_le_card
  intro m hm
  have hm' := (freeSet_finite Y).mem_toFinset.mp hm
  exact (freeSet_finite Y').mem_toFinset.mpr fun i => (hm' i).trans (h i)

theorem free_le_freeC (Y : Fin 3 → ℕ) : free Y ≤ freeC (Y 0) (Y 1) (Y 2) := by
  have h1 : free Y ≤ free ![max (Y 0) (Y 1), Y 1, min (Y 2) (Y 1 / 3)] := by
    unfold free
    apply card_le_card
    intro m hm
    have hm' := (freeSet_finite Y).mem_toFinset.mp hm
    apply (freeSet_finite _).mem_toFinset.mpr
    intro i
    have w1 := hm' 1
    have w2 := hm' 2
    have w0 := hm' 0
    have t3 : m.weight (wv 1) ≥ 3 * m.weight (wv 2) := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, wv, Fin.sum_univ_four, Pi.single_apply]; omega
    fin_cases i
    · exact w0.trans (le_max_left _ _)
    · exact w1
    · show m.weight (wv 2) ≤ min (Y 2) (Y 1 / 3)
      exact le_min w2 (by omega)
  have h2 := free_le_sum (max (Y 0) (Y 1)) (Y 1) (min (Y 2) (Y 1 / 3)) (by have := Nat.min_le_right (Y 2) (Y 1 / 3); omega) (le_max_right _ _)
  have h3 := freeSum_closed (max (Y 0) (Y 1)) (Y 1) (le_max_right _ _) (min (Y 2) (Y 1 / 3)) (by have := Nat.min_le_right (Y 2) (Y 1 / 3); omega)
  unfold freeC
  rw [mx_eq, mn_eq]
  omega

end Gate61FreeCard

end Merged_Gate61FreeCard

-- merged module Gate61FreeU3
section Merged_Gate61FreeU3

set_option autoImplicit false

namespace Gate61FreeU3
open Gate61Shape Finset Gate61FreeCard

theorem inner3 (n e2 : ℕ) (h : e2 ≤ n) :
    2 * (∑ e1 ∈ range (n - e2 + 1), (n + 1 - (e1 + e2))) = (n - e2 + 1) * (n - e2 + 2) := by
  have key : ∀ k : ℕ, 2 * (∑ e1 ∈ range (k + 1), (k + 1 - e1)) = (k + 1) * (k + 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : ∑ e1 ∈ range (k + 1 + 1), (k + 1 + 1 - e1) = (k + 1 + 1) + ∑ e1 ∈ range (k + 1), (k + 1 - e1) := by
        rw [sum_range_succ', Nat.sub_zero]
        have : ∀ i ∈ range (k + 1), k + 1 + 1 - (i + 1) = k + 1 - i := fun i _ => by omega
        rw [sum_congr rfl this]; ring
      rw [this]; nlinarith [ih]
  have := key (n - e2)
  rw [← this]
  congr 1
  refine sum_congr rfl fun e1 he => ?_
  have := mem_range.mp he
  omega

def S3 (n : ℕ) : ℕ := ∑ e2 ∈ range (n + 1), ∑ e1 ∈ range (n - e2 + 1), (n + 1 - (e1 + e2))

theorem tet (n : ℕ) : 6 * S3 n = (n + 1) * (n + 2) * (n + 3) := by
  unfold S3
  have h : ∀ e2 ∈ range (n + 1), 2 * (∑ e1 ∈ range (n - e2 + 1), (n + 1 - (e1 + e2))) = (n - e2 + 1) * (n - e2 + 2) :=
    fun e2 he => inner3 n e2 (by have := mem_range.mp he; omega)
  have h2 : 2 * (∑ e2 ∈ range (n + 1), ∑ e1 ∈ range (n - e2 + 1), (n + 1 - (e1 + e2))) =
      ∑ e2 ∈ range (n + 1), (n - e2 + 1) * (n - e2 + 2) := by
    rw [mul_sum]; exact sum_congr rfl h
  have h3 : ∑ e2 ∈ range (n + 1), (n - e2 + 1) * (n - e2 + 2) = ∑ i ∈ range (n + 1), (i + 1) * (i + 2) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    have : n + 1 - 1 - i = n - i := by omega
    rw [this]
    have : n - (n - i) = i := by omega
    rw [this]
  have h4 : ∀ m : ℕ, 3 * (∑ i ∈ range (m + 1), (i + 1) * (i + 2)) = (m + 1) * (m + 2) * (m + 3) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, mul_add, ih]; ring
  have := h4 n
  omega

def Qn (b t : ℕ) : ℕ := (b - t) * (b - t + 1) * (b - t + 2) * (b - t + 3)

theorem sumQ (b : ℕ) : ∀ t, t ≤ b →
    24 * (∑ e3 ∈ range (t + 1), S3 (b - e3)) + Qn b t = (b + 1) * (b + 2) * (b + 3) * (b + 4) := by
  intro t
  induction t with
  | zero =>
    intro _
    have := tet b
    simp only [Qn, zero_add, range_one, sum_singleton, Nat.sub_zero, Nat.add_zero]
    nlinarith [this]
  | succ t ih =>
    intro h
    have ih' := ih (by omega)
    have h6 := tet (b - (t + 1))
    rw [sum_range_succ]
    unfold Qn at *
    have e1 : b - t = (b - (t + 1)) + 1 := by omega
    rw [e1] at ih'
    have : b - (t + 1) + 1 + 1 = b - (t + 1) + 2 := rfl
    nlinarith [ih', h6]

def U3 (b t : ℕ) : ℕ :=
  ((b + 1) * (b + 2) * (b + 3) * (b + 4) - Qn b (mn t b)) / 24

theorem free_le_U3 (Y : Fin 3 → ℕ) : free Y ≤ U3 (Y 0) (Y 2) := by
  classical
  set b := Y 0
  set t := Y 2
  have ht : mn t b = min t b := mn_eq t b
  let S : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (range (min t b + 1)).sigma fun e3 => (range (b - e3 + 1)).sigma fun e2 =>
      (range (b - e3 - e2 + 1)).sigma fun e1 => range (b + 1 - (e1 + e2 + e3))
  have hcard : S.card = ∑ e3 ∈ range (min t b + 1), S3 (b - e3) := by
    simp only [S, card_sigma, card_range]
    apply sum_congr rfl
    intro e3 he3
    have he := mem_range.mp he3
    unfold S3
    apply sum_congr rfl
    intro e2 he2
    have := mem_range.mp he2
    apply sum_congr rfl
    intro e1 he1
    have := mem_range.mp he1
    omega
  have hle : free Y ≤ S.card := by
    unfold free
    apply card_le_card_of_injOn (fun m : Fin 4 →₀ ℕ => (⟨m 3, m 2, m 1, m 0⟩ : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ))
    · intro m hm
      have hm' := (freeSet_finite Y).mem_toFinset.mp (by simpa using hm)
      have w0 := hm' 0
      have w2 := hm' 2
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, wv, Fin.sum_univ_four, Pi.single_apply] at w0 w2
      simp only [Finset.mem_coe, S, mem_sigma, mem_range]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · intro m _ m' _ h
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨h3, h2, h1, h0⟩ := h
      ext i
      fin_cases i <;> simp [h0, h1, h2, h3]
  have hq := sumQ b (min t b) (min_le_right _ _)
  rw [hcard] at hle
  unfold U3
  rw [ht]
  unfold Qn at hq ⊢
  omega

def freeD (b j t : ℕ) : ℕ := mn (freeC b j t) (U3 b t)

theorem free_le_freeD (Y : Fin 3 → ℕ) : free Y ≤ freeD (Y 0) (Y 1) (Y 2) := by
  unfold freeD; rw [mn_eq]; exact le_min (free_le_freeC Y) (free_le_U3 Y)

end Gate61FreeU3

end Merged_Gate61FreeU3

-- merged module Gate61Cell
section Merged_Gate61Cell

set_option autoImplicit false

namespace Gate61Cell
open Gate61FreeCard (mn mx mn_eq mx_eq free_mono)
open Gate61FreeU3 (freeD free_le_freeD)

structure Gt where
  m00 : ℕ
  m01 : ℕ
  m02 : ℕ
  m11 : ℕ
  m12 : ℕ
  m22 : ℕ
  xb : ℕ
  xj : ℕ
  xt : ℕ
  lb : ℕ
  lj : ℕ
  lt : ℕ
  A : ℕ
  sc : ℕ
  lift : Bool

def Gt.Ok (G : Gt) : Prop :=
  G.m00 ≤ G.m01 ∧ 3 * G.m01 ≤ G.m02 ∧ G.m01 ≤ G.m11 ∧ 3 * G.m11 ≤ G.m12 ∧ G.m02 ≤ G.m12 ∧ 3 * G.m12 ≤ G.m22

def hB (l : Bool) (yb yj : ℕ) : ℕ := bif l then mx (mx yb yj) (mx yj 3) else mx yb yj
def hJ (l : Bool) (yj : ℕ) : ℕ := bif l then mx yj 3 else yj
def hT (l : Bool) (yj yt : ℕ) : ℕ := bif l then mx (mn yt (yj / 3)) 1 else mn yt (yj / 3)

def TT (G : Gt) (ub uj ut vb vj vt : ℕ) : ℕ :=
  (ub - uj) * ((vb - vj) * G.m00 + (vj - 3 * vt) * G.m01 + vt * G.m02) +
  (uj - 3 * ut) * ((vb - vj) * G.m01 + (vj - 3 * vt) * G.m11 + vt * G.m12) +
  ut * ((vb - vj) * G.m02 + (vj - 3 * vt) * G.m12 + vt * G.m22)

def Cone (b j t : ℕ) : Prop := j ≤ b ∧ 3 * t ≤ j

theorem TT_symm (G : Gt) (ub uj ut vb vj vt : ℕ) : TT G ub uj ut vb vj vt = TT G vb vj vt ub uj ut := by
  unfold TT; ring

theorem TT_mono_left (G : Gt) (hG : G.Ok) {ub uj ut ub' uj' ut' vb vj vt : ℕ}
    (hu : Cone ub uj ut) (hu' : Cone ub' uj' ut') (hv : Cone vb vj vt)
    (h0 : ub ≤ ub') (h1 : uj ≤ uj') (h2 : ut ≤ ut') :
    TT G ub uj ut vb vj vt ≤ TT G ub' uj' ut' vb vj vt := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hG
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hu1', hu2'⟩ := hu'
  obtain ⟨hv1, hv2⟩ := hv
  unfold TT
  have q1 : 3 * vt ≤ vb := by omega
  have q2 : 3 * ut ≤ ub := by omega
  have q3 : 3 * ut' ≤ ub' := by omega
  zify [hu1, hu2, hu1', hu2', hv1, hv2, q1, q2, q3]
  have p0 : 0 ≤ (vb : ℤ) - vj := by omega
  have p1 : 0 ≤ (vj : ℤ) - 3 * vt := by omega
  set n0 : ℤ := (vb : ℤ) - vj
  set n1 : ℤ := (vj : ℤ) - 3 * vt
  have p2 : (0 : ℤ) ≤ vt := by positivity
  have c1 : (0 : ℤ) ≤ n0 * (G.m01 - G.m00) + n1 * (G.m11 - G.m01) + vt * (G.m12 - G.m02) := by
    have := mul_nonneg p0 (sub_nonneg.mpr (Int.ofNat_le.mpr a1 : (G.m00 : ℤ) ≤ G.m01))
    have := mul_nonneg p1 (sub_nonneg.mpr (Int.ofNat_le.mpr a3 : (G.m01 : ℤ) ≤ G.m11))
    have := mul_nonneg p2 (sub_nonneg.mpr (Int.ofNat_le.mpr a5 : (G.m02 : ℤ) ≤ G.m12))
    linarith
  have c2 : (0 : ℤ) ≤ n0 * (G.m02 - 3 * G.m01) + n1 * (G.m12 - 3 * G.m11) + vt * (G.m22 - 3 * G.m12) := by
    have := mul_nonneg p0 (sub_nonneg.mpr (by exact_mod_cast a2 : (3 * G.m01 : ℤ) ≤ G.m02))
    have := mul_nonneg p1 (sub_nonneg.mpr (by exact_mod_cast a4 : (3 * G.m11 : ℤ) ≤ G.m12))
    have := mul_nonneg p2 (sub_nonneg.mpr (by exact_mod_cast a6 : (3 * G.m12 : ℤ) ≤ G.m22))
    linarith
  have c0 : (0 : ℤ) ≤ n0 * G.m00 + n1 * G.m01 + vt * G.m02 := by positivity
  have d0 : (ub : ℤ) ≤ ub' := by exact_mod_cast h0
  have d1 : (uj : ℤ) ≤ uj' := by exact_mod_cast h1
  have d2 : (ut : ℤ) ≤ ut' := by exact_mod_cast h2
  have key : (ub' - ub : ℤ) * (n0 * G.m00 + n1 * G.m01 + vt * G.m02) +
      (uj' - uj : ℤ) * (n0 * (G.m01 - G.m00) + n1 * (G.m11 - G.m01) + vt * (G.m12 - G.m02)) +
      (ut' - ut : ℤ) * (n0 * (G.m02 - 3 * G.m01) + n1 * (G.m12 - 3 * G.m11) + vt * (G.m22 - 3 * G.m12)) ≥ 0 := by
    have := mul_nonneg (sub_nonneg.mpr d0) c0
    have := mul_nonneg (sub_nonneg.mpr d1) c1
    have := mul_nonneg (sub_nonneg.mpr d2) c2
    linarith
  nlinarith [key]

theorem TT_mono (G : Gt) (hG : G.Ok) {ub uj ut ub' uj' ut' vb vj vt vb' vj' vt' : ℕ}
    (hu : Cone ub uj ut) (hu' : Cone ub' uj' ut') (hv : Cone vb vj vt) (hv' : Cone vb' vj' vt')
    (h0 : ub ≤ ub') (h1 : uj ≤ uj') (h2 : ut ≤ ut') (g0 : vb ≤ vb') (g1 : vj ≤ vj') (g2 : vt ≤ vt') :
    TT G ub uj ut vb vj vt ≤ TT G ub' uj' ut' vb' vj' vt' := by
  refine (TT_mono_left G hG hu hu' hv h0 h1 h2).trans ?_
  rw [TT_symm G ub' uj' ut' vb vj vt, TT_symm G ub' uj' ut' vb' vj' vt']
  exact TT_mono_left G hG hv hv' hu' g0 g1 g2

theorem hB_mono (l : Bool) {yb yj yb' yj' : ℕ} (h0 : yb ≤ yb') (h1 : yj ≤ yj') : hB l yb yj ≤ hB l yb' yj' := by
  unfold hB; cases l <;> simp only [Bool.cond_true, Bool.cond_false, mx_eq] <;> omega
theorem hJ_mono (l : Bool) {yj yj' : ℕ} (h1 : yj ≤ yj') : hJ l yj ≤ hJ l yj' := by
  unfold hJ; cases l <;> simp only [Bool.cond_true, Bool.cond_false, mx_eq] <;> omega
theorem hT_mono (l : Bool) {yj yt yj' yt' : ℕ} (h1 : yj ≤ yj') (h2 : yt ≤ yt') : hT l yj yt ≤ hT l yj' yt' := by
  unfold hT; cases l <;> simp only [Bool.cond_true, Bool.cond_false, mx_eq, mn_eq] <;> omega
theorem hull_cone (l : Bool) (yb yj yt : ℕ) : Cone (hB l yb yj) (hJ l yj) (hT l yj yt) := by
  unfold Cone hB hJ hT; cases l <;> simp only [Bool.cond_true, Bool.cond_false, mx_eq, mn_eq] <;> omega

structure Pr where
  t0 : ℕ
  t1 : ℕ
  t2 : ℕ
  W : ℕ
  rhs : ℕ
  m00 : ℕ
  m01 : ℕ
  m02 : ℕ
  m11 : ℕ
  m12 : ℕ
  m22 : ℕ
  q00 : ℕ
  q01 : ℕ
  q02 : ℕ
  q10 : ℕ
  q11 : ℕ
  q12 : ℕ
  q20 : ℕ
  q21 : ℕ
  q22 : ℕ
  w0 : ℕ
  w1 : ℕ
  w2 : ℕ
  v0 : ℕ
  v1 : ℕ
  v2 : ℕ
  c0 : ℕ
  lift : Bool

def VD : ℕ := 10000000

def Gt.xh (G : Gt) : ℕ × ℕ × ℕ := (mx G.xb G.xj, G.xj, G.xt)

def Gt.wx0 (G : Gt) : ℕ := (mx G.xb G.xj - G.xj) * G.m00 + (G.xj - 3 * G.xt) * G.m01 + G.xt * G.m02
def Gt.wx1 (G : Gt) : ℕ := (mx G.xb G.xj - G.xj) * G.m01 + (G.xj - 3 * G.xt) * G.m11 + G.xt * G.m12
def Gt.wx2 (G : Gt) : ℕ := (mx G.xb G.xj - G.xj) * G.m02 + (G.xj - 3 * G.xt) * G.m12 + G.xt * G.m22

def Gt.sep (G : Gt) : ℕ × ℕ × ℕ := (hB G.lift (G.xb - 1) (G.xj - 3), hJ G.lift (G.xj - 3), hT G.lift (G.xj - 3) (G.xt - 1))
def Gt.tsep (G : Gt) : ℕ := TT G (mx G.xb G.xj) G.xj G.xt G.sep.1 G.sep.2.1 G.sep.2.2

def mkPr (G : Gt) (r a cn vn W B0 B1 B2 : ℕ) : Pr :=
  let ρ := r - a
  let k1 := (2 * ρ - cn) * VD
  let k2 := 2 * ρ * VD
  let k3 := 2 * ρ * ρ * VD
  let k4 := cn * ρ * VD
  let k5 := 2 * vn * ρ * ρ * ρ
  { t0 := B0 - a * G.lb, t1 := B1 - a * G.lj, t2 := B2 - a * G.lt, W := W
    rhs := G.sc * G.A * (2 * ρ * ρ * ρ) * VD
    m00 := k1 * G.m00, m01 := 2 * k1 * G.m01, m02 := 2 * k1 * G.m02
    m11 := k1 * G.m11, m12 := 2 * k1 * G.m12, m22 := k1 * G.m22
    q00 := k2 * G.m00, q01 := k2 * G.m01, q02 := k2 * G.m02
    q10 := k2 * G.m01, q11 := k2 * G.m11, q12 := k2 * G.m12
    q20 := k2 * G.m02, q21 := k2 * G.m12, q22 := k2 * G.m22
    w0 := k3 * G.wx0, w1 := k3 * G.wx1, w2 := k3 * G.wx2
    v0 := k4 * G.wx0, v1 := k4 * G.wx1, v2 := k4 * G.wx2
    c0 := k5 * G.tsep, lift := G.lift }

def lhsV (P : Pr) (yb yj yt hb hj ht : ℕ) : ℕ :=
  let a0 := hB P.lift yb yj - hJ P.lift yj
  let a1 := hJ P.lift yj - 3 * hT P.lift yj yt
  let a2 := hT P.lift yj yt
  let e0 := hB P.lift hb hj - hJ P.lift hj
  let e1 := hJ P.lift hj - 3 * hT P.lift hj ht
  let e2 := hT P.lift hj ht
  a0 * (P.m00 * a0 + P.m01 * a1 + P.m02 * a2) + a1 * (P.m11 * a1 + P.m12 * a2) + P.m22 * a2 * a2 +
  e0 * (P.q00 * a0 + P.q01 * a1 + P.q02 * a2) + e1 * (P.q10 * a0 + P.q11 * a1 + P.q12 * a2) +
  e2 * (P.q20 * a0 + P.q21 * a1 + P.q22 * a2) +
  P.w0 * e0 + P.w1 * e1 + P.w2 * e2 + P.v0 * a0 + P.v1 * a1 + P.v2 * a2 + P.c0

def LS (G : Gt) (ρ cn vn yb yj yt hb hj ht : ℕ) : ℕ :=
  (2 * ρ - cn) * VD * TT G (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
  2 * ρ * VD * TT G (hB G.lift hb hj) (hJ G.lift hj) (hT G.lift hj ht) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
  2 * ρ * ρ * VD * TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift hb hj) (hJ G.lift hj) (hT G.lift hj ht) +
  cn * ρ * VD * TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
  2 * vn * ρ * ρ * ρ * G.tsep

theorem lhsV_eq (G : Gt) (r a cn vn W B0 B1 B2 yb yj yt hb hj ht : ℕ) :
    lhsV (mkPr G r a cn vn W B0 B1 B2) yb yj yt hb hj ht = LS G (r - a) cn vn yb yj yt hb hj ht := by
  simp only [lhsV, mkPr, LS, TT, Gt.wx0, Gt.wx1, Gt.wx2]
  ring

theorem LS_mono (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (ρ cn vn : ℕ) {yb yj yt hb hj ht yb' yj' yt' hb' hj' ht' : ℕ}
    (a0 : yb ≤ yb') (a1 : yj ≤ yj') (a2 : yt ≤ yt') (b0 : hb ≤ hb') (b1 : hj ≤ hj') (b2 : ht ≤ ht') :
    LS G ρ cn vn yb yj yt hb hj ht ≤ LS G ρ cn vn yb' yj' yt' hb' hj' ht' := by
  have cY := hull_cone G.lift yb yj yt
  have cY' := hull_cone G.lift yb' yj' yt'
  have cE := hull_cone G.lift hb hj ht
  have cE' := hull_cone G.lift hb' hj' ht'
  have cX : Cone (mx G.xb G.xj) G.xj G.xt := ⟨by rw [mx_eq]; exact le_max_right _ _, hx⟩
  have mY0 := hB_mono G.lift a0 a1
  have mY1 := hJ_mono G.lift a1
  have mY2 := hT_mono G.lift a1 a2
  have mE0 := hB_mono G.lift b0 b1
  have mE1 := hJ_mono G.lift b1
  have mE2 := hT_mono G.lift b1 b2
  unfold LS
  have t1 := TT_mono G hG cY cY' cY cY' mY0 mY1 mY2 mY0 mY1 mY2
  have t2 := TT_mono G hG cE cE' cY cY' mE0 mE1 mE2 mY0 mY1 mY2
  have t3 := TT_mono G hG cX cX cE cE' le_rfl le_rfl le_rfl mE0 mE1 mE2
  have t4 := TT_mono G hG cX cX cY cY' le_rfl le_rfl le_rfl mY0 mY1 mY2
  have := Nat.mul_le_mul_left ((2 * ρ - cn) * VD) t1
  have := Nat.mul_le_mul_left (2 * ρ * VD) t2
  have := Nat.mul_le_mul_left (2 * ρ * ρ * VD) t3
  have := Nat.mul_le_mul_left (cn * ρ * VD) t4
  omega

def cell (P : Pr) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _ => false
  | f + 1, l0, l1, l2, h0, h1, h2 =>
    bif Nat.blt (mn h2 (mn (h1 / 3) h0)) l2 || Nat.blt (2 * h0 + mn h2 (mn (h1 / 3) h0)) l1 then true
    else bif Nat.ble (freeD (P.t0 - l0) (P.t1 - l1) (P.t2 - l2)) P.W then true
    else bif Nat.ble (lhsV P (P.t0 - l0) (P.t1 - l1) (P.t2 - l2) h0 h1 h2) P.rhs then true
    else bif Nat.beq l0 h0 && Nat.beq l1 h1 && Nat.beq l2 h2 then false
    else bif Nat.ble (h1 - l1) (h0 - l0) && Nat.ble (h2 - l2) (h0 - l0) then
      cell P f l0 l1 l2 ((l0 + h0) / 2) h1 h2 && cell P f ((l0 + h0) / 2 + 1) l1 l2 h0 h1 h2
    else bif Nat.ble (h2 - l2) (h1 - l1) then
      cell P f l0 l1 l2 h0 ((l1 + h1) / 2) h2 && cell P f l0 ((l1 + h1) / 2 + 1) l2 h0 h1 h2
    else
      cell P f l0 l1 l2 h0 h1 ((l2 + h2) / 2) && cell P f l0 l1 ((l2 + h2) / 2 + 1) h0 h1 h2

def Valid (e0 e1 e2 : ℕ) : Prop := e2 ≤ e0 ∧ 3 * e2 ≤ e1 ∧ e1 ≤ 2 * e0 + e2

theorem cell_sound (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (r a cn vn W B0 B1 B2 : ℕ) :
    ∀ (fuel l0 l1 l2 h0 h1 h2 : ℕ),
      cell (mkPr G r a cn vn W B0 B1 B2) fuel l0 l1 l2 h0 h1 h2 = true →
      ∀ e0 e1 e2 : ℕ, l0 ≤ e0 → e0 ≤ h0 → l1 ≤ e1 → e1 ≤ h1 → l2 ≤ e2 → e2 ≤ h2 → Valid e0 e1 e2 →
        Gate61Shape.free ![B0 - a * G.lb - e0, B1 - a * G.lj - e1, B2 - a * G.lt - e2] ≤ W ∨
        lhsV (mkPr G r a cn vn W B0 B1 B2) (B0 - a * G.lb - e0) (B1 - a * G.lj - e1) (B2 - a * G.lt - e2) e0 e1 e2 ≤
          (mkPr G r a cn vn W B0 B1 B2).rhs := by
  intro fuel
  induction fuel with
  | zero => intro l0 l1 l2 h0 h1 h2 h; simp [cell] at h
  | succ f ih =>
    intro l0 l1 l2 h0 h1 h2 h e0 e1 e2 a0 a1 b0 b1 c0 c1 hv
    obtain ⟨v1, v2, v3⟩ := hv
    set P := mkPr G r a cn vn W B0 B1 B2 with hP
    have hpt0 : P.t0 = B0 - a * G.lb := rfl
    have hpt1 : P.t1 = B1 - a * G.lj := rfl
    have hpt2 : P.t2 = B2 - a * G.lt := rfl
    rw [← hpt0, ← hpt1, ← hpt2]
    unfold cell at h
    simp only [Bool.cond_eq_ite, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq,
      mn_eq] at h
    split_ifs at h with k1 k2 k3 k4 k5 k6
    · exfalso
      rcases k1 with k1 | k1 <;> omega
    · left
      have := free_le_freeD ![P.t0 - l0, P.t1 - l1, P.t2 - l2]
      have hm : Gate61Shape.free ![P.t0 - e0, P.t1 - e1, P.t2 - e2] ≤
          Gate61Shape.free ![P.t0 - l0, P.t1 - l1, P.t2 - l2] := by
        apply Gate61FreeCard.free_mono
        intro i; fin_cases i <;> simp <;> omega
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
      exact hm.trans (this.trans k2)
    · right
      have h1' := LS_mono G hG hx (r - a) cn vn (yb := P.t0 - e0) (yj := P.t1 - e1) (yt := P.t2 - e2)
        (hb := e0) (hj := e1) (ht := e2) (yb' := P.t0 - l0) (yj' := P.t1 - l1) (yt' := P.t2 - l2)
        (hb' := h0) (hj' := h1) (ht' := h2) (by omega) (by omega) (by omega) a1 b1 c1
      have e1' := lhsV_eq G r a cn vn W B0 B1 B2 (P.t0 - e0) (P.t1 - e1) (P.t2 - e2) e0 e1 e2
      have e2' := lhsV_eq G r a cn vn W B0 B1 B2 (P.t0 - l0) (P.t1 - l1) (P.t2 - l2) h0 h1 h2
      rw [← hP] at e1' e2'
      rw [e1']
      exact h1'.trans' (le_of_eq rfl) |>.trans (by rw [← e2']; exact k3)
    · obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      by_cases hc : e0 ≤ (l0 + h0) / 2
      · exact ih _ _ _ _ _ _ hl e0 e1 e2 a0 hc b0 b1 c0 c1 ⟨v1, v2, v3⟩
      · exact ih _ _ _ _ _ _ hr e0 e1 e2 (by omega) a1 b0 b1 c0 c1 ⟨v1, v2, v3⟩
    · obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      by_cases hc : e1 ≤ (l1 + h1) / 2
      · exact ih _ _ _ _ _ _ hl e0 e1 e2 a0 a1 b0 hc c0 c1 ⟨v1, v2, v3⟩
      · exact ih _ _ _ _ _ _ hr e0 e1 e2 a0 a1 (by omega) b1 c0 c1 ⟨v1, v2, v3⟩
    · obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
      by_cases hc : e2 ≤ (l2 + h2) / 2
      · exact ih _ _ _ _ _ _ hl e0 e1 e2 a0 a1 b0 b1 c0 hc ⟨v1, v2, v3⟩
      · exact ih _ _ _ _ _ _ hr e0 e1 e2 a0 a1 b0 b1 (by omega) c1 ⟨v1, v2, v3⟩

end Gate61Cell

end Merged_Gate61Cell

-- merged module Gate61Core
section Merged_Gate61Core

set_option autoImplicit false

namespace Gate61Cell
open Gate61FreeCard (mx)

theorem core (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (r a cn vn W B0 B1 B2 : ℕ) (hρ : a < r)
    (hcn : cn ≤ 2 * (r - a)) {yb yj yt e0 e1 e2 : ℕ}
    (hy0 : yb ≤ B0 - a * G.lb - e0) (hy1 : yj ≤ B1 - a * G.lj - e1) (hy2 : yt ≤ B2 - a * G.lt - e2)
    (h : lhsV (mkPr G r a cn vn W B0 B1 B2) (B0 - a * G.lb - e0) (B1 - a * G.lj - e1) (B2 - a * G.lt - e2)
      e0 e1 e2 ≤ (mkPr G r a cn vn W B0 B1 B2).rhs) :
    (1 - (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) *
        (TT G (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) : ℚ) +
      (TT G (hB G.lift e0 e1) (hJ G.lift e1) (hT G.lift e1 e2) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) : ℚ) +
      ((r - a : ℕ) : ℚ) * (TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift e0 e1) (hJ G.lift e1) (hT G.lift e1 e2) : ℚ) +
      (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ)) * ((r - a : ℕ) : ℚ) *
        (TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) : ℚ) +
      (vn : ℚ) / 10000000 * ((r - a : ℕ) : ℚ) ^ 2 * (G.tsep : ℚ) ≤
      (G.sc : ℚ) * G.A * ((r - a : ℕ) : ℚ) ^ 2 := by
  have hm := LS_mono G hG hx (r - a) cn vn (yb := yb) (yj := yj) (yt := yt) (hb := e0) (hj := e1) (ht := e2)
    (yb' := B0 - a * G.lb - e0) (yj' := B1 - a * G.lj - e1) (yt' := B2 - a * G.lt - e2)
    (hb' := e0) (hj' := e1) (ht' := e2) hy0 hy1 hy2 le_rfl le_rfl le_rfl
  rw [lhsV_eq] at h
  have h2 := hm.trans h
  simp only [mkPr] at h2
  unfold LS VD at h2
  have hρpos : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hρ
  have h3 : ((2 * (r - a) - cn : ℕ) : ℚ) = 2 * ((r - a : ℕ) : ℚ) - cn := by
    push_cast [Nat.cast_sub hcn]; ring
  have h4 : (((2 * (r - a) - cn) * 10000000 * TT G (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
      2 * (r - a) * 10000000 * TT G (hB G.lift e0 e1) (hJ G.lift e1) (hT G.lift e1 e2) (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
      2 * (r - a) * (r - a) * 10000000 * TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift e0 e1) (hJ G.lift e1) (hT G.lift e1 e2) +
      cn * (r - a) * 10000000 * TT G (mx G.xb G.xj) G.xj G.xt (hB G.lift yb yj) (hJ G.lift yj) (hT G.lift yj yt) +
      2 * vn * (r - a) * (r - a) * (r - a) * G.tsep : ℕ) : ℚ) ≤ ((G.sc * G.A * (2 * (r - a) * (r - a) * (r - a)) * 10000000 : ℕ) : ℚ) := by
    exact_mod_cast h2
  push_cast [h3] at h4
  have key : 0 < 2 * ((r - a : ℕ) : ℚ) * 10000000 := by positivity
  rw [← mul_le_mul_iff_of_pos_left key]
  field_simp
  nlinarith [h4]

end Gate61Cell

end Merged_Gate61Core

-- merged module Gate61Level
section Merged_Gate61Level

set_option autoImplicit false

namespace Gate61Cell
open Gate61FreeCard (mn mx mn_eq mx_eq free_mono)
open Gate61FreeU3 (freeD free_le_freeD)

def levelOK (G : Gt) (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ)) : Bool :=
  (List.range (min (B0 / G.lb) (min (B1 / G.lj) (B2 / G.lt)) + 1)).all fun a =>
    bif Nat.ble r a then Nat.ble (freeD (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)) W
    else match cv a with
      | none => Nat.ble (freeD (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)) W
      | some c => cell (mkPr G r a c.1 c.2 W B0 B1 B2) fuel 0 0 0 (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt)

theorem level_sound (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (r W B0 B1 B2 fuel : ℕ) (cv : ℕ → Option (ℕ × ℕ))
    (hcv : ∀ a c, cv a = some c → c.1 ≤ 2 * (r - a))
    (h : levelOK G r W B0 B1 B2 fuel cv = true)
    (x : Fin 3 → ℕ) (hxl : G.lb ≤ x 0 ∧ G.lj ≤ x 1 ∧ G.lt ≤ x 2) (a : ℕ) (η : Fin 3 → ℕ)
    (hfit : ∀ k, a * x k + η k ≤ ![B0, B1, B2] k) (hv : η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2)
    (hfree : W < Gate61Shape.free (fun k => ![B0, B1, B2] k - (a * x k + η k))) :
    a < r ∧ ∃ c, cv a = some c ∧
      lhsV (mkPr G r a c.1 c.2 W B0 B1 B2) (B0 - a * G.lb - η 0) (B1 - a * G.lj - η 1) (B2 - a * G.lt - η 2)
        (η 0) (η 1) (η 2) ≤ (mkPr G r a c.1 c.2 W B0 B1 B2).rhs := by
  have f0 := hfit 0
  have f1 := hfit 1
  have f2 := hfit 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at f0 f1 f2 hfree
  have ha0 : a ≤ B0 / G.lb := (Nat.le_div_iff_mul_le hpos.1).mpr (by
    have := Nat.mul_le_mul_left a hxl.1; nlinarith [Nat.zero_le (η 0)])
  have ha1 : a ≤ B1 / G.lj := (Nat.le_div_iff_mul_le hpos.2.1).mpr (by
    have := Nat.mul_le_mul_left a hxl.2.1; nlinarith [Nat.zero_le (η 1)])
  have ha2 : a ≤ B2 / G.lt := (Nat.le_div_iff_mul_le hpos.2.2).mpr (by
    have := Nat.mul_le_mul_left a hxl.2.2; nlinarith [Nat.zero_le (η 2)])
  have hmem : a ∈ List.range (min (B0 / G.lb) (min (B1 / G.lj) (B2 / G.lt)) + 1) :=
    List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h a hmem
  have g0 := Nat.mul_le_mul_left a hxl.1
  have g1 := Nat.mul_le_mul_left a hxl.2.1
  have g2 := Nat.mul_le_mul_left a hxl.2.2
  have hfd : Gate61Shape.free (fun k => ![B0, B1, B2] k - (a * x k + η k)) ≤
      freeD (B0 - a * G.lb - η 0) (B1 - a * G.lj - η 1) (B2 - a * G.lt - η 2) := by
    refine (Gate61FreeCard.free_mono (Y' := ![B0 - a * G.lb - η 0, B1 - a * G.lj - η 1, B2 - a * G.lt - η 2])
      ?_).trans (free_le_freeD _)
    intro i; fin_cases i <;> simp <;> omega
  have hfd0 : Gate61Shape.free (fun k => ![B0, B1, B2] k - (a * x k + η k)) ≤
      freeD (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt) := by
    refine (Gate61FreeCard.free_mono (Y' := ![B0 - a * G.lb, B1 - a * G.lj, B2 - a * G.lt]) ?_).trans (free_le_freeD _)
    intro i; fin_cases i <;> simp <;> omega
  by_cases hra : r ≤ a
  · exfalso
    simp only [hra, Nat.ble_eq_true_of_le, Bool.cond_true] at hk
    have := Nat.le_of_ble_eq_true hk
    omega
  · have hra' : ¬ r ≤ a := hra
    have hble : Nat.ble r a = false := by
      cases hb : Nat.ble r a
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) hra'
    rw [hble] at hk
    simp only [Bool.cond_false] at hk
    refine ⟨by omega, ?_⟩
    cases hc : cv a with
    | none =>
      exfalso
      rw [hc] at hk
      have := Nat.le_of_ble_eq_true hk
      omega
    | some c =>
      rw [hc] at hk
      refine ⟨c, rfl, ?_⟩
      have hs := cell_sound G hG hx r a c.1 c.2 W B0 B1 B2 fuel 0 0 0 (B0 - a * G.lb) (B1 - a * G.lj) (B2 - a * G.lt) hk
        (η 0) (η 1) (η 2) (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega) (Nat.zero_le _) (by omega) hv
      rcases hs with hs | hs
      · exfalso
        have : Gate61Shape.free (fun k => ![B0, B1, B2] k - (a * x k + η k)) ≤ W := by
          refine le_trans ?_ hs
          refine Gate61FreeCard.free_mono ?_
          intro i; fin_cases i <;> simp <;> omega
        omega
      · exact hs

end Gate61Cell

end Merged_Gate61Level

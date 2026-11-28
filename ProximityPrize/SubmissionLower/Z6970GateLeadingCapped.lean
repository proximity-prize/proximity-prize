import ProximityPrize.SubmissionLower.Gate6966Assm

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

open Gate6966Cell

def capPrefix (F : ℕ → ℕ → ℤ) (n u c : ℕ) : ℤ :=
  F n u - (if 3 * (c + 1) ≤ u then F (n - (c + 1)) (u - 3 * (c + 1)) else 0)

private theorem sum_sub (f g : ℕ → ℤ) (n : ℕ) :
    sumUpTo (fun q => f q - g q) n = sumUpTo f n - sumUpTo g n := by
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih =>
    simp only [sumUpTo, ih]
    ring

private theorem sum_shift (f : ℕ → ℤ) (k n : ℕ) :
    sumUpTo (fun q => bif Nat.ble k q then f (q - k) else 0) n =
      sumUpTo f (n - k) := by
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih =>
    rw [sumUpTo, ih]
    by_cases h : k ≤ n
    · have pass : Nat.ble k n = true := Nat.ble_eq_true_of_le h
      have step : n + 1 - k = (n - k) + 1 := by omega
      simp only [pass, Bool.cond_true, step, sumUpTo]
    · have fail : Nat.ble k n = false :=
        Bool.eq_false_iff.mpr (fun hn => h (Nat.le_of_ble_eq_true hn))
      have step : n + 1 - k = n - k := by omega
      simp only [fail, Bool.cond_false, step, add_zero]

theorem capPrefix_eq (F : ℕ → ℕ → ℤ)
    (hF : ∀ n u, u ≤ 1679 → F n u = sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n)
    (n u c : ℕ) (hu : u ≤ 1679) :
    capPrefix F n u c = sumUpTo (fun q => cappedN q u c) n := by
  unfold capPrefix
  rw [hF n u hu]
  by_cases h : 3 * (c + 1) ≤ u
  · have pass : Nat.ble (3 * (c + 1)) u = true := Nat.ble_eq_true_of_le h
    have cut (q : ℕ) : q - c - 1 = q - (c + 1) := by omega
    simp only [h, if_true, hF (n - (c + 1)) (u - 3 * (c + 1))
      ((Nat.sub_le _ _).trans hu), cappedN, pass, Bool.and_true, cut]
    let shifted := fun q => (cumP q (u - 3 * (c + 1)) : ℤ) - cumQ q (u - 3 * (c + 1))
    change sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u) n -
      sumUpTo shifted (n - (c + 1)) =
      sumUpTo (fun q => (cumP q u : ℤ) - cumQ q u -
        (bif Nat.ble (c + 1) q then shifted (q - (c + 1)) else 0)) n
    rw [sum_sub (fun q => (cumP q u : ℤ) - cumQ q u)
      (fun q => bif Nat.ble (c + 1) q then shifted (q - (c + 1)) else 0) n,
      sum_shift shifted (c + 1) n]
  · have fail : Nat.ble (3 * (c + 1)) u = false :=
      Bool.eq_false_iff.mpr (fun hn => h (Nat.le_of_ble_eq_true hn))
    simp only [h, if_false, cappedN, fail, Bool.and_false, Bool.cond_false, sub_zero]

end Gate6970Leading

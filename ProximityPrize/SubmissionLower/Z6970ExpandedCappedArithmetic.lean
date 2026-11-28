import ProximityPrize.SubmissionLower.Z6970ExpandedColumns

set_option Elab.async false
set_option maxRecDepth 25000

namespace Low6969GateCell
open scoped BigOperators
/-! PERF (69.62): the `Low6969GateAmb.compute` lower bound evaluated in Nat. `cumulative` over ℤ is
slow in the kernel (Int.div/mod, 8 `denominator` calls per count); `denN`/`dg` are the same
quantities with guarded Nat subtraction. -/
def denN (u : ℕ) : ℕ :=
  1 + (u % 6) * (u % 6 + 1) / 2 + (u / 6) * (22 + 7 * (u % 6) + (u % 6) * (u % 6 - 1) / 2) +
    (57 + 6 * (u % 6)) * ((u / 6) * (u / 6 - 1) / 2) + 6 * (u / 6) * (u / 6 - 1) * (u / 6 - 2)

def dg (v c : ℕ) : ℕ := bif Nat.ble c v then denN (v - c) else 0

def cumPV (V d : ℕ) : ℕ := dg V 0 + dg V (2 * d + 3) + dg V (2 * d + 4) + dg V (2 * d + 5)

def cumQV (V d : ℕ) : ℕ := dg V (d + 1) + dg V (d + 2) + dg V (d + 3) + dg V (3 * d + 6)

def cumP (d u : ℕ) : ℕ := cumPV (min u (3 * d)) d

def cumQ (d u : ℕ) : ℕ := cumQV (min u (3 * d)) d

def cappedN (d u c : ℕ) : ℤ :=
  ((cumP d u : ℤ) - cumQ d u) -
    (bif Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u then
      (cumP (d - c - 1) (u - 3 * (c + 1)) : ℤ) - cumQ (d - c - 1) (u - 3 * (c + 1)) else 0)

theorem denN_eq (n : ℕ) : K1_13_2.denominator (n : ℤ) = (denN n : ℤ) := by
  unfold K1_13_2.denominator denN
  rw [if_neg (by omega)]
  have hq : ((n : ℤ) / 6) = ((n / 6 : ℕ) : ℤ) := by omega
  have hr : ((n : ℤ) % 6) = ((n % 6 : ℕ) : ℤ) := by omega
  simp only [hq, hr]
  have hr6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at *
  generalize n / 6 = q at *
  rcases q with _ | _ | q <;> interval_cases r <;> push_cast <;> simp <;> ring_nf <;> simp

theorem den_eq (v c : ℕ) : K1_13_2.denominator ((v : ℤ) - (c : ℤ)) = (dg v c : ℤ) := by
  unfold dg
  by_cases h : c ≤ v
  · have : Nat.ble c v = true := Nat.ble_eq_true_of_le h
    rw [this, show (v : ℤ) - c = ((v - c : ℕ) : ℤ) by omega]
    exact denN_eq _
  · have : Nat.ble c v = false := by
      cases e : Nat.ble c v
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e) h
    rw [this]
    unfold K1_13_2.denominator
    rw [if_pos (by omega)]
    rfl

theorem cum_eq (d u : ℕ) : K1_13_2.cumulative (d : ℤ) (u : ℤ) = (cumP d u : ℤ) - cumQ d u := by
  unfold K1_13_2.cumulative
  have h0 : (decide ((d : ℤ) < 0) || decide ((u : ℤ) < 0)) = false := by simp
  rw [h0]
  simp only [Bool.false_eq_true, if_false]
  have hv : min (u : ℤ) (3 * (d : ℤ)) = ((min u (3 * d) : ℕ) : ℤ) := by push_cast; rfl
  rw [hv]
  unfold cumP cumQ cumPV cumQV
  generalize min u (3 * d) = V
  have e0 := den_eq V 0
  have e1 := den_eq V (d + 1)
  have e2 := den_eq V (d + 2)
  have e3 := den_eq V (d + 3)
  have e4 := den_eq V (2 * d + 3)
  have e5 := den_eq V (2 * d + 4)
  have e6 := den_eq V (2 * d + 5)
  have e7 := den_eq V (3 * d + 6)
  push_cast at e0 e1 e2 e3 e4 e5 e6 e7
  rw [sub_zero] at e0
  have r1 : (V : ℤ) - d - 1 = V - (d + 1) := by ring
  have r2 : (V : ℤ) - d - 2 = V - (d + 2) := by ring
  have r3 : (V : ℤ) - d - 3 = V - (d + 3) := by ring
  have r4 : (V : ℤ) - 2 * d - 3 = V - (2 * d + 3) := by ring
  have r5 : (V : ℤ) - 2 * d - 4 = V - (2 * d + 4) := by ring
  have r6 : (V : ℤ) - 2 * d - 5 = V - (2 * d + 5) := by ring
  have r7 : (V : ℤ) - 3 * d - 6 = V - (3 * d + 6) := by ring
  rw [r1, r2, r3, r4, r5, r6, r7, e0, e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring


theorem capped_eq (d u c : ℕ) : K1_13_2.cappedCount (d : ℤ) (u : ℤ) (c : ℤ) = cappedN d u c := by
  unfold K1_13_2.cappedCount cappedN
  rw [if_neg (by omega), cum_eq]
  by_cases h : c + 1 ≤ d ∧ 3 * (c + 1) ≤ u
  · have e1 : (d : ℤ) - c - 1 = ((d - c - 1 : ℕ) : ℤ) := by omega
    have e2 : (u : ℤ) - 3 * ((c : ℤ) + 1) = ((u - 3 * (c + 1) : ℕ) : ℤ) := by omega
    rw [e1, e2, cum_eq]
    have : (Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u) = true := by
      simp [Nat.ble_eq, h.1, h.2]
    rw [this]; rfl
  · have : (Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u) = false := by
      by_cases h1 : c + 1 ≤ d
      · have h2 : ¬ 3 * (c + 1) ≤ u := fun x => h ⟨h1, x⟩
        have e : Nat.ble (3 * (c + 1)) u = false :=
          Bool.eq_false_iff.mpr (fun e => h2 (Nat.le_of_ble_eq_true e))
        simp [e]
      · have e : Nat.ble (c + 1) d = false :=
          Bool.eq_false_iff.mpr (fun e => h1 (Nat.le_of_ble_eq_true e))
        simp [e]
    rw [this]
    have h2 : K1_13_2.cumulative ((d : ℤ) - c - 1) ((u : ℤ) - 3 * ((c : ℤ) + 1)) = 0 := by
      unfold K1_13_2.cumulative
      rw [if_pos]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    rw [h2]; rfl

def sumUpTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumUpTo f n + f n

theorem sumUpTo_eq (f : ℕ → ℤ) (n : ℕ) : sumUpTo f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

end Low6969GateCell

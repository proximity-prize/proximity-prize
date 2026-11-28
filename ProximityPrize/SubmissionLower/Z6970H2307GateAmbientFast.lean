import ProximityPrize.SubmissionLower.Z6970H2307FastGateNumeric

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedGate6970.H2307Numeric

open Gate6966Cell

private theorem dg_zero {v k : ℕ} (hk : v < k) : dg v k = 0 := by
  have h : Nat.ble k v = false :=
    Bool.eq_false_iff.mpr (fun h => (not_le.mpr hk) (Nat.le_of_ble_eq_true h))
  simp [dg, h]

private theorem cum_flat (d u : ℕ) (h : u ≤ d) : cumP d u = denN u ∧ cumQ d u = 0 := by
  have hv : min u (3*d) = u := min_eq_left (by omega)
  constructor
  · unfold cumP cumPV
    rw [hv, dg_zero (by omega : u < 2*d+3), dg_zero (by omega : u < 2*d+4),
      dg_zero (by omega : u < 2*d+5)]
    simp [dg]
  · unfold cumQ cumQV
    rw [hv, dg_zero (by omega : u < d+1), dg_zero (by omega : u < d+2),
      dg_zero (by omega : u < d+3), dg_zero (by omega : u < 3*d+6)]

private theorem capped_flat (d u c : ℕ) (h : u ≤ d) : cappedN d u c = cappedN u u c := by
  have hd := cum_flat d u h
  have hu := cum_flat u u le_rfl
  unfold cappedN
  rw [hd.1, hd.2, hu.1, hu.2]
  by_cases hc : 3*(c+1) ≤ u
  · have bu : Nat.ble (3*(c+1)) u = true := Nat.ble_eq_true_of_le hc
    have bd : Nat.ble (c+1) d = true := Nat.ble_eq_true_of_le (by omega)
    have b0 : Nat.ble (c+1) u = true := Nat.ble_eq_true_of_le (by omega)
    have fd := cum_flat (d-c-1) (u-3*(c+1)) (by omega)
    have fu := cum_flat (u-c-1) (u-3*(c+1)) (by omega)
    simp only [bu, bd, b0, Bool.and_self, Bool.cond_true, fd.1, fd.2, fu.1, fu.2]
  · have bu : Nat.ble (3*(c+1)) u = false :=
      Bool.eq_false_iff.mpr (fun h => hc (Nat.le_of_ble_eq_true h))
    simp only [bu, Bool.and_false, Bool.cond_false]

private theorem cap_before {q : ℕ} (h : q < 3514) : cap q = min q 1679 := by
  have hb : Nat.blt q 3514 = true := by simp [Nat.blt_eq, h]
  simp only [cap, hb, Bool.cond_true]

def fastCount (n u c : ℕ) : ℤ :=
  let lo := min n u
  let hi := min n 3514
  sumUpTo (fun q => cappedN q u c) lo +
    ((hi - lo : ℕ) : ℤ) * cappedN u u c +
    sumUpTo (fun q => cappedN (cap (hi+q)) u c) (n-hi)

theorem fastCount_eq (n u c : ℕ) (hu : u ≤ 1679) :
    fastCount n u c = sumUpTo (fun q => cappedN (cap q) u c) n := by
  let lo := min n u
  let hi := min n 3514
  let f := fun q => cappedN (cap q) u c
  have hlo : lo ≤ hi := min_le_min_left _ (by omega)
  have hhi : hi ≤ n := min_le_left _ _
  have split (a b : ℕ) (h : a ≤ b) :
      (∑ q ∈ Finset.range b, f q) = (∑ q ∈ Finset.range a, f q) +
        ∑ q ∈ Finset.range (b-a), f (a+q) := by
    conv_lhs => rw [show b = a+(b-a) by omega, Finset.sum_range_add]
  have initial : (∑ q ∈ Finset.range lo, cappedN q u c) = ∑ q ∈ Finset.range lo, f q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqu : q ≤ u := (Finset.mem_range.mp hq).le.trans (min_le_right _ _)
    change cappedN q u c = cappedN (cap q) u c
    rw [cap_before (by omega), min_eq_left (hqu.trans hu)]
  have plateau : (∑ q ∈ Finset.range (hi-lo), f (lo+q)) = ((hi-lo : ℕ) : ℤ) * cappedN u u c := by
    calc
      _ = ∑ _ ∈ Finset.range (hi-lo), cappedN u u c := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqi := Finset.mem_range.mp hq
        have hqhi : lo+q < hi := by omega
        have hlonu : lo = u := by
          have hn : u ≤ n := by
            by_contra hn
            have hh : lo = n := min_eq_left (by omega)
            omega
          exact min_eq_right hn
        have hcut : hi ≤ 3514 := min_le_right _ _
        change cappedN (cap (lo+q)) u c = _
        rw [cap_before (by omega)]
        exact capped_flat _ _ _ (le_min (by omega) hu)
      _ = _ := by simp [nsmul_eq_mul]
  simp only [fastCount, sumUpTo_eq]
  change _ + _ + (∑ q ∈ Finset.range (n-hi), f (hi+q)) = ∑ q ∈ Finset.range n, f q
  rw [split hi n hhi, split lo hi hlo, initial, plateau]

def ambientFast (b j t : ℕ) : ℤ :=
  bif Nat.ble 4024 b && Nat.ble 1679 j && Nat.ble 500 t then 427286700047
  else fastCount (min 4025 (b+1)) (min j 1679) (min t 500)

theorem ambientFast_eq (b j t : ℕ) : ambientFast b j t = ambient b j t := by
  unfold ambientFast ambient
  rw [fastCount_eq _ _ _ (min_le_right _ _)]

def lossFast (lv : Lv) (i : ℕ) : ℤ :=
  let (b,j,t,w) := lv.getD i defaultRow
  427286700047 - ambientFast b j t + w

theorem lossFast_eq (lv : Lv) (i : ℕ) : lossFast lv i = loss lv i := by
  simp only [lossFast, loss, ambientFast_eq]

def massFast (lv : Lv) (lo n : ℕ) : ℤ := sumUpTo (fun i => lossFast lv (lo+i)) n

theorem massFast_eq (lv : Lv) (lo n : ℕ) : massFast lv lo n = mass lv lo n := by
  simp only [massFast, mass, lossFast_eq]

end ExpandedGate6970.H2307Numeric

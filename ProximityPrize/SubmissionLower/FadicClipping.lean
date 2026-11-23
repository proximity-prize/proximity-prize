import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option Elab.async false

namespace FadicClipping

open Finset
open scoped BigOperators

def skip (n a b step : ℕ) : ℕ :=
  if b ≤ a then 0
  else if step = 0 then n
  else min n ((b-a-1)/step+1)

theorem skip_le (n a b step : ℕ) : skip n a b step ≤ n := by
  unfold skip
  split
  · omega
  · split <;> omega

theorem skip_spec {n a b step i : ℕ} (hi : i < n) :
    skip n a b step ≤ i ↔ b ≤ a+step*i := by
  unfold skip
  by_cases hab : b ≤ a
  · rw [ite_eq_left hab]
    omega
  · rw [ite_eq_right hab]
    by_cases hzero : step=0
    · rw [ite_eq_left hzero,hzero,zero_mul,add_zero]
      omega
    · rw [ite_eq_right hzero]
      have hpos : 0 < step := Nat.pos_of_ne_zero hzero
      have hdiv := Nat.le_div_iff_mul_le (x := i) (y := b-a-1) hpos
      rw [Nat.mul_comm i] at hdiv
      rw [min_le_iff]
      omega

theorem sum_ascending (n a b step : ℕ) (f : ℕ → ℕ) :
    let k := skip n a b step
    (∑ i ∈ range n, if b ≤ a+step*i then f (a+step*i-b) else 0) =
      ∑ j ∈ range (n-k), f ((a+step*k-b)+step*j) := by
  dsimp only
  let k := skip n a b step
  let g := fun i => if b ≤ a+step*i then f (a+step*i-b) else 0
  have hk : k ≤ n := skip_le n a b step
  have hsum := sum_range_add g k (n-k)
  rw [Nat.add_sub_of_le hk] at hsum
  change (∑ i ∈ range n, g i) = _
  rw [hsum]
  have hz : ∑ i ∈ range k, g i = 0 := by
    apply sum_eq_zero
    intro i hi
    have hlt := mem_range.mp hi
    exact ite_eq_right (fun h => (not_le_of_gt hlt) ((skip_spec (hlt.trans_le hk)).mpr h))
  rw [hz,zero_add]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hlt : k+j<n := by omega
  have hk' : k<n := by omega
  have hs : b ≤ a+step*k := (skip_spec (a := a) (b := b) (step := step) hk').mp le_rfl
  have hj'' : b ≤ a+step*(k+j) := (skip_spec (a := a) (b := b) (step := step) hlt).mp (by omega)
  change (if b ≤ a+step*(k+j) then f (a+step*(k+j)-b) else 0) = _
  rw [ite_eq_left hj'',Nat.mul_add]
  congr 1
  change a+(step*k+step*j)-b = a+step*k-b+step*j
  omega

def window (n a da b db : ℕ) : ℕ × ℕ × ℕ :=
  if db ≤ da then
    let step := da-db
    let k := skip n a b step
    (n-k,a+step*k-b,step)
  else
    let step := db-da
    let a' := a+da*(n-1)
    let b' := b+db*(n-1)
    let k := skip n a' b' step
    (n-k,a'+step*k-b',step)

theorem sum_window (n a da b db : ℕ) (f : ℕ → ℕ) :
    let w := window n a da b db
    (∑ i ∈ range n, if b+db*i ≤ a+da*i then f (a+da*i-(b+db*i)) else 0) =
      ∑ j ∈ range w.1, f (w.2.1+w.2.2*j) := by
  dsimp only
  unfold window
  split
  · rename_i h
    rw [← sum_ascending n a b (da-db) f]
    apply sum_congr rfl
    intro i _
    have hmul : da*i=(da-db)*i+db*i := by
      rw [← Nat.add_mul,Nat.sub_add_cancel h]
    simp only [hmul,← Nat.add_assoc,Nat.add_le_add_iff_right,Nat.add_sub_add_right]
  · rename_i h
    rw [← sum_ascending n (a+da*(n-1)) (b+db*(n-1)) (db-da) f]
    have hup : da ≤ db := (Nat.lt_of_not_ge h).le
    let g := fun i => if b+db*i ≤ a+da*i then f (a+da*i-(b+db*i)) else 0
    change (∑ i ∈ range n, g i) = _
    rw [← sum_range_reflect g n]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ n-1 := by have := mem_range.mp hi; omega
    have hb : b+db*(n-1-i)+db*i = b+db*(n-1) := by
      rw [Nat.add_assoc,← Nat.mul_add,Nat.sub_add_cancel hi']
    have ha : a+da*(n-1-i)+db*i = a+da*(n-1)+(db-da)*i := by
      rw [show db*i = da*i+(db-da)*i by rw [← Nat.add_mul,Nat.add_sub_of_le hup]]
      rw [← Nat.add_assoc, Nat.add_assoc a,← Nat.mul_add,Nat.sub_add_cancel hi']
    have hg : b+db*(n-1-i) ≤ a+da*(n-1-i) ↔
        b+db*(n-1) ≤ a+da*(n-1)+(db-da)*i := by
      rw [← ha,← hb,Nat.add_le_add_iff_right]
    have he : a+da*(n-1-i)-(b+db*(n-1-i)) =
        a+da*(n-1)+(db-da)*i-(b+db*(n-1)) := by
      rw [← ha,← hb,Nat.add_sub_add_right]
    simp only [g,hg,he]

end FadicClipping

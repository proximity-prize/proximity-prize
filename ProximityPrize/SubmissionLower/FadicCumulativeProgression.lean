import ProximityPrize.SubmissionLower.FadicClipping
import ProximityPrize.SubmissionLower.FadicDenomProgression
import ProximityPrize.SubmissionLower.FadicCastBase

set_option autoImplicit false
set_option Elab.async false

namespace FadicGate

open Finset
open FadicClipping
open K1_13_2 (cumulative cappedCount)
open scoped BigOperators
open private FadicGate.cumulative_split from ProximityPrize.SubmissionLower.FadicCastBase
open FadicGate (cumulative_split)

/-- Sum one denominator argument after clipping its negative values. -/
private def denomClip (n a da b db : ℕ) : ℕ :=
  let w := window n a da b db
  rDenomProg w.1 w.2.1 w.2.2

private theorem denomClip_eq (n a da b db : ℕ) :
    denomClip n a da b db = ∑ i ∈ range n, rDenomSub (a+da*i) (b+db*i) := by
  unfold denomClip
  rw [rDenomProg_eq,← sum_window n a da b db rDenom]
  apply sum_congr rfl
  intro i _
  unfold rDenomSub
  rw [cond_ble]
  rfl

private def scaled (n a step v dv k c : ℕ) : ℕ :=
  denomClip n v dv (k*a+c) (k*step)

private theorem scaled_eq (n a step v dv k c : ℕ) :
    scaled n a step v dv k c =
      ∑ i ∈ range n, rDenomSub (v+dv*i) (k*(a+step*i)+c) := by
  unfold scaled
  rw [denomClip_eq]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

private def pos (d v : ℕ) : ℕ :=
  rDenom v+rDenomSub v (2*d+3)+rDenomSub v (2*d+4)+rDenomSub v (2*d+5)

private def neg (d v : ℕ) : ℕ :=
  rDenomSub v (d+1)+rDenomSub v (d+2)+rDenomSub v (d+3)

private theorem last_term_zero {d v : ℕ} (hv : v ≤ 3*d) :
    rDenomSub v (3*d+6) = 0 := by
  unfold rDenomSub
  rw [cond_ble,ite_eq_right (by omega : ¬3*d+6 ≤ v)]

private theorem parts_ord (d u : ℕ) :
    neg d (min u (3*d)) ≤ pos d (min u (3*d)) := by
  let v := min u (3*d)
  have hz : denomSub v (3*d+6) = 0 := by
    rw [← rDenomSub_eq]
    exact last_term_zero (min_le_right _ _)
  have h := cumulative_nonneg d u
  rw [cumulative_split] at h
  change 0 ≤ ((denomN v + denomSub v (2*d+3) + denomSub v (2*d+4) +
      denomSub v (2*d+5) : ℕ) : ℤ) -
    ((denomSub v (d+1)+denomSub v (d+2)+denomSub v (d+3)+denomSub v (3*d+6) : ℕ) : ℤ) at h
  rw [hz,add_zero] at h
  unfold pos neg
  simp only [rDenomSub_eq]
  exact_mod_cast (sub_nonneg.mp h)

private theorem cumulative_at (d u : ℕ) :
    rCumulative d u = pos d (min u (3*d)) - neg d (min u (3*d)) := by
  have hz : rDenomSub (min u (3*d)) (3*d+6) = 0 := last_term_zero (min_le_right _ _)
  simp only [rCumulative,rCumAux,rMin_eq,Nat.add_eq,Nat.mul_eq,Nat.sub_eq,pos,neg,hz,add_zero]

private def cumulPart (n a step v dv : ℕ) : ℕ :=
  (rDenomProg n v dv+scaled n a step v dv 2 3+scaled n a step v dv 2 4+scaled n a step v dv 2 5) -
    (scaled n a step v dv 1 1+scaled n a step v dv 1 2+scaled n a step v dv 1 3)

private theorem cumulPart_eq (n a step v dv u : ℕ)
    (hv : ∀ i ∈ range n, v+dv*i = min u (3*(a+step*i))) :
    cumulPart n a step v dv = ∑ i ∈ range n, rCumulative (a+step*i) u := by
  unfold cumulPart
  simp only [rDenomProg_eq,scaled_eq,Nat.one_mul,← Finset.sum_add_distrib]
  change (∑ i ∈ range n, pos (a+step*i) (v+dv*i)) -
    (∑ i ∈ range n, neg (a+step*i) (v+dv*i)) = _
  rw [← Finset.sum_tsub_distrib _ (fun i hi => by rw [hv i hi]; exact parts_ord _ _)]
  apply sum_congr rfl
  intro i hi
  rw [hv i hi,cumulative_at]

/-- Sum the cumulative count on one progression, with its one change of slope. -/
def rCumulativeProg (n a step u : ℕ) : ℕ :=
  let k := skip n (3*a) (u+1) (3*step)
  cumulPart k a step (3*a) (3*step) + cumulPart (n-k) (a+step*k) step u 0

theorem rCumulativeProg_eq (n a step u : ℕ) :
    rCumulativeProg n a step u = ∑ i ∈ range n, rCumulative (a+step*i) u := by
  unfold rCumulativeProg
  let k := skip n (3*a) (u+1) (3*step)
  have hk : k ≤ n := skip_le _ _ _ _
  change cumulPart k a step (3*a) (3*step) +
    cumulPart (n-k) (a+step*k) step u 0 = _
  rw [cumulPart_eq (u := u),cumulPart_eq (u := u)]
  · let f := fun i => rCumulative (a+step*i) u
    have h := sum_range_add f k (n-k)
    rw [Nat.add_sub_of_le hk] at h
    change _ = ∑ i ∈ range n, f i
    rw [h]
    congr 1
    apply sum_congr rfl
    intro i _
    simp only [f,Nat.mul_add,Nat.add_assoc]
  · intro i hi
    have hi' : k+i<n := by have := mem_range.mp hi; omega
    have hg : u+1 ≤ 3*a+(3*step)*(k+i) :=
      (skip_spec (a := 3*a) (b := u+1) (step := 3*step) hi').mp (by omega)
    have he : 3*a+(3*step)*(k+i) = 3*(a+step*k+step*i) := by ring
    rw [he] at hg
    rw [min_eq_left (by omega),zero_mul,add_zero]
  · intro i hi
    have hi' : i<k := mem_range.mp hi
    have hg : ¬u+1 ≤ 3*a+(3*step)*i :=
      fun h => (not_le_of_gt hi') ((skip_spec (hi'.trans_le hk)).mpr h)
    have he : 3*a+(3*step)*i = 3*(a+step*i) := by ring
    rw [he] at hg ⊢
    rw [min_eq_right (by omega)]

private theorem cap_cut_le {d u t : ℕ} (hu : 3*(t+1) ≤ u) (hd : t+1 ≤ d) :
    rCumulative (d-(t+1)) (u-3*(t+1)) ≤ rCumulative d u := by
  simp only [rCumulative_eq]
  have h := cappedCount_nonneg (d : ℤ) (u : ℤ) (t : ℤ)
  unfold cappedCount at h
  rw [ite_eq_right (by omega : ¬(t : ℤ)<0)] at h
  have h₁ : ((d-(t+1) : ℕ) : ℤ) = (d:ℤ)-t-1 := by rw [Nat.cast_sub hd]; push_cast; ring
  have h₂ : ((u-3*(t+1) : ℕ) : ℤ) = (u:ℤ)-3*((t:ℤ)+1) := by rw [Nat.cast_sub hu]; push_cast; ring
  rw [← h₁,← h₂,← cumulativeN_cast,← cumulativeN_cast] at h
  exact_mod_cast (sub_nonneg.mp h)

/-- Sum the capped count by subtracting one clipped progression. -/
def rCappedProg (n a step u t : ℕ) : ℕ :=
  let full := rCumulativeProg n a step u
  let s := t+1
  if 3*s ≤ u then
    let k := skip n a s step
    full-rCumulativeProg (n-k) (a+step*k-s) step (u-3*s)
  else full

theorem rCappedProg_eq (n a step u t : ℕ) :
    rCappedProg n a step u t = ∑ i ∈ range n, rCapped (a+step*i) u t := by
  unfold rCappedProg
  dsimp only
  split
  · rename_i h
    let s := t+1
    rw [rCumulativeProg_eq,rCumulativeProg_eq,← sum_ascending n a s step (fun d => rCumulative d (u-3*s))]
    rw [← Finset.sum_tsub_distrib _ (fun i _ => ?_)]
    · apply sum_congr rfl
      intro i _
      simp only [rCapped,cond_ble,Nat.mul_eq,Nat.add_eq,Nat.sub_eq,ite_eq_left h,s]
    · by_cases hd : s ≤ a+step*i
      · rw [ite_eq_left hd]
        exact cap_cut_le h hd
      · rw [ite_eq_right hd]
        exact Nat.zero_le _
  · rename_i h
    rw [rCumulativeProg_eq]
    apply sum_congr rfl
    intro i _
    simp only [rCapped,cond_ble,Nat.mul_eq,Nat.add_eq,Nat.sub_eq,ite_eq_right h,Nat.sub_zero]

end FadicGate

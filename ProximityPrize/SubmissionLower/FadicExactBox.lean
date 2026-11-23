import ProximityPrize.SubmissionLower.FadicCumulativeProgression
import ProximityPrize.SubmissionLower.FadicRamp

set_option autoImplicit false
set_option Elab.async false

namespace FadicGate

open Finset
open scoped BigOperators

private def ramp (theta F N J T : ℕ) : ℕ :=
  if F < N then
    let a := FadicRamp.degree theta (N-1)
    let b := FadicRamp.degree theta F
    let first := a+(25-(theta+a)%26)
    let m := if first ≤ b then (b-first)/26+1 else 0
    rCappedProg (b+1-a) a 1 J T - rCappedProg m first 26 J T
  else 0

private theorem ramp_eq (theta F N J T : ℕ)
    (ht : 26*(N-1) ≤ theta) :
    ramp theta F N J T =
      ∑ q ∈ Ico F N, rCapped (FadicRamp.degree theta q) J T := by
  unfold ramp
  split
  · rename_i h
    dsimp only
    rw [FadicRamp.sum_ramp theta F N h ht (fun d => rCapped d J T),FadicRamp.sum_remove_residue,
        rCappedProg_eq,rCappedProg_eq]
    congr 1
    let a := FadicRamp.degree theta (N-1)
    let b := FadicRamp.degree theta F
    change (∑ i ∈ range (b+1-a), rCapped (a+1*i) J T) = ∑ d ∈ Icc a b, rCapped d J T
    have he : Icc a b = Ico a (b+1) := by ext d; simp only [mem_Icc,mem_Ico]; omega
    rw [he,sum_Ico_eq_sum_range]
    simp only [one_mul,Nat.add_comm a]
  · rename_i h
    have he : Ico F N = ∅ := Ico_eq_empty_of_le (Nat.le_of_not_gt h)
    rw [he,sum_empty]

/-- Exact taper box count using three intervals and no tile traversal. -/
def rExactBox (B J T theta : ℕ) : ℕ :=
  let N := FadicRamp.admissible B theta
  let R := FadicRamp.rise B J theta
  let F := FadicRamp.flatEnd B J theta
  rCappedProg R 0 1 J T + (F-R)*rCapped J J T + ramp theta F N J T

private theorem capped_flat {J d : ℕ} (h : J ≤ d) (T : ℕ) :
    rCapped d J T = rCapped J J T := by
  apply Int.natCast_inj.mp
  rw [rCapped_cast,rCapped_cast]
  exact cappedCount_flat (Nat.cast_nonneg _) (by exact_mod_cast h)

private theorem term_eq (J T theta q : ℕ) :
    FadicRamp.term theta J (fun d => rCapped d J T) q = rTerm J T theta q := by
  unfold FadicRamp.term rTerm rPad FadicRamp.degree
  rw [cond_ble,rMin_eq]
  let d := min q ((theta-26*q)/25)
  change (if 26*q ≤ theta then rCapped (min J d) J T else 0) =
    if 26*q ≤ theta then rCapped d J T else 0
  by_cases h : 26*q ≤ theta
  · simp only [ite_eq_left h]
    by_cases hd : d ≤ J
    · rw [min_eq_right hd]
    · rw [min_eq_left (Nat.lt_of_not_ge hd).le,capped_flat (Nat.lt_of_not_ge hd).le]
  · simp only [ite_eq_right h]

theorem rExactBox_eq (B J T theta : ℕ) :
    rExactBox B J T theta = ∑ q ∈ range (B+1), rTerm J T theta q := by
  unfold rExactBox
  dsimp only
  have ht : 26*(FadicRamp.admissible B theta - 1) ≤ theta := by
    have h : FadicRamp.admissible B theta ≤ theta/26+1 := min_le_right _ _
    omega
  rw [rCappedProg_eq,ramp_eq _ _ _ _ _ ht]
  simp only [one_mul,zero_add]
  simpa only [term_eq] using (FadicRamp.sum_windows B J theta (fun d => rCapped d J T)).symm

theorem rExactBox_cast (B J T theta : ℕ) :
    (rExactBox B J T theta : ℤ) = boxCount B J T theta := by
  rw [rExactBox_eq,boxCount,Nat.cast_sum]
  apply sum_congr rfl
  intro q _
  unfold rTerm rPad term padGrade
  rw [cond_ble,rMin_eq]
  let d := min q ((theta-26*q)/25)
  change ((if 26*q ≤ theta then rCapped d J T else 0 : ℕ) : ℤ) =
    if 26*q ≤ theta then K1_13_2.cappedCount (d : ℤ) J T else 0
  by_cases h : 26*q ≤ theta
  · simp only [ite_eq_left h,rCapped_cast]
  · simp only [ite_eq_right h,Nat.cast_zero]

end FadicGate

import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderCompute
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace ExpandedTaper6970
open Finset
open K1_13_2 (Flag cumulative cappedCount targetCount oldCount)
open Wide50EulerPrimary (cumI cumP cumulative_eq cappedCountI cappedCount_eq
  oldCountI oldCount_eq targetCountI targetCount_eq kernelLowerI)
open scoped BigOperators

def cumLead (d u : ℤ) : ℤ :=
  if d < 0 then 0 else TaperMoments.cumPrefix d.toNat u.toNat


theorem prefix_step (d u : ℤ) : cumLead d (u+1) - cumLead d u = 24 * cumulative d u := by
  by_cases hd : d < 0
  · simp [cumLead,cumulative,hd]
  by_cases hu : u < 0
  · have hx : (u+1).toNat = 0 := by omega
    have hy : u.toNat = 0 := by omega
    simp [cumLead,hd,hx,hy,cumulative,hu]
  · have hx : (u+1).toNat = u.toNat+1 := by omega
    have hdc : (d.toNat : ℤ) = d := by omega
    have huc : (u.toNat : ℤ) = u := by omega
    simp only [cumLead,if_neg hd,hx,TaperMoments.cumPrefix_succ,hdc,huc,add_sub_cancel_left]

theorem prefix_range (d u : ℤ) (n : ℕ) :
    24 * (∑ a ∈ range n, cumulative d (u-(a : ℤ))) =
      cumLead d (u+1)-cumLead d (u+1-n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ,mul_add,ih,← prefix_step]
      push_cast
      ring_nf

def cappedPrefix (d u : ℤ) : ℤ := cumLead d u - cumLead (d-501) (u-1503)

theorem capped_prefix_range (d u : ℤ) (n : ℕ) :
    24 * (∑ a ∈ range n, cappedCountI d (u-(a : ℤ)) 500) =
      cappedPrefix d (u+1)-cappedPrefix d (u+1-n) := by
  simp only [← cappedCount_eq, cappedCount, show ¬ (500 : ℤ) < 0 by decide, if_false]
  rw [sum_sub_distrib,mul_sub,prefix_range]
  have h (a : ℕ) : u-(a : ℤ)-3*(500+1) = u-1503-a := by ring
  simp_rw [h]
  rw [show d-500-1 = d-501 by ring]
  rw [prefix_range]
  unfold cappedPrefix
  ring_nf

def activeFee (q a : ℕ) : ℤ := oldCountI (activeRowFlag q a)
def targetFee (q a : ℕ) : ℤ := targetCountI (rowFlag q a)

private theorem active_nonneg (q a : ℕ) : 0 ≤ activeFee q a := by
  rw [activeFee,← oldCount_eq,← K1_13_2_2_3.proof K1_13_2_2_2.proof]
  positivity

private theorem target_nonneg (q a : ℕ) : 0 ≤ targetFee q a := by
  rw [targetFee,← targetCount_eq,← K1_13_2_2_4.proof K1_13_2_2_2.proof]
  positivity

theorem cell_le_active (q a : ℕ) : (remainderCell q a : ℤ) ≤ activeFee q a := by
  unfold remainderCell
  dsimp only
  split
  · exact active_nonneg q a
  · have h := active_nonneg q a
    unfold activeFee at h ⊢
    omega

theorem cell_le_target (q a : ℕ) : (remainderCell q a : ℤ) ≤ targetFee q a := by
  have ht := target_nonneg q a
  unfold remainderCell
  dsimp only
  split
  · exact ht
  · have hK : (kernelLowerI (rowFlag q a)) =
        oldCountI (rowFlag q a) - targetFee q a := by
      simp [kernelLowerI, targetFee, rowFlag]
    rw [hK]
    omega

def cappedWindow (d u : ℤ) (n : ℕ) : ℤ :=
  cappedPrefix d (u+1) - cappedPrefix d (u+1-n)

def targetWindow (d u : ℤ) (n : ℕ) : ℤ :=
  cumLead d (u+1) - cumLead d (u+1-n)

def activeRun (q lo n : ℕ) : ℤ :=
  let d : ℤ := (min q (cap q) : ℕ)
  let u := if lo < 3000 then 24 * n * cappedCountI d 1679 500
    else cappedWindow d (4678-(lo : ℤ)) n
  u - cappedWindow d (1678-(lo : ℤ)) n

def targetRun (q lo n : ℕ) : ℤ :=
  let d : ℤ := (min q (cap q) : ℕ)
  let bal := 2999-(q : ℤ)+d
  if bal < 0 then 0 else
    let rem := min d (bal/4)+1
    let u := 4678-(q : ℤ)-(lo : ℤ)
    let v := 1678-(lo : ℤ)
    targetWindow d u n - targetWindow (d-rem) (u-3*rem) n -
      targetWindow d v n + targetWindow (d-rem) v n

theorem activeRun_eq (q lo n : ℕ) (h : lo+n ≤ 3000 ∨ 3000 ≤ lo) :
    24 * (∑ a ∈ range n, activeFee q (lo+a)) = activeRun q lo n := by
  let d : ℤ := (min q (cap q) : ℕ)
  have hrow (a : ℕ) :
      activeFee q (lo+a) = cappedCountI d (min 1679 (4678-(lo : ℤ)-(a : ℤ))) 500 -
        cappedCountI d (1678-(lo : ℤ)-(a : ℤ)) 500 := by
    unfold activeFee oldCountI activeRowFlag rowFlag
    dsimp only
    have hU : (2999 : ℤ) - (((lo+a : ℕ) : ℤ)-1679) = 4678-(lo : ℤ)-(a : ℤ) := by
      push_cast; ring
    have hL : -(((lo+a : ℕ) : ℤ)-1679)-1 = 1678-(lo : ℤ)-(a : ℤ) := by
      push_cast; ring
    rw [hU,hL,min_eq_right (by omega : (1678 : ℤ)-(lo : ℤ)-(a : ℤ) ≤
      min 1679 (4678-(lo : ℤ)-(a : ℤ)))]
  simp_rw [hrow]
  unfold activeRun cappedWindow
  dsimp only
  rw [sum_sub_distrib,mul_sub,capped_prefix_range]
  by_cases hx : lo < 3000
  · rw [if_pos hx]
    have hi (a : ℕ) (ha : a ∈ range n) : min (1679 : ℤ) (4678-(lo : ℤ)-(a : ℤ)) = 1679 := by
      have ha' := mem_range.mp ha
      exact min_eq_left (by omega)
    rw [sum_congr rfl (fun a ha => congrArg (fun v => cappedCountI d v 500) (hi a ha))]
    simp only [sum_const,card_range,nsmul_eq_mul]
    ring_nf
    rfl
  · rw [if_neg hx]
    have hi (a : ℕ) : min (1679 : ℤ) (4678-(lo : ℤ)-(a : ℤ)) =
        4678-(lo : ℤ)-(a : ℤ) := min_eq_right (by omega)
    simp_rw [hi]
    rw [capped_prefix_range]

theorem targetRun_eq (q lo n : ℕ) :
    24 * (∑ a ∈ range n, targetFee q (lo+a)) = targetRun q lo n := by
  let d : ℤ := (min q (cap q) : ℕ)
  let bal : ℤ := 2999-(q : ℤ)+d
  let rem : ℤ := min d (bal/4)+1
  let u : ℤ := 4678-(q : ℤ)-(lo : ℤ)
  let v : ℤ := 1678-(lo : ℤ)
  have hmain (a : ℕ) :
      targetFee q (lo+a) = if bal < 0 then 0 else
        cumulative d (u-(a : ℤ)) - cumulative (d-rem) (u-3*rem-(a : ℤ)) -
          cumulative d (v-(a : ℤ)) + cumulative (d-rem) (v-(a : ℤ)) := by
    have hB : (rowFlag q (lo+a)).order-1-(rowFlag q (lo+a)).lower+(rowFlag q (lo+a)).degree = bal := by
      simp only [rowFlag]
      dsimp [bal,d]
      ring
    have hU : (rowFlag q (lo+a)).order-1 = u-(a : ℤ) := by
      simp only [rowFlag]
      dsimp [u]
      push_cast
      ring
    have hV : (rowFlag q (lo+a)).lower-1 = v-(a : ℤ) := by
      simp only [rowFlag]
      dsimp [v]
      push_cast
      ring
    unfold targetFee targetCountI
    dsimp only
    rw [hB,hU,hV]
    by_cases hb : bal < 0
    · simp only [if_pos hb]
    · simp only [if_neg hb, ← cumulative_eq]
      change cumulative d (u-(a : ℤ)) - cumulative (d-rem) (u-(a : ℤ)-3*rem) -
          cumulative d (v-(a : ℤ)) + cumulative (d-rem) (v-(a : ℤ)) = _
      rw [show u-(a : ℤ)-3*rem = u-3*rem-(a : ℤ) by ring]
  simp_rw [hmain]
  change _ = if bal < 0 then 0 else
    targetWindow d u n - targetWindow (d-rem) (u-3*rem) n -
      targetWindow d v n + targetWindow (d-rem) v n
  by_cases hb : bal < 0
  · simp only [if_pos hb,sum_const_zero,mul_zero]
  · simp only [if_neg hb,sum_add_distrib,sum_sub_distrib,mul_add,mul_sub,prefix_range,targetWindow]

end ExpandedTaper6970

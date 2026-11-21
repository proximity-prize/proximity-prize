import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinAggregate

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open private qMin from ProximityPrize.SubmissionLower.Low48PrimaryPivotBinWeight
open private binWeight from ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum
open private binAt_eq_interval from ProximityPrize.SubmissionLower.Low48PrimaryPivotBinAggregate

private def allFree (j q : ℤ) : Prop :=
  j/3 ≤ 1650-q ∧ 3*q-9900+5*j ≤ 0 ∧ q-4950+3*j ≤ 0 ∧ 2*q-4950+2*j ≤ 0

private instance (j q : ℤ) : Decidable (allFree j q) := by unfold allFree; infer_instance

private def allCharged (j q : ℤ) : Prop :=
  1650 < q ∨ j < 3*q-9900+5*j ∨ 2*j < 3*(q-4950+3*j) ∨ j < 2*(2*q-4950+2*j)

private instance (j q : ℤ) : Decidable (allCharged j q) := by unfold allCharged; infer_instance

private theorem no_charge (j q : ℤ) (h : allFree j q) :
    uncharged j q = totalAtIndex j := by
  rw [uncharged_eq, totalAtIndex_eq, min_eq_left h.1]
  apply sum_congr rfl
  intro f hf
  simp only [mem_Ico] at hf
  have hzero :
      max 0 (max (3*q-9900+5*j-3*f) (max (q-4950+3*j-2*f) (2*q-4950+2*j-f))) = 0 := by
    have h₁ := h.2.1
    have h₂ := h.2.2.1
    have h₃ := h.2.2.2
    omega
  rw [hzero,sub_zero,max_eq_right (by omega)]

private theorem all_charge (j q : ℤ) (h : allCharged j q) :
    uncharged j q = 0 := by
  rw [uncharged_eq]
  apply sum_eq_zero
  intro f hf
  simp only [mem_Ico] at hf
  have hf1 := hf.1
  have hf2 := hf.2
  rw [max_eq_left]
  unfold allCharged at h
  omega

private def pricedBin (w : Window) (j q total : ℤ) : ℤ :=
  let volume := binWeight w j q
  if volume = 0 ∨ allFree j q then 0
  else if allCharged j q then volume*total
  else volume*(total-uncharged j q)

private theorem pricedBin_eq (w : Window) (j q : ℤ) :
    pricedBin w j q (totalAtIndex j) = binWeight w j q*(totalAtIndex j-uncharged j q) := by
  unfold pricedBin
  dsimp only
  split
  · rename_i h
    rcases h with h | h
    · rw [h,zero_mul]
    · rw [no_charge j q h,sub_self,mul_zero]
  · split
    · rename_i h
      rw [all_charge j q h,sub_zero]
    · rfl

private def startQ (w : Window) : ℤ :=
  max (qMin w) (indexLo w-(w.gradeHi : ℤ)+3001)

private def stopQ (w : Window) (j : ℕ) : ℤ :=
  min (orderHi w) (min ((j : ℤ)+1) (1651-(w.offsetLo : ℤ))-(w.gradeLo : ℤ)+3000)

private def trimIndex (w : Window) (j : ℕ) : ℤ :=
  let total := totalAtIndex j
  let lo := startQ w
  let hi := stopQ w j
  ((List.range (hi-lo).toNat).map fun i : ℕ => pricedBin w j (lo+(i : ℤ)) total).sum

private theorem trimIndex_eq (w : Window) (j : ℕ) :
    trimIndex w j = binAt w j := by
  rw [binAt_eq_interval]
  have h (q : ℤ) : binWeight w j q ≠ 0 → startQ w ≤ q ∧ q < stopQ w j ∨
      q < qMin w ∨ orderHi w ≤ q := by
    simp only [binWeight,startQ,stopQ,indexLo,max_le_iff,lt_min_iff]
    omega
  let term (q : ℤ) := binWeight w j q * (totalAtIndex j-uncharged j q)
  have hs (q : ℤ) (hq : q ∈ Ico (qMin w) (orderHi w)) :
      term q = if q ∈ Ico (startQ w) (stopQ w j) then term q else 0 := by
    by_cases hh : q ∈ Ico (startQ w) (stopQ w j)
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      have hz : binWeight w j q = 0 := by
        by_contra hn
        have hp := h q hn
        simp only [mem_Ico] at hh hq
        omega
      simp [term,hz]
  change trimIndex w j = ∑ q ∈ Ico (qMin w) (orderHi w), term q
  rw [sum_congr rfl hs,← sum_filter]
  have hfilter : (Ico (qMin w) (orderHi w)).filter
      (fun q => q ∈ Ico (startQ w) (stopQ w j)) = Ico (startQ w) (stopQ w j) := by
    ext q
    simp only [mem_filter,mem_Ico,startQ,stopQ,max_le_iff,lt_min_iff]
    omega
  rw [hfilter,Int.Ico_eq_finset_map,sum_map]
  unfold trimIndex
  change (∑ k ∈ range (stopQ w j-startQ w).toNat,
    pricedBin w j (startQ w+(k:ℤ)) (totalAtIndex j)) = _
  apply sum_congr rfl
  intro k _
  exact pricedBin_eq w _ _

def binAtFast (w : Window) (j : ℕ) : ℤ :=
  if (j : ℤ)+1 ≤ indexLo w then 0 else trimIndex w j

theorem binAtFast_eq (w : Window) (j : ℕ) : binAtFast w j = binAt w j := by
  unfold binAtFast
  split
  · rename_i h
    rw [binAt_eq_interval]
    symm
    apply sum_eq_zero
    intro q _
    have hz : binWeight w j q = 0 := by
      unfold binWeight
      unfold indexLo at h
      omega
    rw [hz,zero_mul]
  · exact trimIndex_eq w j

#print axioms binAtFast_eq
end Low48PrimaryPivot

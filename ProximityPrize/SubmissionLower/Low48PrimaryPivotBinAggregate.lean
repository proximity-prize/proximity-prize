import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinIndex

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open Low48PrimaryPivot (qMin)
open Low48PrimaryPivot (binWeight)
open Low48PrimaryPivot (mem_indexFiber)

attribute [local irreducible] Finset.univ

theorem binAt_eq_interval (w : Window) (j : ℕ) :
    binAt w j = ∑ q ∈ Ico (qMin w) (orderHi w),
      binWeight w j q * (totalAtIndex j-uncharged j q) := by
  rw [Int.Ico_eq_finset_map,sum_map]
  have hsize : (orderHi w-qMin w).toNat = w.diagonalHi+1-w.diagonalLo := by
    simp only [orderHi,qMin]
    omega
  unfold binAt
  change (∑ i ∈ range (w.diagonalHi+1-w.diagonalLo),
      if binWeight w j (qMin w+(i : ℤ)) = 0 then 0
      else binWeight w j (qMin w+(i : ℤ)) *
        (totalAtIndex j-uncharged j (qMin w+(i : ℤ)))) = _
  rw [hsize]
  apply sum_congr rfl
  intro i _
  change _ = binWeight w j (qMin w+(i : ℤ)) *
    (totalAtIndex j-uncharged j (qMin w+(i : ℤ)))
  split
  · rename_i h
    rw [h,zero_mul]
  · rfl

private theorem paid_count (j : ℕ) (q : ℤ) (hj : j ≤ 1650) :
    (∑ c ∈ indexFiber j, if ((columnPoint c).contact : ℤ) < q then (1 : ℤ) else 0) =
      totalAtIndex j-uncharged j q := by
  have point (c : Column) :
      (if ((columnPoint c).contact : ℤ) < q then (1 : ℤ) else 0) =
        1-(if q ≤ ((columnPoint c).contact : ℤ) then 1 else 0) := by
    by_cases h : ((columnPoint c).contact : ℤ) < q
    · simp [h, not_le.mpr h]
    · simp [h,le_of_not_gt h]
  simp_rw [point]
  rw [sum_sub_distrib,← natCast_card_filter,uncharged_card j q hj]
  simp [indexFiber_card j hj]

private theorem index_fee (w : Window) (j : ℕ) (hj : j ≤ 1650) (hg : w.gradeLo ≤ w.gradeHi) :
    (∑ c ∈ indexFiber j, columnFee2 w (columnPoint c)) = 2*binAt w j := by
  have expand (c : Column) (hc : c ∈ indexFiber j) :
      columnFee2 w (columnPoint c) =
        2*(∑ q ∈ Ico (qMin w) (orderHi w),
          if ((columnPoint c).contact : ℤ) < q then binWeight w j q else 0) := by
    have hkey := mem_indexFiber.mp hc
    rw [columnFee2_eq_bins w _ hg (hkey.trans_le hj),hkey]
  rw [sum_congr rfl expand,← mul_sum,sum_comm,binAt_eq_interval]
  congr 1
  apply sum_congr rfl
  intro q _
  have hp (c : Column) :
      (if ((columnPoint c).contact : ℤ) < q then binWeight w j q else 0) =
        binWeight w j q * (if ((columnPoint c).contact : ℤ) < q then 1 else 0) := by
    split <;> simp
  simp_rw [hp]
  rw [← mul_sum,paid_count j q hj]

def binCompute (w : Window) : ℤ := ((List.range 1651).map (binAt w)).sum

theorem fee_eq_binCompute (w : Window) (hg : w.gradeLo ≤ w.gradeHi) :
    (∑ c : Column, columnFee2 w (columnPoint c)) = 2*binCompute w := by
  let idx (c : Column) := (columnPoint c).index
  let chargeAt (c : Column) := columnFee2 w (columnPoint c)
  have hs : (∑ c : Column, chargeAt c) = ∑ c ∈ univ with idx c ∈ range 1651, chargeAt c := by
    rw [sum_filter]
    apply sum_congr rfl
    intro c _
    by_cases hc : idx c ∈ range 1651
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc]
      simp only [mem_range] at hc
      exact ite_eq_right (by change ¬idx c≤1650; omega)
  change (∑ c : Column, chargeAt c) = _
  rw [hs,← sum_fiberwise_eq_sum_filter univ (range 1651) idx chargeAt]
  unfold binCompute
  change (∑ j ∈ range 1651, ∑ c ∈ indexFiber j, columnFee2 w (columnPoint c)) =
      2*(∑ j ∈ range 1651, binAt w j)
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  exact index_fee w j (by have h := mem_range.mp hj; omega) hg

theorem debit_le_binCompute (w : Window) (hg : w.gradeLo ≤ w.gradeHi) :
    (debit w : ℤ) ≤ binCompute w := by
  have h := debit_le_fee w hg
  rw [fee_eq_binCompute w hg] at h
  omega

#print axioms debit_le_binCompute
end Low48PrimaryPivot

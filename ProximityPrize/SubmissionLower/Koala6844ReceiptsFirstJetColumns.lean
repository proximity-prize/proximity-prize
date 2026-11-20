import ProximityPrize.SubmissionLower.Koala6844ReceiptsAffineRows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
open SecondJetRelaxedGlobalIndex (budget yCount)

set_option autoImplicit false
set_option maxHeartbeats 4200000

def slopeColumnCap (cut r : Nat) : Nat := (cut+r-1)/degree

private theorem slopeColumnCap_split (cut r : Nat) (hcut : cut ≠ 0) (hr : r < degree) :
    slopeColumnCap cut r = if r < degree-(cut-1)%degree then (cut-1)/degree
      else (cut-1)/degree+1 := by
  unfold slopeColumnCap degree at *
  have hrem := Nat.mod_lt (cut-1) (by decide : 0 < 131071)
  have hmod := Nat.mod_add_div (cut-1) 131071
  split_ifs <;> omega

private def slopeColumnCount (cut : Nat) (constant : Bool) (r : Nat) : Int :=
  if r ≤ slopeColumnCap cut r then firstJetAffineRow cut (slopeColumnCap cut r) constant r else 0

private theorem sum_Ico_shift (f : Nat → Int) (a b : Nat) :
    (∑ i ∈ Finset.Ico a b, f i) = ∑ i ∈ Finset.range (b-a), f (a+i) := by
  symm
  apply Finset.sum_bij (fun i _ => a+i)
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Ico] at *
    omega
  · intro i _ j _ h
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    refine ⟨j-a,Finset.mem_range.mpr (by omega),by omega⟩
  · intros
    rfl

private theorem firstJetAffineColumns_eq_slopeSum (cut B : Nat) (constant : Bool)
    (hcut : cut ≠ 0) (hB : B < degree) :
    firstJetAffineColumns cut B constant = ∑ r ∈ Finset.range (B+1), slopeColumnCount cut constant r := by
  let cap := (cut-1)/degree
  let turn := degree-(cut-1)%degree
  let begin := min turn (min (B+1) (cap+1))
  let finish := min B (cap+1)+1
  have hlB : begin ≤ B+1 := (min_le_right _ _).trans (min_le_left _ _)
  have hhB : finish ≤ B+1 := Nat.add_le_add_right (min_le_left _ _) 1
  have hsplit : ((Finset.range (B+1)).filter (fun r => r ≤ slopeColumnCap cut r)) =
      Finset.range begin ∪ Finset.Ico turn finish := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_range,Finset.mem_Ico]
    by_cases hrB : r < B+1
    · have hr : r < degree := (Nat.le_of_lt_succ hrB).trans_lt hB
      rw [slopeColumnCap_split cut r hcut hr]
      change _ ∧ r ≤ (if r < turn then cap else cap+1) ↔ _
      dsimp only [begin,finish]
      split_ifs <;> omega
    · omega
  have hdisj : Disjoint (Finset.range begin) (Finset.Ico turn finish) := by
    apply Finset.disjoint_left.mpr
    simp only [Finset.mem_range, Finset.mem_Ico]
    have hl := min_le_left turn (min (B+1) (cap+1))
    intro r h₀ h₁
    omega
  unfold slopeColumnCount
  rw [← Finset.sum_filter, hsplit, Finset.sum_union hdisj, firstJetAffineColumns_eq_interval_sum cut B constant hcut]
  change (∑ i ∈ Finset.range begin, firstJetAffineRow cut cap constant i) +
      (∑ i ∈ Finset.range (finish-turn), firstJetAffineRow cut (cap+1) constant (turn+i)) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    have hl := min_le_left turn (min (B+1) (cap+1))
    have hlt := Finset.mem_range.mp hr
    have hturn : r < turn := by omega
    have hrB : r < degree := (Nat.le_of_lt_succ (hlt.trans_le hlB)).trans_lt hB
    rw [slopeColumnCap_split cut r hcut hrB, ite_eq_left hturn]
  · rw [← sum_Ico_shift (firstJetAffineRow cut (cap+1) constant)]
    apply Finset.sum_congr rfl
    intro r hr
    have hmem := Finset.mem_Ico.mp hr
    have hturn : ¬ r < turn := by omega
    have hrB : r < degree := (Nat.le_of_lt_succ (hmem.2.trans_le hhB)).trans_lt hB
    rw [slopeColumnCap_split cut r hcut hrB, ite_eq_right hturn]

def firstJetColumnRow (cut U L r : Nat) (weighted : Bool) : Int :=
  ∑ y ∈ Finset.range (yCount (fun _ => cut) degree U 0 r),
    ((budget (fun _ => cut) degree 0 r - degree*y : Nat) : Int) *
      (if weighted then ((L+1-r-y : Nat) : Int) else 1)

private theorem firstJetColumnRow_zero (cut U L r : Nat) (weighted : Bool)
    (h : cut ≤ (degree-1)*r) : firstJetColumnRow cut U L r weighted = 0 := by
  unfold firstJetColumnRow
  apply Finset.sum_eq_zero
  intro y _
  simp [budget, Nat.sub_eq_zero_of_le h]

private theorem slopeWindow_eq (cut U r : Nat) (hcut : cut ≠ 0)
    (hr : r ≤ slopeColumnCap cut r) (hU : slopeColumnCap cut r ≤ U) :
    yCount (fun _ => cut) degree U 0 r = slopeColumnCap cut r + 1 - r := by
  unfold yCount budget slopeColumnCap degree at *
  simp only [Nat.mul_zero, Nat.sub_zero]
  omega

private theorem slopeWeight_eq (cut r y : Nat) (hcut : cut ≠ 0)
    (h : r+y ≤ slopeColumnCap cut r) :
    ((budget (fun _ => cut) degree 0 r - degree*y : Nat) : Int) =
      (cut : Int)+r-(degree : Int)*((r : Int)+y) := by
  have hr : (degree-1)*r ≤ cut := by unfold slopeColumnCap degree at *; omega
  have hq : degree*y ≤ cut-(degree-1)*r := by unfold slopeColumnCap degree at *; omega
  unfold budget
  simp only [Nat.mul_zero,Nat.sub_zero]
  rw [Nat.cast_sub hq, Nat.cast_sub hr]
  push_cast [Nat.cast_sub (by decide : 1 ≤ degree)]
  ring

private theorem firstJetColumnRow_eq (cut U L r : Nat) (weighted : Bool)
    (hcut : cut ≠ 0) (hcap : slopeColumnCap cut r ≤ U) (hUL : U ≤ L) :
    firstJetColumnRow cut U L r weighted =
      if weighted then (L : Int)*slopeColumnCount cut false r+slopeColumnCount cut true r
      else slopeColumnCount cut false r := by
  by_cases hr : r ≤ slopeColumnCap cut r
  · unfold firstJetColumnRow slopeColumnCount
    rw [slopeWindow_eq cut U r hcut hr hcap]
    simp only [ite_eq_left hr]
    rw [firstJetAffineRow_eq_sum cut _ r false hr, firstJetAffineRow_eq_sum cut _ r true hr]
    cases weighted
    · simp only [Bool.false_eq_true, ite_false, mul_one]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' := Finset.mem_range.mp hy
      exact slopeWeight_eq cut r y hcut (by omega)
    · simp only [ite_true, mul_one]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' := Finset.mem_range.mp hy
      have htotal : r+y ≤ slopeColumnCap cut r := by omega
      have hR : r ≤ L+1 := by omega
      have hyL : y ≤ L+1-r := by omega
      rw [slopeWeight_eq cut r y hcut htotal, Nat.cast_sub hyL, Nat.cast_sub hR]
      push_cast
      ring
  · have hzero : cut ≤ (degree-1)*r := by unfold slopeColumnCap degree at *; omega
    rw [firstJetColumnRow_zero _ _ _ _ _ hzero]
    unfold slopeColumnCount
    simp only [ite_eq_right hr, mul_zero, Nat.cast_zero, zero_add, ite_self]

theorem firstJetColumnRows_eq (cut B U L : Nat) (weighted : Bool) (hB : B < degree)
    (hcap : slopeColumnCap cut B ≤ U) (hUL : U ≤ L) :
    (∑ r ∈ Finset.range (B+1), firstJetColumnRow cut U L r weighted) =
      if weighted then firstJetAffineColumns cut B false*(L : Int)+firstJetAffineColumns cut B true
      else firstJetAffineColumns cut B false := by
  by_cases hcut : cut = 0
  · have hz : ∀ r, firstJetColumnRow cut U L r weighted = 0 := fun r =>
      firstJetColumnRow_zero _ _ _ _ _ (by simp [hcut])
    rw [Finset.sum_eq_zero (fun r _ => hz r)]
    simp [hcut,firstJetAffineColumns]
  · have hrows : (∑ r ∈ Finset.range (B+1), firstJetColumnRow cut U L r weighted) =
        ∑ r ∈ Finset.range (B+1), (if weighted then
          (L : Int)*slopeColumnCount cut false r+slopeColumnCount cut true r
          else slopeColumnCount cut false r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrB : r ≤ B := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hmono : slopeColumnCap cut r ≤ slopeColumnCap cut B :=
        Nat.div_le_div_right (by omega)
      exact firstJetColumnRow_eq cut U L r weighted hcut (hmono.trans hcap) hUL
    rw [hrows]
    cases weighted
    · simp only [Bool.false_eq_true, ite_false, firstJetAffineColumns_eq_slopeSum cut B _ hcut hB]
    · simp only [ite_true,Finset.sum_add_distrib,←Finset.mul_sum,
        firstJetAffineColumns_eq_slopeSum cut B _ hcut hB]
      rw [mul_comm (L : Int)]

end ProximityPrize.SubmissionLower.Koala6844Receipts

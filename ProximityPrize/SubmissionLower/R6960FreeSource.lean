import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.FreeSource
open Finset
open K1_14 (Shape FX L shapeSum triangle slots)
open K1_14_1 (PoleData CRTLift evaluated)
open P1_7 (Bank debit)
open P1_7_5 (kept)
open HelperSource (cutoffCount WidthGuard)

def rawGain (s : Shape) (A h r : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => cutoffCount s A h r+j-q*(131071-h))

/-- When the slope lower bound exceeds the bank cap, the powered gain reduces
to the unpenalized raw volume. -/
theorem gain_eq_raw (s : Shape) (A h r : ℕ) (hk : 1≤131071-h) :
    HelperSource.gain s A h r (s.J+1) 0 0 = rawGain s A h r := by
  unfold HelperSource.gain rawGain shapeSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
  have hjs : j<s.J+1 := Nat.lt_succ_of_le (hj'.trans (min_le_right _ _))
  have hjq : j≤q := hj'.trans (min_le_left _ _)
  have hweight : j≤q*(131071-h) := hjq.trans (by
    simpa using Nat.mul_le_mul_left q hk)
  have hwidth : s.m*A+j-q*(131071-h)-2*h*r = cutoffCount s A h r+j-q*(131071-h) := by
    unfold cutoffCount
    omega
  simp [HelperSource.coordinateGain, HelperSource.orderCap, Nat.div_eq_of_lt hjs,
    kept, slots, hwidth]

/-- The cutoffs in a buffered row and its reserved shifts stay strictly below
the contact-vanishing bound. -/
theorem buffered_fit (t : Bank) (A h r : ℕ) (width : WidthGuard t A h r) :
    (cutoffCount t.shape A h r-1)+2*h*r < t.shape.m*A := by
  change t.shape.B * (131071-h) < t.shape.m*A-2*h*r at width
  unfold cutoffCount
  omega

/-- The native CRT source supplies a nonzero buffered row once its raw volume
exceeds its certified physical and grouped-pole debits. -/
theorem nonzero_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (t : Bank) (A r : ℕ) (hh : 0<h) (hk : h≤131070) (checked : P3_7_1.BankOK t)
    (width : WidthGuard t A h r) (positive : debit h t < rawGain t.shape A h r) :
    ∃ P ∈ evaluated Crt word t.shape (cutoffCount t.shape A h r-1), P≠0 := by
  let N := cutoffCount t.shape A h r
  have hw : t.shape.B*(131071-h)<N := width
  have hs : N-1+1=N := by omega
  have floor := HelperSource.crt_rank_floor Crt word t hh hk checked.nodes checked.moment.1
    checked.moment.2 (N-1) (by
      intro q hq j _
      rw [hs]
      exact (Nat.mul_le_mul_right _ hq).trans (hw.le.trans (Nat.le_add_right N j)))
  unfold K1_14_1.rawVolumeAt at floor
  rw [hs] at floor
  have hf : rawGain t.shape A h r ≤ debit h t +
      ∑ W ∈ range N, Module.finrank FX (evaluated Crt word t.shape W) := floor
  exact HelperSource.nonzero_of_supply Crt word t.shape N (by omega)

/-- Compute the two heights without enumerating cutoffs or slope/ordinate pairs. -/
def compressedSurplus (t : Bank) (A h r : ℕ) : ℤ :=
  (HelperSource.compressedPhase t.shape A h r (t.shape.J+1) 0 0 0 -
    HelperSource.compressedPhase t.shape A h r (t.shape.J+1) 0 0 1 : ℕ) - (debit h t : ℤ)

theorem compressedSurplus_eq (t : Bank) (A h r : ℕ) :
    compressedSurplus t A h r = HelperSource.surplus t A h r (t.shape.J+1) 0 0 := by
  unfold compressedSurplus HelperSource.surplus
  rw [HelperSource.gain_eq_compressed _ _ _ _ _ _ _ (Nat.succ_pos _)]

theorem rawGain_positive (t : Bank) (A lo h r : ℕ) (hl : lo≤h) (hk : h≤131070)
    (positive : 0<compressedSurplus t A lo r)
    (increasing : compressedSurplus t A lo r ≤ compressedSurplus t A (lo+1) r) :
    debit h t < rawGain t.shape A h r := by
  rw [compressedSurplus_eq t A lo r] at positive
  rw [compressedSurplus_eq t A lo r, compressedSurplus_eq t A (lo+1) r] at increasing
  rw [← gain_eq_raw _ _ _ _ (by omega)]
  exact HelperSource.surplus_positive _ _ _ _ _ _ _ _ hl hk positive increasing

#print axioms nonzero_row
#print axioms rawGain_positive

end Lower6960.FreeSource

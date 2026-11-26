import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCertificate
import ProximityPrize.SubmissionLower.R6960FreeSource6960

set_option Elab.async false

namespace Research6966.FarSourceArithmetic
open Finset
open K1_14 (Shape slots)
open K1_14_4 (shapeSum_swap)
open Lower6960.HelperSource (phaseLayer compressedPhase column_eq gain_eq_compressed surplus WidthGuard)
open HelperWindowPrefix (volume volume_eq_shapeSum)
open HelperWindowGrouping (sumCount sumCount_eq)
set_option maxHeartbeats 1000000

abbrev agreement : ℕ := 179769
abbrev firstHeight : ℕ := 2500
abbrev heightCap : ℕ := 33677

def fastLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  let j := (i+δ)*d
  let used := (i+δ)*c
  let step := 131071-h
  if j≤s.J ∧ used+j≤s.B then
    slots s.U ((i+δ)*v)*
      volume (s.m*A-2*h*(r+i)-(step-1)*j) (s.B-used-j) (s.J-j) step
  else 0

theorem fastLayer_eq (s : Shape) (A h r d c v δ i : ℕ) (narrow : s.J<131071-h) :
    fastLayer s A h r d c v δ i = phaseLayer s A h r d c v δ i := by
  unfold fastLayer phaseLayer
  dsimp only
  rw [P1_7_1_3.evaluate_eq]
  simp_rw [column_eq]
  let j := (i+δ)*d
  let used := (i+δ)*c
  let step := 131071-h
  let stop := s.m*A-2*h*(r+i)-(step-1)*j
  let B := s.B-used-j
  let J := s.J-j
  let box : Shape := ⟨s.m,B,J,s.U⟩
  change (if j≤s.J ∧ used+j≤s.B then slots s.U ((i+δ)*v)*volume stop B J step else 0) =
    slots s.U ((i+δ)*v)*
      ∑ a ∈ range (s.J+1-j), ∑ q ∈ Ico (j+a) (s.B+1-used),
        (s.m*A+(j+a)-q*step-2*h*(r+i))
  by_cases room : j≤s.J ∧ used+j≤s.B
  · rw [ite_eq_left room]
    have nw : box.J<step := (Nat.sub_le _ _).trans_lt narrow
    rw [show volume stop B J step = _ from volume_eq_shapeSum box stop step nw,
      ← shapeSum_swap box, show s.J+1-j=J+1 by dsimp only [J];omega]
    congr 1
    apply sum_congr rfl
    intro a _
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
    have lengths : s.B+1-used-(j+a)=B+1-a := by dsimp only [B];omega
    rw [lengths]
    apply sum_congr rfl
    intro t _
    have pos : 1≤step := (Nat.zero_le _).trans_lt narrow
    have fixed : (step-1)*j+j=j*step := by
      have eq := congrArg (·*j) (Nat.sub_add_cancel pos : step-1+1=step)
      rwa [Nat.add_mul,Nat.one_mul,Nat.mul_comm step j] at eq
    have pays : a≤(a+t)*step := by
      exact (Nat.le_add_right a t).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a+t) pos)
    have product : (j+a+t)*step=j*step+(a+t)*step := by
      rw [Nat.add_assoc,Nat.add_mul]
    change stop+a-step*(a+t) = s.m*A+(j+a)-(j+a+t)*step-2*h*(r+i)
    rw [Nat.mul_comm step (a+t), product]
    dsimp only [stop]
    omega
  · rw [ite_eq_right room]
    symm
    apply mul_eq_zero.mpr
    right
    by_cases enough : j≤s.J
    · have large : s.B+1-used≤j := by omega
      apply sum_eq_zero
      intro a _
      rw [sum_Ico_eq_sum_range, show s.B+1-used-(j+a)=0 by omega, range_zero, sum_empty]
    · rw [show s.J+1-j=0 by omega,range_zero,sum_empty]

def fastPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  sumCount (fastLayer s A h r d c v δ) (s.J/d+1)

theorem fastPhase_eq (s : Shape) (A h r d c v δ : ℕ) (narrow : s.J<131071-h) :
    fastPhase s A h r d c v δ = compressedPhase s A h r d c v δ := by
  unfold fastPhase compressedPhase
  rw [sumCount_eq,P1_7_1_3.evaluate_eq]
  exact sum_congr rfl (fun i _=>fastLayer_eq s A h r d c v δ i narrow)

structure Request where
  bank : P1_7.Bank
  reserve : ℕ
  slope : ℕ
  excess : ℕ
  seed : ℕ

def value (q : Request) (h : ℕ) : ℤ :=
  (fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 0-
    fastPhase q.bank.shape agreement h q.reserve q.slope q.excess q.seed 1 : ℕ) -
      (P1_7.debit h q.bank : ℤ)

theorem value_eq (q : Request) (h : ℕ) (pos : 0<q.slope) (narrow : q.bank.shape.J<131071-h) :
    value q h=surplus q.bank agreement h q.reserve q.slope q.excess q.seed := by
  unfold value surplus
  rw [gain_eq_compressed _ _ _ _ _ _ _ pos,fastPhase_eq _ _ _ _ _ _ _ _ narrow,fastPhase_eq _ _ _ _ _ _ _ _ narrow]

structure Checked (q : Request) : Prop where
  rank : P3_7_1.BankOK q.bank
  width : WidthGuard q.bank agreement firstHeight q.reserve
  reserve_fit : 2*q.reserve≤q.bank.shape.B
  positive_slope : 0<q.slope
  narrow : q.bank.shape.J<131071-(firstHeight+1)
  positive : 0<value q firstHeight
  increases : value q firstHeight≤value q (firstHeight+1)

theorem Checked.window {q : Request} (cert : Checked q) {h : ℕ} (lo : firstHeight≤h) (hi : h≤heightCap) :
    WidthGuard q.bank agreement h q.reserve :=
  Lower6960.HelperSource.width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width

theorem Checked.gain {q : Request} (cert : Checked q) {h : ℕ} (lo : firstHeight≤h) (hi : h≤heightCap) :
    P1_7.debit h q.bank<Lower6960.HelperSource.gain q.bank.shape agreement h q.reserve q.slope q.excess q.seed := by
  have earlier := cert.narrow.trans_le (Nat.sub_le_sub_left (Nat.le_succ firstHeight) _)
  have pos := cert.positive
  have next := cert.increases
  rw [value_eq _ _ cert.positive_slope earlier] at pos
  rw [value_eq _ _ cert.positive_slope earlier,value_eq _ _ cert.positive_slope cert.narrow] at next
  exact Lower6960.HelperSource.surplus_positive _ _ _ _ _ _ _ _ lo (hi.trans (by decide)) pos next

end Research6966.FarSourceArithmetic

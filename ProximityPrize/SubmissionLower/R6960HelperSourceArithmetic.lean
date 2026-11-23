import ProximityPrize.SubmissionLower.R6960HelperSource

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.HelperSource
open Finset
open K1_14 (Shape shapeSum slots)
open P1_7 (Bank debit)
open P1_7_5 (kept)
open P1_7_6 (linearEnd lt_linearEnd)
open P1_7_1_3 (evaluate evaluate_eq)
open private slots_anti from ProximityPrize.SubmissionLower.UpperBranch6

/-- Positive part of an arithmetic progression, summed using its support length. -/
def clippedSum (base step bound cap : ℕ) : ℕ :=
  let len := linearEnd base step bound cap
  len*bound-(len*base+step*(len*(len-1)/2))

theorem clippedSum_eq (base step bound cap : ℕ) :
    clippedSum base step bound cap = ∑ a ∈ range cap, (bound-(base+step*a)) := by
  let len := linearEnd base step bound cap
  have hle : len ≤ cap := by
    by_contra! bad
    exact (lt_linearEnd base step bound cap cap).mp bad |>.1.false
  rw [← sum_subset (range_mono hle) (f := fun a => bound-(base+step*a)) (by
    intro a ha hna
    apply Nat.sub_eq_zero_of_le
    have hn := fun h => hna (mem_range.mpr ((lt_linearEnd base step bound cap a).mpr
      ⟨mem_range.mp ha,h⟩))
    exact Nat.le_of_not_gt hn)]
  have hadd : (∑ a ∈ range len, (bound-(base+step*a))) +
      (∑ a ∈ range len, (base+step*a)) = len*bound := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ range len, bound := by
        apply sum_congr rfl
        intro a ha
        exact Nat.sub_add_cancel ((lt_linearEnd base step bound cap a).mp (mem_range.mp ha)).2.le
      _ = _ := by simp
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Finset.sum_range_id] at hadd
  change len*bound-(len*base+step*(len*(len-1)/2)) = _
  exact (Nat.eq_sub_of_add_eq hadd).symm

private def boxPhase (s : Shape) (A h r d c v δ q j : ℕ) : ℕ :=
  ∑ i ∈ range (s.J/d+1),
    if j≤q ∧ (i+δ)*d≤j ∧ q+(i+δ)*c≤s.B then
      slots s.U ((i+δ)*v)*(s.m*A+j-q*(131071-h)-2*h*(r+i))
    else 0

private theorem coordinate_phases (s : Shape) (A h r d c v q j : ℕ)
    (hd : 0<d) (hq : q≤s.B) (hjq : j≤q) (hj : j≤s.J) :
    coordinateGain s A h r d c v q j + boxPhase s A h r d c v 1 q j =
      boxPhase s A h r d c v 0 q j := by
  let K := orderCap s d c q j
  let C := kept s.U v K
  let w := fun i => s.m*A+j-q*(131071-h)-2*h*(r+i)
  have hphase (δ : ℕ) : boxPhase s A h r d c v δ q j =
      ∑ i ∈ range (s.J/d+1), C (i+δ)*w i := by
    apply sum_congr rfl
    intro i _
    simp only [C, K, w, kept, le_orderCap s hd hq, hjq, true_and, ite_mul, zero_mul]
  have hmono : Antitone C := by
    intro i l hi
    by_cases hl : l≤K
    · simp only [C, kept, ite_eq_left hl, ite_eq_left (hi.trans hl)]
      exact slots_anti _ (Nat.mul_le_mul_right _ hi)
    · simp [C, kept, hl]
  have hK : K ≤ s.J/d := by
    have h := ((le_orderCap s hd hq).mp (le_rfl (a := K))).1.trans hj
    exact (Nat.le_div_iff_mul_le hd).mpr h
  have hsum : coordinateGain s A h r d c v q j =
      ∑ i ∈ range (s.J/d+1), (C i-C (i+1))*w i := by
    apply sum_subset (range_mono (Nat.succ_le_succ hK))
    intro i _ hi
    have hi' : ¬ i≤K := by
      intro h
      exact hi (mem_range.mpr (Nat.lt_succ_of_le h))
    have hi'' : ¬ i+1≤K := by omega
    change (C i-C (i+1))*w i = 0
    simp only [C, kept, ite_eq_right hi', ite_eq_right hi'', Nat.sub_self, Nat.zero_mul]
  rw [hsum, hphase 1, hphase 0, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [← Nat.add_mul, Nat.sub_add_cancel (hmono (Nat.le_succ i)), Nat.add_zero]

/-- The column arithmetic in one Hasse layer. -/
def column (s : Shape) (A h r c i δ j : ℕ) : ℕ :=
  clippedSum (j*(131071-h)+2*h*(r+i)) (131071-h) (s.m*A+j)
    (s.B+1-(i+δ)*c-j)

theorem column_eq (s : Shape) (A h r c i δ j : ℕ) :
    column s A h r c i δ j =
      ∑ q ∈ Ico j (s.B+1-(i+δ)*c), (s.m*A+j-q*(131071-h)-2*h*(r+i)) := by
  rw [column, clippedSum_eq, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro a _
  have h := Nat.add_mul j a (131071-h)
  rw [Nat.sub_sub, h]
  congr 1
  ring

def phaseLayer (s : Shape) (A h r d c v δ i : ℕ) : ℕ :=
  slots s.U ((i+δ)*v) *
    evaluate (fun a => column s A h r c i δ ((i+δ)*d+a)) (s.J+1-(i+δ)*d)

def compressedPhase (s : Shape) (A h r d c v δ : ℕ) : ℕ :=
  evaluate (phaseLayer s A h r d c v δ) (s.J/d+1)

private theorem sum_boxPhase (s : Shape) (A h r d c v δ : ℕ) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
      compressedPhase s A h r d c v δ := by
  unfold boxPhase compressedPhase
  rw [evaluate_eq]
  conv_lhs =>
    enter [2, q]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm, phaseLayer, evaluate_eq, ← sum_Ico_eq_sum_range, mul_sum]
  have hfilter : (range (s.J+1)).filter ((i+δ)*d ≤ ·) = Ico ((i+δ)*d) (s.J+1) := by
    ext j; simp [and_comm]
  rw [← hfilter, sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases hj : (i+δ)*d≤j
  · rw [ite_eq_left hj, column_eq, mul_sum]
    have hqfilter :
        (range (s.B+1)).filter (fun q => j≤q ∧ q+(i+δ)*c≤s.B) =
          Ico j (s.B+1-(i+δ)*c) := by
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    simp only [hj, true_and]
    rw [← sum_filter, hqfilter]
  · simp [hj]

/-- A compressed computation of the exact gain. It enumerates slope indices and
power layers. All ordinate sums are closed arithmetic progressions. -/
theorem gain_eq_compressed (s : Shape) (A h r d c v : ℕ) (hd : 0<d) :
    gain s A h r d c v =
      compressedPhase s A h r d c v 0 - compressedPhase s A h r d c v 1 := by
  have hbox (δ q : ℕ) :
      (∑ j ∈ range (s.J+1), boxPhase s A h r d c v δ q j) =
        ∑ j ∈ range (min q s.J+1), boxPhase s A h r d c v δ q j := by
    symm
    apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
    intro j hj hnot
    have hn : ¬ j≤q := by
      simp only [mem_range, Nat.lt_succ_iff, le_min_iff] at hj hnot
      omega
    simp [boxPhase, hn]
  apply Nat.eq_sub_of_add_eq
  rw [← sum_boxPhase, ← sum_boxPhase]
  simp only [hbox, gain, shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
  exact coordinate_phases s A h r d c v q j hd (Nat.le_of_lt_succ (mem_range.mp hq))
    (hj'.trans (min_le_left _ _)) (hj'.trans (min_le_right _ _))

#print axioms gain_eq_compressed

end Lower6960.HelperSource

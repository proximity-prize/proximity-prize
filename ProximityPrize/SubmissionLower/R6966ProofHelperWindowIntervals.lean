import ProximityPrize.SubmissionLower.R6966ProofHelperAvoidance

set_option Elab.async false

-- merged module R6966ProofHelperWindowPrefix
section Merged_R6966ProofHelperWindowPrefix

namespace Research6966.HelperWindowPrefix
open Finset
open K1_14 (Shape shapeSum)
open PadeFiltered (physicalWindow)
set_option maxHeartbeats 1100000

private theorem grade_sum (stop B J w : ℕ) (hw : 0 < w) :
    (∑ W ∈ range stop, (physicalWindow B J w W).card) =
      ∑ q ∈ range (B+1), ∑ j ∈ range (min q J+1), (stop+j-w*q) := by
  let s : Shape := ⟨0,B,J,0⟩
  have point (t : ℕ × ℕ) :
      (∑ W ∈ range stop, if w*t.2+(w-1)*t.1 ≤ W then 1 else 0) =
        stop+t.1-w*(t.1+t.2) := by
    have hj : t.1 ≤ w*(t.1+t.2) := by
      have h := Nat.mul_le_mul_right (t.1+t.2) (show 1 ≤ w from hw)
      omega
    have eq := K1_14_4.sum_interval stop t.1 (w*(t.1+t.2)) 0 1 hj
    rw [Nat.sub_zero, Nat.one_mul] at eq
    rw [← eq]
    apply sum_congr rfl
    intro W hW
    simp only [Nat.add_zero, mem_range.mp hW, and_true]
    have rel : w*(t.1+t.2) = w*t.2+(w-1)*t.1+t.1 := by
      rw [Nat.mul_add]
      have exp := congrArg (fun v => v*t.1) (Nat.sub_add_cancel hw : w-1+1=w)
      rw [Nat.add_mul, Nat.one_mul] at exp
      omega
    simp only [rel, Nat.add_le_add_iff_right]
  calc
    _ = ∑ W ∈ range stop, ∑ t ∈ PadeRank.positions (B+1) (J+1),
          if w*t.2+(w-1)*t.1 ≤ W then 1 else 0 := by
      apply sum_congr rfl
      intro W _
      rw [physicalWindow, card_filter]
    _ = ∑ t ∈ PadeRank.positions (B+1) (J+1), (stop+t.1-w*(t.1+t.2)) := by
      rw [sum_comm]; exact sum_congr rfl (fun t _ => point t)
    _ = ∑ j ∈ range (J+1), ∑ q ∈ Ico j (B+1), (stop+j-w*q) := by
      rw [PadeRank.positions, sum_filter, sum_product]
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      have range_eq : (range (B+1)).filter (fun i => j+i < B+1) = range (B+1-j) := by
        ext i; simp only [mem_filter, mem_range]; omega
      rw [range_eq, sum_Ico_eq_sum_range]
    _ = _ := K1_14_4.shapeSum_swap s (fun q j => stop+j-w*q)

private def trianglePart (stop n w : ℕ) : ℕ :=
  let moment := n*(n+1)*(n+2)
  (3*stop*(n+1)*(n+2)+moment-2*w*moment)/6

private def tailPart (stop n r J w : ℕ) : ℕ :=
  let length := r-n
  (length*(2*stop*(J+1)+J*(J+1))-w*(J+1)*(r+n+1)*length)/2

/-- Cumulative physical-window volume below an exclusive weight cutoff.
The complete triangle, the complete strip, and one partial grade are
evaluated with natural arithmetic. The equality requires `J < w`. -/
def volume (stop B J w : ℕ) : ℕ :=
  if stop = 0 then 0 else
    let last := min B ((stop-1)/w)
    let n := min last J
    let length := min (last+1) J - (w*(last+1)-stop)
    trianglePart stop n w + tailPart stop n last J w +
      if last < B then length*(length+1)/2 else 0

private theorem row_scaled (stop q J w : ℕ) (live : w*q ≤ stop) :
    2*(∑ j ∈ range (J+1), (stop+j-w*q))+2*w*q*(J+1) =
      2*stop*(J+1)+J*(J+1) := by
  have move (j : ℕ) : stop+j-w*q = (stop-w*q)+j := by omega
  simp_rw [move]
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
  have hs := sum_range_id_mul_two (J+1)
  rw [Nat.add_sub_cancel] at hs
  have ht := Nat.sub_add_cancel live
  nlinarith only [hs, congrArg (fun x => 2*(J+1)*x) ht]

private theorem triangle_scaled (stop n w : ℕ) (live : w*n ≤ stop) :
    6*(∑ q ∈ range (n+1), ∑ j ∈ range (q+1), (stop+j-w*q))+2*w*n*(n+1)*(n+2) =
      3*stop*(n+1)*(n+2)+n*(n+1)*(n+2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ]
    have prev := ih ((Nat.mul_le_mul_left w (Nat.le_succ n)).trans live)
    have row := row_scaled stop (n+1) (n+1) w live
    nlinarith only [prev, congrArg (3*·) row]

private theorem triangle_eq (stop n w : ℕ) (live : w*n ≤ stop) :
    (∑ q ∈ range (n+1), ∑ j ∈ range (q+1), (stop+j-w*q)) = trianglePart stop n w := by
  have eq := triangle_scaled stop n w live
  unfold trianglePart
  dsimp only
  rw [show 2*w*(n*(n+1)*(n+2)) = 2*w*n*(n+1)*(n+2) by ring, ← eq,
    Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 6)]

private theorem tail_scaled (stop n count J w : ℕ) (live : w*(n+count) ≤ stop) :
    2*(∑ i ∈ range count, ∑ j ∈ range (J+1), (stop+j-w*(n+1+i)))+
      w*(J+1)*(2*n+count+1)*count = count*(2*stop*(J+1)+J*(J+1)) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [sum_range_succ]
    have prev := ih ((Nat.mul_le_mul_left w (Nat.add_le_add_left (Nat.le_succ count) n)).trans live)
    have flip : n+(count+1)=n+1+count := by omega
    have row := row_scaled stop (n+1+count) J w (flip ▸ live)
    nlinarith only [prev,row]

private theorem tail_eq (stop n r J w : ℕ) (nr : n ≤ r) (live : w*r ≤ stop) :
    (∑ q ∈ Ico (n+1) (r+1), ∑ j ∈ range (J+1), (stop+j-w*q)) =
      tailPart stop n r J w := by
  rw [sum_Ico_eq_sum_range, show r+1-(n+1)=r-n by omega]
  have live' : w*(n+(r-n)) ≤ stop := by rwa [Nat.add_sub_of_le nr]
  have eq := tail_scaled stop n (r-n) J w live'
  have h := (show 2*n+(r-n)+1=r+n+1 by omega)
  rw [h] at eq
  unfold tailPart
  dsimp only
  rw [← eq, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

private theorem partial_scaled (J gap : ℕ) :
    2*(∑ j ∈ range (J+1), (j-gap)) = (J-gap)*(J-gap+1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    by_cases h : gap ≤ J
    · rw [show J+1-gap = J-gap+1 by omega]
      ring
    · rw [show J-gap=0 by omega, show J+1-gap=0 by omega]

private theorem partial_eq (stop q J w : ℕ) (dead : stop ≤ w*q) :
    (∑ j ∈ range (J+1), (stop+j-w*q)) =
      (J-(w*q-stop))*(J-(w*q-stop)+1)/2 := by
  have move (j : ℕ) : stop+j-w*q = j-(w*q-stop) := by omega
  simp_rw [move]
  rw [← partial_scaled, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

/-- The closed form computes the same cumulative dimension as summing
every physical weight. A positive slope exponent can add only one
partial grade when the slope cap is below the physical step. -/
theorem volume_eq_sum (stop B J w : ℕ) (narrow : J < w) :
    volume stop B J w = ∑ W ∈ range stop, (physicalWindow B J w W).card := by
  classical
  have hw : 0 < w := by omega
  rw [grade_sum stop B J w hw]
  by_cases z : stop = 0
  · subst stop
    rw [volume, ite_eq_left rfl]
    symm
    apply sum_eq_zero
    intro q _
    apply sum_eq_zero
    intro j hj
    have jle : j ≤ q := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left _ _)
    have qle := Nat.mul_le_mul_right q (show 1 ≤ w from hw)
    omega
  rw [volume, ite_eq_right z]
  dsimp only
  let last := min B ((stop-1)/w)
  let n := min last J
  let grade (q : ℕ) := ∑ j ∈ range (min q J+1), (stop+j-w*q)
  have lB : last ≤ B := min_le_left _ _
  have nl : n ≤ last := min_le_left _ _
  have nJ : n ≤ J := min_le_right _ _
  have live : w*last ≤ stop := by
    have h := (Nat.le_div_iff_mul_le hw).mp (show last ≤ (stop-1)/w from min_le_right _ _)
    rw [Nat.mul_comm last w] at h
    omega
  have complete : (∑ q ∈ range (last+1), grade q) =
      trianglePart stop n w+tailPart stop n last J w := by
    rw [← sum_range_add_sum_Ico grade (Nat.succ_le_succ nl)]
    congr 1
    · rw [← triangle_eq stop n w ((Nat.mul_le_mul_left w nl).trans live)]
      apply sum_congr rfl
      intro q hq
      unfold grade
      rw [min_eq_left ((Nat.lt_succ_iff.mp (mem_range.mp hq)).trans nJ)]
    · rw [← tail_eq stop n last J w nl live]
      apply sum_congr rfl
      intro q hq
      have jle : J ≤ q := by
        have lo := (mem_Ico.mp hq).1
        have hi := (mem_Ico.mp hq).2
        dsimp only [n] at lo
        omega
      unfold grade
      rw [min_eq_right jle]
  change trianglePart stop n w+tailPart stop n last J w+
    (if last < B then
      (min (last+1) J-(w*(last+1)-stop))*(min (last+1) J-(w*(last+1)-stop)+1)/2
    else 0) = ∑ q ∈ range (B+1), grade q
  rw [← sum_range_add_sum_Ico grade (Nat.succ_le_succ lB), complete]
  congr 1
  by_cases more : last < B
  · rw [ite_eq_left more]
    have exactLast : last = (stop-1)/w := by
      dsimp only [last] at more ⊢
      omega
    have dead : stop ≤ w*(last+1) := by
      have h := (Nat.div_lt_iff_lt_mul hw).mp (show (stop-1)/w < last+1 by omega)
      rw [Nat.mul_comm (last+1) w] at h
      omega
    rw [sum_eq_single (last+1)]
    · exact (partial_eq _ _ _ _ dead).symm
    · intro q hq ne
      have lo := (mem_Ico.mp hq).1
      have paid := Nat.mul_le_mul_left w (show last+2 ≤ q by omega)
      rw [show last+2=(last+1)+1 by omega, Nat.mul_add, Nat.mul_one] at paid
      apply sum_eq_zero
      intro j hj
      have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_right q J)
      omega
    · intro notMem
      exact (notMem (mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ more⟩)).elim
  · rw [ite_eq_right more, show last=B by omega, Ico_self, sum_empty]

/-- The same closed form is the leading term in the helper rank floor. -/
theorem volume_eq_shapeSum (s : Shape) (stop w : ℕ) (narrow : s.J < w) :
    volume stop s.B s.J w = shapeSum s (fun q j => stop+j-w*q) := by
  exact (volume_eq_sum stop s.B s.J w narrow).trans (grade_sum stop s.B s.J w (by omega))

#print axioms volume_eq_sum
#print axioms volume_eq_shapeSum
end Research6966.HelperWindowPrefix

end Merged_R6966ProofHelperWindowPrefix

-- merged module R6966ProofHelperWindowGrouping
section Merged_R6966ProofHelperWindowGrouping

namespace Research6966.HelperWindowGrouping
open Finset
open K1_14 (Shape)
open HelperAvoidance (power debitAt rectSlots triSlots)
open HelperBankRank (cells)
open HelperWindowPrefix (volume)
open PadeFiltered (physicalWindow)
set_option maxHeartbeats 850000

def sumCount (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumCount f n + f n

theorem sumCount_eq (f : ℕ → ℕ) (n : ℕ) :
    sumCount f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [sumCount]
  | succ n ih => rw [sumCount, ih, sum_range_succ]

/-- One physical layer for the divisor power `k+1`. The start and stop are
exclusive prefixes in the residual window after paying the divisor. -/
def layer (s : Shape) (h N k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let hi := N-2*h*k-(k+1)*wt
    let lo := hi-2*h
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume hi B J (131071-h) - volume lo B J (131071-h)
  else 0

def grouped (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layer s h N k a b wt * slots (k+1)) limit

private theorem power_eq_window {N h W k : ℕ} (hp : 0 < h) (mem : W < N) :
    power N h W = k+1 ↔ N-2*h*(k+1) ≤ W ∧ W < N-2*h*k := by
  have hs : 0 < 2*h := by omega
  have lo := K1_14_4.power_threshold N (2*h) W 0 k mem hs
  have hi := K1_14_4.power_threshold N (2*h) W 0 (k+1) mem hs
  simp only [Nat.zero_add, Nat.sub_zero] at lo hi
  change k < power N h W ↔ W+2*h*k < N at lo
  change k+1 < power N h W ↔ W+2*h*(k+1) < N at hi
  omega

private theorem shifted_prefix (f : ℕ → ℕ) (stop paid : ℕ) :
    (∑ W ∈ range stop, if paid ≤ W then f (W-paid) else 0) =
      ∑ W ∈ range (stop-paid), f W := by
  classical
  by_cases live : paid ≤ stop
  · rw [← sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) live]
    have early : (∑ W ∈ range paid, if paid ≤ W then f (W-paid) else 0) = 0 := by
      apply sum_eq_zero
      intro W hw
      rw [ite_eq_right (Nat.not_le.mpr (mem_range.mp hw))]
    rw [early, Nat.zero_add]
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro W _
    simp only [Nat.le_add_right paid W, ite_true, Nat.add_sub_cancel_left]
  · rw [Nat.sub_eq_zero_of_le (by omega), range_zero, sum_empty]
    apply sum_eq_zero
    intro W hw
    have := mem_range.mp hw
    rw [ite_eq_right (by omega)]

private theorem shifted_interval (f : ℕ → ℕ) (lo hi paid : ℕ) (range_ok : lo ≤ hi) :
    (∑ W ∈ Ico lo hi, if paid ≤ W then f (W-paid) else 0) =
      (∑ W ∈ range (hi-paid), f W)-(∑ W ∈ range (lo-paid), f W) := by
  have eq := sum_range_add_sum_Ico (fun W => if paid ≤ W then f (W-paid) else 0) range_ok
  rw [shifted_prefix, shifted_prefix] at eq
  omega

theorem layer_eq (s : Shape) (h N k a b wt : ℕ) (hp : 0 < h) (narrow : s.J < 131071-h) :
    layer s h N k a b wt =
      ∑ W ∈ range N, if power N h W = k+1 then (cells s h W (k+1) a b wt).card else 0 := by
  classical
  unfold layer
  by_cases room : (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J
  · rw [ite_eq_left room]
    dsimp only
    let endW := N-2*h*k
    let startW := N-2*h*(k+1)
    let paid := (k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    let f (W : ℕ) := (physicalWindow B J (131071-h) W).card
    have filter_eq : (range N).filter (fun W => power N h W = k+1) = Ico startW endW := by
      ext W
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · rintro ⟨mem,eq⟩
        exact (power_eq_window hp mem).mp eq
      · intro interval
        have mem : W < N := interval.2.trans_le (Nat.sub_le _ _)
        exact ⟨mem,(power_eq_window hp mem).mpr interval⟩
    have order : startW ≤ endW := by
      dsimp only [startW,endW]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have lo : endW-paid-2*h = startW-paid := by
      dsimp only [startW,endW,paid]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    change volume (endW-paid) B J (131071-h)-volume (endW-paid-2*h) B J (131071-h) = _
    have nJ : J < 131071-h := (Nat.sub_le _ _).trans_lt narrow
    rw [lo, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ, HelperWindowPrefix.volume_eq_sum _ _ _ _ nJ,
      ← sum_filter, filter_eq, ← shifted_interval f startW endW paid order]
    apply sum_congr rfl
    intro W _
    by_cases full : paid ≤ W
    · rw [ite_eq_left full, cells, ite_eq_left ⟨room.1,room.2,full⟩]
    · rw [ite_eq_right full, cells, ite_eq_right (fun all => full all.2.2), card_empty]
  · rw [ite_eq_right room]
    symm
    apply sum_eq_zero
    intro W _
    have no : ¬ ((k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J ∧ (k+1)*wt ≤ W) :=
      fun all => room ⟨all.1,all.2.1⟩
    rw [cells, ite_eq_right no, card_empty]
    split <;> rfl

/-- Group the raw-weight debit into disjoint divisor powers. The caller may
cut off any powers that have zero slot count or cannot fit the degree box. -/
theorem grouped_eq_debit_of_cutoff (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b ∨ N ≤ 2*h*(k-1)+k*wt) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  classical
  rw [grouped, sumCount_eq]
  calc
    _ = ∑ k ∈ range limit, ∑ W ∈ range N,
        if power N h W = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0 := by
      apply sum_congr rfl
      intro k _
      rw [layer_eq s h N k a b wt hp narrow, sum_mul]
      apply sum_congr rfl
      intro W _
      split <;> simp_all
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro W hW
      let t := power N h W
      have pos : 0 < t := (show 0 < 1 by decide).trans_le (Nat.le_add_right _ _)
      change (∑ k ∈ range limit, if t = k+1 then (cells s h W (k+1) a b wt).card*slots (k+1) else 0) =
        (cells s h W t a b wt).card*slots t
      by_cases active : t ≤ limit
      · have live : t-1 ∈ range limit := mem_range.mpr (by omega)
        rw [sum_eq_single_of_mem (t-1) live]
        · rw [Nat.sub_add_cancel pos, ite_eq_left rfl]
        · intro k _ ne
          rw [ite_eq_right (by omega)]
      · have zero : (cells s h W t a b wt).card*slots t = 0 := by
          rcases tail t (by omega) with fee | aLarge | bLarge | closed
          · rw [fee, Nat.mul_zero]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr aLarge) live.1), card_empty, Nat.zero_mul]
          · rw [cells, ite_eq_right (fun live => (Nat.not_le.mpr bLarge) live.2.1), card_empty, Nat.zero_mul]
          · have inWindow := (@power_eq_window N h W (t-1) hp (mem_range.mp hW)).mp
                (show power N h W = t-1+1 from (Nat.sub_add_cancel pos).symm)
            have stale : ¬ t*wt ≤ W := by omega
            rw [cells, ite_eq_right (fun live => stale live.2.2), card_empty, Nat.zero_mul]
        rw [zero]
        apply sum_eq_zero
        intro k hk
        have kin := mem_range.mp hk
        rw [ite_eq_right (by omega)]

theorem grouped_eq_debit (s : Shape) (h N a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (narrow : s.J < 131071-h)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    grouped s h N a b wt limit slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  apply grouped_eq_debit_of_cutoff s h N a b wt limit slots hp narrow
  intro k large
  rcases tail k large with fee | width | slope
  · exact Or.inl fee
  · exact Or.inr (Or.inl width)
  · exact Or.inr (Or.inr (Or.inl slope))

theorem grouped_by_slope (s : Shape) (h N a b wt : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (bp : 0 < b) (narrow : s.J < 131071-h) :
    grouped s h N a b wt (s.J/b) slots = ∑ W ∈ range N, debitAt s h N W a b wt slots := by
  apply grouped_eq_debit s h N a b wt (s.J/b) slots hp narrow
  intro k large
  exact Or.inr (Or.inr ((Nat.div_lt_iff_lt_mul bp).mp large))

#print axioms grouped_eq_debit
#print axioms grouped_by_slope
end Research6966.HelperWindowGrouping

end Merged_R6966ProofHelperWindowGrouping

-- merged module R6966ProofHelperWindowIntervals
section Merged_R6966ProofHelperWindowIntervals

namespace Research6966.HelperWindowIntervals
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowGrouping (sumCount sumCount_eq grouped layer)
open HelperWindowPrefix (volume volume_eq_shapeSum)
set_option maxHeartbeats 850000

private theorem shape_mono (s : Shape) (f g : ℕ → ℕ → ℕ)
    (cap : ∀ q ≤ s.B, ∀ j ≤ min q s.J, f q j ≤ g q j) : shapeSum s f ≤ shapeSum s g := by
  unfold shapeSum
  exact sum_le_sum (fun q hq => sum_le_sum (fun j hj =>
    cap q (Nat.lt_succ_iff.mp (mem_range.mp hq)) j (Nat.lt_succ_iff.mp (mem_range.mp hj))))

theorem volume_mono (s : Shape) {lo hi wLo wHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (narrow : s.J < wLo) :
    volume lo s.B s.J wHi ≤ volume hi s.B s.J wLo := by
  rw [volume_eq_shapeSum s _ _ (narrow.trans_le step), volume_eq_shapeSum s _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ =>
    (Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _))

private theorem slice_eq (s : Shape) (stop w span : ℕ) (narrow : s.J < w) :
    volume stop s.B s.J w-volume (stop-span) s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q)) := by
  have pieces : volume stop s.B s.J w =
      shapeSum s (fun q j => min span (stop+j-w*q))+volume (stop-span) s.B s.J w := by
    rw [volume_eq_shapeSum s _ _ narrow, volume_eq_shapeSum s _ _ narrow]
    unfold shapeSum
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro j hj
    have jle := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans (min_le_left q s.J)
    have qw := Nat.mul_le_mul_right q (show 1 ≤ w by omega)
    omega
  omega

theorem slice_mono (B J : ℕ) {lo hi wLo wHi spanLo spanHi : ℕ}
    (stop : lo ≤ hi) (step : wLo ≤ wHi) (span : spanLo ≤ spanHi) (narrow : J < wLo) :
    volume lo B J wHi-volume (lo-spanLo) B J wHi ≤
      volume hi B J wLo-volume (hi-spanHi) B J wLo := by
  let s : Shape := ⟨0,B,J,0⟩
  change volume lo s.B s.J wHi-volume (lo-spanLo) s.B s.J wHi ≤
    volume hi s.B s.J wLo-volume (hi-spanHi) s.B s.J wLo
  rw [slice_eq s _ _ _ (narrow.trans_le step), slice_eq s _ _ _ narrow]
  exact shape_mono s _ _ (fun q _ j _ => min_le_min span
    ((Nat.sub_le_sub_right (Nat.add_le_add_right stop j) _).trans
      (Nat.sub_le_sub_left (Nat.mul_le_mul_right q step) _)))

def cutoff (s : Shape) (agreement h reserve : ℕ) : ℕ := s.m*agreement-2*h*reserve

def layerBound (s : Shape) (agreement reserve lo hi k a b wt : ℕ) : ℕ :=
  if (k+1)*a ≤ s.B ∧ (k+1)*b ≤ s.J then
    let stop := cutoff s agreement lo reserve-2*lo*k-(k+1)*wt
    let B := s.B-(k+1)*a
    let J := s.J-(k+1)*b
    volume stop B J (131071-hi)-volume (stop-2*hi) B J (131071-hi)
  else 0

def bound (s : Shape) (agreement reserve lo hi a b wt limit : ℕ) (slots : ℕ → ℕ) : ℕ :=
  sumCount (fun k => layerBound s agreement reserve lo hi k a b wt * slots (k+1)) limit

theorem debit_le (s : Shape) (agreement reserve lo hi h a b wt limit : ℕ) (slots : ℕ → ℕ)
    (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b) :
    (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) ≤
      bound s agreement reserve lo hi a b wt limit slots := by
  have narrow' : s.J < 131071-h := narrow.trans_le (Nat.sub_le_sub_left hh _)
  rw [← HelperWindowGrouping.grouped_eq_debit s h _ a b wt limit slots hp narrow' tail]
  unfold grouped bound
  rw [sumCount_eq, sumCount_eq]
  apply sum_le_sum
  intro k hk
  apply Nat.mul_le_mul_right
  unfold layer layerBound
  split
  · dsimp only
    have cut : cutoff s agreement h reserve ≤ cutoff s agreement lo reserve :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hl)) _
    have stop : cutoff s agreement h reserve-2*h*k-(k+1)*wt ≤
        cutoff s agreement lo reserve-2*lo*k-(k+1)*wt :=
      Nat.sub_le_sub_right ((Nat.sub_le_sub_right cut _).trans
        (Nat.sub_le_sub_left (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hl)) _)) _
    exact slice_mono _ _ stop (Nat.sub_le_sub_left hh _) (Nat.mul_le_mul_left 2 hh)
      ((Nat.sub_le _ _).trans_lt narrow)
  · exact le_rfl

/-- A bank inequality certified at the two ends of an interval applies at
each integer height in it. The residual debit is bounded as a single
clipped window, preserving the cancellation between its two prefixes. -/
theorem positive (s : Shape) (agreement reserve lo hi h a b wt limit width rate nodes moment : ℕ)
    (slots : ℕ → ℕ) (hp : 0 < h) (hl : lo ≤ h) (hh : h ≤ hi) (narrow : s.J < 131071-hi)
    (tail : ∀ k > limit, slots k = 0 ∨ s.B < k*a ∨ s.J < k*b)
    (cert : width*nodes+hi*rate*moment+bound s agreement reserve lo hi a b wt limit slots <
      width*volume (cutoff s agreement hi reserve) s.B s.J (131071-lo)) :
    width*nodes+h*rate*moment+
        (∑ W ∈ range (cutoff s agreement h reserve), debitAt s h (cutoff s agreement h reserve) W a b wt slots) <
      width*shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
  have pay := debit_le s agreement reserve lo hi h a b wt limit slots hp hl hh narrow tail
  have pole := Nat.mul_le_mul_right moment (Nat.mul_le_mul_right rate hh)
  have cut : cutoff s agreement hi reserve ≤ cutoff s agreement h reserve :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_right reserve (Nat.mul_le_mul_left 2 hh)) _
  have n := narrow.trans_le (Nat.sub_le_sub_left hh 131071)
  have src := volume_mono s cut (Nat.sub_le_sub_left hl _) n
  rw [volume_eq_shapeSum s (cutoff s agreement h reserve) (131071-h) n] at src
  have agree : shapeSum s (fun q j => cutoff s agreement h reserve+j-(131071-h)*q) =
      shapeSum s (fun q j => cutoff s agreement h reserve+j-q*(131071-h)) := by
    simp only [Nat.mul_comm (131071-h)]
  exact ((Nat.add_le_add (Nat.add_le_add_left pole _) pay).trans_lt cert).trans_le
    (Nat.mul_le_mul_left _ (src.trans_eq agree))

def slotLimit (s : Shape) (U u : ℕ) : ℕ := if u = 0 then s.J else min s.J (U/u)

private theorem slot_limit {s : Shape} {U u k : ℕ} (large : slotLimit s U u < k) :
    U < k*u ∨ s.J < k := by
  unfold slotLimit at large
  split at large
  · exact Or.inr large
  · rename_i nz
    by_cases h : s.J < k
    · exact Or.inr h
    · exact Or.inl ((Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero nz)).mp (by omega))

theorem triangle_tail (s : Shape) (a U u : ℕ) :
    ∀ k > slotLimit s U u, triSlots U u k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · exact Or.inl (ite_eq_right (Nat.not_le.mpr cap))
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

def box (CAP v : ℕ) : Fin 2 → ℕ := ![CAP-v,v]
def axis (u : ℕ) : Fin 2 → ℕ := ![0,u]

theorem rectangle_tail (s : Shape) (a CAP v u : ℕ) :
    ∀ k > slotLimit s v u, rectSlots (box CAP v) (axis u) k = 0 ∨ s.B < k*a ∨ s.J < k*1 := by
  intro k large
  rcases slot_limit large with cap | slope
  · apply Or.inl
    apply ite_eq_right
    intro room
    exact (Nat.not_le.mpr cap) (room 1)
  · exact Or.inr (Or.inr (by simpa only [Nat.mul_one] using slope))

#print axioms positive
end Research6966.HelperWindowIntervals

end Merged_R6966ProofHelperWindowIntervals

import ProximityPrize.SubmissionLower.Koala6844ReceiptsSource

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

def recSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => recSum f n + f n

theorem recSum_eq (f : Nat → Nat) (n : Nat) : recSum f n = sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [recSum,ih,sumRange,List.range_succ,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

def auxColumnsRec (src : SourceShape) (j : Nat) : Nat :=
  recSum (fun h => recSum (fun r => auxiliaryColumnRow src j h r) (src.B-2*h+1)) (src.s+1)

theorem auxColumnsRec_eq (src : SourceShape) (j : Nat) :
    auxColumnsRec src j = auxiliaryColumnSlice src j := by
  simp only [auxColumnsRec,recSum_eq,auxiliaryColumnSlice]

private theorem triangle_twice (n : Nat) :
    2 * triangle n + (n+2) = (n+2)*(n+2) := by
  have even : ((n+1)*(n+2)) % 2 = 0 := by
    rw [Nat.mul_mod]
    rcases (show (n+1)%2 = 0 ∨ (n+2)%2 = 0 by omega) with h | h <;> simp [h]
  have he : 2 * ((n+1)*(n+2)/2) = (n+1)*(n+2) := by omega
  unfold triangle
  rw [he]
  exact (Nat.succ_mul (n+1) (n+2)).symm

private theorem shiftedTriangle_twice (h a : Nat) :
    2 * shiftedTriangle h a + (h+2-a) = (h+2-a)*(h+2-a) := by
  unfold shiftedTriangle
  split <;> rename_i ha
  · rw [show h+2-a = (h-a)+2 by omega]
    exact triangle_twice _
  · rcases (show h+2-a = 0 ∨ h+2-a = 1 by omega) with hz | hz <;> simp [hz]

private theorem seedlessRectangle_of_full (a b h : Nat) (hfull : a+b ≤ h+2) :
    seedlessRectangle a b h = a*b := by
  let c := h+2-(a+b)
  have hab : h+2 = c+a+b := by omega
  have ha : h+2-a = c+b := by omega
  have hb : h+2-b = c+a := by omega
  have p := triangle_twice h
  have q := shiftedTriangle_twice h (a+b)
  have r := shiftedTriangle_twice h a
  have s := shiftedTriangle_twice h b
  rw [hab] at p
  change 2 * shiftedTriangle h (a+b) + c = c*c at q
  rw [ha] at r
  rw [hb] at s
  have alg : (c+a+b)*(c+a+b)+c*c =
      (c+b)*(c+b)+(c+a)*(c+a) + 2*(a*b) := by
    rw [show 2*(a*b) = a*b+a*b by omega]
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  unfold seedlessRectangle
  omega

private def rankRectangle (a b height : Nat) : Nat :=
  if a + b ≤ height + 2 then a * b else seedlessRectangle a b height

private theorem rankRectangle_eq (a b height : Nat) :
    rankRectangle a b height = seedlessRectangle a b height := by
  unfold rankRectangle
  split
  · exact (seedlessRectangle_of_full _ _ _ ‹_›).symm
  · rfl

private theorem recSum_congr_lt (f g : Nat → Nat) (n : Nat)
    (hf : ∀ i < n, f i = g i) : recSum f n = recSum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [recSum, recSum, ih (fun i hi => hf i (by omega)), hf n (by omega)]

private theorem recSum_split (f : Nat → Nat) (m n : Nat) :
    recSum f (m+n) = recSum f m + recSum (fun i => f (m+i)) n := by
  simp only [recSum_eq, sumRange_add]

private def rankCell (m U B s t h : Nat) : Nat :=
  let height := U-h
  let b := B+1-2*h
  let k := localKernelOrder m t s h
  let total := rankRectangle (t+1) b height
  if k ≤ t ∧ m-t+2*h ≤ B then
    if k ≤ height then total-rankRectangle (t-k+1) (b-k) (height-k)
    else total
  else total

private def rankRowSum (m U B s t : Nat) : Nat :=
  recSum (rankCell m U B s t) (min s U + 1)

private theorem rankCell_of_full_unremoved (m U B s t h : Nat)
    (hs : 2*s ≤ B) (hU : h ≤ U) (hh : h ≤ s)
    (hfull : t+B ≤ U+h) (hno : B < m-t+2*h) :
    rankCell m U B s t h = (t+1)*(B+1-2*h) := by
  have ha : (t+1)+(B+1-2*h) ≤ U-h+2 := by omega
  simp [rankCell, rankRectangle, ha, Nat.not_le_of_lt hno]

private def rankDirect (m U B s : Nat) : Nat := recSum (rankRowSum m U B s) m

private theorem recSum_mulLeft (c : Nat) (f : Nat → Nat) (n : Nat) :
    recSum (fun i => c * f i) n = c * recSum f n := by
  induction n with
  | zero => simp [recSum]
  | succ n ih => simp only [recSum, ih, Nat.mul_add]

private theorem recSum_fullRankHeight (t B s : Nat) (hs : 2*s ≤ B) :
    recSum (fun h => (t+1)*(B+1-2*h)) (s+1) = (t+1)*(s+1)*(B+1-s) := by
  rw [recSum_mulLeft, Nat.mul_assoc]
  congr 1
  induction s with
  | zero => simp [recSum]
  | succ s ih =>
    rw [recSum, ih (by omega), show B+1-s = B+1-(s+1)+1 by omega, Nat.mul_add,
      Nat.succ_mul (s+1), Nat.mul_one]
    omega

private theorem recSum_fullRankPrefix (n k : Nat) :
    recSum (fun t => (t+1)*k) n = n*(n+1)/2*k := by
  induction n with
  | zero => simp [recSum]
  | succ n ih =>
    rw [recSum, ih, ← Nat.add_mul]
    congr 1
    have h : (n+1)*(n+1+1) = n*(n+1) + (n+1)*2 := by
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]
      omega
    rw [h, Nat.add_mul_div_right _ _ (by decide : 0 < 2)]

private theorem recSum_fullRankHeightTail (t B s i : Nat) (hi : i ≤ s) (hs : 2*s ≤ B) :
    recSum (fun h => (t+1)*(B+1-2*(i+h))) (s-i+1) =
      (t+1)*(s-i+1)*(B+1-s-i) := by
  have rows : (fun h => (t+1)*(B+1-2*(i+h))) =
      (fun h => (t+1)*((B-2*i)+1-2*h)) := by
    funext h
    rw [Nat.mul_add]
    congr 1
    omega
  rw [rows, recSum_fullRankHeight _ _ _ (by omega)]
  congr 1
  omega

private def rankRowTail (m U B s t : Nat) : Nat :=
  let i := min (s+1) (max ((B+2-(m-t))/2) (t+B-U))
  if i ≤ s then
    recSum (rankCell m U B s t) i + (t+1)*(s-i+1)*(B+1-s-i)
  else rankRowSum m U B s t

private theorem rankRowTail_eq (m U B s t : Nat) (hs : 2*s ≤ B) (hU : s ≤ U) :
    rankRowTail m U B s t = rankRowSum m U B s t := by
  let i := min (s+1) (max ((B+2-(m-t))/2) (t+B-U))
  change (if i ≤ s then recSum _ i + (t+1)*(s-i+1)*(B+1-s-i) else _) = _
  split
  · rename_i hi
    change i ≤ s at hi
    have hno : (B+2-(m-t))/2 ≤ i := by dsimp [i] at hi ⊢; omega
    have hfull : t+B-U ≤ i := by dsimp [i] at hi ⊢; omega
    have heq : ∀ h < s-i+1, (t+1)*(B+1-2*(i+h)) = rankCell m U B s t (i+h) := by
      intro h hh
      symm
      apply rankCell_of_full_unremoved <;> omega
    change recSum _ i + (t+1)*(s-i+1)*(B+1-s-i) = _
    rw [← recSum_fullRankHeightTail _ _ _ _ hi hs, recSum_congr_lt _ _ _ heq,
      ← recSum_split]
    unfold rankRowSum
    rw [Nat.min_eq_left hU, show i + (s-i+1) = s+1 by omega]
  · rfl

private def rankPrefixEval (m U B s : Nat) : Nat :=
  if m ≤ U ∧ 2*s ≤ B ∧ s ≤ U then
    let n := m-B
    (n*(n+1)/2)*((s+1)*(B+1-s)) +
      recSum (fun i => rankRowTail m U B s (n+i)) (m-n)
  else rankDirect m U B s

private theorem rankPrefixEval_eq (m U B s : Nat) :
    rankPrefixEval m U B s = rankDirect m U B s := by
  unfold rankPrefixEval
  split
  · rename_i cond
    obtain ⟨hm, hs, hU⟩ := cond
    let n := m-B
    have full : ∀ t < n, rankRowSum m U B s t = (t+1)*((s+1)*(B+1-s)) := by
      intro t ht
      have hprefix : t < m-B := ht
      unfold rankRowSum
      rw [Nat.min_eq_left hU]
      calc
        _ = recSum (fun h => (t+1)*(B+1-2*h)) (s+1) := by
          apply recSum_congr_lt
          intro h hh
          exact rankCell_of_full_unremoved _ _ _ _ _ _ hs (by omega) (by omega)
            (by omega) (by omega)
        _ = _ := by rw [recSum_fullRankHeight _ _ _ hs, Nat.mul_assoc]
    have htail : ∀ i < m-n, rankRowTail m U B s (n+i) = rankRowSum m U B s (n+i) :=
      fun _ _ => rankRowTail_eq _ _ _ _ _ hs hU
    change (n*(n+1)/2)*((s+1)*(B+1-s)) + recSum (fun i => rankRowTail m U B s (n+i)) (m-n) = _
    have join : n+(m-n) = m := by dsimp [n]; omega
    unfold rankDirect
    rw [← show recSum (rankRowSum m U B s) (n+(m-n)) = recSum (rankRowSum m U B s) m by rw [join],
      recSum_split, recSum_congr_lt _ _ _ full, recSum_fullRankPrefix, recSum_congr_lt _ _ _ htail]
  · rfl

def auxRankRec (src : SourceShape) (j : Nat) : Nat :=
  if j ≤ src.U then
    rankPrefixEval (src.m-j) (src.U-j) src.B src.s
  else 0

theorem auxRankRec_eq (src : SourceShape) (j : Nat) :
    auxRankRec src j = auxiliaryRankSlice src j := by
  unfold auxRankRec auxiliaryRankSlice
  split
  · rw [rankPrefixEval_eq]
    unfold rankDirect
    rw [recSum_eq]
    apply congrArg (sumRange _)
    funext t
    unfold rankRowSum
    rw [recSum_eq]
    apply congrArg (sumRange _)
    funext h
    simp only [rankCell, rankRectangle_eq]
  · rfl

theorem auxRankRecWindow_eq (src : SourceShape) (start length : Nat) :
    recSum (fun i => auxRankRec src (start+i+1)) length =
      sumRange length (fun i => auxiliaryRankSlice src (start+i+1)) := by
  simp only [recSum_eq,auxRankRec_eq]

theorem auxColumnsRecWindow_eq (src : SourceShape) (start length : Nat) :
    recSum (fun i => auxColumnsRec src (start+i+1)) length =
      sumRange length (fun i => auxiliaryColumnSlice src (start+i+1)) := by
  simp only [recSum_eq,auxColumnsRec_eq]

theorem contactRankWindow_of_rec (src : SourceShape) (start len value : Nat)
    (h : recSum (fun i => auxRankRec src (start+i+1)) len = value) :
    sumRange len (fun i => auxiliaryRankSlice src (start+i+1)) = value :=
  (auxRankRecWindow_eq src start len).symm.trans h

theorem contactColumnsWindow_of_rec (src : SourceShape) (start len value : Nat)
    (h : recSum (fun i => auxColumnsRec src (start+i+1)) len = value) :
    sumRange len (fun i => auxiliaryColumnSlice src (start+i+1)) = value :=
  (auxColumnsRecWindow_eq src start len).symm.trans h

end ProximityPrize.SubmissionLower.Koala6844Receipts

import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinsFast

namespace Low48PrimaryPivot
open K1_13_2_3

def binChunk (w : Window) (start count : ℕ) : ℤ :=
  ((List.range' start count).map (binAtFast w)).sum

theorem binChunk_append (w : Window) (start left right : ℕ) :
    binChunk w start (left+right) =
      binChunk w start left + binChunk w (start+left) right := by
  unfold binChunk
  rw [← List.range'_append_1, List.map_append, List.sum_append]

theorem binChunk_join {w : Window} {start left right : ℕ} {x y : ℤ}
    (hleft : binChunk w start left = x) (hright : binChunk w (start+left) right = y) :
    binChunk w start (left+right) = x+y := by
  rw [binChunk_append,hleft,hright]

private theorem binChunk_zero (w : Window) (n : ℕ) (h : (n : ℤ) ≤ indexLo w) :
    binChunk w 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [binChunk_append,ih (by omega)]
    have hk : binAtFast w k = 0 := by
      unfold binAtFast
      rw [ite_eq_left (by omega)]
    rw [zero_add]
    simp [binChunk,List.range'_succ,hk]

theorem binCompute_eq_chunk (w : Window) (n : ℕ) (hn : n ≤ 1651) (h : (n : ℤ) ≤ indexLo w) :
    binCompute w = binChunk w n (1651-n) := by
  have hStart : binCompute w = binChunk w 0 1651 := by
    unfold binCompute binChunk
    rw [List.range_eq_range']
    apply congrArg List.sum
    exact List.map_congr_left fun j _ => (binAtFast_eq w j).symm
  calc
    _ = binChunk w 0 (n+(1651-n)) :=
      hStart.trans (congrArg (binChunk w 0) (Nat.add_sub_of_le hn).symm)
    _ = _ := by rw [binChunk_append,binChunk_zero w n h]; simp only [zero_add]

end Low48PrimaryPivot

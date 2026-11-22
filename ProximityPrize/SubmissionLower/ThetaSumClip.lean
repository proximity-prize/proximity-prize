import ProximityPrize.SubmissionLower.ThetaSumDefs

set_option Elab.async false
set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace ThetaSumClip
open ThetaSum (rangeSum rangeSum_append tsFast entry row chunk)

private def start (s : ℕ) : ℕ := 3000 + 9*(s-2304)/20 - s
private def stop (s : ℕ) : ℕ := min 1647 (3000 + (s-1354)/4 - s + 1)

private theorem support (s j : ℕ) (ha : 1354 ≤ s) (hb : s < 3012) (hj : j < 1647) :
    (3000 ≤ s+j ∧ 4*(s+j-3000) ≤ s-1354 ∧ 9*(s-2304) ≤ 20*(s+j-3000)+19) ↔
    start s ≤ j ∧ j < stop s := by
  unfold start stop
  omega

private theorem strip_nonempty (s : ℕ) (ha : 1354 ≤ s) (hb : s < 3012) : start s ≤ stop s := by
  unfold start stop
  omega

private theorem range_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ k < n, f k = g k) :
    rangeSum f n = rangeSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rangeSum, rangeSum, ih (fun k hk => h k (by omega)), h n (by omega)]

private theorem range_zero (n : ℕ) : rangeSum (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rangeSum, ih]

private theorem range_window (f : ℕ → ℕ) (a b n : ℕ) (hab : a ≤ b) (hbn : b ≤ n) :
    rangeSum (fun j => if a ≤ j ∧ j < b then f j else 0) n =
      rangeSum (fun j => f (a+j)) (b-a) := by
  let g := fun j => if a ≤ j ∧ j < b then f j else 0
  have hpre : rangeSum g a = 0 :=
    (range_congr _ _ _ (fun k hk => by simp [g, show ¬ a ≤ k by omega])).trans (range_zero a)
  have hpost : rangeSum (fun k => g (b+k)) (n-b) = 0 :=
    (range_congr _ _ _ (fun k hk => by simp [g, show ¬ b+k < b by omega])).trans (range_zero (n-b))
  have hmid : rangeSum (fun k => g (a+k)) (b-a) = rangeSum (fun k => f (a+k)) (b-a) :=
    range_congr _ _ _ (fun k hk => by simp [g, show a+k < b by omega])
  change rangeSum g n = _
  calc
    _ = rangeSum g b + rangeSum (fun k => g (b+k)) (n-b) := by
      rw [← rangeSum_append, Nat.add_sub_of_le hbn]
    _ = rangeSum g b := by rw [hpost, Nat.add_zero]
    _ = rangeSum g a + rangeSum (fun k => g (a+k)) (b-a) := by
      rw [← rangeSum_append, Nat.add_sub_of_le hab]
    _ = _ := by rw [hpre, hmid, Nat.zero_add]

private def fastRow (s : ℕ) : ℕ := rangeSum (fun j => tsFast s (start s+j)) (stop s-start s)

private theorem fastRow_eq (s : ℕ) (ha : 1354 ≤ s) (hb : s < 3012) : fastRow s = row s := by
  unfold fastRow row
  rw [← range_window (tsFast s) (start s) (stop s) 1647 (strip_nonempty s ha hb)
    (min_le_left ..)]
  apply range_congr
  intro j hj
  let hw := support s j ha hb hj
  by_cases h : start s ≤ j ∧ j < stop s
  · simp only [entry, if_pos h, if_pos (hw.mpr h)]
  · simp only [entry, if_neg h, if_neg (fun hg => h (hw.mp hg))]

private def fastChunk (lo n : ℕ) : ℕ := rangeSum (fun t => fastRow (lo+t)) n

theorem fastChunk_eq (lo n : ℕ) (ha : 1354 ≤ lo) (hb : lo+n ≤ 3012) : fastChunk lo n = chunk lo n := by
  unfold fastChunk chunk
  apply range_congr
  intro t ht
  exact fastRow_eq _ (by omega) (by omega)

end ThetaSumClip

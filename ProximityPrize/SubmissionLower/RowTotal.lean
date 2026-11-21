import ProximityPrize.SubmissionLower.PoleFamily
import ProximityPrize.SubmissionLower.PoleSavings
import ProximityPrize.SubmissionLower.Fast065

namespace RowTotal
open Finset PoleBlocks
open scoped BigOperators

private theorem prefix_eq (B n : ℕ) (f : ℕ → ℕ) :
    (∑ s ∈ range (min n B+1), f s) =
      ∑ s ∈ range (B+1), if s ≤ n then f s else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext s
  simp only [mem_range, mem_filter]
  omega

private theorem count_n (B d s : ℕ) (hs : s ≤ B) (v : ℕ) :
    (∑ n ∈ range (B+d+1), if s ≤ n then v else 0) = (B-s+d+1)*v := by
  rw [← Finset.sum_filter]
  have f : (range (B+d+1)).filter (fun n => s ≤ n) = Ico s (B+d+1) := by
    ext n
    simp [and_comm]
  rw [f, sum_const, Nat.card_Ico, nsmul_eq_mul]
  have he : B+d+1-s = B-s+d+1 := by omega
  rw [he]
  rfl

theorem joint_count (B d : ℕ) (f : ℕ → ℕ) :
    (∑ n : Fin (B+d+1), ∑ s : Fin (min n.val B+1), f s.val) =
      ∑ s ∈ range (B+1), (B-s+d+1)*f s := by
  simp_rw [Fin.sum_univ_eq_sum_range]
  simp_rw [prefix_eq B _ f]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if s ≤ n then f s else 0) (B+d+1)]
  exact count_n B d s (by simpa only [mem_range,Nat.lt_succ_iff] using hs) (f s)

private theorem triangle_tail (U : ℕ) :
    (∑ u ∈ range (U+1), (U-u+1)) = K1_14.triangle U := by
  induction U with
  | zero => decide
  | succ U ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ih]
    unfold K1_14.triangle
    have h : (U+1+1)*(U+1+2) = (U+1)*(U+2) + 2*(U+2) := by ring
    omega

theorem joint_and_passive (B U : ℕ) (f : ℕ → ℕ) :
    (∑ u : Fin (U+1), ∑ n : Fin (B+(U-u.val)+1), ∑ s : Fin (min n.val B+1), f s.val) =
      ∑ s ∈ range (B+1), ((U+1)*(B-s)+K1_14.triangle U)*f s := by
  simp_rw [joint_count]
  rw [Fin.sum_univ_eq_sum_range (fun u : ℕ => ∑ s ∈ range (B+1), (B-s+(U-u)+1)*f s) (U+1),Finset.sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [show ∀ u : ℕ, B-s+(U-u)+1 = (B-s)+(U-u+1) from fun u => by omega]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,triangle_tail]
  rfl

def allRows (s : K1_14.Shape) : ℕ :=
  ∑ u : Fin (s.U+1), ∑ n : Fin (s.B+(s.U-u.val)+1), ∑ h : Fin (s.B+2*s.J),
    ∑ k : Fin (min n.val s.B+1), min (slotCount ((h.val : ℤ)-s.J) s.J k.val)
      (((s.B+s.J : ℕ) : ℤ)-((h.val : ℤ)-s.J)-k.val).toNat

theorem row_budget (s : K1_14.Shape) : allRows s =
    ∑ k ∈ range (s.B+1), ((s.U+1)*(s.B-k)+K1_14.triangle s.U)*
      ((s.B+s.J-k)*(min s.J k+1)) := by
  unfold allRows
  convert joint_and_passive s.B s.U (fun k => (s.B+s.J-k)*(min s.J k+1)) using 1
  refine sum_congr rfl fun u _ => sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => PoleSavings.sum_rowCount _ _ _ ?_
  have h := k.isLt
  omega

theorem old_charge (h : ℕ) (s : K1_14.Shape) :
    (2*h)*allRows s = K1_14_1.poleCredit h s + K1_14_1.poleSeedDebit h s := by
  rw [row_budget]
  simp only [K1_14_1.poleCredit,K1_14_1.poleSeedDebit,K1_14.shapeSum,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,Nat.cast_id,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [min_comm k s.J]
  ring

end RowTotal

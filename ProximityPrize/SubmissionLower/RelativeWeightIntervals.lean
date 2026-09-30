import ProximityPrize.SubmissionLower.RelativeProfileSupplier
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open RCN100
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem coefficientCount_mono_cutoff (w L s : ℕ) :
    Monotone (fun D => coefficientCount D w L s) := by
  intro D1 D2 hD
  unfold coefficientCount
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_left
  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right hD _) _

theorem profile_rows_mono_weight {D w L s T R B N alpha beta lo nu : ℕ}
    (hnu : lo ≤ nu)
    (hrows : ∀ mu ≤ B+R, coefficientCount (D-lo) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s) :
    ∀ mu ≤ B+R, coefficientCount (D-nu) w (L-T) (s-R) +
      N*profileRowRank alpha beta L s T R mu < coefficientCount D w L s := by
  intro mu hmu
  have hcoef := coefficientCount_mono_cutoff w (L-T) (s-R)
    (Nat.sub_le_sub_left hnu D)
  exact (Nat.add_le_add_right hcoef _).trans_lt (hrows mu hmu)

theorem clipped_cutoff_antitone (alpha beta w B R A : ℕ) :
    Antitone (fun nu => alpha*A-beta*min (nu-w+1) ((B+R-1)*A)) := by
  intro lo hi h
  apply Nat.sub_le_sub_left
  apply Nat.mul_le_mul_left
  exact min_le_min (Nat.add_le_add_right (Nat.sub_le_sub_right h w) 1) le_rfl

end ProximityPrize.SubmissionLower.RelativeBounded6814

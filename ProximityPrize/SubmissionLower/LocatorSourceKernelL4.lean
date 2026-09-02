import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL4
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L4 = (1600, 200000, 480) at agreements 181520: rank and nullity, the cutoff
count split into 4 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 1600 200000 480 = 93335513436880 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1600 200000 480 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (200000 + 1 - i - j) * (290432000 - 131071 * i - 131070 * j)) 481
private theorem cum_623 : LocatorKernelEval.sumRange row 623 = 13044082725894418562 := by decide +kernel
private theorem blk_623 : LocatorKernelEval.sumRange (fun i => row (623 + i)) 623 = 8138117313316952598 := by decide +kernel
private theorem cum_1246 : LocatorKernelEval.sumRange row 1246 = 21182200039211371160 := by
  rw [show (1246 : ℕ) = 623 + 623 from rfl, sumRange_add, cum_623, blk_623]
private theorem blk_1246 : LocatorKernelEval.sumRange (fun i => row (1246 + i)) 623 = 3272838833854771447 := by decide +kernel
private theorem cum_1869 : LocatorKernelEval.sumRange row 1869 = 24455038873066142607 := by
  rw [show (1869 : ℕ) = 1246 + 623 from rfl, sumRange_add, cum_1246, blk_1246]
private theorem blk_1869 : LocatorKernelEval.sumRange (fun i => row (1869 + i)) 347 = 181995270883041753 := by decide +kernel
private theorem cum_2216 : LocatorKernelEval.sumRange row 2216 = 24637034143949184360 := by
  rw [show (2216 : ℕ) = 1869 + 347 from rfl, sumRange_add, cum_1869, blk_1869]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 290432000 131071 200000 480 2216 = 24637034143949184360 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 2216 = _
  exact cum_2216
theorem nullity_eq :
    coefficientCount 290432000 131071 200000 480 - 262144 * localRankBound 1600 200000 480 = 169689309551713640 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 290432000 131071 200000 480 2216 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL4

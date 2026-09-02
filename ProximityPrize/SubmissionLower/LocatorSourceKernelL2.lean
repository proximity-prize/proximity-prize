import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL2
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L2 = (1760, 100000, 540) at agreements 181520: rank and nullity, the cutoff
count split into 5 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 1760 100000 540 = 62894479678030 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1760 100000 540 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (100000 + 1 - i - j) * (319475200 - 131071 * i - 131070 * j)) 541
private theorem cum_554 : LocatorKernelEval.sumRange row 554 = 7389708345970111558 := by decide +kernel
private theorem blk_554 : LocatorKernelEval.sumRange (fun i => row (554 + i)) 554 = 5196161144346419734 := by decide +kernel
private theorem cum_1108 : LocatorKernelEval.sumRange row 1108 = 12585869490316531292 := by
  rw [show (1108 : ℕ) = 554 + 554 from rfl, sumRange_add, cum_554, blk_554]
private theorem blk_1108 : LocatorKernelEval.sumRange (fun i => row (1108 + i)) 554 = 3026727604650143318 := by decide +kernel
private theorem cum_1662 : LocatorKernelEval.sumRange row 1662 = 15612597094966674610 := by
  rw [show (1662 : ℕ) = 1108 + 554 from rfl, sumRange_add, cum_1108, blk_1108]
private theorem blk_1662 : LocatorKernelEval.sumRange (fun i => row (1662 + i)) 554 = 950204873852043134 := by decide +kernel
private theorem cum_2216 : LocatorKernelEval.sumRange row 2216 = 16562801968818717744 := by
  rw [show (2216 : ℕ) = 1662 + 554 from rfl, sumRange_add, cum_1662, blk_1662]
private theorem blk_2216 : LocatorKernelEval.sumRange (fun i => row (2216 + i)) 222 = 23478253554933423 := by decide +kernel
private theorem cum_2438 : LocatorKernelEval.sumRange row 2438 = 16586280222373651167 := by
  rw [show (2438 : ℕ) = 2216 + 222 from rfl, sumRange_add, cum_2216, blk_2216]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 319475200 131071 100000 540 2438 = 16586280222373651167 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 2438 = _
  exact cum_2438
theorem nullity_eq :
    coefficientCount 319475200 131071 100000 540 - 262144 * localRankBound 1760 100000 540 = 98869741656154847 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 319475200 131071 100000 540 2438 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL2

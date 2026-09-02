import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelN1
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel N1 = (2600, 400000, 800) at agreements 181520: rank and nullity, the cutoff
count split into 10 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 2600 400000 800 = 816167924395200 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 2600 400000 800 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (400000 + 1 - i - j) * (471952000 - 131071 * i - 131070 * j)) 801
private theorem cum_374 : LocatorKernelEval.sumRange row 374 = 47275449449956674408 := by decide +kernel
private theorem blk_374 : LocatorKernelEval.sumRange (fun i => row (374 + i)) 374 = 41371161654626869824 := by decide +kernel
private theorem cum_748 : LocatorKernelEval.sumRange row 748 = 88646611104583544232 := by
  rw [show (748 : ℕ) = 374 + 374 from rfl, sumRange_add, cum_374, blk_374]
private theorem blk_748 : LocatorKernelEval.sumRange (fun i => row (748 + i)) 374 = 35477858451313174248 := by decide +kernel
private theorem cum_1122 : LocatorKernelEval.sumRange row 1122 = 124124469555896718480 := by
  rw [show (1122 : ℕ) = 748 + 374 from rfl, sumRange_add, cum_748, blk_748]
private theorem blk_1122 : LocatorKernelEval.sumRange (fun i => row (1122 + i)) 374 = 29595539840015587680 := by decide +kernel
private theorem cum_1496 : LocatorKernelEval.sumRange row 1496 = 153720009395912306160 := by
  rw [show (1496 : ℕ) = 1122 + 374 from rfl, sumRange_add, cum_1122, blk_1122]
private theorem blk_1496 : LocatorKernelEval.sumRange (fun i => row (1496 + i)) 374 = 23724205820734110120 := by decide +kernel
private theorem cum_1870 : LocatorKernelEval.sumRange row 1870 = 177444215216646416280 := by
  rw [show (1870 : ℕ) = 1496 + 374 from rfl, sumRange_add, cum_1496, blk_1496]
private theorem blk_1870 : LocatorKernelEval.sumRange (fun i => row (1870 + i)) 374 = 17863856393468741568 := by decide +kernel
private theorem cum_2244 : LocatorKernelEval.sumRange row 2244 = 195308071610115157848 := by
  rw [show (2244 : ℕ) = 1870 + 374 from rfl, sumRange_add, cum_1870, blk_1870]
private theorem blk_2244 : LocatorKernelEval.sumRange (fun i => row (2244 + i)) 374 = 12014491558219482024 := by decide +kernel
private theorem cum_2618 : LocatorKernelEval.sumRange row 2618 = 207322563168334639872 := by
  rw [show (2618 : ℕ) = 2244 + 374 from rfl, sumRange_add, cum_2244, blk_2244]
private theorem blk_2618 : LocatorKernelEval.sumRange (fun i => row (2618 + i)) 374 = 6236679483393709488 := by decide +kernel
private theorem cum_2992 : LocatorKernelEval.sumRange row 2992 = 213559242651728349360 := by
  rw [show (2992 : ℕ) = 2618 + 374 from rfl, sumRange_add, cum_2618, blk_2618]
private theorem blk_2992 : LocatorKernelEval.sumRange (fun i => row (2992 + i)) 374 = 1851019388732094955 := by decide +kernel
private theorem cum_3366 : LocatorKernelEval.sumRange row 3366 = 215410262040460444315 := by
  rw [show (3366 : ℕ) = 2992 + 374 from rfl, sumRange_add, cum_2992, blk_2992]
private theorem blk_3366 : LocatorKernelEval.sumRange (fun i => row (3366 + i)) 235 = 113473196820479885 := by decide +kernel
private theorem cum_3601 : LocatorKernelEval.sumRange row 3601 = 215523735237280924200 := by
  rw [show (3601 : ℕ) = 3366 + 235 from rfl, sumRange_add, cum_3366, blk_3366]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 471952000 131071 400000 800 3601 = 215523735237280924200 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 3601 = _
  exact cum_3601
theorem nullity_eq :
    coefficientCount 471952000 131071 400000 800 - 262144 * localRankBound 2600 400000 800 = 1570210864625615400 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 471952000 131071 400000 800 3601 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelN1

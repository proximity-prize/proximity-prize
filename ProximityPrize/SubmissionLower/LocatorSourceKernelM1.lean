import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelM1
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel M1 = (2600, 300000, 800) at agreements 181520: rank and nullity, the cutoff
count split into 10 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 2600 300000 800 = 611531114395200 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 2600 300000 800 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (300000 + 1 - i - j) * (471952000 - 131071 * i - 131070 * j)) 801
private theorem cum_374 : LocatorKernelEval.sumRange row 374 = 35439902071368774408 := by decide +kernel
private theorem blk_374 : LocatorKernelEval.sumRange (fun i => row (374 + i)) 374 = 31004142620438569824 := by decide +kernel
private theorem cum_748 : LocatorKernelEval.sumRange row 748 = 66444044691807344232 := by
  rw [show (748 : ℕ) = 374 + 374 from rfl, sumRange_add, cum_374, blk_374]
private theorem blk_748 : LocatorKernelEval.sumRange (fun i => row (748 + i)) 374 = 26579367761524474248 := by decide +kernel
private theorem cum_1122 : LocatorKernelEval.sumRange row 1122 = 93023412453331818480 := by
  rw [show (1122 : ℕ) = 748 + 374 from rfl, sumRange_add, cum_748, blk_748]
private theorem blk_1122 : LocatorKernelEval.sumRange (fun i => row (1122 + i)) 374 = 22165577494626487680 := by decide +kernel
private theorem cum_1496 : LocatorKernelEval.sumRange row 1496 = 115188989947958306160 := by
  rw [show (1496 : ℕ) = 1122 + 374 from rfl, sumRange_add, cum_1122, blk_1122]
private theorem blk_1496 : LocatorKernelEval.sumRange (fun i => row (1496 + i)) 374 = 17762771819744610120 := by decide +kernel
private theorem cum_1870 : LocatorKernelEval.sumRange row 1870 = 132951761767702916280 := by
  rw [show (1870 : ℕ) = 1496 + 374 from rfl, sumRange_add, cum_1496, blk_1496]
private theorem blk_1870 : LocatorKernelEval.sumRange (fun i => row (1870 + i)) 374 = 13370950736878841568 := by decide +kernel
private theorem cum_2244 : LocatorKernelEval.sumRange row 2244 = 146322712504581757848 := by
  rw [show (2244 : ℕ) = 1870 + 374 from rfl, sumRange_add, cum_1870, blk_1870]
private theorem blk_2244 : LocatorKernelEval.sumRange (fun i => row (2244 + i)) 374 = 8990114246029182024 := by decide +kernel
private theorem cum_2618 : LocatorKernelEval.sumRange row 2618 = 155312826750610939872 := by
  rw [show (2618 : ℕ) = 2244 + 374 from rfl, sumRange_add, cum_2244, blk_2244]
private theorem blk_2618 : LocatorKernelEval.sumRange (fun i => row (2618 + i)) 374 = 4665547280521409488 := by decide +kernel
private theorem cum_2992 : LocatorKernelEval.sumRange row 2992 = 159978374031132349360 := by
  rw [show (2992 : ℕ) = 2618 + 374 from rfl, sumRange_add, cum_2618, blk_2618]
private theorem blk_2992 : LocatorKernelEval.sumRange (fun i => row (2992 + i)) 374 = 1384434580196094955 := by decide +kernel
private theorem cum_3366 : LocatorKernelEval.sumRange row 3366 = 161362808611328444315 := by
  rw [show (3366 : ℕ) = 2992 + 374 from rfl, sumRange_add, cum_2992, blk_2992]
private theorem blk_3366 : LocatorKernelEval.sumRange (fun i => row (3366 + i)) 235 = 84855792452479885 := by decide +kernel
private theorem cum_3601 : LocatorKernelEval.sumRange row 3601 = 161447664403780924200 := by
  rw [show (3601 : ℕ) = 3366 + 235 from rfl, sumRange_add, cum_3366, blk_3366]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 471952000 131071 300000 800 3601 = 161447664403780924200 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 3601 = _
  exact cum_3601
theorem nullity_eq :
    coefficientCount 471952000 131071 300000 800 - 262144 * localRankBound 2600 300000 800 = 1138451951765615400 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 471952000 131071 300000 800 3601 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelM1

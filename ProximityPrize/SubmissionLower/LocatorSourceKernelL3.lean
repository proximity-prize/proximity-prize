import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L3 = (2320, 100000, 720) at agreements 181520: rank and nullity, the cutoff
count split into 8 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 2320 100000 720 = 144846693595800 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 2320 100000 720 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (100000 + 1 - i - j) * (421126400 - 131071 * i - 131070 * j)) 721
private theorem cum_416 : LocatorKernelEval.sumRange row 416 = 10343453261536041920 := by decide +kernel
private theorem blk_416 : LocatorKernelEval.sumRange (fun i => row (416 + i)) 416 = 8680839702704128960 := by decide +kernel
private theorem cum_832 : LocatorKernelEval.sumRange row 832 = 19024292964240170880 := by
  rw [show (832 : ℕ) = 416 + 416 from rfl, sumRange_add, cum_416, blk_416]
private theorem blk_832 : LocatorKernelEval.sumRange (fun i => row (832 + i)) 416 = 7031832814282075072 := by decide +kernel
private theorem cum_1248 : LocatorKernelEval.sumRange row 1248 = 26056125778522245952 := by
  rw [show (1248 : ℕ) = 832 + 416 from rfl, sumRange_add, cum_832, blk_832]
private theorem blk_1248 : LocatorKernelEval.sumRange (fun i => row (1248 + i)) 416 = 5396432596269880256 := by decide +kernel
private theorem cum_1664 : LocatorKernelEval.sumRange row 1664 = 31452558374792126208 := by
  rw [show (1664 : ℕ) = 1248 + 416 from rfl, sumRange_add, cum_1248, blk_1248]
private theorem blk_1664 : LocatorKernelEval.sumRange (fun i => row (1664 + i)) 416 = 3774639048667544512 := by decide +kernel
private theorem cum_2080 : LocatorKernelEval.sumRange row 2080 = 35227197423459670720 := by
  rw [show (2080 : ℕ) = 1664 + 416 from rfl, sumRange_add, cum_1664, blk_1664]
private theorem blk_2080 : LocatorKernelEval.sumRange (fun i => row (2080 + i)) 416 = 2166452224543706529 := by decide +kernel
private theorem cum_2496 : LocatorKernelEval.sumRange row 2496 = 37393649648003377249 := by
  rw [show (2496 : ℕ) = 2080 + 416 from rfl, sumRange_add, cum_2080, blk_2080]
private theorem blk_2496 : LocatorKernelEval.sumRange (fun i => row (2496 + i)) 416 = 727101312850529656 := by decide +kernel
private theorem cum_2912 : LocatorKernelEval.sumRange row 2912 = 38120750960853906905 := by
  rw [show (2912 : ℕ) = 2496 + 416 from rfl, sumRange_add, cum_2496, blk_2496]
private theorem blk_2912 : LocatorKernelEval.sumRange (fun i => row (2912 + i)) 301 = 58306685278191847 := by decide +kernel
private theorem cum_3213 : LocatorKernelEval.sumRange row 3213 = 38179057646132098752 := by
  rw [show (3213 : ℕ) = 2912 + 301 from rfl, sumRange_add, cum_2912, blk_2912]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 421126400 131071 100000 720 3213 = 38179057646132098752 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 3213 = _
  exact cum_3213
theorem nullity_eq :
    coefficientCount 421126400 131071 100000 720 - 262144 * localRankBound 2320 100000 720 = 208366000154703552 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 421126400 131071 100000 720 3213 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL3

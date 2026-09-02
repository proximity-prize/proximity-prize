import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelM3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel M3 = (3100, 300000, 950) at agreements 181520: rank and nullity, the cutoff
count split into 14 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 3100 300000 950 = 1032289695622850 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3100 300000 950 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (300000 + 1 - i - j) * (562712000 - 131071 * i - 131070 * j)) 951
private theorem cum_315 : LocatorKernelEval.sumRange row 315 = 43038755629728326685 := by decide +kernel
private theorem blk_315 : LocatorKernelEval.sumRange (fun i => row (315 + i)) 315 = 39294698655355256610 := by decide +kernel
private theorem cum_630 : LocatorKernelEval.sumRange row 630 = 82333454285083583295 := by
  rw [show (630 : ℕ) = 315 + 315 from rfl, sumRange_add, cum_315, blk_315]
private theorem blk_630 : LocatorKernelEval.sumRange (fun i => row (630 + i)) 315 = 35558433678164808285 := by decide +kernel
private theorem cum_945 : LocatorKernelEval.sumRange row 945 = 117891887963248391580 := by
  rw [show (945 : ℕ) = 630 + 315 from rfl, sumRange_add, cum_630, blk_630]
private theorem blk_945 : LocatorKernelEval.sumRange (fun i => row (945 + i)) 315 = 31829960698156981710 := by decide +kernel
private theorem cum_1260 : LocatorKernelEval.sumRange row 1260 = 149721848661405373290 := by
  rw [show (1260 : ℕ) = 945 + 315 from rfl, sumRange_add, cum_945, blk_945]
private theorem blk_1260 : LocatorKernelEval.sumRange (fun i => row (1260 + i)) 315 = 28109279715331776885 := by decide +kernel
private theorem cum_1575 : LocatorKernelEval.sumRange row 1575 = 177831128376737150175 := by
  rw [show (1575 : ℕ) = 1260 + 315 from rfl, sumRange_add, cum_1260, blk_1260]
private theorem blk_1575 : LocatorKernelEval.sumRange (fun i => row (1575 + i)) 315 = 24396390729689193810 := by decide +kernel
private theorem cum_1890 : LocatorKernelEval.sumRange row 1890 = 202227519106426343985 := by
  rw [show (1890 : ℕ) = 1575 + 315 from rfl, sumRange_add, cum_1575, blk_1575]
private theorem blk_1890 : LocatorKernelEval.sumRange (fun i => row (1890 + i)) 315 = 20691293741229232485 := by decide +kernel
private theorem cum_2205 : LocatorKernelEval.sumRange row 2205 = 222918812847655576470 := by
  rw [show (2205 : ℕ) = 1890 + 315 from rfl, sumRange_add, cum_1890, blk_1890]
private theorem blk_2205 : LocatorKernelEval.sumRange (fun i => row (2205 + i)) 315 = 16993988749951892910 := by decide +kernel
private theorem cum_2520 : LocatorKernelEval.sumRange row 2520 = 239912801597607469380 := by
  rw [show (2520 : ℕ) = 2205 + 315 from rfl, sumRange_add, cum_2205, blk_2205]
private theorem blk_2520 : LocatorKernelEval.sumRange (fun i => row (2520 + i)) 315 = 13304475755857175085 := by decide +kernel
private theorem cum_2835 : LocatorKernelEval.sumRange row 2835 = 253217277353464644465 := by
  rw [show (2835 : ℕ) = 2520 + 315 from rfl, sumRange_add, cum_2520, blk_2520]
private theorem blk_2835 : LocatorKernelEval.sumRange (fun i => row (2835 + i)) 315 = 9622754758945079010 := by decide +kernel
private theorem cum_3150 : LocatorKernelEval.sumRange row 3150 = 262840032112409723475 := by
  rw [show (3150 : ℕ) = 2835 + 315 from rfl, sumRange_add, cum_2835, blk_2835]
private theorem blk_3150 : LocatorKernelEval.sumRange (fun i => row (3150 + i)) 315 = 5960497757848859183 := by decide +kernel
private theorem cum_3465 : LocatorKernelEval.sumRange row 3465 = 268800529870258582658 := by
  rw [show (3465 : ℕ) = 3150 + 315 from rfl, sumRange_add, cum_3150, blk_3150]
private theorem blk_3465 : LocatorKernelEval.sumRange (fun i => row (3465 + i)) 315 = 2809003445327116695 := by decide +kernel
private theorem cum_3780 : LocatorKernelEval.sumRange row 3780 = 271609533315585699353 := by
  rw [show (3780 : ℕ) = 3465 + 315 from rfl, sumRange_add, cum_3465, blk_3465]
private theorem blk_3780 : LocatorKernelEval.sumRange (fun i => row (3780 + i)) 315 = 827866194841603470 := by decide +kernel
private theorem cum_4095 : LocatorKernelEval.sumRange row 4095 = 272437399510427302823 := by
  rw [show (4095 : ℕ) = 3780 + 315 from rfl, sumRange_add, cum_3780, blk_3780]
private theorem blk_4095 : LocatorKernelEval.sumRange (fun i => row (4095 + i)) 199 = 51065671831789850 := by decide +kernel
private theorem cum_4294 : LocatorKernelEval.sumRange row 4294 = 272488465182259092673 := by
  rw [show (4294 : ℕ) = 4095 + 199 from rfl, sumRange_add, cum_4095, blk_4095]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 562712000 131071 300000 950 4294 = 272488465182259092673 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 4294 = _
  exact cum_4294
theorem nullity_eq :
    coefficientCount 562712000 131071 300000 950 - 262144 * localRankBound 3100 300000 950 = 1879915212902702273 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 562712000 131071 300000 950 4294 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelM3

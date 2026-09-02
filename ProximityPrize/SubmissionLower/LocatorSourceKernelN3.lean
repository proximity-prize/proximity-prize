import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelN3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel N3 = (4600, 400000, 1400) at agreements 181520: rank and nullity, the cutoff
count split into 30 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 4600 400000 1400 = 4469050310913300 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 4600 400000 1400 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (400000 + 1 - i - j) * (834992000 - 131071 * i - 131070 * j)) 1401
private theorem cum_214 : LocatorKernelEval.sumRange row 214 = 87290269278923534988 := by decide +kernel
private theorem blk_214 : LocatorKernelEval.sumRange (fun i => row (214 + i)) 214 = 83888235385623712404 := by decide +kernel
private theorem cum_428 : LocatorKernelEval.sumRange row 428 = 171178504664547247392 := by
  rw [show (428 : ℕ) = 214 + 214 from rfl, sumRange_add, cum_214, blk_214]
private theorem blk_428 : LocatorKernelEval.sumRange (fun i => row (428 + i)) 214 = 80489800775893253868 := by decide +kernel
private theorem cum_642 : LocatorKernelEval.sumRange row 642 = 251668305440440501260 := by
  rw [show (642 : ℕ) = 428 + 214 from rfl, sumRange_add, cum_428, blk_428]
private theorem blk_642 : LocatorKernelEval.sumRange (fun i => row (642 + i)) 214 = 77094965449732159380 := by decide +kernel
private theorem cum_856 : LocatorKernelEval.sumRange row 856 = 328763270890172660640 := by
  rw [show (856 : ℕ) = 642 + 214 from rfl, sumRange_add, cum_642, blk_642]
private theorem blk_856 : LocatorKernelEval.sumRange (fun i => row (856 + i)) 214 = 73703729407140428940 := by decide +kernel
private theorem cum_1070 : LocatorKernelEval.sumRange row 1070 = 402467000297313089580 := by
  rw [show (1070 : ℕ) = 856 + 214 from rfl, sumRange_add, cum_856, blk_856]
private theorem blk_1070 : LocatorKernelEval.sumRange (fun i => row (1070 + i)) 214 = 70316092648118062548 := by decide +kernel
private theorem cum_1284 : LocatorKernelEval.sumRange row 1284 = 472783092945431152128 := by
  rw [show (1284 : ℕ) = 1070 + 214 from rfl, sumRange_add, cum_1070, blk_1070]
private theorem blk_1284 : LocatorKernelEval.sumRange (fun i => row (1284 + i)) 214 = 66932055172665060204 := by decide +kernel
private theorem cum_1498 : LocatorKernelEval.sumRange row 1498 = 539715148118096212332 := by
  rw [show (1498 : ℕ) = 1284 + 214 from rfl, sumRange_add, cum_1284, blk_1284]
private theorem blk_1498 : LocatorKernelEval.sumRange (fun i => row (1498 + i)) 214 = 63551616980781421908 := by decide +kernel
private theorem cum_1712 : LocatorKernelEval.sumRange row 1712 = 603266765098877634240 := by
  rw [show (1712 : ℕ) = 1498 + 214 from rfl, sumRange_add, cum_1498, blk_1498]
private theorem blk_1712 : LocatorKernelEval.sumRange (fun i => row (1712 + i)) 214 = 60174778072467147660 := by decide +kernel
private theorem cum_1926 : LocatorKernelEval.sumRange row 1926 = 663441543171344781900 := by
  rw [show (1926 : ℕ) = 1712 + 214 from rfl, sumRange_add, cum_1712, blk_1712]
private theorem blk_1926 : LocatorKernelEval.sumRange (fun i => row (1926 + i)) 214 = 56801538447722237460 := by decide +kernel
private theorem cum_2140 : LocatorKernelEval.sumRange row 2140 = 720243081619067019360 := by
  rw [show (2140 : ℕ) = 1926 + 214 from rfl, sumRange_add, cum_1926, blk_1926]
private theorem blk_2140 : LocatorKernelEval.sumRange (fun i => row (2140 + i)) 214 = 53431898106546691308 := by decide +kernel
private theorem cum_2354 : LocatorKernelEval.sumRange row 2354 = 773674979725613710668 := by
  rw [show (2354 : ℕ) = 2140 + 214 from rfl, sumRange_add, cum_2140, blk_2140]
private theorem blk_2354 : LocatorKernelEval.sumRange (fun i => row (2354 + i)) 214 = 50065857048940509204 := by decide +kernel
private theorem cum_2568 : LocatorKernelEval.sumRange row 2568 = 823740836774554219872 := by
  rw [show (2568 : ℕ) = 2354 + 214 from rfl, sumRange_add, cum_2354, blk_2354]
private theorem blk_2568 : LocatorKernelEval.sumRange (fun i => row (2568 + i)) 214 = 46703415274903691148 := by decide +kernel
private theorem cum_2782 : LocatorKernelEval.sumRange row 2782 = 870444252049457911020 := by
  rw [show (2782 : ℕ) = 2568 + 214 from rfl, sumRange_add, cum_2568, blk_2568]
private theorem blk_2782 : LocatorKernelEval.sumRange (fun i => row (2782 + i)) 214 = 43344572784436237140 := by decide +kernel
private theorem cum_2996 : LocatorKernelEval.sumRange row 2996 = 913788824833894148160 := by
  rw [show (2996 : ℕ) = 2782 + 214 from rfl, sumRange_add, cum_2782, blk_2782]
private theorem blk_2996 : LocatorKernelEval.sumRange (fun i => row (2996 + i)) 214 = 39989329577538147180 := by decide +kernel
private theorem cum_3210 : LocatorKernelEval.sumRange row 3210 = 953778154411432295340 := by
  rw [show (3210 : ℕ) = 2996 + 214 from rfl, sumRange_add, cum_2996, blk_2996]
private theorem blk_3210 : LocatorKernelEval.sumRange (fun i => row (3210 + i)) 214 = 36637685654209421268 := by decide +kernel
private theorem cum_3424 : LocatorKernelEval.sumRange row 3424 = 990415840065641716608 := by
  rw [show (3424 : ℕ) = 3210 + 214 from rfl, sumRange_add, cum_3210, blk_3210]
private theorem blk_3424 : LocatorKernelEval.sumRange (fun i => row (3424 + i)) 214 = 33289641014450059404 := by decide +kernel
private theorem cum_3638 : LocatorKernelEval.sumRange row 3638 = 1023705481080091776012 := by
  rw [show (3638 : ℕ) = 3424 + 214 from rfl, sumRange_add, cum_3424, blk_3424]
private theorem blk_3638 : LocatorKernelEval.sumRange (fun i => row (3638 + i)) 214 = 29945195658260061588 := by decide +kernel
private theorem cum_3852 : LocatorKernelEval.sumRange row 3852 = 1053650676738351837600 := by
  rw [show (3852 : ℕ) = 3638 + 214 from rfl, sumRange_add, cum_3638, blk_3638]
private theorem blk_3852 : LocatorKernelEval.sumRange (fun i => row (3852 + i)) 214 = 26604349585639427820 := by decide +kernel
private theorem cum_4066 : LocatorKernelEval.sumRange row 4066 = 1080255026323991265420 := by
  rw [show (4066 : ℕ) = 3852 + 214 from rfl, sumRange_add, cum_3852, blk_3852]
private theorem blk_4066 : LocatorKernelEval.sumRange (fun i => row (4066 + i)) 214 = 23267102796588158100 := by decide +kernel
private theorem cum_4280 : LocatorKernelEval.sumRange row 4280 = 1103522129120579423520 := by
  rw [show (4280 : ℕ) = 4066 + 214 from rfl, sumRange_add, cum_4066, blk_4066]
private theorem blk_4280 : LocatorKernelEval.sumRange (fun i => row (4280 + i)) 214 = 19933455291106252428 := by decide +kernel
private theorem cum_4494 : LocatorKernelEval.sumRange row 4494 = 1123455584411685675948 := by
  rw [show (4494 : ℕ) = 4280 + 214 from rfl, sumRange_add, cum_4280, blk_4280]
private theorem blk_4494 : LocatorKernelEval.sumRange (fun i => row (4494 + i)) 214 = 16603407069193710804 := by decide +kernel
private theorem cum_4708 : LocatorKernelEval.sumRange row 4708 = 1140058991480879386752 := by
  rw [show (4708 : ℕ) = 4494 + 214 from rfl, sumRange_add, cum_4494, blk_4494]
private theorem blk_4708 : LocatorKernelEval.sumRange (fun i => row (4708 + i)) 214 = 13276958130850533228 := by decide +kernel
private theorem cum_4922 : LocatorKernelEval.sumRange row 4922 = 1153335949611729919980 := by
  rw [show (4922 : ℕ) = 4708 + 214 from rfl, sumRange_add, cum_4708, blk_4708]
private theorem blk_4922 : LocatorKernelEval.sumRange (fun i => row (4922 + i)) 214 = 9993049731090926245 := by decide +kernel
private theorem cum_5136 : LocatorKernelEval.sumRange row 5136 = 1163328999342820846225 := by
  rw [show (5136 : ℕ) = 4922 + 214 from rfl, sumRange_add, cum_4922, blk_4922]
private theorem blk_5136 : LocatorKernelEval.sumRange (fun i => row (5136 + i)) 214 = 7065514598584936490 := by decide +kernel
private theorem cum_5350 : LocatorKernelEval.sumRange row 5350 = 1170394513941405782715 := by
  rw [show (5350 : ℕ) = 5136 + 214 from rfl, sumRange_add, cum_5136, blk_5136]
private theorem blk_5350 : LocatorKernelEval.sumRange (fun i => row (5350 + i)) 214 = 4645533502498362447 := by decide +kernel
private theorem cum_5564 : LocatorKernelEval.sumRange row 5564 = 1175040047443904145162 := by
  rw [show (5564 : ℕ) = 5350 + 214 from rfl, sumRange_add, cum_5350, blk_5350]
private theorem blk_5564 : LocatorKernelEval.sumRange (fun i => row (5564 + i)) 214 = 2733540211656865448 := by decide +kernel
private theorem cum_5778 : LocatorKernelEval.sumRange row 5778 = 1177773587655561010610 := by
  rw [show (5778 : ℕ) = 5564 + 214 from rfl, sumRange_add, cum_5564, blk_5564]
private theorem blk_5778 : LocatorKernelEval.sumRange (fun i => row (5778 + i)) 214 = 1328984940462926405 := by decide +kernel
private theorem cum_5992 : LocatorKernelEval.sumRange row 5992 = 1179102572596023937015 := by
  rw [show (5992 : ℕ) = 5778 + 214 from rfl, sumRange_add, cum_5778, blk_5778]
private theorem blk_5992 : LocatorKernelEval.sumRange (fun i => row (5992 + i)) 214 = 431317903319026230 := by decide +kernel
private theorem cum_6206 : LocatorKernelEval.sumRange row 6206 = 1179533890499342963245 := by
  rw [show (6206 : ℕ) = 5992 + 214 from rfl, sumRange_add, cum_5992, blk_5992]
private theorem blk_6206 : LocatorKernelEval.sumRange (fun i => row (6206 + i)) 165 = 39010412472019615 := by decide +kernel
private theorem cum_6371 : LocatorKernelEval.sumRange row 6371 = 1179572900911814982860 := by
  rw [show (6371 : ℕ) = 6206 + 165 from rfl, sumRange_add, cum_6206, blk_6206]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 834992000 131071 400000 1400 6371 = 1179572900911814982860 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 6371 = _
  exact cum_6371
theorem nullity_eq :
    coefficientCount 834992000 131071 400000 1400 - 262144 * localRankBound 4600 400000 1400 = 8038176207758867660 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 834992000 131071 400000 1400 6371 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelN3

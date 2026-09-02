import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL6
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L6 = (3900, 200000, 1200) at agreements 181520: rank and nullity, the cutoff
count split into 22 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 3900 200000 1200 = 1368423036387800 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3900 200000 1200 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (200000 + 1 - i - j) * (707928000 - 131071 * i - 131070 * j)) 1201
private theorem cum_249 : LocatorKernelEval.sumRange row 249 = 36537761368576800808 := by decide +kernel
private theorem blk_249 : LocatorKernelEval.sumRange (fun i => row (249 + i)) 249 = 34549606397993339824 := by decide +kernel
private theorem cum_498 : LocatorKernelEval.sumRange row 498 = 71087367766570140632 := by
  rw [show (498 : ℕ) = 249 + 249 from rfl, sumRange_add, cum_249, blk_249]
private theorem blk_498 : LocatorKernelEval.sumRange (fun i => row (498 + i)) 249 = 32566311890586577798 := by decide +kernel
private theorem cum_747 : LocatorKernelEval.sumRange row 747 = 103653679657156718430 := by
  rw [show (747 : ℕ) = 498 + 249 from rfl, sumRange_add, cum_498, blk_498]
private theorem blk_747 : LocatorKernelEval.sumRange (fun i => row (747 + i)) 249 = 30587877846356514730 := by decide +kernel
private theorem cum_996 : LocatorKernelEval.sumRange row 996 = 134241557503513233160 := by
  rw [show (996 : ℕ) = 747 + 249 from rfl, sumRange_add, cum_747, blk_747]
private theorem blk_996 : LocatorKernelEval.sumRange (fun i => row (996 + i)) 249 = 28614304265303150620 := by decide +kernel
private theorem cum_1245 : LocatorKernelEval.sumRange row 1245 = 162855861768816383780 := by
  rw [show (1245 : ℕ) = 996 + 249 from rfl, sumRange_add, cum_996, blk_996]
private theorem blk_1245 : LocatorKernelEval.sumRange (fun i => row (1245 + i)) 249 = 26645591147426485468 := by decide +kernel
private theorem cum_1494 : LocatorKernelEval.sumRange row 1494 = 189501452916242869248 := by
  rw [show (1494 : ℕ) = 1245 + 249 from rfl, sumRange_add, cum_1245, blk_1245]
private theorem blk_1494 : LocatorKernelEval.sumRange (fun i => row (1494 + i)) 249 = 24681738492726519274 := by decide +kernel
private theorem cum_1743 : LocatorKernelEval.sumRange row 1743 = 214183191408969388522 := by
  rw [show (1743 : ℕ) = 1494 + 249 from rfl, sumRange_add, cum_1494, blk_1494]
private theorem blk_1743 : LocatorKernelEval.sumRange (fun i => row (1743 + i)) 249 = 22722746301203252038 := by decide +kernel
private theorem cum_1992 : LocatorKernelEval.sumRange row 1992 = 236905937710172640560 := by
  rw [show (1992 : ℕ) = 1743 + 249 from rfl, sumRange_add, cum_1743, blk_1743]
private theorem blk_1992 : LocatorKernelEval.sumRange (fun i => row (1992 + i)) 249 = 20768614572856683760 := by decide +kernel
private theorem cum_2241 : LocatorKernelEval.sumRange row 2241 = 257674552283029324320 := by
  rw [show (2241 : ℕ) = 1992 + 249 from rfl, sumRange_add, cum_1992, blk_1992]
private theorem blk_2241 : LocatorKernelEval.sumRange (fun i => row (2241 + i)) 249 = 18819343307686814440 := by decide +kernel
private theorem cum_2490 : LocatorKernelEval.sumRange row 2490 = 276493895590716138760 := by
  rw [show (2490 : ℕ) = 2241 + 249 from rfl, sumRange_add, cum_2241, blk_2241]
private theorem blk_2490 : LocatorKernelEval.sumRange (fun i => row (2490 + i)) 249 = 16874932505693644078 := by decide +kernel
private theorem cum_2739 : LocatorKernelEval.sumRange row 2739 = 293368828096409782838 := by
  rw [show (2739 : ℕ) = 2490 + 249 from rfl, sumRange_add, cum_2490, blk_2490]
private theorem blk_2739 : LocatorKernelEval.sumRange (fun i => row (2739 + i)) 249 = 14935382166877172674 := by decide +kernel
private theorem cum_2988 : LocatorKernelEval.sumRange row 2988 = 308304210263286955512 := by
  rw [show (2988 : ℕ) = 2739 + 249 from rfl, sumRange_add, cum_2739, blk_2739]
private theorem blk_2988 : LocatorKernelEval.sumRange (fun i => row (2988 + i)) 249 = 13000692291237400228 := by decide +kernel
private theorem cum_3237 : LocatorKernelEval.sumRange row 3237 = 321304902554524355740 := by
  rw [show (3237 : ℕ) = 2988 + 249 from rfl, sumRange_add, cum_2988, blk_2988]
private theorem blk_3237 : LocatorKernelEval.sumRange (fun i => row (3237 + i)) 249 = 11070862878774326740 := by decide +kernel
private theorem cum_3486 : LocatorKernelEval.sumRange row 3486 = 332375765433298682480 := by
  rw [show (3486 : ℕ) = 3237 + 249 from rfl, sumRange_add, cum_3237, blk_3237]
private theorem blk_3486 : LocatorKernelEval.sumRange (fun i => row (3486 + i)) 249 = 9145893929487952210 := by decide +kernel
private theorem cum_3735 : LocatorKernelEval.sumRange row 3735 = 341521659362786634690 := by
  rw [show (3735 : ℕ) = 3486 + 249 from rfl, sumRange_add, cum_3486, blk_3486]
private theorem blk_3735 : LocatorKernelEval.sumRange (fun i => row (3735 + i)) 249 = 7225785443378276638 := by decide +kernel
private theorem cum_3984 : LocatorKernelEval.sumRange row 3984 = 348747444806164911328 := by
  rw [show (3984 : ℕ) = 3735 + 249 from rfl, sumRange_add, cum_3735, blk_3735]
private theorem blk_3984 : LocatorKernelEval.sumRange (fun i => row (3984 + i)) 249 = 5310675151391185712 := by decide +kernel
private theorem cum_4233 : LocatorKernelEval.sumRange row 4233 = 354058119957556097040 := by
  rw [show (4233 : ℕ) = 3984 + 249 from rfl, sumRange_add, cum_3984, blk_3984]
private theorem blk_4233 : LocatorKernelEval.sumRange (fun i => row (4233 + i)) 249 = 3494153745756108830 := by decide +kernel
private theorem cum_4482 : LocatorKernelEval.sumRange row 4482 = 357552273703312205870 := by
  rw [show (4482 : ℕ) = 4233 + 249 from rfl, sumRange_add, cum_4233, blk_4233]
private theorem blk_4482 : LocatorKernelEval.sumRange (fun i => row (4482 + i)) 249 = 2032106874098652110 := by decide +kernel
private theorem cum_4731 : LocatorKernelEval.sumRange row 4731 = 359584380577410857980 := by
  rw [show (4731 : ℕ) = 4482 + 249 from rfl, sumRange_add, cum_4482, blk_4482]
private theorem blk_4731 : LocatorKernelEval.sumRange (fun i => row (4731 + i)) 249 = 967057037645337155 := by decide +kernel
private theorem cum_4980 : LocatorKernelEval.sumRange row 4980 = 360551437615056195135 := by
  rw [show (4980 : ℕ) = 4731 + 249 from rfl, sumRange_add, cum_4731, blk_4731]
private theorem blk_4980 : LocatorKernelEval.sumRange (fun i => row (4980 + i)) 249 = 297996526198169822 := by decide +kernel
private theorem cum_5229 : LocatorKernelEval.sumRange row 5229 = 360849434141254364957 := by
  rw [show (5229 : ℕ) = 4980 + 249 from rfl, sumRange_add, cum_4980, blk_4980]
private theorem blk_5229 : LocatorKernelEval.sumRange (fun i => row (5229 + i)) 173 = 22059687618404743 := by decide +kernel
private theorem cum_5402 : LocatorKernelEval.sumRange row 5402 = 360871493828872769700 := by
  rw [show (5402 : ℕ) = 5229 + 173 from rfl, sumRange_add, cum_5229, blk_5229]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 707928000 131071 200000 1200 5402 = 360871493828872769700 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 5402 = _
  exact cum_5402
theorem nullity_eq :
    coefficientCount 707928000 131071 200000 1200 - 262144 * localRankBound 3900 200000 1200 = 2147605378029326500 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 707928000 131071 200000 1200 5402 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL6

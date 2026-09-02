import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL5
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L5 = (3120, 200000, 960) at agreements 181520: rank and nullity, the cutoff
count split into 14 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 3120 200000 960 = 702078387192640 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3120 200000 960 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (200000 + 1 - i - j) * (566342400 - 131071 * i - 131070 * j)) 961
private theorem cum_312 : LocatorKernelEval.sumRange row 312 = 28878051869144923120 := by decide +kernel
private theorem blk_312 : LocatorKernelEval.sumRange (fun i => row (312 + i)) 312 = 26392194280367579248 := by decide +kernel
private theorem cum_624 : LocatorKernelEval.sumRange row 624 = 55270246149512502368 := by
  rw [show (624 : ℕ) = 312 + 312 from rfl, sumRange_add, cum_312, blk_312]
private theorem blk_624 : LocatorKernelEval.sumRange (fun i => row (624 + i)) 312 = 23913987789828892912 := by decide +kernel
private theorem cum_936 : LocatorKernelEval.sumRange row 936 = 79184233939341395280 := by
  rw [show (936 : ℕ) = 624 + 312 from rfl, sumRange_add, cum_624, blk_624]
private theorem blk_936 : LocatorKernelEval.sumRange (fun i => row (936 + i)) 312 = 21443432397528864112 := by decide +kernel
private theorem cum_1248 : LocatorKernelEval.sumRange row 1248 = 100627666336870259392 := by
  rw [show (1248 : ℕ) = 936 + 312 from rfl, sumRange_add, cum_936, blk_936]
private theorem blk_1248 : LocatorKernelEval.sumRange (fun i => row (1248 + i)) 312 = 18980528103467492848 := by decide +kernel
private theorem cum_1560 : LocatorKernelEval.sumRange row 1560 = 119608194440337752240 := by
  rw [show (1560 : ℕ) = 1248 + 312 from rfl, sumRange_add, cum_1248, blk_1248]
private theorem blk_1560 : LocatorKernelEval.sumRange (fun i => row (1560 + i)) 312 = 16525274907644779120 := by decide +kernel
private theorem cum_1872 : LocatorKernelEval.sumRange row 1872 = 136133469347982531360 := by
  rw [show (1872 : ℕ) = 1560 + 312 from rfl, sumRange_add, cum_1560, blk_1560]
private theorem blk_1872 : LocatorKernelEval.sumRange (fun i => row (1872 + i)) 312 = 14077672810060722928 := by decide +kernel
private theorem cum_2184 : LocatorKernelEval.sumRange row 2184 = 150211142158043254288 := by
  rw [show (2184 : ℕ) = 1872 + 312 from rfl, sumRange_add, cum_1872, blk_1872]
private theorem blk_2184 : LocatorKernelEval.sumRange (fun i => row (2184 + i)) 312 = 11637721810715324272 := by decide +kernel
private theorem cum_2496 : LocatorKernelEval.sumRange row 2496 = 161848863968758578560 := by
  rw [show (2496 : ℕ) = 2184 + 312 from rfl, sumRange_add, cum_2184, blk_2184]
private theorem blk_2496 : LocatorKernelEval.sumRange (fun i => row (2496 + i)) 312 = 9205421909608583152 := by decide +kernel
private theorem cum_2808 : LocatorKernelEval.sumRange row 2808 = 171054285878367161712 := by
  rw [show (2808 : ℕ) = 2496 + 312 from rfl, sumRange_add, cum_2496, blk_2496]
private theorem blk_2808 : LocatorKernelEval.sumRange (fun i => row (2808 + i)) 312 = 6780773106740499568 := by decide +kernel
private theorem cum_3120 : LocatorKernelEval.sumRange row 3120 = 177835058985107661280 := by
  rw [show (3120 : ℕ) = 2808 + 312 from rfl, sumRange_add, cum_2808, blk_2808]
private theorem blk_3120 : LocatorKernelEval.sumRange (fun i => row (3120 + i)) 312 = 4365311998321264150 := by decide +kernel
private theorem cum_3432 : LocatorKernelEval.sumRange row 3432 = 182200370983428925430 := by
  rw [show (3432 : ℕ) = 3120 + 312 from rfl, sumRange_add, cum_3120, blk_3120]
private theorem blk_3432 : LocatorKernelEval.sumRange (fun i => row (3432 + i)) 312 = 2193023476361289962 := by decide +kernel
private theorem cum_3744 : LocatorKernelEval.sumRange row 3744 = 184393394459790215392 := by
  rw [show (3744 : ℕ) = 3432 + 312 from rfl, sumRange_add, cum_3432, blk_3432]
private theorem blk_3744 : LocatorKernelEval.sumRange (fun i => row (3744 + i)) 312 = 745758029665096058 := by decide +kernel
private theorem cum_4056 : LocatorKernelEval.sumRange row 4056 = 185139152489455311450 := by
  rw [show (4056 : ℕ) = 3744 + 312 from rfl, sumRange_add, cum_3744, blk_3744]
private theorem blk_4056 : LocatorKernelEval.sumRange (fun i => row (4056 + i)) 265 = 80401784090693590 := by decide +kernel
private theorem cum_4321 : LocatorKernelEval.sumRange row 4321 = 185219554273546005040 := by
  rw [show (4321 : ℕ) = 4056 + 265 from rfl, sumRange_add, cum_4056, blk_4056]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 566342400 131071 200000 960 4321 = 185219554273546005040 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 4321 = _
  exact cum_4321
theorem nullity_eq :
    coefficientCount 566342400 131071 200000 960 - 262144 * localRankBound 3120 200000 960 = 1173917541318584880 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 566342400 131071 200000 960 4321 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL5

import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelN4
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel N4 = (5200, 400000, 1600) at agreements 181520: rank and nullity, the cutoff
count split into 39 row blocks of the Nat-recursive `LocatorKernelEval.sumRange`. -/
theorem rank_eq : localRankBound 5200 400000 1600 = 6504399142910400 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 5200 400000 1600 (by decide)]
  decide +kernel
theorem sumRange_add (f : ℕ → ℕ) (n k : ℕ) :
    LocatorKernelEval.sumRange f (n + k) = LocatorKernelEval.sumRange f n + LocatorKernelEval.sumRange (fun i => f (n + i)) k := by
  induction k with
  | zero => simp [LocatorKernelEval.sumRange]
  | succ k ih => rw [Nat.add_succ, LocatorKernelEval.sumRange_succ, ih, LocatorKernelEval.sumRange_succ, Nat.add_assoc]
def row (i : ℕ) : ℕ := LocatorKernelEval.sumRange (fun j => (400000 + 1 - i - j) * (943904000 - 131071 * i - 131070 * j)) 1601
private theorem cum_187 : LocatorKernelEval.sumRange row 187 = 98807942928734501990 := by decide +kernel
private theorem blk_187 : LocatorKernelEval.sumRange (fun i => row (187 + i)) 187 = 95834345401094023218 := by decide +kernel
private theorem cum_374 : LocatorKernelEval.sumRange row 374 = 194642288329828525208 := by
  rw [show (374 : ℕ) = 187 + 187 from rfl, sumRange_add, cum_187, blk_187]
private theorem blk_374 : LocatorKernelEval.sumRange (fun i => row (374 + i)) 187 = 92863492307257818872 := by decide +kernel
private theorem cum_561 : LocatorKernelEval.sumRange row 561 = 287505780637086344080 := by
  rw [show (561 : ℕ) = 374 + 187 from rfl, sumRange_add, cum_374, blk_374]
private theorem blk_561 : LocatorKernelEval.sumRange (fun i => row (561 + i)) 187 = 89895383647225888952 := by decide +kernel
private theorem cum_748 : LocatorKernelEval.sumRange row 748 = 377401164284312233032 := by
  rw [show (748 : ℕ) = 561 + 187 from rfl, sumRange_add, cum_561, blk_561]
private theorem blk_748 : LocatorKernelEval.sumRange (fun i => row (748 + i)) 187 = 86930019420998233458 := by decide +kernel
private theorem cum_935 : LocatorKernelEval.sumRange row 935 = 464331183705310466490 := by
  rw [show (935 : ℕ) = 748 + 187 from rfl, sumRange_add, cum_748, blk_748]
private theorem blk_935 : LocatorKernelEval.sumRange (fun i => row (935 + i)) 187 = 83967399628574852390 := by decide +kernel
private theorem cum_1122 : LocatorKernelEval.sumRange row 1122 = 548298583333885318880 := by
  rw [show (1122 : ℕ) = 935 + 187 from rfl, sumRange_add, cum_935, blk_935]
private theorem blk_1122 : LocatorKernelEval.sumRange (fun i => row (1122 + i)) 187 = 81007524269955745748 := by decide +kernel
private theorem cum_1309 : LocatorKernelEval.sumRange row 1309 = 629306107603841064628 := by
  rw [show (1309 : ℕ) = 1122 + 187 from rfl, sumRange_add, cum_1122, blk_1122]
private theorem blk_1309 : LocatorKernelEval.sumRange (fun i => row (1309 + i)) 187 = 78050393345140913532 := by decide +kernel
private theorem cum_1496 : LocatorKernelEval.sumRange row 1496 = 707356500948981978160 := by
  rw [show (1496 : ℕ) = 1309 + 187 from rfl, sumRange_add, cum_1309, blk_1309]
private theorem blk_1496 : LocatorKernelEval.sumRange (fun i => row (1496 + i)) 187 = 75096006854130355742 := by decide +kernel
private theorem cum_1683 : LocatorKernelEval.sumRange row 1683 = 782452507803112333902 := by
  rw [show (1683 : ℕ) = 1496 + 187 from rfl, sumRange_add, cum_1496, blk_1496]
private theorem blk_1683 : LocatorKernelEval.sumRange (fun i => row (1683 + i)) 187 = 72144364796924072378 := by decide +kernel
private theorem cum_1870 : LocatorKernelEval.sumRange row 1870 = 854596872600036406280 := by
  rw [show (1870 : ℕ) = 1683 + 187 from rfl, sumRange_add, cum_1683, blk_1683]
private theorem blk_1870 : LocatorKernelEval.sumRange (fun i => row (1870 + i)) 187 = 69195467173522063440 := by decide +kernel
private theorem cum_2057 : LocatorKernelEval.sumRange row 2057 = 923792339773558469720 := by
  rw [show (2057 : ℕ) = 1870 + 187 from rfl, sumRange_add, cum_1870, blk_1870]
private theorem blk_2057 : LocatorKernelEval.sumRange (fun i => row (2057 + i)) 187 = 66249313983924328928 := by decide +kernel
private theorem cum_2244 : LocatorKernelEval.sumRange row 2244 = 990041653757482798648 := by
  rw [show (2244 : ℕ) = 2057 + 187 from rfl, sumRange_add, cum_2057, blk_2057]
private theorem blk_2244 : LocatorKernelEval.sumRange (fun i => row (2244 + i)) 187 = 63305905228130868842 := by decide +kernel
private theorem cum_2431 : LocatorKernelEval.sumRange row 2431 = 1053347558985613667490 := by
  rw [show (2431 : ℕ) = 2244 + 187 from rfl, sumRange_add, cum_2244, blk_2244]
private theorem blk_2431 : LocatorKernelEval.sumRange (fun i => row (2431 + i)) 187 = 60365240906141683182 := by decide +kernel
private theorem cum_2618 : LocatorKernelEval.sumRange row 2618 = 1113712799891755350672 := by
  rw [show (2618 : ℕ) = 2431 + 187 from rfl, sumRange_add, cum_2431, blk_2431]
private theorem blk_2618 : LocatorKernelEval.sumRange (fun i => row (2618 + i)) 187 = 57427321017956771948 := by decide +kernel
private theorem cum_2805 : LocatorKernelEval.sumRange row 2805 = 1171140120909712122620 := by
  rw [show (2805 : ℕ) = 2618 + 187 from rfl, sumRange_add, cum_2618, blk_2618]
private theorem blk_2805 : LocatorKernelEval.sumRange (fun i => row (2805 + i)) 187 = 54492145563576135140 := by decide +kernel
private theorem cum_2992 : LocatorKernelEval.sumRange row 2992 = 1225632266473288257760 := by
  rw [show (2992 : ℕ) = 2805 + 187 from rfl, sumRange_add, cum_2805, blk_2805]
private theorem blk_2992 : LocatorKernelEval.sumRange (fun i => row (2992 + i)) 187 = 51559714542999772758 := by decide +kernel
private theorem cum_3179 : LocatorKernelEval.sumRange row 3179 = 1277191981016288030518 := by
  rw [show (3179 : ℕ) = 2992 + 187 from rfl, sumRange_add, cum_2992, blk_2992]
private theorem blk_3179 : LocatorKernelEval.sumRange (fun i => row (3179 + i)) 187 = 48630027956227684802 := by decide +kernel
private theorem cum_3366 : LocatorKernelEval.sumRange row 3366 = 1325822008972515715320 := by
  rw [show (3366 : ℕ) = 3179 + 187 from rfl, sumRange_add, cum_3179, blk_3179]
private theorem blk_3366 : LocatorKernelEval.sumRange (fun i => row (3366 + i)) 187 = 45703085803259871272 := by decide +kernel
private theorem cum_3553 : LocatorKernelEval.sumRange row 3553 = 1371525094775775586592 := by
  rw [show (3553 : ℕ) = 3366 + 187 from rfl, sumRange_add, cum_3366, blk_3366]
private theorem blk_3553 : LocatorKernelEval.sumRange (fun i => row (3553 + i)) 187 = 42778888084096332168 := by decide +kernel
private theorem cum_3740 : LocatorKernelEval.sumRange row 3740 = 1414303982859871918760 := by
  rw [show (3740 : ℕ) = 3553 + 187 from rfl, sumRange_add, cum_3553, blk_3553]
private theorem blk_3740 : LocatorKernelEval.sumRange (fun i => row (3740 + i)) 187 = 39857434798737067490 := by decide +kernel
private theorem cum_3927 : LocatorKernelEval.sumRange row 3927 = 1454161417658608986250 := by
  rw [show (3927 : ℕ) = 3740 + 187 from rfl, sumRange_add, cum_3740, blk_3740]
private theorem blk_3927 : LocatorKernelEval.sumRange (fun i => row (3927 + i)) 187 = 36938725947182077238 := by decide +kernel
private theorem cum_4114 : LocatorKernelEval.sumRange row 4114 = 1491100143605791063488 := by
  rw [show (4114 : ℕ) = 3927 + 187 from rfl, sumRange_add, cum_3927, blk_3927]
private theorem blk_4114 : LocatorKernelEval.sumRange (fun i => row (4114 + i)) 187 = 34022761529431361412 := by decide +kernel
private theorem cum_4301 : LocatorKernelEval.sumRange row 4301 = 1525122905135222424900 := by
  rw [show (4301 : ℕ) = 4114 + 187 from rfl, sumRange_add, cum_4114, blk_4114]
private theorem blk_4301 : LocatorKernelEval.sumRange (fun i => row (4301 + i)) 187 = 31109541545484920012 := by decide +kernel
private theorem cum_4488 : LocatorKernelEval.sumRange row 4488 = 1556232446680707344912 := by
  rw [show (4488 : ℕ) = 4301 + 187 from rfl, sumRange_add, cum_4301, blk_4301]
private theorem blk_4488 : LocatorKernelEval.sumRange (fun i => row (4488 + i)) 187 = 28199065995342753038 := by decide +kernel
private theorem cum_4675 : LocatorKernelEval.sumRange row 4675 = 1584431512676050097950 := by
  rw [show (4675 : ℕ) = 4488 + 187 from rfl, sumRange_add, cum_4488, blk_4488]
private theorem blk_4675 : LocatorKernelEval.sumRange (fun i => row (4675 + i)) 187 = 25291334879004860490 := by decide +kernel
private theorem cum_4862 : LocatorKernelEval.sumRange row 4862 = 1609722847555054958440 := by
  rw [show (4862 : ℕ) = 4675 + 187 from rfl, sumRange_add, cum_4675, blk_4675]
private theorem blk_4862 : LocatorKernelEval.sumRange (fun i => row (4862 + i)) 187 = 22386348196471242368 := by decide +kernel
private theorem cum_5049 : LocatorKernelEval.sumRange row 5049 = 1632109195751526200808 := by
  rw [show (5049 : ℕ) = 4862 + 187 from rfl, sumRange_add, cum_4862, blk_4862]
private theorem blk_5049 : LocatorKernelEval.sumRange (fun i => row (5049 + i)) 187 = 19484105947741898672 := by decide +kernel
private theorem cum_5236 : LocatorKernelEval.sumRange row 5236 = 1651593301699268099480 := by
  rw [show (5236 : ℕ) = 5049 + 187 from rfl, sumRange_add, cum_5049, blk_5049]
private theorem blk_5236 : LocatorKernelEval.sumRange (fun i => row (5236 + i)) 187 = 16584608132816829402 := by decide +kernel
private theorem cum_5423 : LocatorKernelEval.sumRange row 5423 = 1668177909832084928882 := by
  rw [show (5423 : ℕ) = 5236 + 187 from rfl, sumRange_add, cum_5236, blk_5236]
private theorem blk_5423 : LocatorKernelEval.sumRange (fun i => row (5423 + i)) 187 = 13687860034305783488 := by decide +kernel
private theorem cum_5610 : LocatorKernelEval.sumRange row 5610 = 1681865769866390712370 := by
  rw [show (5610 : ℕ) = 5423 + 187 from rfl, sumRange_add, cum_5423, blk_5423]
private theorem blk_5610 : LocatorKernelEval.sumRange (fun i => row (5610 + i)) 187 = 10857957215400871235 := by decide +kernel
private theorem cum_5797 : LocatorKernelEval.sumRange row 5797 = 1692723727081791583605 := by
  rw [show (5797 : ℕ) = 5610 + 187 from rfl, sumRange_add, cum_5610, blk_5610]
private theorem blk_5797 : LocatorKernelEval.sumRange (fun i => row (5797 + i)) 187 = 8318495292993488427 := by decide +kernel
private theorem cum_5984 : LocatorKernelEval.sumRange row 5984 = 1701042222374785072032 := by
  rw [show (5984 : ℕ) = 5797 + 187 from rfl, sumRange_add, cum_5797, blk_5797]
private theorem blk_5984 : LocatorKernelEval.sumRange (fun i => row (5984 + i)) 187 = 6117953355847258838 := by decide +kernel
private theorem cum_6171 : LocatorKernelEval.sumRange row 6171 = 1707160175730632330870 := by
  rw [show (6171 : ℕ) = 5984 + 187 from rfl, sumRange_add, cum_5984, blk_5984]
private theorem blk_6171 : LocatorKernelEval.sumRange (fun i => row (6171 + i)) 187 = 4256010847385573045 := by decide +kernel
private theorem cum_6358 : LocatorKernelEval.sumRange row 6358 = 1711416186578017903915 := by
  rw [show (6358 : ℕ) = 6171 + 187 from rfl, sumRange_add, cum_6171, blk_6171]
private theorem blk_6358 : LocatorKernelEval.sumRange (fun i => row (6358 + i)) 187 = 2732347211031821625 := by decide +kernel
private theorem cum_6545 : LocatorKernelEval.sumRange row 6545 = 1714148533789049725540 := by
  rw [show (6545 : ℕ) = 6358 + 187 from rfl, sumRange_add, cum_6358, blk_6358]
private theorem blk_6545 : LocatorKernelEval.sumRange (fun i => row (6545 + i)) 187 = 1546641890209395155 := by decide +kernel
private theorem cum_6732 : LocatorKernelEval.sumRange row 6732 = 1715695175679259120695 := by
  rw [show (6732 : ℕ) = 6545 + 187 from rfl, sumRange_add, cum_6545, blk_6545]
private theorem blk_6732 : LocatorKernelEval.sumRange (fun i => row (6732 + i)) 187 = 698574328341684212 := by decide +kernel
private theorem cum_6919 : LocatorKernelEval.sumRange row 6919 = 1716393750007600804907 := by
  rw [show (6919 : ℕ) = 6732 + 187 from rfl, sumRange_add, cum_6732, blk_6732]
private theorem blk_6919 : LocatorKernelEval.sumRange (fun i => row (6919 + i)) 187 = 187823968852079373 := by decide +kernel
private theorem cum_7106 : LocatorKernelEval.sumRange row 7106 = 1716581573976452884280 := by
  rw [show (7106 : ℕ) = 6919 + 187 from rfl, sumRange_add, cum_6919, blk_6919]
private theorem blk_7106 : LocatorKernelEval.sumRange (fun i => row (7106 + i)) 96 = 7704791877075320 := by decide +kernel
private theorem cum_7202 : LocatorKernelEval.sumRange row 7202 = 1716589278768329959600 := by
  rw [show (7202 : ℕ) = 7106 + 96 from rfl, sumRange_add, cum_7106, blk_7106]
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 943904000 131071 400000 1600 7202 = 1716589278768329959600 := by
  unfold LocatorKernelEval.coefficientCountCutoff
  change LocatorKernelEval.sumRange row 7202 = _
  exact cum_7202
theorem nullity_eq :
    coefficientCount 943904000 131071 400000 1600 - 262144 * localRankBound 5200 400000 1600 = 11500069849226062000 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 943904000 131071 400000 1600 7202 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelN4

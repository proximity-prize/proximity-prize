import ProximityPrize.SubmissionLower.Koala6844ReceiptsColumnsClosed
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticFast
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false


private def sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : sliceWindow f a b = x) (hy : sliceWindow f (a+b) c = y) :
    sliceWindow f a (b+c) = x+y := by
  simp only [sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [sliceWindow,Nat.zero_add]

private theorem margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← sliceWindow_zero (auxiliaryRankSlice src),
    ← sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem contact01OrdinaryColumns : ordinaryColumnCount contact01 = 2431757391734239 := by decide +kernel
private theorem contact01ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact01) 0 4 = 7338988038648 :=
  contactColumnsWindow_fast contact01 0 4 7338988038648 (by decide +kernel)
private theorem contact01ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact01) 4 4 = 6989755965688 :=
  contactColumnsWindow_fast contact01 4 4 6989755965688 (by decide +kernel)
private theorem contact01ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact01) 8 4 = 6649067586988 :=
  contactColumnsWindow_fast contact01 8 4 6649067586988 (by decide +kernel)
private theorem contact01ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact01) 12 4 = 6316923127084 :=
  contactColumnsWindow_fast contact01 12 4 6316923127084 (by decide +kernel)
private theorem contact01ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact01) 16 4 = 5993354512684 :=
  contactColumnsWindow_fast contact01 16 4 5993354512684 (by decide +kernel)
private theorem contact01ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact01) 20 4 = 5678348071555 :=
  contactColumnsWindow_fast contact01 20 4 5678348071555 (by decide +kernel)
private theorem contact01ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact01) 24 4 = 5371888886115 :=
  contactColumnsWindow_fast contact01 24 4 5371888886115 (by decide +kernel)
private theorem contact01ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact01) 28 4 = 5073975664496 :=
  contactColumnsWindow_fast contact01 28 4 5073975664496 (by decide +kernel)
private theorem contact01ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact01) 32 4 = 4784611343068 :=
  contactColumnsWindow_fast contact01 32 4 4784611343068 (by decide +kernel)
private theorem contact01ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact01) 36 4 = 4503827209030 :=
  contactColumnsWindow_fast contact01 36 4 4503827209030 (by decide +kernel)
private theorem contact01ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact01) 40 4 = 4231606350034 :=
  contactColumnsWindow_fast contact01 40 4 4231606350034 (by decide +kernel)
private theorem contact01ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact01) 44 4 = 3967934604201 :=
  contactColumnsWindow_fast contact01 44 4 3967934604201 (by decide +kernel)
private theorem contact01ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact01) 48 4 = 3712813233556 :=
  contactColumnsWindow_fast contact01 48 4 3712813233556 (by decide +kernel)
private theorem contact01ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact01) 52 4 = 3466244074441 :=
  contactColumnsWindow_fast contact01 52 4 3466244074441 (by decide +kernel)
private theorem contact01ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact01) 56 4 = 3228261792323 :=
  contactColumnsWindow_fast contact01 56 4 3228261792323 (by decide +kernel)
private theorem contact01ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact01) 60 4 = 2998842463630 :=
  contactColumnsWindow_fast contact01 60 4 2998842463630 (by decide +kernel)
private theorem contact01ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact01) 64 4 = 2777975627103 :=
  contactColumnsWindow_fast contact01 64 4 2777975627103 (by decide +kernel)
private theorem contact01ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact01) 68 4 = 2565659125300 :=
  contactColumnsWindow_fast contact01 68 4 2565659125300 (by decide +kernel)
private theorem contact01ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact01) 72 4 = 2361897148444 :=
  contactColumnsWindow_fast contact01 72 4 2361897148444 (by decide +kernel)
private theorem contact01ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact01) 76 4 = 2166722383649 :=
  contactColumnsWindow_fast contact01 76 4 2166722383649 (by decide +kernel)
private theorem contact01ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact01) 80 4 = 1980108500410 :=
  contactColumnsWindow_fast contact01 80 4 1980108500410 (by decide +kernel)
private theorem contact01ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact01) 84 4 = 1802046637550 :=
  contactColumnsWindow_fast contact01 84 4 1802046637550 (by decide +kernel)
private theorem contact01ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact01) 88 4 = 1632535067082 :=
  contactColumnsWindow_fast contact01 88 4 1632535067082 (by decide +kernel)
private theorem contact01ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact01) 92 4 = 1471580477548 :=
  contactColumnsWindow_fast contact01 92 4 1471580477548 (by decide +kernel)
private theorem contact01ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact01) 96 4 = 1319212943909 :=
  contactColumnsWindow_fast contact01 96 4 1319212943909 (by decide +kernel)
private theorem contact01ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact01) 100 4 = 1175404531149 :=
  contactColumnsWindow_fast contact01 100 4 1175404531149 (by decide +kernel)
private theorem contact01ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact01) 104 4 = 1040147764778 :=
  contactColumnsWindow_fast contact01 104 4 1040147764778 (by decide +kernel)
private theorem contact01ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact01) 108 4 = 913440936702 :=
  contactColumnsWindow_fast contact01 108 4 913440936702 (by decide +kernel)
private theorem contact01ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact01) 112 4 = 795293922820 :=
  contactColumnsWindow_fast contact01 112 4 795293922820 (by decide +kernel)
private theorem contact01ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact01) 116 4 = 685733742542 :=
  contactColumnsWindow_fast contact01 116 4 685733742542 (by decide +kernel)
private theorem contact01ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact01) 120 4 = 584730540747 :=
  contactColumnsWindow_fast contact01 120 4 584730540747 (by decide +kernel)
private theorem contact01ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact01) 124 4 = 492278815190 :=
  contactColumnsWindow_fast contact01 124 4 492278815190 (by decide +kernel)
private theorem contact01ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact01) 128 4 = 408376903531 :=
  contactColumnsWindow_fast contact01 128 4 408376903531 (by decide +kernel)
private theorem contact01ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact01) 132 4 = 333038372908 :=
  contactColumnsWindow_fast contact01 132 4 333038372908 (by decide +kernel)
private theorem contact01ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact01) 136 4 = 266284503002 :=
  contactColumnsWindow_fast contact01 136 4 266284503002 (by decide +kernel)
private theorem contact01ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact01) 140 4 = 208084956283 :=
  contactColumnsWindow_fast contact01 140 4 208084956283 (by decide +kernel)
private theorem contact01ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact01) 144 4 = 158378679237 :=
  contactColumnsWindow_fast contact01 144 4 158378679237 (by decide +kernel)
private theorem contact01ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact01) 148 4 = 116922757909 :=
  contactColumnsWindow_fast contact01 148 4 116922757909 (by decide +kernel)
private theorem contact01ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact01) 152 4 = 83312370385 :=
  contactColumnsWindow_fast contact01 152 4 83312370385 (by decide +kernel)
private theorem contact01ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact01) 156 4 = 56978055919 :=
  contactColumnsWindow_fast contact01 156 4 56978055919 (by decide +kernel)
private theorem contact01ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact01) 160 4 = 37145496062 :=
  contactColumnsWindow_fast contact01 160 4 37145496062 (by decide +kernel)
private theorem contact01ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact01) 164 1 = 6865037672 :=
  contactColumnsWindow_fast contact01 164 1 6865037672 (by decide +kernel)
private theorem contact01ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact01) 0 8 = 14328744004336 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 4 4 7338988038648 6989755965688 contact01ColumnsSlice0 contact01ColumnsSlice4
private theorem contact01ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact01) 8 8 = 12965990714072 :=
  combineSlices (auxiliaryColumnSlice contact01) 8 4 4 6649067586988 6316923127084 contact01ColumnsSlice8 contact01ColumnsSlice12
private theorem contact01ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact01) 16 8 = 11671702584239 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 4 4 5993354512684 5678348071555 contact01ColumnsSlice16 contact01ColumnsSlice20
private theorem contact01ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact01) 24 8 = 10445864550611 :=
  combineSlices (auxiliaryColumnSlice contact01) 24 4 4 5371888886115 5073975664496 contact01ColumnsSlice24 contact01ColumnsSlice28
private theorem contact01ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact01) 32 8 = 9288438552098 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 4 4 4784611343068 4503827209030 contact01ColumnsSlice32 contact01ColumnsSlice36
private theorem contact01ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact01) 40 8 = 8199540954235 :=
  combineSlices (auxiliaryColumnSlice contact01) 40 4 4 4231606350034 3967934604201 contact01ColumnsSlice40 contact01ColumnsSlice44
private theorem contact01ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact01) 48 8 = 7179057307997 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 4 4 3712813233556 3466244074441 contact01ColumnsSlice48 contact01ColumnsSlice52
private theorem contact01ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact01) 56 8 = 6227104255953 :=
  combineSlices (auxiliaryColumnSlice contact01) 56 4 4 3228261792323 2998842463630 contact01ColumnsSlice56 contact01ColumnsSlice60
private theorem contact01ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact01) 64 8 = 5343634752403 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 4 4 2777975627103 2565659125300 contact01ColumnsSlice64 contact01ColumnsSlice68
private theorem contact01ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact01) 72 8 = 4528619532093 :=
  combineSlices (auxiliaryColumnSlice contact01) 72 4 4 2361897148444 2166722383649 contact01ColumnsSlice72 contact01ColumnsSlice76
private theorem contact01ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact01) 80 8 = 3782155137960 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 4 4 1980108500410 1802046637550 contact01ColumnsSlice80 contact01ColumnsSlice84
private theorem contact01ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact01) 88 8 = 3104115544630 :=
  combineSlices (auxiliaryColumnSlice contact01) 88 4 4 1632535067082 1471580477548 contact01ColumnsSlice88 contact01ColumnsSlice92
private theorem contact01ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact01) 96 8 = 2494617475058 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 4 4 1319212943909 1175404531149 contact01ColumnsSlice96 contact01ColumnsSlice100
private theorem contact01ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact01) 104 8 = 1953588701480 :=
  combineSlices (auxiliaryColumnSlice contact01) 104 4 4 1040147764778 913440936702 contact01ColumnsSlice104 contact01ColumnsSlice108
private theorem contact01ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact01) 112 8 = 1481027665362 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 4 4 795293922820 685733742542 contact01ColumnsSlice112 contact01ColumnsSlice116
private theorem contact01ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact01) 120 8 = 1077009355937 :=
  combineSlices (auxiliaryColumnSlice contact01) 120 4 4 584730540747 492278815190 contact01ColumnsSlice120 contact01ColumnsSlice124
private theorem contact01ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact01) 128 8 = 741415276439 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 4 4 408376903531 333038372908 contact01ColumnsSlice128 contact01ColumnsSlice132
private theorem contact01ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact01) 136 8 = 474369459285 :=
  combineSlices (auxiliaryColumnSlice contact01) 136 4 4 266284503002 208084956283 contact01ColumnsSlice136 contact01ColumnsSlice140
private theorem contact01ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact01) 144 8 = 275301437146 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 4 4 158378679237 116922757909 contact01ColumnsSlice144 contact01ColumnsSlice148
private theorem contact01ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact01) 152 8 = 140290426304 :=
  combineSlices (auxiliaryColumnSlice contact01) 152 4 4 83312370385 56978055919 contact01ColumnsSlice152 contact01ColumnsSlice156
private theorem contact01ColumnsJoin160_5 : sliceWindow (auxiliaryColumnSlice contact01) 160 5 = 44010533734 :=
  combineSlices (auxiliaryColumnSlice contact01) 160 4 1 37145496062 6865037672 contact01ColumnsSlice160 contact01ColumnsSlice164
private theorem contact01ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact01) 0 16 = 27294734718408 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 8 8 14328744004336 12965990714072 contact01ColumnsJoin0_8 contact01ColumnsJoin8_8
private theorem contact01ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact01) 16 16 = 22117567134850 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 8 8 11671702584239 10445864550611 contact01ColumnsJoin16_8 contact01ColumnsJoin24_8
private theorem contact01ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact01) 32 16 = 17487979506333 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 8 8 9288438552098 8199540954235 contact01ColumnsJoin32_8 contact01ColumnsJoin40_8
private theorem contact01ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact01) 48 16 = 13406161563950 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 8 8 7179057307997 6227104255953 contact01ColumnsJoin48_8 contact01ColumnsJoin56_8
private theorem contact01ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact01) 64 16 = 9872254284496 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 8 8 5343634752403 4528619532093 contact01ColumnsJoin64_8 contact01ColumnsJoin72_8
private theorem contact01ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact01) 80 16 = 6886270682590 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 8 8 3782155137960 3104115544630 contact01ColumnsJoin80_8 contact01ColumnsJoin88_8
private theorem contact01ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact01) 96 16 = 4448206176538 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 8 8 2494617475058 1953588701480 contact01ColumnsJoin96_8 contact01ColumnsJoin104_8
private theorem contact01ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact01) 112 16 = 2558037021299 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 8 8 1481027665362 1077009355937 contact01ColumnsJoin112_8 contact01ColumnsJoin120_8
private theorem contact01ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact01) 128 16 = 1215784735724 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 8 8 741415276439 474369459285 contact01ColumnsJoin128_8 contact01ColumnsJoin136_8
private theorem contact01ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact01) 144 16 = 415591863450 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 8 8 275301437146 140290426304 contact01ColumnsJoin144_8 contact01ColumnsJoin152_8
private theorem contact01ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact01) 0 32 = 49412301853258 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 16 16 27294734718408 22117567134850 contact01ColumnsJoin0_16 contact01ColumnsJoin16_16
private theorem contact01ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact01) 32 32 = 30894141070283 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 16 16 17487979506333 13406161563950 contact01ColumnsJoin32_16 contact01ColumnsJoin48_16
private theorem contact01ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact01) 64 32 = 16758524967086 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 16 16 9872254284496 6886270682590 contact01ColumnsJoin64_16 contact01ColumnsJoin80_16
private theorem contact01ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact01) 96 32 = 7006243197837 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 16 16 4448206176538 2558037021299 contact01ColumnsJoin96_16 contact01ColumnsJoin112_16
private theorem contact01ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact01) 128 32 = 1631376599174 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 16 16 1215784735724 415591863450 contact01ColumnsJoin128_16 contact01ColumnsJoin144_16
private theorem contact01ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact01) 0 64 = 80306442923541 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 32 32 49412301853258 30894141070283 contact01ColumnsJoin0_32 contact01ColumnsJoin32_32
private theorem contact01ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact01) 64 64 = 23764768164923 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 32 32 16758524967086 7006243197837 contact01ColumnsJoin64_32 contact01ColumnsJoin96_32
private theorem contact01ColumnsJoin128_37 : sliceWindow (auxiliaryColumnSlice contact01) 128 37 = 1675387132908 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 32 5 1631376599174 44010533734 contact01ColumnsJoin128_32 contact01ColumnsJoin160_5
private theorem contact01ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact01) 0 128 = 104071211088464 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 64 64 80306442923541 23764768164923 contact01ColumnsJoin0_64 contact01ColumnsJoin64_64
private theorem contact01ColumnsJoin0_165 : sliceWindow (auxiliaryColumnSlice contact01) 0 165 = 105746598221372 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 128 37 104071211088464 1675387132908 contact01ColumnsJoin0_128 contact01ColumnsJoin128_37
private theorem contact01OrdinaryRanks : ordinaryRankBound contact01 = 9360836325 := by decide +kernel
private theorem contact01RanksSlice0 : sliceWindow (auxiliaryRankSlice contact01) 0 4 = 27670216 :=
  contactRankWindow_of_rec contact01 0 4 27670216 (by decide +kernel)
private theorem contact01RanksSlice4 : sliceWindow (auxiliaryRankSlice contact01) 4 4 = 25947880 :=
  contactRankWindow_of_rec contact01 4 4 25947880 (by decide +kernel)
private theorem contact01RanksSlice8 : sliceWindow (auxiliaryRankSlice contact01) 8 4 = 24284680 :=
  contactRankWindow_of_rec contact01 8 4 24284680 (by decide +kernel)
private theorem contact01RanksSlice12 : sliceWindow (auxiliaryRankSlice contact01) 12 4 = 22680616 :=
  contactRankWindow_of_rec contact01 12 4 22680616 (by decide +kernel)
private theorem contact01RanksSlice16 : sliceWindow (auxiliaryRankSlice contact01) 16 4 = 21135688 :=
  contactRankWindow_of_rec contact01 16 4 21135688 (by decide +kernel)
private theorem contact01RanksSlice20 : sliceWindow (auxiliaryRankSlice contact01) 20 4 = 19649896 :=
  contactRankWindow_of_rec contact01 20 4 19649896 (by decide +kernel)
private theorem contact01RanksSlice24 : sliceWindow (auxiliaryRankSlice contact01) 24 4 = 18223240 :=
  contactRankWindow_of_rec contact01 24 4 18223240 (by decide +kernel)
private theorem contact01RanksSlice28 : sliceWindow (auxiliaryRankSlice contact01) 28 4 = 16855720 :=
  contactRankWindow_of_rec contact01 28 4 16855720 (by decide +kernel)
private theorem contact01RanksSlice32 : sliceWindow (auxiliaryRankSlice contact01) 32 4 = 15547336 :=
  contactRankWindow_of_rec contact01 32 4 15547336 (by decide +kernel)
private theorem contact01RanksSlice36 : sliceWindow (auxiliaryRankSlice contact01) 36 4 = 14298088 :=
  contactRankWindow_of_rec contact01 36 4 14298088 (by decide +kernel)
private theorem contact01RanksSlice40 : sliceWindow (auxiliaryRankSlice contact01) 40 4 = 13107976 :=
  contactRankWindow_of_rec contact01 40 4 13107976 (by decide +kernel)
private theorem contact01RanksSlice44 : sliceWindow (auxiliaryRankSlice contact01) 44 4 = 11977000 :=
  contactRankWindow_of_rec contact01 44 4 11977000 (by decide +kernel)
private theorem contact01RanksSlice48 : sliceWindow (auxiliaryRankSlice contact01) 48 4 = 10905160 :=
  contactRankWindow_of_rec contact01 48 4 10905160 (by decide +kernel)
private theorem contact01RanksSlice52 : sliceWindow (auxiliaryRankSlice contact01) 52 4 = 9892456 :=
  contactRankWindow_of_rec contact01 52 4 9892456 (by decide +kernel)
private theorem contact01RanksSlice56 : sliceWindow (auxiliaryRankSlice contact01) 56 4 = 8938888 :=
  contactRankWindow_of_rec contact01 56 4 8938888 (by decide +kernel)
private theorem contact01RanksSlice60 : sliceWindow (auxiliaryRankSlice contact01) 60 4 = 8044062 :=
  contactRankWindow_of_rec contact01 60 4 8044062 (by decide +kernel)
private theorem contact01RanksSlice64 : sliceWindow (auxiliaryRankSlice contact01) 64 4 = 7206864 :=
  contactRankWindow_of_rec contact01 64 4 7206864 (by decide +kernel)
private theorem contact01RanksSlice68 : sliceWindow (auxiliaryRankSlice contact01) 68 4 = 6426007 :=
  contactRankWindow_of_rec contact01 68 4 6426007 (by decide +kernel)
private theorem contact01RanksSlice72 : sliceWindow (auxiliaryRankSlice contact01) 72 4 = 5699924 :=
  contactRankWindow_of_rec contact01 72 4 5699924 (by decide +kernel)
private theorem contact01RanksSlice76 : sliceWindow (auxiliaryRankSlice contact01) 76 4 = 5026868 :=
  contactRankWindow_of_rec contact01 76 4 5026868 (by decide +kernel)
private theorem contact01RanksSlice80 : sliceWindow (auxiliaryRankSlice contact01) 80 4 = 4405039 :=
  contactRankWindow_of_rec contact01 80 4 4405039 (by decide +kernel)
private theorem contact01RanksSlice84 : sliceWindow (auxiliaryRankSlice contact01) 84 4 = 3832868 :=
  contactRankWindow_of_rec contact01 84 4 3832868 (by decide +kernel)
private theorem contact01RanksSlice88 : sliceWindow (auxiliaryRankSlice contact01) 88 4 = 3308472 :=
  contactRankWindow_of_rec contact01 88 4 3308472 (by decide +kernel)
private theorem contact01RanksSlice92 : sliceWindow (auxiliaryRankSlice contact01) 92 4 = 2830055 :=
  contactRankWindow_of_rec contact01 92 4 2830055 (by decide +kernel)
private theorem contact01RanksSlice96 : sliceWindow (auxiliaryRankSlice contact01) 96 4 = 2396180 :=
  contactRankWindow_of_rec contact01 96 4 2396180 (by decide +kernel)
private theorem contact01RanksSlice100 : sliceWindow (auxiliaryRankSlice contact01) 100 4 = 2004828 :=
  contactRankWindow_of_rec contact01 100 4 2004828 (by decide +kernel)
private theorem contact01RanksSlice104 : sliceWindow (auxiliaryRankSlice contact01) 104 4 = 1654207 :=
  contactRankWindow_of_rec contact01 104 4 1654207 (by decide +kernel)
private theorem contact01RanksSlice108 : sliceWindow (auxiliaryRankSlice contact01) 108 4 = 1343012 :=
  contactRankWindow_of_rec contact01 108 4 1343012 (by decide +kernel)
private theorem contact01RanksSlice112 : sliceWindow (auxiliaryRankSlice contact01) 112 4 = 1069088 :=
  contactRankWindow_of_rec contact01 112 4 1069088 (by decide +kernel)
private theorem contact01RanksSlice116 : sliceWindow (auxiliaryRankSlice contact01) 116 4 = 830647 :=
  contactRankWindow_of_rec contact01 116 4 830647 (by decide +kernel)
private theorem contact01RanksSlice120 : sliceWindow (auxiliaryRankSlice contact01) 120 4 = 626516 :=
  contactRankWindow_of_rec contact01 120 4 626516 (by decide +kernel)
private theorem contact01RanksSlice124 : sliceWindow (auxiliaryRankSlice contact01) 124 4 = 454404 :=
  contactRankWindow_of_rec contact01 124 4 454404 (by decide +kernel)
private theorem contact01RanksSlice128 : sliceWindow (auxiliaryRankSlice contact01) 128 4 = 312527 :=
  contactRankWindow_of_rec contact01 128 4 312527 (by decide +kernel)
private theorem contact01RanksSlice132 : sliceWindow (auxiliaryRankSlice contact01) 132 4 = 199844 :=
  contactRankWindow_of_rec contact01 132 4 199844 (by decide +kernel)
private theorem contact01RanksSlice136 : sliceWindow (auxiliaryRankSlice contact01) 136 4 = 113928 :=
  contactRankWindow_of_rec contact01 136 4 113928 (by decide +kernel)
private theorem contact01RanksSlice140 : sliceWindow (auxiliaryRankSlice contact01) 140 4 = 52999 :=
  contactRankWindow_of_rec contact01 140 4 52999 (by decide +kernel)
private theorem contact01RanksSlice144 : sliceWindow (auxiliaryRankSlice contact01) 144 4 = 16157 :=
  contactRankWindow_of_rec contact01 144 4 16157 (by decide +kernel)
private theorem contact01RanksSlice148 : sliceWindow (auxiliaryRankSlice contact01) 148 4 = 914 :=
  contactRankWindow_of_rec contact01 148 4 914 (by decide +kernel)
private theorem contact01RanksSlice152 : sliceWindow (auxiliaryRankSlice contact01) 152 13 = 0 :=
  contactRankWindow_of_rec contact01 152 13 0 (by decide +kernel)
private theorem contact01RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact01) 0 8 = 53618096 :=
  combineSlices (auxiliaryRankSlice contact01) 0 4 4 27670216 25947880 contact01RanksSlice0 contact01RanksSlice4
private theorem contact01RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact01) 8 8 = 46965296 :=
  combineSlices (auxiliaryRankSlice contact01) 8 4 4 24284680 22680616 contact01RanksSlice8 contact01RanksSlice12
private theorem contact01RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact01) 16 8 = 40785584 :=
  combineSlices (auxiliaryRankSlice contact01) 16 4 4 21135688 19649896 contact01RanksSlice16 contact01RanksSlice20
private theorem contact01RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact01) 24 8 = 35078960 :=
  combineSlices (auxiliaryRankSlice contact01) 24 4 4 18223240 16855720 contact01RanksSlice24 contact01RanksSlice28
private theorem contact01RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact01) 32 8 = 29845424 :=
  combineSlices (auxiliaryRankSlice contact01) 32 4 4 15547336 14298088 contact01RanksSlice32 contact01RanksSlice36
private theorem contact01RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact01) 40 8 = 25084976 :=
  combineSlices (auxiliaryRankSlice contact01) 40 4 4 13107976 11977000 contact01RanksSlice40 contact01RanksSlice44
private theorem contact01RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact01) 48 8 = 20797616 :=
  combineSlices (auxiliaryRankSlice contact01) 48 4 4 10905160 9892456 contact01RanksSlice48 contact01RanksSlice52
private theorem contact01RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact01) 56 8 = 16982950 :=
  combineSlices (auxiliaryRankSlice contact01) 56 4 4 8938888 8044062 contact01RanksSlice56 contact01RanksSlice60
private theorem contact01RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact01) 64 8 = 13632871 :=
  combineSlices (auxiliaryRankSlice contact01) 64 4 4 7206864 6426007 contact01RanksSlice64 contact01RanksSlice68
private theorem contact01RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact01) 72 8 = 10726792 :=
  combineSlices (auxiliaryRankSlice contact01) 72 4 4 5699924 5026868 contact01RanksSlice72 contact01RanksSlice76
private theorem contact01RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact01) 80 8 = 8237907 :=
  combineSlices (auxiliaryRankSlice contact01) 80 4 4 4405039 3832868 contact01RanksSlice80 contact01RanksSlice84
private theorem contact01RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact01) 88 8 = 6138527 :=
  combineSlices (auxiliaryRankSlice contact01) 88 4 4 3308472 2830055 contact01RanksSlice88 contact01RanksSlice92
private theorem contact01RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact01) 96 8 = 4401008 :=
  combineSlices (auxiliaryRankSlice contact01) 96 4 4 2396180 2004828 contact01RanksSlice96 contact01RanksSlice100
private theorem contact01RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact01) 104 8 = 2997219 :=
  combineSlices (auxiliaryRankSlice contact01) 104 4 4 1654207 1343012 contact01RanksSlice104 contact01RanksSlice108
private theorem contact01RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact01) 112 8 = 1899735 :=
  combineSlices (auxiliaryRankSlice contact01) 112 4 4 1069088 830647 contact01RanksSlice112 contact01RanksSlice116
private theorem contact01RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact01) 120 8 = 1080920 :=
  combineSlices (auxiliaryRankSlice contact01) 120 4 4 626516 454404 contact01RanksSlice120 contact01RanksSlice124
private theorem contact01RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact01) 128 8 = 512371 :=
  combineSlices (auxiliaryRankSlice contact01) 128 4 4 312527 199844 contact01RanksSlice128 contact01RanksSlice132
private theorem contact01RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact01) 136 8 = 166927 :=
  combineSlices (auxiliaryRankSlice contact01) 136 4 4 113928 52999 contact01RanksSlice136 contact01RanksSlice140
private theorem contact01RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact01) 144 8 = 17071 :=
  combineSlices (auxiliaryRankSlice contact01) 144 4 4 16157 914 contact01RanksSlice144 contact01RanksSlice148
private theorem contact01RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact01) 0 16 = 100583392 :=
  combineSlices (auxiliaryRankSlice contact01) 0 8 8 53618096 46965296 contact01RanksJoin0_8 contact01RanksJoin8_8
private theorem contact01RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact01) 16 16 = 75864544 :=
  combineSlices (auxiliaryRankSlice contact01) 16 8 8 40785584 35078960 contact01RanksJoin16_8 contact01RanksJoin24_8
private theorem contact01RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact01) 32 16 = 54930400 :=
  combineSlices (auxiliaryRankSlice contact01) 32 8 8 29845424 25084976 contact01RanksJoin32_8 contact01RanksJoin40_8
private theorem contact01RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact01) 48 16 = 37780566 :=
  combineSlices (auxiliaryRankSlice contact01) 48 8 8 20797616 16982950 contact01RanksJoin48_8 contact01RanksJoin56_8
private theorem contact01RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact01) 64 16 = 24359663 :=
  combineSlices (auxiliaryRankSlice contact01) 64 8 8 13632871 10726792 contact01RanksJoin64_8 contact01RanksJoin72_8
private theorem contact01RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact01) 80 16 = 14376434 :=
  combineSlices (auxiliaryRankSlice contact01) 80 8 8 8237907 6138527 contact01RanksJoin80_8 contact01RanksJoin88_8
private theorem contact01RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact01) 96 16 = 7398227 :=
  combineSlices (auxiliaryRankSlice contact01) 96 8 8 4401008 2997219 contact01RanksJoin96_8 contact01RanksJoin104_8
private theorem contact01RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact01) 112 16 = 2980655 :=
  combineSlices (auxiliaryRankSlice contact01) 112 8 8 1899735 1080920 contact01RanksJoin112_8 contact01RanksJoin120_8
private theorem contact01RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact01) 128 16 = 679298 :=
  combineSlices (auxiliaryRankSlice contact01) 128 8 8 512371 166927 contact01RanksJoin128_8 contact01RanksJoin136_8
private theorem contact01RanksJoin144_21 : sliceWindow (auxiliaryRankSlice contact01) 144 21 = 17071 :=
  combineSlices (auxiliaryRankSlice contact01) 144 8 13 17071 0 contact01RanksJoin144_8 contact01RanksSlice152
private theorem contact01RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact01) 0 32 = 176447936 :=
  combineSlices (auxiliaryRankSlice contact01) 0 16 16 100583392 75864544 contact01RanksJoin0_16 contact01RanksJoin16_16
private theorem contact01RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact01) 32 32 = 92710966 :=
  combineSlices (auxiliaryRankSlice contact01) 32 16 16 54930400 37780566 contact01RanksJoin32_16 contact01RanksJoin48_16
private theorem contact01RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact01) 64 32 = 38736097 :=
  combineSlices (auxiliaryRankSlice contact01) 64 16 16 24359663 14376434 contact01RanksJoin64_16 contact01RanksJoin80_16
private theorem contact01RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact01) 96 32 = 10378882 :=
  combineSlices (auxiliaryRankSlice contact01) 96 16 16 7398227 2980655 contact01RanksJoin96_16 contact01RanksJoin112_16
private theorem contact01RanksJoin128_37 : sliceWindow (auxiliaryRankSlice contact01) 128 37 = 696369 :=
  combineSlices (auxiliaryRankSlice contact01) 128 16 21 679298 17071 contact01RanksJoin128_16 contact01RanksJoin144_21
private theorem contact01RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact01) 0 64 = 269158902 :=
  combineSlices (auxiliaryRankSlice contact01) 0 32 32 176447936 92710966 contact01RanksJoin0_32 contact01RanksJoin32_32
private theorem contact01RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact01) 64 64 = 49114979 :=
  combineSlices (auxiliaryRankSlice contact01) 64 32 32 38736097 10378882 contact01RanksJoin64_32 contact01RanksJoin96_32
private theorem contact01RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact01) 0 128 = 318273881 :=
  combineSlices (auxiliaryRankSlice contact01) 0 64 64 269158902 49114979 contact01RanksJoin0_64 contact01RanksJoin64_64
private theorem contact01RanksJoin0_165 : sliceWindow (auxiliaryRankSlice contact01) 0 165 = 318970250 :=
  combineSlices (auxiliaryRankSlice contact01) 0 128 37 318273881 696369 contact01RanksJoin0_128 contact01RanksJoin128_37
theorem contact01_margin : sourceMargin contact01 :=
  margin_of_checked_counts contact01 165 2431757391734239 105746598221372 9360836325 318970250 rfl contact01OrdinaryColumns contact01ColumnsJoin0_165 contact01OrdinaryRanks contact01RanksJoin0_165 (by decide +kernel)

private theorem contact03OrdinaryColumns : ordinaryColumnCount contact03 = 2260574159127977 := by decide +kernel
private theorem contact03ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact03) 0 4 = 7519028710404 :=
  contactColumnsWindow_fast contact03 0 4 7519028710404 (by decide +kernel)
private theorem contact03ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact03) 4 4 = 7160274088868 :=
  contactColumnsWindow_fast contact03 4 4 7160274088868 (by decide +kernel)
private theorem contact03ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact03) 8 4 = 6810322038864 :=
  contactColumnsWindow_fast contact03 8 4 6810322038864 (by decide +kernel)
private theorem contact03ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact03) 12 4 = 6469172799608 :=
  contactColumnsWindow_fast contact03 12 4 6469172799608 (by decide +kernel)
private theorem contact03ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact03) 16 4 = 6136859605488 :=
  contactColumnsWindow_fast contact03 16 4 6136859605488 (by decide +kernel)
private theorem contact03ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact03) 20 4 = 5813368199133 :=
  contactColumnsWindow_fast contact03 20 4 5813368199133 (by decide +kernel)
private theorem contact03ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact03) 24 4 = 5498682998998 :=
  contactColumnsWindow_fast contact03 24 4 5498682998998 (by decide +kernel)
private theorem contact03ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact03) 28 4 = 5192802685824 :=
  contactColumnsWindow_fast contact03 28 4 5192802685824 (by decide +kernel)
private theorem contact03ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact03) 32 4 = 4895730285476 :=
  contactColumnsWindow_fast contact03 32 4 4895730285476 (by decide +kernel)
private theorem contact03ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact03) 36 4 = 4607498407134 :=
  contactColumnsWindow_fast contact03 36 4 4607498407134 (by decide +kernel)
private theorem contact03ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact03) 40 4 = 4328089359876 :=
  contactColumnsWindow_fast contact03 40 4 4328089359876 (by decide +kernel)
private theorem contact03ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact03) 44 4 = 4057488408571 :=
  contactColumnsWindow_fast contact03 44 4 4057488408571 (by decide +kernel)
private theorem contact03ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact03) 48 4 = 3795696834906 :=
  contactColumnsWindow_fast contact03 48 4 3795696834906 (by decide +kernel)
private theorem contact03ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact03) 52 4 = 3542716569635 :=
  contactColumnsWindow_fast contact03 52 4 3542716569635 (by decide +kernel)
private theorem contact03ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact03) 56 4 = 3298583688805 :=
  contactColumnsWindow_fast contact03 56 4 3298583688805 (by decide +kernel)
private theorem contact03ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact03) 60 4 = 3063273226626 :=
  contactColumnsWindow_fast contact03 60 4 3063273226626 (by decide +kernel)
private theorem contact03ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact03) 64 4 = 2836774294201 :=
  contactColumnsWindow_fast contact03 64 4 2836774294201 (by decide +kernel)
private theorem contact03ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact03) 68 4 = 2619084698952 :=
  contactColumnsWindow_fast contact03 68 4 2619084698952 (by decide +kernel)
private theorem contact03ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact03) 72 4 = 2410208814676 :=
  contactColumnsWindow_fast contact03 72 4 2410208814676 (by decide +kernel)
private theorem contact03ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact03) 76 4 = 2210180668843 :=
  contactColumnsWindow_fast contact03 76 4 2210180668843 (by decide +kernel)
private theorem contact03ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact03) 80 4 = 2018972771808 :=
  contactColumnsWindow_fast contact03 80 4 2018972771808 (by decide +kernel)
private theorem contact03ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact03) 84 4 = 1836575923898 :=
  contactColumnsWindow_fast contact03 84 4 1836575923898 (by decide +kernel)
private theorem contact03ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact03) 88 4 = 1662988370697 :=
  contactColumnsWindow_fast contact03 88 4 1662988370697 (by decide +kernel)
private theorem contact03ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact03) 92 4 = 1498217082064 :=
  contactColumnsWindow_fast contact03 92 4 1498217082064 (by decide +kernel)
private theorem contact03ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact03) 96 4 = 1342293373795 :=
  contactColumnsWindow_fast contact03 96 4 1342293373795 (by decide +kernel)
private theorem contact03ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact03) 100 4 = 1195188067587 :=
  contactColumnsWindow_fast contact03 100 4 1195188067587 (by decide +kernel)
private theorem contact03ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact03) 104 4 = 1056893429408 :=
  contactColumnsWindow_fast contact03 104 4 1056893429408 (by decide +kernel)
private theorem contact03ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact03) 108 4 = 927407725644 :=
  contactColumnsWindow_fast contact03 108 4 927407725644 (by decide +kernel)
private theorem contact03ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact03) 112 4 = 806741228208 :=
  contactColumnsWindow_fast contact03 112 4 806741228208 (by decide +kernel)
private theorem contact03ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact03) 116 4 = 694922078451 :=
  contactColumnsWindow_fast contact03 116 4 694922078451 (by decide +kernel)
private theorem contact03ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact03) 120 4 = 591919098612 :=
  contactColumnsWindow_fast contact03 120 4 591919098612 (by decide +kernel)
private theorem contact03ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact03) 124 4 = 497726613350 :=
  contactColumnsWindow_fast contact03 124 4 497726613350 (by decide +kernel)
private theorem contact03ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact03) 128 4 = 412342936077 :=
  contactColumnsWindow_fast contact03 128 4 412342936077 (by decide +kernel)
private theorem contact03ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact03) 132 4 = 335782177656 :=
  contactColumnsWindow_fast contact03 132 4 335782177656 (by decide +kernel)
private theorem contact03ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact03) 136 4 = 268066500954 :=
  contactColumnsWindow_fast contact03 136 4 268066500954 (by decide +kernel)
private theorem contact03ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact03) 140 4 = 209160810113 :=
  contactColumnsWindow_fast contact03 140 4 209160810113 (by decide +kernel)
private theorem contact03ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact03) 144 4 = 158969310947 :=
  contactColumnsWindow_fast contact03 144 4 158969310947 (by decide +kernel)
private theorem contact03ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact03) 148 4 = 117201249758 :=
  contactColumnsWindow_fast contact03 148 4 117201249758 (by decide +kernel)
private theorem contact03ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact03) 152 4 = 83414626076 :=
  contactColumnsWindow_fast contact03 152 4 83414626076 (by decide +kernel)
private theorem contact03ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact03) 156 4 = 57001189274 :=
  contactColumnsWindow_fast contact03 156 4 57001189274 (by decide +kernel)
private theorem contact03ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact03) 160 4 = 37146906877 :=
  contactColumnsWindow_fast contact03 160 4 37146906877 (by decide +kernel)
private theorem contact03ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact03) 0 8 = 14679302799272 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 4 4 7519028710404 7160274088868 contact03ColumnsSlice0 contact03ColumnsSlice4
private theorem contact03ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact03) 8 8 = 13279494838472 :=
  combineSlices (auxiliaryColumnSlice contact03) 8 4 4 6810322038864 6469172799608 contact03ColumnsSlice8 contact03ColumnsSlice12
private theorem contact03ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact03) 16 8 = 11950227804621 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 4 4 6136859605488 5813368199133 contact03ColumnsSlice16 contact03ColumnsSlice20
private theorem contact03ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact03) 24 8 = 10691485684822 :=
  combineSlices (auxiliaryColumnSlice contact03) 24 4 4 5498682998998 5192802685824 contact03ColumnsSlice24 contact03ColumnsSlice28
private theorem contact03ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact03) 32 8 = 9503228692610 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 4 4 4895730285476 4607498407134 contact03ColumnsSlice32 contact03ColumnsSlice36
private theorem contact03ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact03) 40 8 = 8385577768447 :=
  combineSlices (auxiliaryColumnSlice contact03) 40 4 4 4328089359876 4057488408571 contact03ColumnsSlice40 contact03ColumnsSlice44
private theorem contact03ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact03) 48 8 = 7338413404541 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 4 4 3795696834906 3542716569635 contact03ColumnsSlice48 contact03ColumnsSlice52
private theorem contact03ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact03) 56 8 = 6361856915431 :=
  combineSlices (auxiliaryColumnSlice contact03) 56 4 4 3298583688805 3063273226626 contact03ColumnsSlice56 contact03ColumnsSlice60
private theorem contact03ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact03) 64 8 = 5455858993153 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 4 4 2836774294201 2619084698952 contact03ColumnsSlice64 contact03ColumnsSlice68
private theorem contact03ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact03) 72 8 = 4620389483519 :=
  combineSlices (auxiliaryColumnSlice contact03) 72 4 4 2410208814676 2210180668843 contact03ColumnsSlice72 contact03ColumnsSlice76
private theorem contact03ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact03) 80 8 = 3855548695706 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 4 4 2018972771808 1836575923898 contact03ColumnsSlice80 contact03ColumnsSlice84
private theorem contact03ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact03) 88 8 = 3161205452761 :=
  combineSlices (auxiliaryColumnSlice contact03) 88 4 4 1662988370697 1498217082064 contact03ColumnsSlice88 contact03ColumnsSlice92
private theorem contact03ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact03) 96 8 = 2537481441382 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 4 4 1342293373795 1195188067587 contact03ColumnsSlice96 contact03ColumnsSlice100
private theorem contact03ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact03) 104 8 = 1984301155052 :=
  combineSlices (auxiliaryColumnSlice contact03) 104 4 4 1056893429408 927407725644 contact03ColumnsSlice104 contact03ColumnsSlice108
private theorem contact03ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact03) 112 8 = 1501663306659 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 4 4 806741228208 694922078451 contact03ColumnsSlice112 contact03ColumnsSlice116
private theorem contact03ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact03) 120 8 = 1089645711962 :=
  combineSlices (auxiliaryColumnSlice contact03) 120 4 4 591919098612 497726613350 contact03ColumnsSlice120 contact03ColumnsSlice124
private theorem contact03ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact03) 128 8 = 748125113733 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 4 4 412342936077 335782177656 contact03ColumnsSlice128 contact03ColumnsSlice132
private theorem contact03ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact03) 136 8 = 477227311067 :=
  combineSlices (auxiliaryColumnSlice contact03) 136 4 4 268066500954 209160810113 contact03ColumnsSlice136 contact03ColumnsSlice140
private theorem contact03ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact03) 144 8 = 276170560705 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 4 4 158969310947 117201249758 contact03ColumnsSlice144 contact03ColumnsSlice148
private theorem contact03ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact03) 152 8 = 140415815350 :=
  combineSlices (auxiliaryColumnSlice contact03) 152 4 4 83414626076 57001189274 contact03ColumnsSlice152 contact03ColumnsSlice156
private theorem contact03ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact03) 0 16 = 27958797637744 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 8 8 14679302799272 13279494838472 contact03ColumnsJoin0_8 contact03ColumnsJoin8_8
private theorem contact03ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact03) 16 16 = 22641713489443 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 8 8 11950227804621 10691485684822 contact03ColumnsJoin16_8 contact03ColumnsJoin24_8
private theorem contact03ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact03) 32 16 = 17888806461057 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 8 8 9503228692610 8385577768447 contact03ColumnsJoin32_8 contact03ColumnsJoin40_8
private theorem contact03ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact03) 48 16 = 13700270319972 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 8 8 7338413404541 6361856915431 contact03ColumnsJoin48_8 contact03ColumnsJoin56_8
private theorem contact03ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact03) 64 16 = 10076248476672 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 8 8 5455858993153 4620389483519 contact03ColumnsJoin64_8 contact03ColumnsJoin72_8
private theorem contact03ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact03) 80 16 = 7016754148467 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 8 8 3855548695706 3161205452761 contact03ColumnsJoin80_8 contact03ColumnsJoin88_8
private theorem contact03ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact03) 96 16 = 4521782596434 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 8 8 2537481441382 1984301155052 contact03ColumnsJoin96_8 contact03ColumnsJoin104_8
private theorem contact03ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact03) 112 16 = 2591309018621 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 8 8 1501663306659 1089645711962 contact03ColumnsJoin112_8 contact03ColumnsJoin120_8
private theorem contact03ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact03) 128 16 = 1225352424800 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 8 8 748125113733 477227311067 contact03ColumnsJoin128_8 contact03ColumnsJoin136_8
private theorem contact03ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact03) 144 16 = 416586376055 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 8 8 276170560705 140415815350 contact03ColumnsJoin144_8 contact03ColumnsJoin152_8
private theorem contact03ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact03) 0 32 = 50600511127187 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 16 16 27958797637744 22641713489443 contact03ColumnsJoin0_16 contact03ColumnsJoin16_16
private theorem contact03ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact03) 32 32 = 31589076781029 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 16 16 17888806461057 13700270319972 contact03ColumnsJoin32_16 contact03ColumnsJoin48_16
private theorem contact03ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact03) 64 32 = 17093002625139 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 16 16 10076248476672 7016754148467 contact03ColumnsJoin64_16 contact03ColumnsJoin80_16
private theorem contact03ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact03) 96 32 = 7113091615055 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 16 16 4521782596434 2591309018621 contact03ColumnsJoin96_16 contact03ColumnsJoin112_16
private theorem contact03ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact03) 128 32 = 1641938800855 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 16 16 1225352424800 416586376055 contact03ColumnsJoin128_16 contact03ColumnsJoin144_16
private theorem contact03ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact03) 0 64 = 82189587908216 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 32 32 50600511127187 31589076781029 contact03ColumnsJoin0_32 contact03ColumnsJoin32_32
private theorem contact03ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact03) 64 64 = 24206094240194 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 32 32 17093002625139 7113091615055 contact03ColumnsJoin64_32 contact03ColumnsJoin96_32
private theorem contact03ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact03) 128 36 = 1679085707732 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 32 4 1641938800855 37146906877 contact03ColumnsJoin128_32 contact03ColumnsSlice160
private theorem contact03ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact03) 0 128 = 106395682148410 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 64 64 82189587908216 24206094240194 contact03ColumnsJoin0_64 contact03ColumnsJoin64_64
private theorem contact03ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact03) 0 164 = 108074767856142 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 128 36 106395682148410 1679085707732 contact03ColumnsJoin0_128 contact03ColumnsJoin128_36
private theorem contact03OrdinaryRanks : ordinaryRankBound contact03 = 8709054079 := by decide +kernel
private theorem contact03RanksSlice0 : sliceWindow (auxiliaryRankSlice contact03) 0 4 = 28342844 :=
  contactRankWindow_of_rec contact03 0 4 28342844 (by decide +kernel)
private theorem contact03RanksSlice4 : sliceWindow (auxiliaryRankSlice contact03) 4 4 = 26575932 :=
  contactRankWindow_of_rec contact03 4 4 26575932 (by decide +kernel)
private theorem contact03RanksSlice8 : sliceWindow (auxiliaryRankSlice contact03) 8 4 = 24869948 :=
  contactRankWindow_of_rec contact03 8 4 24869948 (by decide +kernel)
private theorem contact03RanksSlice12 : sliceWindow (auxiliaryRankSlice contact03) 12 4 = 23224892 :=
  contactRankWindow_of_rec contact03 12 4 23224892 (by decide +kernel)
private theorem contact03RanksSlice16 : sliceWindow (auxiliaryRankSlice contact03) 16 4 = 21640764 :=
  contactRankWindow_of_rec contact03 16 4 21640764 (by decide +kernel)
private theorem contact03RanksSlice20 : sliceWindow (auxiliaryRankSlice contact03) 20 4 = 20117564 :=
  contactRankWindow_of_rec contact03 20 4 20117564 (by decide +kernel)
private theorem contact03RanksSlice24 : sliceWindow (auxiliaryRankSlice contact03) 24 4 = 18655292 :=
  contactRankWindow_of_rec contact03 24 4 18655292 (by decide +kernel)
private theorem contact03RanksSlice28 : sliceWindow (auxiliaryRankSlice contact03) 28 4 = 17253948 :=
  contactRankWindow_of_rec contact03 28 4 17253948 (by decide +kernel)
private theorem contact03RanksSlice32 : sliceWindow (auxiliaryRankSlice contact03) 32 4 = 15913532 :=
  contactRankWindow_of_rec contact03 32 4 15913532 (by decide +kernel)
private theorem contact03RanksSlice36 : sliceWindow (auxiliaryRankSlice contact03) 36 4 = 14634044 :=
  contactRankWindow_of_rec contact03 36 4 14634044 (by decide +kernel)
private theorem contact03RanksSlice40 : sliceWindow (auxiliaryRankSlice contact03) 40 4 = 13415484 :=
  contactRankWindow_of_rec contact03 40 4 13415484 (by decide +kernel)
private theorem contact03RanksSlice44 : sliceWindow (auxiliaryRankSlice contact03) 44 4 = 12257852 :=
  contactRankWindow_of_rec contact03 44 4 12257852 (by decide +kernel)
private theorem contact03RanksSlice48 : sliceWindow (auxiliaryRankSlice contact03) 48 4 = 11161148 :=
  contactRankWindow_of_rec contact03 48 4 11161148 (by decide +kernel)
private theorem contact03RanksSlice52 : sliceWindow (auxiliaryRankSlice contact03) 52 4 = 10125372 :=
  contactRankWindow_of_rec contact03 52 4 10125372 (by decide +kernel)
private theorem contact03RanksSlice56 : sliceWindow (auxiliaryRankSlice contact03) 56 4 = 9150440 :=
  contactRankWindow_of_rec contact03 56 4 9150440 (by decide +kernel)
private theorem contact03RanksSlice60 : sliceWindow (auxiliaryRankSlice contact03) 60 4 = 8235530 :=
  contactRankWindow_of_rec contact03 60 4 8235530 (by decide +kernel)
private theorem contact03RanksSlice64 : sliceWindow (auxiliaryRankSlice contact03) 64 4 = 7379404 :=
  contactRankWindow_of_rec contact03 64 4 7379404 (by decide +kernel)
private theorem contact03RanksSlice68 : sliceWindow (auxiliaryRankSlice contact03) 68 4 = 6580786 :=
  contactRankWindow_of_rec contact03 68 4 6580786 (by decide +kernel)
private theorem contact03RanksSlice72 : sliceWindow (auxiliaryRankSlice contact03) 72 4 = 5838084 :=
  contactRankWindow_of_rec contact03 72 4 5838084 (by decide +kernel)
private theorem contact03RanksSlice76 : sliceWindow (auxiliaryRankSlice contact03) 76 4 = 5149500 :=
  contactRankWindow_of_rec contact03 76 4 5149500 (by decide +kernel)
private theorem contact03RanksSlice80 : sliceWindow (auxiliaryRankSlice contact03) 80 4 = 4513226 :=
  contactRankWindow_of_rec contact03 80 4 4513226 (by decide +kernel)
private theorem contact03RanksSlice84 : sliceWindow (auxiliaryRankSlice contact03) 84 4 = 3927668 :=
  contactRankWindow_of_rec contact03 84 4 3927668 (by decide +kernel)
private theorem contact03RanksSlice88 : sliceWindow (auxiliaryRankSlice contact03) 88 4 = 3390892 :=
  contactRankWindow_of_rec contact03 88 4 3390892 (by decide +kernel)
private theorem contact03RanksSlice92 : sliceWindow (auxiliaryRankSlice contact03) 92 4 = 2901090 :=
  contactRankWindow_of_rec contact03 92 4 2901090 (by decide +kernel)
private theorem contact03RanksSlice96 : sliceWindow (auxiliaryRankSlice contact03) 96 4 = 2456804 :=
  contactRankWindow_of_rec contact03 96 4 2456804 (by decide +kernel)
private theorem contact03RanksSlice100 : sliceWindow (auxiliaryRankSlice contact03) 100 4 = 2055964 :=
  contactRankWindow_of_rec contact03 100 4 2055964 (by decide +kernel)
private theorem contact03RanksSlice104 : sliceWindow (auxiliaryRankSlice contact03) 104 4 = 1696762 :=
  contactRankWindow_of_rec contact03 104 4 1696762 (by decide +kernel)
private theorem contact03RanksSlice108 : sliceWindow (auxiliaryRankSlice contact03) 108 4 = 1377876 :=
  contactRankWindow_of_rec contact03 108 4 1377876 (by decide +kernel)
private theorem contact03RanksSlice112 : sliceWindow (auxiliaryRankSlice contact03) 112 4 = 1097100 :=
  contactRankWindow_of_rec contact03 112 4 1097100 (by decide +kernel)
private theorem contact03RanksSlice116 : sliceWindow (auxiliaryRankSlice contact03) 116 4 = 852626 :=
  contactRankWindow_of_rec contact03 116 4 852626 (by decide +kernel)
private theorem contact03RanksSlice120 : sliceWindow (auxiliaryRankSlice contact03) 120 4 = 643268 :=
  contactRankWindow_of_rec contact03 120 4 643268 (by decide +kernel)
private theorem contact03RanksSlice124 : sliceWindow (auxiliaryRankSlice contact03) 124 4 = 466684 :=
  contactRankWindow_of_rec contact03 124 4 466684 (by decide +kernel)
private theorem contact03RanksSlice128 : sliceWindow (auxiliaryRankSlice contact03) 128 4 = 321066 :=
  contactRankWindow_of_rec contact03 128 4 321066 (by decide +kernel)
private theorem contact03RanksSlice132 : sliceWindow (auxiliaryRankSlice contact03) 132 4 = 205364 :=
  contactRankWindow_of_rec contact03 132 4 205364 (by decide +kernel)
private theorem contact03RanksSlice136 : sliceWindow (auxiliaryRankSlice contact03) 136 4 = 117100 :=
  contactRankWindow_of_rec contact03 136 4 117100 (by decide +kernel)
private theorem contact03RanksSlice140 : sliceWindow (auxiliaryRankSlice contact03) 140 4 = 54466 :=
  contactRankWindow_of_rec contact03 140 4 54466 (by decide +kernel)
private theorem contact03RanksSlice144 : sliceWindow (auxiliaryRankSlice contact03) 144 4 = 16582 :=
  contactRankWindow_of_rec contact03 144 4 16582 (by decide +kernel)
private theorem contact03RanksSlice148 : sliceWindow (auxiliaryRankSlice contact03) 148 4 = 937 :=
  contactRankWindow_of_rec contact03 148 4 937 (by decide +kernel)
private theorem contact03RanksSlice152 : sliceWindow (auxiliaryRankSlice contact03) 152 12 = 0 :=
  contactRankWindow_of_rec contact03 152 12 0 (by decide +kernel)
private theorem contact03RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact03) 0 8 = 54918776 :=
  combineSlices (auxiliaryRankSlice contact03) 0 4 4 28342844 26575932 contact03RanksSlice0 contact03RanksSlice4
private theorem contact03RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact03) 8 8 = 48094840 :=
  combineSlices (auxiliaryRankSlice contact03) 8 4 4 24869948 23224892 contact03RanksSlice8 contact03RanksSlice12
private theorem contact03RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact03) 16 8 = 41758328 :=
  combineSlices (auxiliaryRankSlice contact03) 16 4 4 21640764 20117564 contact03RanksSlice16 contact03RanksSlice20
private theorem contact03RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact03) 24 8 = 35909240 :=
  combineSlices (auxiliaryRankSlice contact03) 24 4 4 18655292 17253948 contact03RanksSlice24 contact03RanksSlice28
private theorem contact03RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact03) 32 8 = 30547576 :=
  combineSlices (auxiliaryRankSlice contact03) 32 4 4 15913532 14634044 contact03RanksSlice32 contact03RanksSlice36
private theorem contact03RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact03) 40 8 = 25673336 :=
  combineSlices (auxiliaryRankSlice contact03) 40 4 4 13415484 12257852 contact03RanksSlice40 contact03RanksSlice44
private theorem contact03RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact03) 48 8 = 21286520 :=
  combineSlices (auxiliaryRankSlice contact03) 48 4 4 11161148 10125372 contact03RanksSlice48 contact03RanksSlice52
private theorem contact03RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact03) 56 8 = 17385970 :=
  combineSlices (auxiliaryRankSlice contact03) 56 4 4 9150440 8235530 contact03RanksSlice56 contact03RanksSlice60
private theorem contact03RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact03) 64 8 = 13960190 :=
  combineSlices (auxiliaryRankSlice contact03) 64 4 4 7379404 6580786 contact03RanksSlice64 contact03RanksSlice68
private theorem contact03RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact03) 72 8 = 10987584 :=
  combineSlices (auxiliaryRankSlice contact03) 72 4 4 5838084 5149500 contact03RanksSlice72 contact03RanksSlice76
private theorem contact03RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact03) 80 8 = 8440894 :=
  combineSlices (auxiliaryRankSlice contact03) 80 4 4 4513226 3927668 contact03RanksSlice80 contact03RanksSlice84
private theorem contact03RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact03) 88 8 = 6291982 :=
  combineSlices (auxiliaryRankSlice contact03) 88 4 4 3390892 2901090 contact03RanksSlice88 contact03RanksSlice92
private theorem contact03RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact03) 96 8 = 4512768 :=
  combineSlices (auxiliaryRankSlice contact03) 96 4 4 2456804 2055964 contact03RanksSlice96 contact03RanksSlice100
private theorem contact03RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact03) 104 8 = 3074638 :=
  combineSlices (auxiliaryRankSlice contact03) 104 4 4 1696762 1377876 contact03RanksSlice104 contact03RanksSlice108
private theorem contact03RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact03) 112 8 = 1949726 :=
  combineSlices (auxiliaryRankSlice contact03) 112 4 4 1097100 852626 contact03RanksSlice112 contact03RanksSlice116
private theorem contact03RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact03) 120 8 = 1109952 :=
  combineSlices (auxiliaryRankSlice contact03) 120 4 4 643268 466684 contact03RanksSlice120 contact03RanksSlice124
private theorem contact03RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact03) 128 8 = 526430 :=
  combineSlices (auxiliaryRankSlice contact03) 128 4 4 321066 205364 contact03RanksSlice128 contact03RanksSlice132
private theorem contact03RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact03) 136 8 = 171566 :=
  combineSlices (auxiliaryRankSlice contact03) 136 4 4 117100 54466 contact03RanksSlice136 contact03RanksSlice140
private theorem contact03RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact03) 144 8 = 17519 :=
  combineSlices (auxiliaryRankSlice contact03) 144 4 4 16582 937 contact03RanksSlice144 contact03RanksSlice148
private theorem contact03RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact03) 0 16 = 103013616 :=
  combineSlices (auxiliaryRankSlice contact03) 0 8 8 54918776 48094840 contact03RanksJoin0_8 contact03RanksJoin8_8
private theorem contact03RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact03) 16 16 = 77667568 :=
  combineSlices (auxiliaryRankSlice contact03) 16 8 8 41758328 35909240 contact03RanksJoin16_8 contact03RanksJoin24_8
private theorem contact03RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact03) 32 16 = 56220912 :=
  combineSlices (auxiliaryRankSlice contact03) 32 8 8 30547576 25673336 contact03RanksJoin32_8 contact03RanksJoin40_8
private theorem contact03RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact03) 48 16 = 38672490 :=
  combineSlices (auxiliaryRankSlice contact03) 48 8 8 21286520 17385970 contact03RanksJoin48_8 contact03RanksJoin56_8
private theorem contact03RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact03) 64 16 = 24947774 :=
  combineSlices (auxiliaryRankSlice contact03) 64 8 8 13960190 10987584 contact03RanksJoin64_8 contact03RanksJoin72_8
private theorem contact03RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact03) 80 16 = 14732876 :=
  combineSlices (auxiliaryRankSlice contact03) 80 8 8 8440894 6291982 contact03RanksJoin80_8 contact03RanksJoin88_8
private theorem contact03RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact03) 96 16 = 7587406 :=
  combineSlices (auxiliaryRankSlice contact03) 96 8 8 4512768 3074638 contact03RanksJoin96_8 contact03RanksJoin104_8
private theorem contact03RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact03) 112 16 = 3059678 :=
  combineSlices (auxiliaryRankSlice contact03) 112 8 8 1949726 1109952 contact03RanksJoin112_8 contact03RanksJoin120_8
private theorem contact03RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact03) 128 16 = 697996 :=
  combineSlices (auxiliaryRankSlice contact03) 128 8 8 526430 171566 contact03RanksJoin128_8 contact03RanksJoin136_8
private theorem contact03RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact03) 144 20 = 17519 :=
  combineSlices (auxiliaryRankSlice contact03) 144 8 12 17519 0 contact03RanksJoin144_8 contact03RanksSlice152
private theorem contact03RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact03) 0 32 = 180681184 :=
  combineSlices (auxiliaryRankSlice contact03) 0 16 16 103013616 77667568 contact03RanksJoin0_16 contact03RanksJoin16_16
private theorem contact03RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact03) 32 32 = 94893402 :=
  combineSlices (auxiliaryRankSlice contact03) 32 16 16 56220912 38672490 contact03RanksJoin32_16 contact03RanksJoin48_16
private theorem contact03RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact03) 64 32 = 39680650 :=
  combineSlices (auxiliaryRankSlice contact03) 64 16 16 24947774 14732876 contact03RanksJoin64_16 contact03RanksJoin80_16
private theorem contact03RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact03) 96 32 = 10647084 :=
  combineSlices (auxiliaryRankSlice contact03) 96 16 16 7587406 3059678 contact03RanksJoin96_16 contact03RanksJoin112_16
private theorem contact03RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact03) 128 36 = 715515 :=
  combineSlices (auxiliaryRankSlice contact03) 128 16 20 697996 17519 contact03RanksJoin128_16 contact03RanksJoin144_20
private theorem contact03RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact03) 0 64 = 275574586 :=
  combineSlices (auxiliaryRankSlice contact03) 0 32 32 180681184 94893402 contact03RanksJoin0_32 contact03RanksJoin32_32
private theorem contact03RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact03) 64 64 = 50327734 :=
  combineSlices (auxiliaryRankSlice contact03) 64 32 32 39680650 10647084 contact03RanksJoin64_32 contact03RanksJoin96_32
private theorem contact03RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact03) 0 128 = 325902320 :=
  combineSlices (auxiliaryRankSlice contact03) 0 64 64 275574586 50327734 contact03RanksJoin0_64 contact03RanksJoin64_64
private theorem contact03RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact03) 0 164 = 326617835 :=
  combineSlices (auxiliaryRankSlice contact03) 0 128 36 325902320 715515 contact03RanksJoin0_128 contact03RanksJoin128_36
theorem contact03_margin : sourceMargin contact03 :=
  margin_of_checked_counts contact03 164 2260574159127977 108074767856142 8709054079 326617835 rfl contact03OrdinaryColumns contact03ColumnsJoin0_164 contact03OrdinaryRanks contact03RanksJoin0_164 (by decide +kernel)

private theorem contact05OrdinaryColumns : ordinaryColumnCount contact05 = 2162075175551218 := by decide +kernel
private theorem contact05ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact05) 0 4 = 7743415703300 :=
  contactColumnsWindow_fast contact05 0 4 7743415703300 (by decide +kernel)
private theorem contact05ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact05) 4 4 = 7372951169572 :=
  contactColumnsWindow_fast contact05 4 4 7372951169572 (by decide +kernel)
private theorem contact05ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact05) 8 4 = 7011603546148 :=
  contactColumnsWindow_fast contact05 8 4 7011603546148 (by decide +kernel)
private theorem contact05ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact05) 12 4 = 6659373093413 :=
  contactColumnsWindow_fast contact05 12 4 6659373093413 (by decide +kernel)
private theorem contact05ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact05) 16 4 = 6316294760712 :=
  contactColumnsWindow_fast contact05 16 4 6316294760712 (by decide +kernel)
private theorem contact05ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact05) 20 4 = 5982353512806 :=
  contactColumnsWindow_fast contact05 20 4 5982353512806 (by decide +kernel)
private theorem contact05ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact05) 24 4 = 5657532883156 :=
  contactColumnsWindow_fast contact05 24 4 5657532883156 (by decide +kernel)
private theorem contact05ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact05) 28 4 = 5341831525110 :=
  contactColumnsWindow_fast contact05 28 4 5341831525110 (by decide +kernel)
private theorem contact05ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact05) 32 4 = 5035252575687 :=
  contactColumnsWindow_fast contact05 32 4 5035252575687 (by decide +kernel)
private theorem contact05ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact05) 36 4 = 4737830388500 :=
  contactColumnsWindow_fast contact05 36 4 4737830388500 (by decide +kernel)
private theorem contact05ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact05) 40 4 = 4449546225452 :=
  contactColumnsWindow_fast contact05 40 4 4449546225452 (by decide +kernel)
private theorem contact05ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact05) 44 4 = 4170384602653 :=
  contactColumnsWindow_fast contact05 44 4 4170384602653 (by decide +kernel)
private theorem contact05ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact05) 48 4 = 3900346821450 :=
  contactColumnsWindow_fast contact05 48 4 3900346821450 (by decide +kernel)
private theorem contact05ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact05) 52 4 = 3639434943839 :=
  contactColumnsWindow_fast contact05 52 4 3639434943839 (by decide +kernel)
private theorem contact05ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact05) 56 4 = 3387686894075 :=
  contactColumnsWindow_fast contact05 56 4 3387686894075 (by decide +kernel)
private theorem contact05ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact05) 60 4 = 3145076319680 :=
  contactColumnsWindow_fast contact05 60 4 3145076319680 (by decide +kernel)
private theorem contact05ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact05) 64 4 = 2911591774135 :=
  contactColumnsWindow_fast contact05 64 4 2911591774135 (by decide +kernel)
private theorem contact05ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact05) 68 4 = 2687231029722 :=
  contactColumnsWindow_fast contact05 68 4 2687231029722 (by decide +kernel)
private theorem contact05ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact05) 72 4 = 2471998707738 :=
  contactColumnsWindow_fast contact05 72 4 2471998707738 (by decide +kernel)
private theorem contact05ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact05) 76 4 = 2265930593045 :=
  contactColumnsWindow_fast contact05 76 4 2265930593045 (by decide +kernel)
private theorem contact05ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact05) 80 4 = 2068997652284 :=
  contactColumnsWindow_fast contact05 80 4 2068997652284 (by decide +kernel)
private theorem contact05ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact05) 84 4 = 1881190250900 :=
  contactColumnsWindow_fast contact05 84 4 1881190250900 (by decide +kernel)
private theorem contact05ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact05) 88 4 = 1702506608049 :=
  contactColumnsWindow_fast contact05 88 4 1702506608049 (by decide +kernel)
private theorem contact05ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact05) 92 4 = 1532954069178 :=
  contactColumnsWindow_fast contact05 92 4 1532954069178 (by decide +kernel)
private theorem contact05ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact05) 96 4 = 1372565577604 :=
  contactColumnsWindow_fast contact05 96 4 1372565577604 (by decide +kernel)
private theorem contact05ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact05) 100 4 = 1221310296818 :=
  contactColumnsWindow_fast contact05 100 4 1221310296818 (by decide +kernel)
private theorem contact05ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact05) 104 4 = 1079180167208 :=
  contactColumnsWindow_fast contact05 104 4 1079180167208 (by decide +kernel)
private theorem contact05ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact05) 108 4 = 946173429639 :=
  contactColumnsWindow_fast contact05 108 4 946173429639 (by decide +kernel)
private theorem contact05ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact05) 112 4 = 822300878849 :=
  contactColumnsWindow_fast contact05 112 4 822300878849 (by decide +kernel)
private theorem contact05ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact05) 116 4 = 707592127893 :=
  contactColumnsWindow_fast contact05 116 4 707592127893 (by decide +kernel)
private theorem contact05ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact05) 120 4 = 602014237682 :=
  contactColumnsWindow_fast contact05 120 4 602014237682 (by decide +kernel)
private theorem contact05ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact05) 124 4 = 505561321892 :=
  contactColumnsWindow_fast contact05 124 4 505561321892 (by decide +kernel)
private theorem contact05ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact05) 128 4 = 418231669686 :=
  contactColumnsWindow_fast contact05 128 4 418231669686 (by decide +kernel)
private theorem contact05ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact05) 132 4 = 340040107991 :=
  contactColumnsWindow_fast contact05 132 4 340040107991 (by decide +kernel)
private theorem contact05ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact05) 136 4 = 271009950958 :=
  contactColumnsWindow_fast contact05 136 4 271009950958 (by decide +kernel)
private theorem contact05ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact05) 140 4 = 211096605102 :=
  contactColumnsWindow_fast contact05 140 4 211096605102 (by decide +kernel)
private theorem contact05ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact05) 144 4 = 160161329666 :=
  contactColumnsWindow_fast contact05 144 4 160161329666 (by decide +kernel)
private theorem contact05ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact05) 148 4 = 117868919889 :=
  contactColumnsWindow_fast contact05 148 4 117868919889 (by decide +kernel)
private theorem contact05ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact05) 152 4 = 83740305576 :=
  contactColumnsWindow_fast contact05 152 4 83740305576 (by decide +kernel)
private theorem contact05ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact05) 156 4 = 57128556513 :=
  contactColumnsWindow_fast contact05 156 4 57128556513 (by decide +kernel)
private theorem contact05ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact05) 160 3 = 29426205957 :=
  contactColumnsWindow_fast contact05 160 3 29426205957 (by decide +kernel)
private theorem contact05ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact05) 0 8 = 15116366872872 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 4 4 7743415703300 7372951169572 contact05ColumnsSlice0 contact05ColumnsSlice4
private theorem contact05ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact05) 8 8 = 13670976639561 :=
  combineSlices (auxiliaryColumnSlice contact05) 8 4 4 7011603546148 6659373093413 contact05ColumnsSlice8 contact05ColumnsSlice12
private theorem contact05ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact05) 16 8 = 12298648273518 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 4 4 6316294760712 5982353512806 contact05ColumnsSlice16 contact05ColumnsSlice20
private theorem contact05ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact05) 24 8 = 10999364408266 :=
  combineSlices (auxiliaryColumnSlice contact05) 24 4 4 5657532883156 5341831525110 contact05ColumnsSlice24 contact05ColumnsSlice28
private theorem contact05ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact05) 32 8 = 9773082964187 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 4 4 5035252575687 4737830388500 contact05ColumnsSlice32 contact05ColumnsSlice36
private theorem contact05ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact05) 40 8 = 8619930828105 :=
  combineSlices (auxiliaryColumnSlice contact05) 40 4 4 4449546225452 4170384602653 contact05ColumnsSlice40 contact05ColumnsSlice44
private theorem contact05ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact05) 48 8 = 7539781765289 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 4 4 3900346821450 3639434943839 contact05ColumnsSlice48 contact05ColumnsSlice52
private theorem contact05ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact05) 56 8 = 6532763213755 :=
  combineSlices (auxiliaryColumnSlice contact05) 56 4 4 3387686894075 3145076319680 contact05ColumnsSlice56 contact05ColumnsSlice60
private theorem contact05ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact05) 64 8 = 5598822803857 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 4 4 2911591774135 2687231029722 contact05ColumnsSlice64 contact05ColumnsSlice68
private theorem contact05ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact05) 72 8 = 4737929300783 :=
  combineSlices (auxiliaryColumnSlice contact05) 72 4 4 2471998707738 2265930593045 contact05ColumnsSlice72 contact05ColumnsSlice76
private theorem contact05ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact05) 80 8 = 3950187903184 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 4 4 2068997652284 1881190250900 contact05ColumnsSlice80 contact05ColumnsSlice84
private theorem contact05ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact05) 88 8 = 3235460677227 :=
  combineSlices (auxiliaryColumnSlice contact05) 88 4 4 1702506608049 1532954069178 contact05ColumnsSlice88 contact05ColumnsSlice92
private theorem contact05ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact05) 96 8 = 2593875874422 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 4 4 1372565577604 1221310296818 contact05ColumnsSlice96 contact05ColumnsSlice100
private theorem contact05ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact05) 104 8 = 2025353596847 :=
  combineSlices (auxiliaryColumnSlice contact05) 104 4 4 1079180167208 946173429639 contact05ColumnsSlice104 contact05ColumnsSlice108
private theorem contact05ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact05) 112 8 = 1529893006742 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 4 4 822300878849 707592127893 contact05ColumnsSlice112 contact05ColumnsSlice116
private theorem contact05ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact05) 120 8 = 1107575559574 :=
  combineSlices (auxiliaryColumnSlice contact05) 120 4 4 602014237682 505561321892 contact05ColumnsSlice120 contact05ColumnsSlice124
private theorem contact05ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact05) 128 8 = 758271777677 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 4 4 418231669686 340040107991 contact05ColumnsSlice128 contact05ColumnsSlice132
private theorem contact05ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact05) 136 8 = 482106556060 :=
  combineSlices (auxiliaryColumnSlice contact05) 136 4 4 271009950958 211096605102 contact05ColumnsSlice136 contact05ColumnsSlice140
private theorem contact05ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact05) 144 8 = 278030249555 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 4 4 160161329666 117868919889 contact05ColumnsSlice144 contact05ColumnsSlice148
private theorem contact05ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact05) 152 8 = 140868862089 :=
  combineSlices (auxiliaryColumnSlice contact05) 152 4 4 83740305576 57128556513 contact05ColumnsSlice152 contact05ColumnsSlice156
private theorem contact05ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact05) 0 16 = 28787343512433 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 8 8 15116366872872 13670976639561 contact05ColumnsJoin0_8 contact05ColumnsJoin8_8
private theorem contact05ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact05) 16 16 = 23298012681784 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 8 8 12298648273518 10999364408266 contact05ColumnsJoin16_8 contact05ColumnsJoin24_8
private theorem contact05ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact05) 32 16 = 18393013792292 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 8 8 9773082964187 8619930828105 contact05ColumnsJoin32_8 contact05ColumnsJoin40_8
private theorem contact05ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact05) 48 16 = 14072544979044 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 8 8 7539781765289 6532763213755 contact05ColumnsJoin48_8 contact05ColumnsJoin56_8
private theorem contact05ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact05) 64 16 = 10336752104640 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 8 8 5598822803857 4737929300783 contact05ColumnsJoin64_8 contact05ColumnsJoin72_8
private theorem contact05ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact05) 80 16 = 7185648580411 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 8 8 3950187903184 3235460677227 contact05ColumnsJoin80_8 contact05ColumnsJoin88_8
private theorem contact05ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact05) 96 16 = 4619229471269 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 8 8 2593875874422 2025353596847 contact05ColumnsJoin96_8 contact05ColumnsJoin104_8
private theorem contact05ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact05) 112 16 = 2637468566316 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 8 8 1529893006742 1107575559574 contact05ColumnsJoin112_8 contact05ColumnsJoin120_8
private theorem contact05ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact05) 128 16 = 1240378333737 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 8 8 758271777677 482106556060 contact05ColumnsJoin128_8 contact05ColumnsJoin136_8
private theorem contact05ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact05) 144 16 = 418899111644 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 8 8 278030249555 140868862089 contact05ColumnsJoin144_8 contact05ColumnsJoin152_8
private theorem contact05ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact05) 0 32 = 52085356194217 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 16 16 28787343512433 23298012681784 contact05ColumnsJoin0_16 contact05ColumnsJoin16_16
private theorem contact05ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact05) 32 32 = 32465558771336 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 16 16 18393013792292 14072544979044 contact05ColumnsJoin32_16 contact05ColumnsJoin48_16
private theorem contact05ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact05) 64 32 = 17522400685051 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 16 16 10336752104640 7185648580411 contact05ColumnsJoin64_16 contact05ColumnsJoin80_16
private theorem contact05ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact05) 96 32 = 7256698037585 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 16 16 4619229471269 2637468566316 contact05ColumnsJoin96_16 contact05ColumnsJoin112_16
private theorem contact05ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact05) 128 32 = 1659277445381 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 16 16 1240378333737 418899111644 contact05ColumnsJoin128_16 contact05ColumnsJoin144_16
private theorem contact05ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact05) 0 64 = 84550914965553 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 32 32 52085356194217 32465558771336 contact05ColumnsJoin0_32 contact05ColumnsJoin32_32
private theorem contact05ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact05) 64 64 = 24779098722636 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 32 32 17522400685051 7256698037585 contact05ColumnsJoin64_32 contact05ColumnsJoin96_32
private theorem contact05ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact05) 128 35 = 1688703651338 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 32 3 1659277445381 29426205957 contact05ColumnsJoin128_32 contact05ColumnsSlice160
private theorem contact05ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact05) 0 128 = 109330013688189 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 64 64 84550914965553 24779098722636 contact05ColumnsJoin0_64 contact05ColumnsJoin64_64
private theorem contact05ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact05) 0 163 = 111018717339527 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 128 35 109330013688189 1688703651338 contact05ColumnsJoin0_128 contact05ColumnsJoin128_35
private theorem contact05OrdinaryRanks : ordinaryRankBound contact05 = 8334935272 := by decide +kernel
private theorem contact05RanksSlice0 : sliceWindow (auxiliaryRankSlice contact05) 0 4 = 29183538 :=
  contactRankWindow_of_rec contact05 0 4 29183538 (by decide +kernel)
private theorem contact05RanksSlice4 : sliceWindow (auxiliaryRankSlice contact05) 4 4 = 27361410 :=
  contactRankWindow_of_rec contact05 4 4 27361410 (by decide +kernel)
private theorem contact05RanksSlice8 : sliceWindow (auxiliaryRankSlice contact05) 8 4 = 25602386 :=
  contactRankWindow_of_rec contact05 8 4 25602386 (by decide +kernel)
private theorem contact05RanksSlice12 : sliceWindow (auxiliaryRankSlice contact05) 12 4 = 23906466 :=
  contactRankWindow_of_rec contact05 12 4 23906466 (by decide +kernel)
private theorem contact05RanksSlice16 : sliceWindow (auxiliaryRankSlice contact05) 16 4 = 22273650 :=
  contactRankWindow_of_rec contact05 16 4 22273650 (by decide +kernel)
private theorem contact05RanksSlice20 : sliceWindow (auxiliaryRankSlice contact05) 20 4 = 20703938 :=
  contactRankWindow_of_rec contact05 20 4 20703938 (by decide +kernel)
private theorem contact05RanksSlice24 : sliceWindow (auxiliaryRankSlice contact05) 24 4 = 19197330 :=
  contactRankWindow_of_rec contact05 24 4 19197330 (by decide +kernel)
private theorem contact05RanksSlice28 : sliceWindow (auxiliaryRankSlice contact05) 28 4 = 17753826 :=
  contactRankWindow_of_rec contact05 28 4 17753826 (by decide +kernel)
private theorem contact05RanksSlice32 : sliceWindow (auxiliaryRankSlice contact05) 32 4 = 16373426 :=
  contactRankWindow_of_rec contact05 32 4 16373426 (by decide +kernel)
private theorem contact05RanksSlice36 : sliceWindow (auxiliaryRankSlice contact05) 36 4 = 15056130 :=
  contactRankWindow_of_rec contact05 36 4 15056130 (by decide +kernel)
private theorem contact05RanksSlice40 : sliceWindow (auxiliaryRankSlice contact05) 40 4 = 13801938 :=
  contactRankWindow_of_rec contact05 40 4 13801938 (by decide +kernel)
private theorem contact05RanksSlice44 : sliceWindow (auxiliaryRankSlice contact05) 44 4 = 12610850 :=
  contactRankWindow_of_rec contact05 44 4 12610850 (by decide +kernel)
private theorem contact05RanksSlice48 : sliceWindow (auxiliaryRankSlice contact05) 48 4 = 11482866 :=
  contactRankWindow_of_rec contact05 48 4 11482866 (by decide +kernel)
private theorem contact05RanksSlice52 : sliceWindow (auxiliaryRankSlice contact05) 52 4 = 10417986 :=
  contactRankWindow_of_rec contact05 52 4 10417986 (by decide +kernel)
private theorem contact05RanksSlice56 : sliceWindow (auxiliaryRankSlice contact05) 56 4 = 9416006 :=
  contactRankWindow_of_rec contact05 56 4 9416006 (by decide +kernel)
private theorem contact05RanksSlice60 : sliceWindow (auxiliaryRankSlice contact05) 60 4 = 8475868 :=
  contactRankWindow_of_rec contact05 60 4 8475868 (by decide +kernel)
private theorem contact05RanksSlice64 : sliceWindow (auxiliaryRankSlice contact05) 64 4 = 7596310 :=
  contactRankWindow_of_rec contact05 64 4 7596310 (by decide +kernel)
private theorem contact05RanksSlice68 : sliceWindow (auxiliaryRankSlice contact05) 68 4 = 6775747 :=
  contactRankWindow_of_rec contact05 68 4 6775747 (by decide +kernel)
private theorem contact05RanksSlice72 : sliceWindow (auxiliaryRankSlice contact05) 72 4 = 6012456 :=
  contactRankWindow_of_rec contact05 72 4 6012456 (by decide +kernel)
private theorem contact05RanksSlice76 : sliceWindow (auxiliaryRankSlice contact05) 76 4 = 5304598 :=
  contactRankWindow_of_rec contact05 76 4 5304598 (by decide +kernel)
private theorem contact05RanksSlice80 : sliceWindow (auxiliaryRankSlice contact05) 80 4 = 4650315 :=
  contactRankWindow_of_rec contact05 80 4 4650315 (by decide +kernel)
private theorem contact05RanksSlice84 : sliceWindow (auxiliaryRankSlice contact05) 84 4 = 4048020 :=
  contactRankWindow_of_rec contact05 84 4 4048020 (by decide +kernel)
private theorem contact05RanksSlice88 : sliceWindow (auxiliaryRankSlice contact05) 88 4 = 3495734 :=
  contactRankWindow_of_rec contact05 88 4 3495734 (by decide +kernel)
private theorem contact05RanksSlice92 : sliceWindow (auxiliaryRankSlice contact05) 92 4 = 2991603 :=
  contactRankWindow_of_rec contact05 92 4 2991603 (by decide +kernel)
private theorem contact05RanksSlice96 : sliceWindow (auxiliaryRankSlice contact05) 96 4 = 2534176 :=
  contactRankWindow_of_rec contact05 96 4 2534176 (by decide +kernel)
private theorem contact05RanksSlice100 : sliceWindow (auxiliaryRankSlice contact05) 100 4 = 2121334 :=
  contactRankWindow_of_rec contact05 100 4 2121334 (by decide +kernel)
private theorem contact05RanksSlice104 : sliceWindow (auxiliaryRankSlice contact05) 104 4 = 1751227 :=
  contactRankWindow_of_rec contact05 104 4 1751227 (by decide +kernel)
private theorem contact05RanksSlice108 : sliceWindow (auxiliaryRankSlice contact05) 108 4 = 1422540 :=
  contactRankWindow_of_rec contact05 108 4 1422540 (by decide +kernel)
private theorem contact05RanksSlice112 : sliceWindow (auxiliaryRankSlice contact05) 112 4 = 1133014 :=
  contactRankWindow_of_rec contact05 112 4 1133014 (by decide +kernel)
private theorem contact05RanksSlice116 : sliceWindow (auxiliaryRankSlice contact05) 116 4 = 880803 :=
  contactRankWindow_of_rec contact05 116 4 880803 (by decide +kernel)
private theorem contact05RanksSlice120 : sliceWindow (auxiliaryRankSlice contact05) 120 4 = 664728 :=
  contactRankWindow_of_rec contact05 120 4 664728 (by decide +kernel)
private theorem contact05RanksSlice124 : sliceWindow (auxiliaryRankSlice contact05) 124 4 = 482390 :=
  contactRankWindow_of_rec contact05 124 4 482390 (by decide +kernel)
private theorem contact05RanksSlice128 : sliceWindow (auxiliaryRankSlice contact05) 128 4 = 331947 :=
  contactRankWindow_of_rec contact05 128 4 331947 (by decide +kernel)
private theorem contact05RanksSlice132 : sliceWindow (auxiliaryRankSlice contact05) 132 4 = 212356 :=
  contactRankWindow_of_rec contact05 132 4 212356 (by decide +kernel)
private theorem contact05RanksSlice136 : sliceWindow (auxiliaryRankSlice contact05) 136 4 = 121078 :=
  contactRankWindow_of_rec contact05 136 4 121078 (by decide +kernel)
private theorem contact05RanksSlice140 : sliceWindow (auxiliaryRankSlice contact05) 140 4 = 56275 :=
  contactRankWindow_of_rec contact05 140 4 56275 (by decide +kernel)
private theorem contact05RanksSlice144 : sliceWindow (auxiliaryRankSlice contact05) 144 4 = 17102 :=
  contactRankWindow_of_rec contact05 144 4 17102 (by decide +kernel)
private theorem contact05RanksSlice148 : sliceWindow (auxiliaryRankSlice contact05) 148 4 = 965 :=
  contactRankWindow_of_rec contact05 148 4 965 (by decide +kernel)
private theorem contact05RanksSlice152 : sliceWindow (auxiliaryRankSlice contact05) 152 11 = 0 :=
  contactRankWindow_of_rec contact05 152 11 0 (by decide +kernel)
private theorem contact05RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact05) 0 8 = 56544948 :=
  combineSlices (auxiliaryRankSlice contact05) 0 4 4 29183538 27361410 contact05RanksSlice0 contact05RanksSlice4
private theorem contact05RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact05) 8 8 = 49508852 :=
  combineSlices (auxiliaryRankSlice contact05) 8 4 4 25602386 23906466 contact05RanksSlice8 contact05RanksSlice12
private theorem contact05RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact05) 16 8 = 42977588 :=
  combineSlices (auxiliaryRankSlice contact05) 16 4 4 22273650 20703938 contact05RanksSlice16 contact05RanksSlice20
private theorem contact05RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact05) 24 8 = 36951156 :=
  combineSlices (auxiliaryRankSlice contact05) 24 4 4 19197330 17753826 contact05RanksSlice24 contact05RanksSlice28
private theorem contact05RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact05) 32 8 = 31429556 :=
  combineSlices (auxiliaryRankSlice contact05) 32 4 4 16373426 15056130 contact05RanksSlice32 contact05RanksSlice36
private theorem contact05RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact05) 40 8 = 26412788 :=
  combineSlices (auxiliaryRankSlice contact05) 40 4 4 13801938 12610850 contact05RanksSlice40 contact05RanksSlice44
private theorem contact05RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact05) 48 8 = 21900852 :=
  combineSlices (auxiliaryRankSlice contact05) 48 4 4 11482866 10417986 contact05RanksSlice48 contact05RanksSlice52
private theorem contact05RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact05) 56 8 = 17891874 :=
  combineSlices (auxiliaryRankSlice contact05) 56 4 4 9416006 8475868 contact05RanksSlice56 contact05RanksSlice60
private theorem contact05RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact05) 64 8 = 14372057 :=
  combineSlices (auxiliaryRankSlice contact05) 64 4 4 7596310 6775747 contact05RanksSlice64 contact05RanksSlice68
private theorem contact05RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact05) 72 8 = 11317054 :=
  combineSlices (auxiliaryRankSlice contact05) 72 4 4 6012456 5304598 contact05RanksSlice72 contact05RanksSlice76
private theorem contact05RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact05) 80 8 = 8698335 :=
  combineSlices (auxiliaryRankSlice contact05) 80 4 4 4650315 4048020 contact05RanksSlice80 contact05RanksSlice84
private theorem contact05RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact05) 88 8 = 6487337 :=
  combineSlices (auxiliaryRankSlice contact05) 88 4 4 3495734 2991603 contact05RanksSlice88 contact05RanksSlice92
private theorem contact05RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact05) 96 8 = 4655510 :=
  combineSlices (auxiliaryRankSlice contact05) 96 4 4 2534176 2121334 contact05RanksSlice96 contact05RanksSlice100
private theorem contact05RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact05) 104 8 = 3173767 :=
  combineSlices (auxiliaryRankSlice contact05) 104 4 4 1751227 1422540 contact05RanksSlice104 contact05RanksSlice108
private theorem contact05RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact05) 112 8 = 2013817 :=
  combineSlices (auxiliaryRankSlice contact05) 112 4 4 1133014 880803 contact05RanksSlice112 contact05RanksSlice116
private theorem contact05RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact05) 120 8 = 1147118 :=
  combineSlices (auxiliaryRankSlice contact05) 120 4 4 664728 482390 contact05RanksSlice120 contact05RanksSlice124
private theorem contact05RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact05) 128 8 = 544303 :=
  combineSlices (auxiliaryRankSlice contact05) 128 4 4 331947 212356 contact05RanksSlice128 contact05RanksSlice132
private theorem contact05RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact05) 136 8 = 177353 :=
  combineSlices (auxiliaryRankSlice contact05) 136 4 4 121078 56275 contact05RanksSlice136 contact05RanksSlice140
private theorem contact05RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact05) 144 8 = 18067 :=
  combineSlices (auxiliaryRankSlice contact05) 144 4 4 17102 965 contact05RanksSlice144 contact05RanksSlice148
private theorem contact05RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact05) 0 16 = 106053800 :=
  combineSlices (auxiliaryRankSlice contact05) 0 8 8 56544948 49508852 contact05RanksJoin0_8 contact05RanksJoin8_8
private theorem contact05RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact05) 16 16 = 79928744 :=
  combineSlices (auxiliaryRankSlice contact05) 16 8 8 42977588 36951156 contact05RanksJoin16_8 contact05RanksJoin24_8
private theorem contact05RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact05) 32 16 = 57842344 :=
  combineSlices (auxiliaryRankSlice contact05) 32 8 8 31429556 26412788 contact05RanksJoin32_8 contact05RanksJoin40_8
private theorem contact05RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact05) 48 16 = 39792726 :=
  combineSlices (auxiliaryRankSlice contact05) 48 8 8 21900852 17891874 contact05RanksJoin48_8 contact05RanksJoin56_8
private theorem contact05RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact05) 64 16 = 25689111 :=
  combineSlices (auxiliaryRankSlice contact05) 64 8 8 14372057 11317054 contact05RanksJoin64_8 contact05RanksJoin72_8
private theorem contact05RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact05) 80 16 = 15185672 :=
  combineSlices (auxiliaryRankSlice contact05) 80 8 8 8698335 6487337 contact05RanksJoin80_8 contact05RanksJoin88_8
private theorem contact05RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact05) 96 16 = 7829277 :=
  combineSlices (auxiliaryRankSlice contact05) 96 8 8 4655510 3173767 contact05RanksJoin96_8 contact05RanksJoin104_8
private theorem contact05RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact05) 112 16 = 3160935 :=
  combineSlices (auxiliaryRankSlice contact05) 112 8 8 2013817 1147118 contact05RanksJoin112_8 contact05RanksJoin120_8
private theorem contact05RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact05) 128 16 = 721656 :=
  combineSlices (auxiliaryRankSlice contact05) 128 8 8 544303 177353 contact05RanksJoin128_8 contact05RanksJoin136_8
private theorem contact05RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact05) 144 19 = 18067 :=
  combineSlices (auxiliaryRankSlice contact05) 144 8 11 18067 0 contact05RanksJoin144_8 contact05RanksSlice152
private theorem contact05RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact05) 0 32 = 185982544 :=
  combineSlices (auxiliaryRankSlice contact05) 0 16 16 106053800 79928744 contact05RanksJoin0_16 contact05RanksJoin16_16
private theorem contact05RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact05) 32 32 = 97635070 :=
  combineSlices (auxiliaryRankSlice contact05) 32 16 16 57842344 39792726 contact05RanksJoin32_16 contact05RanksJoin48_16
private theorem contact05RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact05) 64 32 = 40874783 :=
  combineSlices (auxiliaryRankSlice contact05) 64 16 16 25689111 15185672 contact05RanksJoin64_16 contact05RanksJoin80_16
private theorem contact05RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact05) 96 32 = 10990212 :=
  combineSlices (auxiliaryRankSlice contact05) 96 16 16 7829277 3160935 contact05RanksJoin96_16 contact05RanksJoin112_16
private theorem contact05RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact05) 128 35 = 739723 :=
  combineSlices (auxiliaryRankSlice contact05) 128 16 19 721656 18067 contact05RanksJoin128_16 contact05RanksJoin144_19
private theorem contact05RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact05) 0 64 = 283617614 :=
  combineSlices (auxiliaryRankSlice contact05) 0 32 32 185982544 97635070 contact05RanksJoin0_32 contact05RanksJoin32_32
private theorem contact05RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact05) 64 64 = 51864995 :=
  combineSlices (auxiliaryRankSlice contact05) 64 32 32 40874783 10990212 contact05RanksJoin64_32 contact05RanksJoin96_32
private theorem contact05RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact05) 0 128 = 335482609 :=
  combineSlices (auxiliaryRankSlice contact05) 0 64 64 283617614 51864995 contact05RanksJoin0_64 contact05RanksJoin64_64
private theorem contact05RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact05) 0 163 = 336222332 :=
  combineSlices (auxiliaryRankSlice contact05) 0 128 35 335482609 739723 contact05RanksJoin0_128 contact05RanksJoin128_35
theorem contact05_margin : sourceMargin contact05 :=
  margin_of_checked_counts contact05 163 2162075175551218 111018717339527 8334935272 336222332 rfl contact05OrdinaryColumns contact05ColumnsJoin0_163 contact05OrdinaryRanks contact05RanksJoin0_163 (by decide +kernel)

private theorem contact07OrdinaryColumns : ordinaryColumnCount contact07 = 2063443214608264 := by decide +kernel
private theorem contact07ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact07) 0 4 = 8153036173108 :=
  contactColumnsWindow_fast contact07 0 4 8153036173108 (by decide +kernel)
private theorem contact07ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact07) 4 4 = 7760867190644 :=
  contactColumnsWindow_fast contact07 4 4 7760867190644 (by decide +kernel)
private theorem contact07ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact07) 8 4 = 7378406821680 :=
  contactColumnsWindow_fast contact07 8 4 7378406821680 (by decide +kernel)
private theorem contact07ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact07) 12 4 = 7005655364549 :=
  contactColumnsWindow_fast contact07 12 4 7005655364549 (by decide +kernel)
private theorem contact07ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact07) 16 4 = 6642650926884 :=
  contactColumnsWindow_fast contact07 16 4 6642650926884 (by decide +kernel)
private theorem contact07ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact07) 20 4 = 6289377046645 :=
  contactColumnsWindow_fast contact07 20 4 6289377046645 (by decide +kernel)
private theorem contact07ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact07) 24 4 = 5945815634401 :=
  contactColumnsWindow_fast contact07 24 4 5945815634401 (by decide +kernel)
private theorem contact07ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact07) 28 4 = 5611965288708 :=
  contactColumnsWindow_fast contact07 28 4 5611965288708 (by decide +kernel)
private theorem contact07ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact07) 32 4 = 5287829354375 :=
  contactColumnsWindow_fast contact07 32 4 5287829354375 (by decide +kernel)
private theorem contact07ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact07) 36 4 = 4973445392142 :=
  contactColumnsWindow_fast contact07 36 4 4973445392142 (by decide +kernel)
private theorem contact07ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact07) 40 4 = 4668792749074 :=
  contactColumnsWindow_fast contact07 40 4 4668792749074 (by decide +kernel)
private theorem contact07ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact07) 44 4 = 4373854560517 :=
  contactColumnsWindow_fast contact07 44 4 4373854560517 (by decide +kernel)
private theorem contact07ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact07) 48 4 = 4088632167132 :=
  contactColumnsWindow_fast contact07 48 4 4088632167132 (by decide +kernel)
private theorem contact07ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact07) 52 4 = 3813127868756 :=
  contactColumnsWindow_fast contact07 52 4 3813127868756 (by decide +kernel)
private theorem contact07ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact07) 56 4 = 3547382994211 :=
  contactColumnsWindow_fast contact07 56 4 3547382994211 (by decide +kernel)
private theorem contact07ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact07) 60 4 = 3291368647738 :=
  contactColumnsWindow_fast contact07 60 4 3291368647738 (by decide +kernel)
private theorem contact07ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact07) 64 4 = 3045072353983 :=
  contactColumnsWindow_fast contact07 64 4 3045072353983 (by decide +kernel)
private theorem contact07ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact07) 68 4 = 2808491814936 :=
  contactColumnsWindow_fast contact07 68 4 2808491814936 (by decide +kernel)
private theorem contact07ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact07) 72 4 = 2581632104090 :=
  contactColumnsWindow_fast contact07 72 4 2581632104090 (by decide +kernel)
private theorem contact07ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact07) 76 4 = 2364532243261 :=
  contactColumnsWindow_fast contact07 76 4 2364532243261 (by decide +kernel)
private theorem contact07ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact07) 80 4 = 2157160368202 :=
  contactColumnsWindow_fast contact07 80 4 2157160368202 (by decide +kernel)
private theorem contact07ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact07) 84 4 = 1959506038694 :=
  contactColumnsWindow_fast contact07 84 4 1959506038694 (by decide +kernel)
private theorem contact07ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact07) 88 4 = 1771567421040 :=
  contactColumnsWindow_fast contact07 88 4 1771567421040 (by decide +kernel)
private theorem contact07ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact07) 92 4 = 1593352548818 :=
  contactColumnsWindow_fast contact07 92 4 1593352548818 (by decide +kernel)
private theorem contact07ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact07) 96 4 = 1424897362783 :=
  contactColumnsWindow_fast contact07 96 4 1424897362783 (by decide +kernel)
private theorem contact07ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact07) 100 4 = 1266167986795 :=
  contactColumnsWindow_fast contact07 100 4 1266167986795 (by decide +kernel)
private theorem contact07ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact07) 104 4 = 1117155753950 :=
  contactColumnsWindow_fast contact07 104 4 1117155753950 (by decide +kernel)
private theorem contact07ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact07) 108 4 = 977858854068 :=
  contactColumnsWindow_fast contact07 108 4 977858854068 (by decide +kernel)
private theorem contact07ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact07) 112 4 = 848289042709 :=
  contactColumnsWindow_fast contact07 112 4 848289042709 (by decide +kernel)
private theorem contact07ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact07) 116 4 = 728478643620 :=
  contactColumnsWindow_fast contact07 116 4 728478643620 (by decide +kernel)
private theorem contact07ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact07) 120 4 = 618391487425 :=
  contactColumnsWindow_fast contact07 120 4 618391487425 (by decide +kernel)
private theorem contact07ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact07) 124 4 = 518021291006 :=
  contactColumnsWindow_fast contact07 124 4 518021291006 (by decide +kernel)
private theorem contact07ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact07) 128 4 = 427366295025 :=
  contactColumnsWindow_fast contact07 128 4 427366295025 (by decide +kernel)
private theorem contact07ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact07) 132 4 = 346442643379 :=
  contactColumnsWindow_fast contact07 132 4 346442643379 (by decide +kernel)
private theorem contact07ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact07) 136 4 = 275274621777 :=
  contactColumnsWindow_fast contact07 136 4 275274621777 (by decide +kernel)
private theorem contact07ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact07) 140 4 = 213776835093 :=
  contactColumnsWindow_fast contact07 140 4 213776835093 (by decide +kernel)
private theorem contact07ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact07) 144 4 = 161712334566 :=
  contactColumnsWindow_fast contact07 144 4 161712334566 (by decide +kernel)
private theorem contact07ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact07) 148 4 = 118666038029 :=
  contactColumnsWindow_fast contact07 148 4 118666038029 (by decide +kernel)
private theorem contact07ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact07) 152 4 = 84083293634 :=
  contactColumnsWindow_fast contact07 152 4 84083293634 (by decide +kernel)
private theorem contact07ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact07) 156 4 = 57239581295 :=
  contactColumnsWindow_fast contact07 156 4 57239581295 (by decide +kernel)
private theorem contact07ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact07) 160 3 = 29445902787 :=
  contactColumnsWindow_fast contact07 160 3 29445902787 (by decide +kernel)
private theorem contact07ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact07) 0 8 = 15913903363752 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 4 4 8153036173108 7760867190644 contact07ColumnsSlice0 contact07ColumnsSlice4
private theorem contact07ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact07) 8 8 = 14384062186229 :=
  combineSlices (auxiliaryColumnSlice contact07) 8 4 4 7378406821680 7005655364549 contact07ColumnsSlice8 contact07ColumnsSlice12
private theorem contact07ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact07) 16 8 = 12932027973529 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 4 4 6642650926884 6289377046645 contact07ColumnsSlice16 contact07ColumnsSlice20
private theorem contact07ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact07) 24 8 = 11557780923109 :=
  combineSlices (auxiliaryColumnSlice contact07) 24 4 4 5945815634401 5611965288708 contact07ColumnsSlice24 contact07ColumnsSlice28
private theorem contact07ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact07) 32 8 = 10261274746517 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 4 4 5287829354375 4973445392142 contact07ColumnsSlice32 contact07ColumnsSlice36
private theorem contact07ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact07) 40 8 = 9042647309591 :=
  combineSlices (auxiliaryColumnSlice contact07) 40 4 4 4668792749074 4373854560517 contact07ColumnsSlice40 contact07ColumnsSlice44
private theorem contact07ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact07) 48 8 = 7901760035888 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 4 4 4088632167132 3813127868756 contact07ColumnsSlice48 contact07ColumnsSlice52
private theorem contact07ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact07) 56 8 = 6838751641949 :=
  combineSlices (auxiliaryColumnSlice contact07) 56 4 4 3547382994211 3291368647738 contact07ColumnsSlice56 contact07ColumnsSlice60
private theorem contact07ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact07) 64 8 = 5853564168919 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 4 4 3045072353983 2808491814936 contact07ColumnsSlice64 contact07ColumnsSlice68
private theorem contact07ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact07) 72 8 = 4946164347351 :=
  combineSlices (auxiliaryColumnSlice contact07) 72 4 4 2581632104090 2364532243261 contact07ColumnsSlice72 contact07ColumnsSlice76
private theorem contact07ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact07) 80 8 = 4116666406896 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 4 4 2157160368202 1959506038694 contact07ColumnsSlice80 contact07ColumnsSlice84
private theorem contact07ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact07) 88 8 = 3364919969858 :=
  combineSlices (auxiliaryColumnSlice contact07) 88 4 4 1771567421040 1593352548818 contact07ColumnsSlice88 contact07ColumnsSlice92
private theorem contact07ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact07) 96 8 = 2691065349578 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 4 4 1424897362783 1266167986795 contact07ColumnsSlice96 contact07ColumnsSlice100
private theorem contact07ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact07) 104 8 = 2095014608018 :=
  combineSlices (auxiliaryColumnSlice contact07) 104 4 4 1117155753950 977858854068 contact07ColumnsSlice104 contact07ColumnsSlice108
private theorem contact07ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact07) 112 8 = 1576767686329 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 4 4 848289042709 728478643620 contact07ColumnsSlice112 contact07ColumnsSlice116
private theorem contact07ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact07) 120 8 = 1136412778431 :=
  combineSlices (auxiliaryColumnSlice contact07) 120 4 4 618391487425 518021291006 contact07ColumnsSlice120 contact07ColumnsSlice124
private theorem contact07ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact07) 128 8 = 773808938404 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 4 4 427366295025 346442643379 contact07ColumnsSlice128 contact07ColumnsSlice132
private theorem contact07ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact07) 136 8 = 489051456870 :=
  combineSlices (auxiliaryColumnSlice contact07) 136 4 4 275274621777 213776835093 contact07ColumnsSlice136 contact07ColumnsSlice140
private theorem contact07ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact07) 144 8 = 280378372595 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 4 4 161712334566 118666038029 contact07ColumnsSlice144 contact07ColumnsSlice148
private theorem contact07ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact07) 152 8 = 141322874929 :=
  combineSlices (auxiliaryColumnSlice contact07) 152 4 4 84083293634 57239581295 contact07ColumnsSlice152 contact07ColumnsSlice156
private theorem contact07ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact07) 0 16 = 30297965549981 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 8 8 15913903363752 14384062186229 contact07ColumnsJoin0_8 contact07ColumnsJoin8_8
private theorem contact07ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact07) 16 16 = 24489808896638 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 8 8 12932027973529 11557780923109 contact07ColumnsJoin16_8 contact07ColumnsJoin24_8
private theorem contact07ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact07) 32 16 = 19303922056108 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 8 8 10261274746517 9042647309591 contact07ColumnsJoin32_8 contact07ColumnsJoin40_8
private theorem contact07ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact07) 48 16 = 14740511677837 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 8 8 7901760035888 6838751641949 contact07ColumnsJoin48_8 contact07ColumnsJoin56_8
private theorem contact07ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact07) 64 16 = 10799728516270 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 8 8 5853564168919 4946164347351 contact07ColumnsJoin64_8 contact07ColumnsJoin72_8
private theorem contact07ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact07) 80 16 = 7481586376754 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 8 8 4116666406896 3364919969858 contact07ColumnsJoin80_8 contact07ColumnsJoin88_8
private theorem contact07ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact07) 96 16 = 4786079957596 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 8 8 2691065349578 2095014608018 contact07ColumnsJoin96_8 contact07ColumnsJoin104_8
private theorem contact07ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact07) 112 16 = 2713180464760 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 8 8 1576767686329 1136412778431 contact07ColumnsJoin112_8 contact07ColumnsJoin120_8
private theorem contact07ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact07) 128 16 = 1262860395274 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 8 8 773808938404 489051456870 contact07ColumnsJoin128_8 contact07ColumnsJoin136_8
private theorem contact07ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact07) 144 16 = 421701247524 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 8 8 280378372595 141322874929 contact07ColumnsJoin144_8 contact07ColumnsJoin152_8
private theorem contact07ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact07) 0 32 = 54787774446619 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 16 16 30297965549981 24489808896638 contact07ColumnsJoin0_16 contact07ColumnsJoin16_16
private theorem contact07ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact07) 32 32 = 34044433733945 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 16 16 19303922056108 14740511677837 contact07ColumnsJoin32_16 contact07ColumnsJoin48_16
private theorem contact07ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact07) 64 32 = 18281314893024 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 16 16 10799728516270 7481586376754 contact07ColumnsJoin64_16 contact07ColumnsJoin80_16
private theorem contact07ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact07) 96 32 = 7499260422356 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 16 16 4786079957596 2713180464760 contact07ColumnsJoin96_16 contact07ColumnsJoin112_16
private theorem contact07ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact07) 128 32 = 1684561642798 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 16 16 1262860395274 421701247524 contact07ColumnsJoin128_16 contact07ColumnsJoin144_16
private theorem contact07ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact07) 0 64 = 88832208180564 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 32 32 54787774446619 34044433733945 contact07ColumnsJoin0_32 contact07ColumnsJoin32_32
private theorem contact07ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact07) 64 64 = 25780575315380 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 32 32 18281314893024 7499260422356 contact07ColumnsJoin64_32 contact07ColumnsJoin96_32
private theorem contact07ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact07) 128 35 = 1714007545585 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 32 3 1684561642798 29445902787 contact07ColumnsJoin128_32 contact07ColumnsSlice160
private theorem contact07ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact07) 0 128 = 114612783495944 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 64 64 88832208180564 25780575315380 contact07ColumnsJoin0_64 contact07ColumnsJoin64_64
private theorem contact07ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact07) 0 163 = 116326791041529 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 128 35 114612783495944 1714007545585 contact07ColumnsJoin0_128 contact07ColumnsJoin128_35
private theorem contact07OrdinaryRanks : ordinaryRankBound contact07 = 7961367686 := by decide +kernel
private theorem contact07RanksSlice0 : sliceWindow (auxiliaryRankSlice contact07) 0 4 = 30720414 :=
  contactRankWindow_of_rec contact07 0 4 30720414 (by decide +kernel)
private theorem contact07RanksSlice4 : sliceWindow (auxiliaryRankSlice contact07) 4 4 = 28796814 :=
  contactRankWindow_of_rec contact07 4 4 28796814 (by decide +kernel)
private theorem contact07RanksSlice8 : sliceWindow (auxiliaryRankSlice contact07) 8 4 = 26940414 :=
  contactRankWindow_of_rec contact07 8 4 26940414 (by decide +kernel)
private theorem contact07RanksSlice12 : sliceWindow (auxiliaryRankSlice contact07) 12 4 = 25151214 :=
  contactRankWindow_of_rec contact07 12 4 25151214 (by decide +kernel)
private theorem contact07RanksSlice16 : sliceWindow (auxiliaryRankSlice contact07) 16 4 = 23429214 :=
  contactRankWindow_of_rec contact07 16 4 23429214 (by decide +kernel)
private theorem contact07RanksSlice20 : sliceWindow (auxiliaryRankSlice contact07) 20 4 = 21774414 :=
  contactRankWindow_of_rec contact07 20 4 21774414 (by decide +kernel)
private theorem contact07RanksSlice24 : sliceWindow (auxiliaryRankSlice contact07) 24 4 = 20186814 :=
  contactRankWindow_of_rec contact07 24 4 20186814 (by decide +kernel)
private theorem contact07RanksSlice28 : sliceWindow (auxiliaryRankSlice contact07) 28 4 = 18666414 :=
  contactRankWindow_of_rec contact07 28 4 18666414 (by decide +kernel)
private theorem contact07RanksSlice32 : sliceWindow (auxiliaryRankSlice contact07) 32 4 = 17213214 :=
  contactRankWindow_of_rec contact07 32 4 17213214 (by decide +kernel)
private theorem contact07RanksSlice36 : sliceWindow (auxiliaryRankSlice contact07) 36 4 = 15827214 :=
  contactRankWindow_of_rec contact07 36 4 15827214 (by decide +kernel)
private theorem contact07RanksSlice40 : sliceWindow (auxiliaryRankSlice contact07) 40 4 = 14508414 :=
  contactRankWindow_of_rec contact07 40 4 14508414 (by decide +kernel)
private theorem contact07RanksSlice44 : sliceWindow (auxiliaryRankSlice contact07) 44 4 = 13256814 :=
  contactRankWindow_of_rec contact07 44 4 13256814 (by decide +kernel)
private theorem contact07RanksSlice48 : sliceWindow (auxiliaryRankSlice contact07) 48 4 = 12072414 :=
  contactRankWindow_of_rec contact07 48 4 12072414 (by decide +kernel)
private theorem contact07RanksSlice52 : sliceWindow (auxiliaryRankSlice contact07) 52 4 = 10955124 :=
  contactRankWindow_of_rec contact07 52 4 10955124 (by decide +kernel)
private theorem contact07RanksSlice56 : sliceWindow (auxiliaryRankSlice contact07) 56 4 = 9904064 :=
  contactRankWindow_of_rec contact07 56 4 9904064 (by decide +kernel)
private theorem contact07RanksSlice60 : sliceWindow (auxiliaryRankSlice contact07) 60 4 = 8917910 :=
  contactRankWindow_of_rec contact07 60 4 8917910 (by decide +kernel)
private theorem contact07RanksSlice64 : sliceWindow (auxiliaryRankSlice contact07) 64 4 = 7995198 :=
  contactRankWindow_of_rec contact07 64 4 7995198 (by decide +kernel)
private theorem contact07RanksSlice68 : sliceWindow (auxiliaryRankSlice contact07) 68 4 = 7134043 :=
  contactRankWindow_of_rec contact07 68 4 7134043 (by decide +kernel)
private theorem contact07RanksSlice72 : sliceWindow (auxiliaryRankSlice contact07) 72 4 = 6332702 :=
  contactRankWindow_of_rec contact07 72 4 6332702 (by decide +kernel)
private theorem contact07RanksSlice76 : sliceWindow (auxiliaryRankSlice contact07) 76 4 = 5589242 :=
  contactRankWindow_of_rec contact07 76 4 5589242 (by decide +kernel)
private theorem contact07RanksSlice80 : sliceWindow (auxiliaryRankSlice contact07) 80 4 = 4901747 :=
  contactRankWindow_of_rec contact07 80 4 4901747 (by decide +kernel)
private theorem contact07RanksSlice84 : sliceWindow (auxiliaryRankSlice contact07) 84 4 = 4268614 :=
  contactRankWindow_of_rec contact07 84 4 4268614 (by decide +kernel)
private theorem contact07RanksSlice88 : sliceWindow (auxiliaryRankSlice contact07) 88 4 = 3687766 :=
  contactRankWindow_of_rec contact07 88 4 3687766 (by decide +kernel)
private theorem contact07RanksSlice92 : sliceWindow (auxiliaryRankSlice contact07) 92 4 = 3157291 :=
  contactRankWindow_of_rec contact07 92 4 3157291 (by decide +kernel)
private theorem contact07RanksSlice96 : sliceWindow (auxiliaryRankSlice contact07) 96 4 = 2675726 :=
  contactRankWindow_of_rec contact07 96 4 2675726 (by decide +kernel)
private theorem contact07RanksSlice100 : sliceWindow (auxiliaryRankSlice contact07) 100 4 = 2240850 :=
  contactRankWindow_of_rec contact07 100 4 2240850 (by decide +kernel)
private theorem contact07RanksSlice104 : sliceWindow (auxiliaryRankSlice contact07) 104 4 = 1850755 :=
  contactRankWindow_of_rec contact07 104 4 1850755 (by decide +kernel)
private theorem contact07RanksSlice108 : sliceWindow (auxiliaryRankSlice contact07) 108 4 = 1504118 :=
  contactRankWindow_of_rec contact07 108 4 1504118 (by decide +kernel)
private theorem contact07RanksSlice112 : sliceWindow (auxiliaryRankSlice contact07) 112 4 = 1198574 :=
  contactRankWindow_of_rec contact07 112 4 1198574 (by decide +kernel)
private theorem contact07RanksSlice116 : sliceWindow (auxiliaryRankSlice contact07) 116 4 = 932219 :=
  contactRankWindow_of_rec contact07 116 4 932219 (by decide +kernel)
private theorem contact07RanksSlice120 : sliceWindow (auxiliaryRankSlice contact07) 120 4 = 703870 :=
  contactRankWindow_of_rec contact07 120 4 703870 (by decide +kernel)
private theorem contact07RanksSlice124 : sliceWindow (auxiliaryRankSlice contact07) 124 4 = 511018 :=
  contactRankWindow_of_rec contact07 124 4 511018 (by decide +kernel)
private theorem contact07RanksSlice128 : sliceWindow (auxiliaryRankSlice contact07) 128 4 = 351763 :=
  contactRankWindow_of_rec contact07 128 4 351763 (by decide +kernel)
private theorem contact07RanksSlice132 : sliceWindow (auxiliaryRankSlice contact07) 132 4 = 225062 :=
  contactRankWindow_of_rec contact07 132 4 225062 (by decide +kernel)
private theorem contact07RanksSlice136 : sliceWindow (auxiliaryRankSlice contact07) 136 4 = 128262 :=
  contactRankWindow_of_rec contact07 136 4 128262 (by decide +kernel)
private theorem contact07RanksSlice140 : sliceWindow (auxiliaryRankSlice contact07) 140 4 = 59482 :=
  contactRankWindow_of_rec contact07 140 4 59482 (by decide +kernel)
private theorem contact07RanksSlice144 : sliceWindow (auxiliaryRankSlice contact07) 144 4 = 18013 :=
  contactRankWindow_of_rec contact07 144 4 18013 (by decide +kernel)
private theorem contact07RanksSlice148 : sliceWindow (auxiliaryRankSlice contact07) 148 4 = 1014 :=
  contactRankWindow_of_rec contact07 148 4 1014 (by decide +kernel)
private theorem contact07RanksSlice152 : sliceWindow (auxiliaryRankSlice contact07) 152 11 = 0 :=
  contactRankWindow_of_rec contact07 152 11 0 (by decide +kernel)
private theorem contact07RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact07) 0 8 = 59517228 :=
  combineSlices (auxiliaryRankSlice contact07) 0 4 4 30720414 28796814 contact07RanksSlice0 contact07RanksSlice4
private theorem contact07RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact07) 8 8 = 52091628 :=
  combineSlices (auxiliaryRankSlice contact07) 8 4 4 26940414 25151214 contact07RanksSlice8 contact07RanksSlice12
private theorem contact07RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact07) 16 8 = 45203628 :=
  combineSlices (auxiliaryRankSlice contact07) 16 4 4 23429214 21774414 contact07RanksSlice16 contact07RanksSlice20
private theorem contact07RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact07) 24 8 = 38853228 :=
  combineSlices (auxiliaryRankSlice contact07) 24 4 4 20186814 18666414 contact07RanksSlice24 contact07RanksSlice28
private theorem contact07RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact07) 32 8 = 33040428 :=
  combineSlices (auxiliaryRankSlice contact07) 32 4 4 17213214 15827214 contact07RanksSlice32 contact07RanksSlice36
private theorem contact07RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact07) 40 8 = 27765228 :=
  combineSlices (auxiliaryRankSlice contact07) 40 4 4 14508414 13256814 contact07RanksSlice40 contact07RanksSlice44
private theorem contact07RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact07) 48 8 = 23027538 :=
  combineSlices (auxiliaryRankSlice contact07) 48 4 4 12072414 10955124 contact07RanksSlice48 contact07RanksSlice52
private theorem contact07RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact07) 56 8 = 18821974 :=
  combineSlices (auxiliaryRankSlice contact07) 56 4 4 9904064 8917910 contact07RanksSlice56 contact07RanksSlice60
private theorem contact07RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact07) 64 8 = 15129241 :=
  combineSlices (auxiliaryRankSlice contact07) 64 4 4 7995198 7134043 contact07RanksSlice64 contact07RanksSlice68
private theorem contact07RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact07) 72 8 = 11921944 :=
  combineSlices (auxiliaryRankSlice contact07) 72 4 4 6332702 5589242 contact07RanksSlice72 contact07RanksSlice76
private theorem contact07RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact07) 80 8 = 9170361 :=
  combineSlices (auxiliaryRankSlice contact07) 80 4 4 4901747 4268614 contact07RanksSlice80 contact07RanksSlice84
private theorem contact07RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact07) 88 8 = 6845057 :=
  combineSlices (auxiliaryRankSlice contact07) 88 4 4 3687766 3157291 contact07RanksSlice88 contact07RanksSlice92
private theorem contact07RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact07) 96 8 = 4916576 :=
  combineSlices (auxiliaryRankSlice contact07) 96 4 4 2675726 2240850 contact07RanksSlice96 contact07RanksSlice100
private theorem contact07RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact07) 104 8 = 3354873 :=
  combineSlices (auxiliaryRankSlice contact07) 104 4 4 1850755 1504118 contact07RanksSlice104 contact07RanksSlice108
private theorem contact07RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact07) 112 8 = 2130793 :=
  combineSlices (auxiliaryRankSlice contact07) 112 4 4 1198574 932219 contact07RanksSlice112 contact07RanksSlice116
private theorem contact07RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact07) 120 8 = 1214888 :=
  combineSlices (auxiliaryRankSlice contact07) 120 4 4 703870 511018 contact07RanksSlice120 contact07RanksSlice124
private theorem contact07RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact07) 128 8 = 576825 :=
  combineSlices (auxiliaryRankSlice contact07) 128 4 4 351763 225062 contact07RanksSlice128 contact07RanksSlice132
private theorem contact07RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact07) 136 8 = 187744 :=
  combineSlices (auxiliaryRankSlice contact07) 136 4 4 128262 59482 contact07RanksSlice136 contact07RanksSlice140
private theorem contact07RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact07) 144 8 = 19027 :=
  combineSlices (auxiliaryRankSlice contact07) 144 4 4 18013 1014 contact07RanksSlice144 contact07RanksSlice148
private theorem contact07RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact07) 0 16 = 111608856 :=
  combineSlices (auxiliaryRankSlice contact07) 0 8 8 59517228 52091628 contact07RanksJoin0_8 contact07RanksJoin8_8
private theorem contact07RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact07) 16 16 = 84056856 :=
  combineSlices (auxiliaryRankSlice contact07) 16 8 8 45203628 38853228 contact07RanksJoin16_8 contact07RanksJoin24_8
private theorem contact07RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact07) 32 16 = 60805656 :=
  combineSlices (auxiliaryRankSlice contact07) 32 8 8 33040428 27765228 contact07RanksJoin32_8 contact07RanksJoin40_8
private theorem contact07RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact07) 48 16 = 41849512 :=
  combineSlices (auxiliaryRankSlice contact07) 48 8 8 23027538 18821974 contact07RanksJoin48_8 contact07RanksJoin56_8
private theorem contact07RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact07) 64 16 = 27051185 :=
  combineSlices (auxiliaryRankSlice contact07) 64 8 8 15129241 11921944 contact07RanksJoin64_8 contact07RanksJoin72_8
private theorem contact07RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact07) 80 16 = 16015418 :=
  combineSlices (auxiliaryRankSlice contact07) 80 8 8 9170361 6845057 contact07RanksJoin80_8 contact07RanksJoin88_8
private theorem contact07RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact07) 96 16 = 8271449 :=
  combineSlices (auxiliaryRankSlice contact07) 96 8 8 4916576 3354873 contact07RanksJoin96_8 contact07RanksJoin104_8
private theorem contact07RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact07) 112 16 = 3345681 :=
  combineSlices (auxiliaryRankSlice contact07) 112 8 8 2130793 1214888 contact07RanksJoin112_8 contact07RanksJoin120_8
private theorem contact07RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact07) 128 16 = 764569 :=
  combineSlices (auxiliaryRankSlice contact07) 128 8 8 576825 187744 contact07RanksJoin128_8 contact07RanksJoin136_8
private theorem contact07RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact07) 144 19 = 19027 :=
  combineSlices (auxiliaryRankSlice contact07) 144 8 11 19027 0 contact07RanksJoin144_8 contact07RanksSlice152
private theorem contact07RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact07) 0 32 = 195665712 :=
  combineSlices (auxiliaryRankSlice contact07) 0 16 16 111608856 84056856 contact07RanksJoin0_16 contact07RanksJoin16_16
private theorem contact07RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact07) 32 32 = 102655168 :=
  combineSlices (auxiliaryRankSlice contact07) 32 16 16 60805656 41849512 contact07RanksJoin32_16 contact07RanksJoin48_16
private theorem contact07RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact07) 64 32 = 43066603 :=
  combineSlices (auxiliaryRankSlice contact07) 64 16 16 27051185 16015418 contact07RanksJoin64_16 contact07RanksJoin80_16
private theorem contact07RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact07) 96 32 = 11617130 :=
  combineSlices (auxiliaryRankSlice contact07) 96 16 16 8271449 3345681 contact07RanksJoin96_16 contact07RanksJoin112_16
private theorem contact07RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact07) 128 35 = 783596 :=
  combineSlices (auxiliaryRankSlice contact07) 128 16 19 764569 19027 contact07RanksJoin128_16 contact07RanksJoin144_19
private theorem contact07RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact07) 0 64 = 298320880 :=
  combineSlices (auxiliaryRankSlice contact07) 0 32 32 195665712 102655168 contact07RanksJoin0_32 contact07RanksJoin32_32
private theorem contact07RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact07) 64 64 = 54683733 :=
  combineSlices (auxiliaryRankSlice contact07) 64 32 32 43066603 11617130 contact07RanksJoin64_32 contact07RanksJoin96_32
private theorem contact07RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact07) 0 128 = 353004613 :=
  combineSlices (auxiliaryRankSlice contact07) 0 64 64 298320880 54683733 contact07RanksJoin0_64 contact07RanksJoin64_64
private theorem contact07RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact07) 0 163 = 353788209 :=
  combineSlices (auxiliaryRankSlice contact07) 0 128 35 353004613 783596 contact07RanksJoin0_128 contact07RanksJoin128_35
theorem contact07_margin : sourceMargin contact07 :=
  margin_of_checked_counts contact07 163 2063443214608264 116326791041529 7961367686 353788209 rfl contact07OrdinaryColumns contact07ColumnsJoin0_163 contact07OrdinaryRanks contact07RanksJoin0_163 (by decide +kernel)

private theorem contact09OrdinaryColumns : ordinaryColumnCount contact09 = 2711217976880244 := by decide +kernel
private theorem contact09ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact09) 0 4 = 6674842130844 :=
  contactColumnsWindow_fast contact09 0 4 6674842130844 (by decide +kernel)
private theorem contact09ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact09) 4 4 = 6347970754668 :=
  contactColumnsWindow_fast contact09 4 4 6347970754668 (by decide +kernel)
private theorem contact09ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact09) 8 4 = 6029336119014 :=
  contactColumnsWindow_fast contact09 8 4 6029336119014 (by decide +kernel)
private theorem contact09ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact09) 12 4 = 5718940963584 :=
  contactColumnsWindow_fast contact09 12 4 5718940963584 (by decide +kernel)
private theorem contact09ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact09) 16 4 = 5416783422140 :=
  contactColumnsWindow_fast contact09 16 4 5416783422140 (by decide +kernel)
private theorem contact09ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact09) 20 4 = 5122865363200 :=
  contactColumnsWindow_fast contact09 20 4 5122865363200 (by decide +kernel)
private theorem contact09ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact09) 24 4 = 4837200775380 :=
  contactColumnsWindow_fast contact09 24 4 4837200775380 (by decide +kernel)
private theorem contact09ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact09) 28 4 = 4559806495668 :=
  contactColumnsWindow_fast contact09 28 4 4559806495668 (by decide +kernel)
private theorem contact09ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact09) 32 4 = 4290654685528 :=
  contactColumnsWindow_fast contact09 32 4 4290654685528 (by decide +kernel)
private theorem contact09ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact09) 36 4 = 4029743490299 :=
  contactColumnsWindow_fast contact09 36 4 4029743490299 (by decide +kernel)
private theorem contact09ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact09) 40 4 = 3777074763984 :=
  contactColumnsWindow_fast contact09 40 4 3777074763984 (by decide +kernel)
private theorem contact09ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact09) 44 4 = 3532665954924 :=
  contactColumnsWindow_fast contact09 44 4 3532665954924 (by decide +kernel)
private theorem contact09ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact09) 48 4 = 3296528072913 :=
  contactColumnsWindow_fast contact09 48 4 3296528072913 (by decide +kernel)
private theorem contact09ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact09) 52 4 = 3068634326379 :=
  contactColumnsWindow_fast contact09 52 4 3068634326379 (by decide +kernel)
private theorem contact09ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact09) 56 4 = 2848985370264 :=
  contactColumnsWindow_fast contact09 56 4 2848985370264 (by decide +kernel)
private theorem contact09ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact09) 60 4 = 2637580912212 :=
  contactColumnsWindow_fast contact09 60 4 2637580912212 (by decide +kernel)
private theorem contact09ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact09) 64 4 = 2434445377229 :=
  contactColumnsWindow_fast contact09 64 4 2434445377229 (by decide +kernel)
private theorem contact09ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact09) 68 4 = 2239578513276 :=
  contactColumnsWindow_fast contact09 68 4 2239578513276 (by decide +kernel)
private theorem contact09ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact09) 72 4 = 2052960585084 :=
  contactColumnsWindow_fast contact09 72 4 2052960585084 (by decide +kernel)
private theorem contact09ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact09) 76 4 = 1874587916703 :=
  contactColumnsWindow_fast contact09 76 4 1874587916703 (by decide +kernel)
private theorem contact09ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact09) 80 4 = 1704459530694 :=
  contactColumnsWindow_fast contact09 80 4 1704459530694 (by decide +kernel)
private theorem contact09ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact09) 84 4 = 1542604712676 :=
  contactColumnsWindow_fast contact09 84 4 1542604712676 (by decide +kernel)
private theorem contact09ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact09) 88 4 = 1389014558161 :=
  contactColumnsWindow_fast contact09 88 4 1389014558161 (by decide +kernel)
private theorem contact09ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact09) 92 4 = 1243672869690 :=
  contactColumnsWindow_fast contact09 92 4 1243672869690 (by decide +kernel)
private theorem contact09ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact09) 96 4 = 1106576460498 :=
  contactColumnsWindow_fast contact09 96 4 1106576460498 (by decide +kernel)
private theorem contact09ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact09) 100 4 = 977725212152 :=
  contactColumnsWindow_fast contact09 100 4 977725212152 (by decide +kernel)
private theorem contact09ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact09) 104 4 = 857150127258 :=
  contactColumnsWindow_fast contact09 104 4 857150127258 (by decide +kernel)
private theorem contact09ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact09) 108 4 = 744836644159 :=
  contactColumnsWindow_fast contact09 108 4 744836644159 (by decide +kernel)
private theorem contact09ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact09) 112 4 = 640771219837 :=
  contactColumnsWindow_fast contact09 112 4 640771219837 (by decide +kernel)
private theorem contact09ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact09) 116 4 = 544951128690 :=
  contactColumnsWindow_fast contact09 116 4 544951128690 (by decide +kernel)
private theorem contact09ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact09) 120 4 = 457377180890 :=
  contactColumnsWindow_fast contact09 120 4 457377180890 (by decide +kernel)
private theorem contact09ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact09) 124 4 = 378081539937 :=
  contactColumnsWindow_fast contact09 124 4 378081539937 (by decide +kernel)
private theorem contact09ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact09) 128 4 = 307044847422 :=
  contactColumnsWindow_fast contact09 128 4 307044847422 (by decide +kernel)
private theorem contact09ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact09) 132 4 = 244255752055 :=
  contactColumnsWindow_fast contact09 132 4 244255752055 (by decide +kernel)
private theorem contact09ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact09) 136 4 = 189709409757 :=
  contactColumnsWindow_fast contact09 136 4 189709409757 (by decide +kernel)
private theorem contact09ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact09) 140 4 = 143341917249 :=
  contactColumnsWindow_fast contact09 140 4 143341917249 (by decide +kernel)
private theorem contact09ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact09) 144 4 = 104928820067 :=
  contactColumnsWindow_fast contact09 144 4 104928820067 (by decide +kernel)
private theorem contact09ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact09) 148 4 = 74010747156 :=
  contactColumnsWindow_fast contact09 148 4 74010747156 (by decide +kernel)
private theorem contact09ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact09) 152 4 = 49983639691 :=
  contactColumnsWindow_fast contact09 152 4 49983639691 (by decide +kernel)
private theorem contact09ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact09) 156 4 = 32089766824 :=
  contactColumnsWindow_fast contact09 156 4 32089766824 (by decide +kernel)
private theorem contact09ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact09) 160 3 = 15502137463 :=
  contactColumnsWindow_fast contact09 160 3 15502137463 (by decide +kernel)
private theorem contact09ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact09) 0 8 = 13022812885512 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 4 4 6674842130844 6347970754668 contact09ColumnsSlice0 contact09ColumnsSlice4
private theorem contact09ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact09) 8 8 = 11748277082598 :=
  combineSlices (auxiliaryColumnSlice contact09) 8 4 4 6029336119014 5718940963584 contact09ColumnsSlice8 contact09ColumnsSlice12
private theorem contact09ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact09) 16 8 = 10539648785340 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 4 4 5416783422140 5122865363200 contact09ColumnsSlice16 contact09ColumnsSlice20
private theorem contact09ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact09) 24 8 = 9397007271048 :=
  combineSlices (auxiliaryColumnSlice contact09) 24 4 4 4837200775380 4559806495668 contact09ColumnsSlice24 contact09ColumnsSlice28
private theorem contact09ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact09) 32 8 = 8320398175827 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 4 4 4290654685528 4029743490299 contact09ColumnsSlice32 contact09ColumnsSlice36
private theorem contact09ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact09) 40 8 = 7309740718908 :=
  combineSlices (auxiliaryColumnSlice contact09) 40 4 4 3777074763984 3532665954924 contact09ColumnsSlice40 contact09ColumnsSlice44
private theorem contact09ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact09) 48 8 = 6365162399292 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 4 4 3296528072913 3068634326379 contact09ColumnsSlice48 contact09ColumnsSlice52
private theorem contact09ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact09) 56 8 = 5486566282476 :=
  combineSlices (auxiliaryColumnSlice contact09) 56 4 4 2848985370264 2637580912212 contact09ColumnsSlice56 contact09ColumnsSlice60
private theorem contact09ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact09) 64 8 = 4674023890505 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 4 4 2434445377229 2239578513276 contact09ColumnsSlice64 contact09ColumnsSlice68
private theorem contact09ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact09) 72 8 = 3927548501787 :=
  combineSlices (auxiliaryColumnSlice contact09) 72 4 4 2052960585084 1874587916703 contact09ColumnsSlice72 contact09ColumnsSlice76
private theorem contact09ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact09) 80 8 = 3247064243370 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 4 4 1704459530694 1542604712676 contact09ColumnsSlice80 contact09ColumnsSlice84
private theorem contact09ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact09) 88 8 = 2632687427851 :=
  combineSlices (auxiliaryColumnSlice contact09) 88 4 4 1389014558161 1243672869690 contact09ColumnsSlice88 contact09ColumnsSlice92
private theorem contact09ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact09) 96 8 = 2084301672650 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 4 4 1106576460498 977725212152 contact09ColumnsSlice96 contact09ColumnsSlice100
private theorem contact09ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact09) 104 8 = 1601986771417 :=
  combineSlices (auxiliaryColumnSlice contact09) 104 4 4 857150127258 744836644159 contact09ColumnsSlice104 contact09ColumnsSlice108
private theorem contact09ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact09) 112 8 = 1185722348527 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 4 4 640771219837 544951128690 contact09ColumnsSlice112 contact09ColumnsSlice116
private theorem contact09ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact09) 120 8 = 835458720827 :=
  combineSlices (auxiliaryColumnSlice contact09) 120 4 4 457377180890 378081539937 contact09ColumnsSlice120 contact09ColumnsSlice124
private theorem contact09ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact09) 128 8 = 551300599477 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 4 4 307044847422 244255752055 contact09ColumnsSlice128 contact09ColumnsSlice132
private theorem contact09ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact09) 136 8 = 333051327006 :=
  combineSlices (auxiliaryColumnSlice contact09) 136 4 4 189709409757 143341917249 contact09ColumnsSlice136 contact09ColumnsSlice140
private theorem contact09ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact09) 144 8 = 178939567223 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 4 4 104928820067 74010747156 contact09ColumnsSlice144 contact09ColumnsSlice148
private theorem contact09ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact09) 152 8 = 82073406515 :=
  combineSlices (auxiliaryColumnSlice contact09) 152 4 4 49983639691 32089766824 contact09ColumnsSlice152 contact09ColumnsSlice156
private theorem contact09ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact09) 0 16 = 24771089968110 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 8 8 13022812885512 11748277082598 contact09ColumnsJoin0_8 contact09ColumnsJoin8_8
private theorem contact09ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact09) 16 16 = 19936656056388 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 8 8 10539648785340 9397007271048 contact09ColumnsJoin16_8 contact09ColumnsJoin24_8
private theorem contact09ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact09) 32 16 = 15630138894735 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 8 8 8320398175827 7309740718908 contact09ColumnsJoin32_8 contact09ColumnsJoin40_8
private theorem contact09ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact09) 48 16 = 11851728681768 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 8 8 6365162399292 5486566282476 contact09ColumnsJoin48_8 contact09ColumnsJoin56_8
private theorem contact09ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact09) 64 16 = 8601572392292 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 8 8 4674023890505 3927548501787 contact09ColumnsJoin64_8 contact09ColumnsJoin72_8
private theorem contact09ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact09) 80 16 = 5879751671221 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 8 8 3247064243370 2632687427851 contact09ColumnsJoin80_8 contact09ColumnsJoin88_8
private theorem contact09ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact09) 96 16 = 3686288444067 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 8 8 2084301672650 1601986771417 contact09ColumnsJoin96_8 contact09ColumnsJoin104_8
private theorem contact09ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact09) 112 16 = 2021181069354 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 8 8 1185722348527 835458720827 contact09ColumnsJoin112_8 contact09ColumnsJoin120_8
private theorem contact09ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact09) 128 16 = 884351926483 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 8 8 551300599477 333051327006 contact09ColumnsJoin128_8 contact09ColumnsJoin136_8
private theorem contact09ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact09) 144 16 = 261012973738 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 8 8 178939567223 82073406515 contact09ColumnsJoin144_8 contact09ColumnsJoin152_8
private theorem contact09ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact09) 0 32 = 44707746024498 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 16 16 24771089968110 19936656056388 contact09ColumnsJoin0_16 contact09ColumnsJoin16_16
private theorem contact09ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact09) 32 32 = 27481867576503 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 16 16 15630138894735 11851728681768 contact09ColumnsJoin32_16 contact09ColumnsJoin48_16
private theorem contact09ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact09) 64 32 = 14481324063513 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 16 16 8601572392292 5879751671221 contact09ColumnsJoin64_16 contact09ColumnsJoin80_16
private theorem contact09ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact09) 96 32 = 5707469513421 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 16 16 3686288444067 2021181069354 contact09ColumnsJoin96_16 contact09ColumnsJoin112_16
private theorem contact09ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact09) 128 32 = 1145364900221 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 16 16 884351926483 261012973738 contact09ColumnsJoin128_16 contact09ColumnsJoin144_16
private theorem contact09ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact09) 0 64 = 72189613601001 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 32 32 44707746024498 27481867576503 contact09ColumnsJoin0_32 contact09ColumnsJoin32_32
private theorem contact09ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact09) 64 64 = 20188793576934 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 32 32 14481324063513 5707469513421 contact09ColumnsJoin64_32 contact09ColumnsJoin96_32
private theorem contact09ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact09) 128 35 = 1160867037684 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 32 3 1145364900221 15502137463 contact09ColumnsJoin128_32 contact09ColumnsSlice160
private theorem contact09ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact09) 0 128 = 92378407177935 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 64 64 72189613601001 20188793576934 contact09ColumnsJoin0_64 contact09ColumnsJoin64_64
private theorem contact09ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact09) 0 163 = 93539274215619 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 128 35 92378407177935 1160867037684 contact09ColumnsJoin0_128 contact09ColumnsJoin128_35
private theorem contact09OrdinaryRanks : ordinaryRankBound contact09 = 10416628107 := by decide +kernel
private theorem contact09RanksSlice0 : sliceWindow (auxiliaryRankSlice contact09) 0 4 = 25172484 :=
  contactRankWindow_of_rec contact09 0 4 25172484 (by decide +kernel)
private theorem contact09RanksSlice4 : sliceWindow (auxiliaryRankSlice contact09) 4 4 = 23561556 :=
  contactRankWindow_of_rec contact09 4 4 23561556 (by decide +kernel)
private theorem contact09RanksSlice8 : sliceWindow (auxiliaryRankSlice contact09) 8 4 = 22007652 :=
  contactRankWindow_of_rec contact09 8 4 22007652 (by decide +kernel)
private theorem contact09RanksSlice12 : sliceWindow (auxiliaryRankSlice contact09) 12 4 = 20510772 :=
  contactRankWindow_of_rec contact09 12 4 20510772 (by decide +kernel)
private theorem contact09RanksSlice16 : sliceWindow (auxiliaryRankSlice contact09) 16 4 = 19070916 :=
  contactRankWindow_of_rec contact09 16 4 19070916 (by decide +kernel)
private theorem contact09RanksSlice20 : sliceWindow (auxiliaryRankSlice contact09) 20 4 = 17688084 :=
  contactRankWindow_of_rec contact09 20 4 17688084 (by decide +kernel)
private theorem contact09RanksSlice24 : sliceWindow (auxiliaryRankSlice contact09) 24 4 = 16362276 :=
  contactRankWindow_of_rec contact09 24 4 16362276 (by decide +kernel)
private theorem contact09RanksSlice28 : sliceWindow (auxiliaryRankSlice contact09) 28 4 = 15093492 :=
  contactRankWindow_of_rec contact09 28 4 15093492 (by decide +kernel)
private theorem contact09RanksSlice32 : sliceWindow (auxiliaryRankSlice contact09) 32 4 = 13881732 :=
  contactRankWindow_of_rec contact09 32 4 13881732 (by decide +kernel)
private theorem contact09RanksSlice36 : sliceWindow (auxiliaryRankSlice contact09) 36 4 = 12726996 :=
  contactRankWindow_of_rec contact09 36 4 12726996 (by decide +kernel)
private theorem contact09RanksSlice40 : sliceWindow (auxiliaryRankSlice contact09) 40 4 = 11629284 :=
  contactRankWindow_of_rec contact09 40 4 11629284 (by decide +kernel)
private theorem contact09RanksSlice44 : sliceWindow (auxiliaryRankSlice contact09) 44 4 = 10588596 :=
  contactRankWindow_of_rec contact09 44 4 10588596 (by decide +kernel)
private theorem contact09RanksSlice48 : sliceWindow (auxiliaryRankSlice contact09) 48 4 = 9604932 :=
  contactRankWindow_of_rec contact09 48 4 9604932 (by decide +kernel)
private theorem contact09RanksSlice52 : sliceWindow (auxiliaryRankSlice contact09) 52 4 = 8678292 :=
  contactRankWindow_of_rec contact09 52 4 8678292 (by decide +kernel)
private theorem contact09RanksSlice56 : sliceWindow (auxiliaryRankSlice contact09) 56 4 = 7808486 :=
  contactRankWindow_of_rec contact09 56 4 7808486 (by decide +kernel)
private theorem contact09RanksSlice60 : sliceWindow (auxiliaryRankSlice contact09) 60 4 = 6994528 :=
  contactRankWindow_of_rec contact09 60 4 6994528 (by decide +kernel)
private theorem contact09RanksSlice64 : sliceWindow (auxiliaryRankSlice contact09) 64 4 = 6235240 :=
  contactRankWindow_of_rec contact09 64 4 6235240 (by decide +kernel)
private theorem contact09RanksSlice68 : sliceWindow (auxiliaryRankSlice contact09) 68 4 = 5529325 :=
  contactRankWindow_of_rec contact09 68 4 5529325 (by decide +kernel)
private theorem contact09RanksSlice72 : sliceWindow (auxiliaryRankSlice contact09) 72 4 = 4875143 :=
  contactRankWindow_of_rec contact09 72 4 4875143 (by decide +kernel)
private theorem contact09RanksSlice76 : sliceWindow (auxiliaryRankSlice contact09) 76 4 = 4270944 :=
  contactRankWindow_of_rec contact09 76 4 4270944 (by decide +kernel)
private theorem contact09RanksSlice80 : sliceWindow (auxiliaryRankSlice contact09) 80 4 = 3715153 :=
  contactRankWindow_of_rec contact09 80 4 3715153 (by decide +kernel)
private theorem contact09RanksSlice84 : sliceWindow (auxiliaryRankSlice contact09) 84 4 = 3205931 :=
  contactRankWindow_of_rec contact09 84 4 3205931 (by decide +kernel)
private theorem contact09RanksSlice88 : sliceWindow (auxiliaryRankSlice contact09) 88 4 = 2741528 :=
  contactRankWindow_of_rec contact09 88 4 2741528 (by decide +kernel)
private theorem contact09RanksSlice92 : sliceWindow (auxiliaryRankSlice contact09) 92 4 = 2320501 :=
  contactRankWindow_of_rec contact09 92 4 2320501 (by decide +kernel)
private theorem contact09RanksSlice96 : sliceWindow (auxiliaryRankSlice contact09) 96 4 = 1940879 :=
  contactRankWindow_of_rec contact09 96 4 1940879 (by decide +kernel)
private theorem contact09RanksSlice100 : sliceWindow (auxiliaryRankSlice contact09) 100 4 = 1600912 :=
  contactRankWindow_of_rec contact09 100 4 1600912 (by decide +kernel)
private theorem contact09RanksSlice104 : sliceWindow (auxiliaryRankSlice contact09) 104 4 = 1299289 :=
  contactRankWindow_of_rec contact09 104 4 1299289 (by decide +kernel)
private theorem contact09RanksSlice108 : sliceWindow (auxiliaryRankSlice contact09) 108 4 = 1033907 :=
  contactRankWindow_of_rec contact09 108 4 1033907 (by decide +kernel)
private theorem contact09RanksSlice112 : sliceWindow (auxiliaryRankSlice contact09) 112 4 = 803016 :=
  contactRankWindow_of_rec contact09 112 4 803016 (by decide +kernel)
private theorem contact09RanksSlice116 : sliceWindow (auxiliaryRankSlice contact09) 116 4 = 605437 :=
  contactRankWindow_of_rec contact09 116 4 605437 (by decide +kernel)
private theorem contact09RanksSlice120 : sliceWindow (auxiliaryRankSlice contact09) 120 4 = 438935 :=
  contactRankWindow_of_rec contact09 120 4 438935 (by decide +kernel)
private theorem contact09RanksSlice124 : sliceWindow (auxiliaryRankSlice contact09) 124 4 = 301760 :=
  contactRankWindow_of_rec contact09 124 4 301760 (by decide +kernel)
private theorem contact09RanksSlice128 : sliceWindow (auxiliaryRankSlice contact09) 128 4 = 192865 :=
  contactRankWindow_of_rec contact09 128 4 192865 (by decide +kernel)
private theorem contact09RanksSlice132 : sliceWindow (auxiliaryRankSlice contact09) 132 4 = 109883 :=
  contactRankWindow_of_rec contact09 132 4 109883 (by decide +kernel)
private theorem contact09RanksSlice136 : sliceWindow (auxiliaryRankSlice contact09) 136 4 = 51064 :=
  contactRankWindow_of_rec contact09 136 4 51064 (by decide +kernel)
private theorem contact09RanksSlice140 : sliceWindow (auxiliaryRankSlice contact09) 140 4 = 15527 :=
  contactRankWindow_of_rec contact09 140 4 15527 (by decide +kernel)
private theorem contact09RanksSlice144 : sliceWindow (auxiliaryRankSlice contact09) 144 4 = 876 :=
  contactRankWindow_of_rec contact09 144 4 876 (by decide +kernel)
private theorem contact09RanksSlice148 : sliceWindow (auxiliaryRankSlice contact09) 148 15 = 0 :=
  contactRankWindow_of_rec contact09 148 15 0 (by decide +kernel)
private theorem contact09RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact09) 0 8 = 48734040 :=
  combineSlices (auxiliaryRankSlice contact09) 0 4 4 25172484 23561556 contact09RanksSlice0 contact09RanksSlice4
private theorem contact09RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact09) 8 8 = 42518424 :=
  combineSlices (auxiliaryRankSlice contact09) 8 4 4 22007652 20510772 contact09RanksSlice8 contact09RanksSlice12
private theorem contact09RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact09) 16 8 = 36759000 :=
  combineSlices (auxiliaryRankSlice contact09) 16 4 4 19070916 17688084 contact09RanksSlice16 contact09RanksSlice20
private theorem contact09RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact09) 24 8 = 31455768 :=
  combineSlices (auxiliaryRankSlice contact09) 24 4 4 16362276 15093492 contact09RanksSlice24 contact09RanksSlice28
private theorem contact09RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact09) 32 8 = 26608728 :=
  combineSlices (auxiliaryRankSlice contact09) 32 4 4 13881732 12726996 contact09RanksSlice32 contact09RanksSlice36
private theorem contact09RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact09) 40 8 = 22217880 :=
  combineSlices (auxiliaryRankSlice contact09) 40 4 4 11629284 10588596 contact09RanksSlice40 contact09RanksSlice44
private theorem contact09RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact09) 48 8 = 18283224 :=
  combineSlices (auxiliaryRankSlice contact09) 48 4 4 9604932 8678292 contact09RanksSlice48 contact09RanksSlice52
private theorem contact09RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact09) 56 8 = 14803014 :=
  combineSlices (auxiliaryRankSlice contact09) 56 4 4 7808486 6994528 contact09RanksSlice56 contact09RanksSlice60
private theorem contact09RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact09) 64 8 = 11764565 :=
  combineSlices (auxiliaryRankSlice contact09) 64 4 4 6235240 5529325 contact09RanksSlice64 contact09RanksSlice68
private theorem contact09RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact09) 72 8 = 9146087 :=
  combineSlices (auxiliaryRankSlice contact09) 72 4 4 4875143 4270944 contact09RanksSlice72 contact09RanksSlice76
private theorem contact09RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact09) 80 8 = 6921084 :=
  combineSlices (auxiliaryRankSlice contact09) 80 4 4 3715153 3205931 contact09RanksSlice80 contact09RanksSlice84
private theorem contact09RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact09) 88 8 = 5062029 :=
  combineSlices (auxiliaryRankSlice contact09) 88 4 4 2741528 2320501 contact09RanksSlice88 contact09RanksSlice92
private theorem contact09RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact09) 96 8 = 3541791 :=
  combineSlices (auxiliaryRankSlice contact09) 96 4 4 1940879 1600912 contact09RanksSlice96 contact09RanksSlice100
private theorem contact09RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact09) 104 8 = 2333196 :=
  combineSlices (auxiliaryRankSlice contact09) 104 4 4 1299289 1033907 contact09RanksSlice104 contact09RanksSlice108
private theorem contact09RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact09) 112 8 = 1408453 :=
  combineSlices (auxiliaryRankSlice contact09) 112 4 4 803016 605437 contact09RanksSlice112 contact09RanksSlice116
private theorem contact09RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact09) 120 8 = 740695 :=
  combineSlices (auxiliaryRankSlice contact09) 120 4 4 438935 301760 contact09RanksSlice120 contact09RanksSlice124
private theorem contact09RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact09) 128 8 = 302748 :=
  combineSlices (auxiliaryRankSlice contact09) 128 4 4 192865 109883 contact09RanksSlice128 contact09RanksSlice132
private theorem contact09RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact09) 136 8 = 66591 :=
  combineSlices (auxiliaryRankSlice contact09) 136 4 4 51064 15527 contact09RanksSlice136 contact09RanksSlice140
private theorem contact09RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact09) 144 19 = 876 :=
  combineSlices (auxiliaryRankSlice contact09) 144 4 15 876 0 contact09RanksSlice144 contact09RanksSlice148
private theorem contact09RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact09) 0 16 = 91252464 :=
  combineSlices (auxiliaryRankSlice contact09) 0 8 8 48734040 42518424 contact09RanksJoin0_8 contact09RanksJoin8_8
private theorem contact09RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact09) 16 16 = 68214768 :=
  combineSlices (auxiliaryRankSlice contact09) 16 8 8 36759000 31455768 contact09RanksJoin16_8 contact09RanksJoin24_8
private theorem contact09RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact09) 32 16 = 48826608 :=
  combineSlices (auxiliaryRankSlice contact09) 32 8 8 26608728 22217880 contact09RanksJoin32_8 contact09RanksJoin40_8
private theorem contact09RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact09) 48 16 = 33086238 :=
  combineSlices (auxiliaryRankSlice contact09) 48 8 8 18283224 14803014 contact09RanksJoin48_8 contact09RanksJoin56_8
private theorem contact09RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact09) 64 16 = 20910652 :=
  combineSlices (auxiliaryRankSlice contact09) 64 8 8 11764565 9146087 contact09RanksJoin64_8 contact09RanksJoin72_8
private theorem contact09RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact09) 80 16 = 11983113 :=
  combineSlices (auxiliaryRankSlice contact09) 80 8 8 6921084 5062029 contact09RanksJoin80_8 contact09RanksJoin88_8
private theorem contact09RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact09) 96 16 = 5874987 :=
  combineSlices (auxiliaryRankSlice contact09) 96 8 8 3541791 2333196 contact09RanksJoin96_8 contact09RanksJoin104_8
private theorem contact09RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact09) 112 16 = 2149148 :=
  combineSlices (auxiliaryRankSlice contact09) 112 8 8 1408453 740695 contact09RanksJoin112_8 contact09RanksJoin120_8
private theorem contact09RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact09) 128 16 = 369339 :=
  combineSlices (auxiliaryRankSlice contact09) 128 8 8 302748 66591 contact09RanksJoin128_8 contact09RanksJoin136_8
private theorem contact09RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact09) 0 32 = 159467232 :=
  combineSlices (auxiliaryRankSlice contact09) 0 16 16 91252464 68214768 contact09RanksJoin0_16 contact09RanksJoin16_16
private theorem contact09RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact09) 32 32 = 81912846 :=
  combineSlices (auxiliaryRankSlice contact09) 32 16 16 48826608 33086238 contact09RanksJoin32_16 contact09RanksJoin48_16
private theorem contact09RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact09) 64 32 = 32893765 :=
  combineSlices (auxiliaryRankSlice contact09) 64 16 16 20910652 11983113 contact09RanksJoin64_16 contact09RanksJoin80_16
private theorem contact09RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact09) 96 32 = 8024135 :=
  combineSlices (auxiliaryRankSlice contact09) 96 16 16 5874987 2149148 contact09RanksJoin96_16 contact09RanksJoin112_16
private theorem contact09RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact09) 128 35 = 370215 :=
  combineSlices (auxiliaryRankSlice contact09) 128 16 19 369339 876 contact09RanksJoin128_16 contact09RanksJoin144_19
private theorem contact09RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact09) 0 64 = 241380078 :=
  combineSlices (auxiliaryRankSlice contact09) 0 32 32 159467232 81912846 contact09RanksJoin0_32 contact09RanksJoin32_32
private theorem contact09RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact09) 64 64 = 40917900 :=
  combineSlices (auxiliaryRankSlice contact09) 64 32 32 32893765 8024135 contact09RanksJoin64_32 contact09RanksJoin96_32
private theorem contact09RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact09) 0 128 = 282297978 :=
  combineSlices (auxiliaryRankSlice contact09) 0 64 64 241380078 40917900 contact09RanksJoin0_64 contact09RanksJoin64_64
private theorem contact09RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact09) 0 163 = 282668193 :=
  combineSlices (auxiliaryRankSlice contact09) 0 128 35 282297978 370215 contact09RanksJoin0_128 contact09RanksJoin128_35
theorem contact09_margin : sourceMargin contact09 :=
  margin_of_checked_counts contact09 163 2711217976880244 93539274215619 10416628107 282668193 rfl contact09OrdinaryColumns contact09ColumnsJoin0_163 contact09OrdinaryRanks contact09RanksJoin0_163 (by decide +kernel)

private theorem contact11OrdinaryColumns : ordinaryColumnCount contact11 = 212282755866085 := by decide +kernel
private theorem contact11ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact11) 0 4 = 913645315472 :=
  contactColumnsWindow_fast contact11 0 4 913645315472 (by decide +kernel)
private theorem contact11ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact11) 4 4 = 839563533850 :=
  contactColumnsWindow_fast contact11 4 4 839563533850 (by decide +kernel)
private theorem contact11ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact11) 8 4 = 768643648868 :=
  contactColumnsWindow_fast contact11 8 4 768643648868 (by decide +kernel)
private theorem contact11ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact11) 12 4 = 700871503812 :=
  contactColumnsWindow_fast contact11 12 4 700871503812 (by decide +kernel)
private theorem contact11ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact11) 16 4 = 636244742436 :=
  contactColumnsWindow_fast contact11 16 4 636244742436 (by decide +kernel)
private theorem contact11ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact11) 20 4 = 574761965205 :=
  contactColumnsWindow_fast contact11 20 4 574761965205 (by decide +kernel)
private theorem contact11ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact11) 24 4 = 516427783126 :=
  contactColumnsWindow_fast contact11 24 4 516427783126 (by decide +kernel)
private theorem contact11ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact11) 28 4 = 461256913850 :=
  contactColumnsWindow_fast contact11 28 4 461256913850 (by decide +kernel)
private theorem contact11ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact11) 32 4 = 409235294388 :=
  contactColumnsWindow_fast contact11 32 4 409235294388 (by decide +kernel)
private theorem contact11ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact11) 36 4 = 360359123364 :=
  contactColumnsWindow_fast contact11 36 4 360359123364 (by decide +kernel)
private theorem contact11ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact11) 40 4 = 314627036091 :=
  contactColumnsWindow_fast contact11 40 4 314627036091 (by decide +kernel)
private theorem contact11ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact11) 44 4 = 272044575802 :=
  contactColumnsWindow_fast contact11 44 4 272044575802 (by decide +kernel)
private theorem contact11ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact11) 48 4 = 232625634740 :=
  contactColumnsWindow_fast contact11 48 4 232625634740 (by decide +kernel)
private theorem contact11ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact11) 52 4 = 196354761828 :=
  contactColumnsWindow_fast contact11 52 4 196354761828 (by decide +kernel)
private theorem contact11ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact11) 56 4 = 163229103732 :=
  contactColumnsWindow_fast contact11 56 4 163229103732 (by decide +kernel)
private theorem contact11ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact11) 60 4 = 133247706417 :=
  contactColumnsWindow_fast contact11 60 4 133247706417 (by decide +kernel)
private theorem contact11ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact11) 64 4 = 106417351077 :=
  contactColumnsWindow_fast contact11 64 4 106417351077 (by decide +kernel)
private theorem contact11ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact11) 68 4 = 82750026836 :=
  contactColumnsWindow_fast contact11 68 4 82750026836 (by decide +kernel)
private theorem contact11ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact11) 72 4 = 62229828708 :=
  contactColumnsWindow_fast contact11 72 4 62229828708 (by decide +kernel)
private theorem contact11ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact11) 76 4 = 44854683540 :=
  contactColumnsWindow_fast contact11 76 4 44854683540 (by decide +kernel)
private theorem contact11ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact11) 80 4 = 30623920249 :=
  contactColumnsWindow_fast contact11 80 4 30623920249 (by decide +kernel)
private theorem contact11ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact11) 84 4 = 19524039903 :=
  contactColumnsWindow_fast contact11 84 4 19524039903 (by decide +kernel)
private theorem contact11ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact11) 88 4 = 11417844301 :=
  contactColumnsWindow_fast contact11 88 4 11417844301 (by decide +kernel)
private theorem contact11ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact11) 92 4 = 5971670439 :=
  contactColumnsWindow_fast contact11 92 4 5971670439 (by decide +kernel)
private theorem contact11ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact11) 96 1 = 910182909 :=
  contactColumnsWindow_fast contact11 96 1 910182909 (by decide +kernel)
private theorem contact11ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact11) 0 8 = 1753208849322 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 4 4 913645315472 839563533850 contact11ColumnsSlice0 contact11ColumnsSlice4
private theorem contact11ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact11) 8 8 = 1469515152680 :=
  combineSlices (auxiliaryColumnSlice contact11) 8 4 4 768643648868 700871503812 contact11ColumnsSlice8 contact11ColumnsSlice12
private theorem contact11ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact11) 16 8 = 1211006707641 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 4 4 636244742436 574761965205 contact11ColumnsSlice16 contact11ColumnsSlice20
private theorem contact11ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact11) 24 8 = 977684696976 :=
  combineSlices (auxiliaryColumnSlice contact11) 24 4 4 516427783126 461256913850 contact11ColumnsSlice24 contact11ColumnsSlice28
private theorem contact11ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact11) 32 8 = 769594417752 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 4 4 409235294388 360359123364 contact11ColumnsSlice32 contact11ColumnsSlice36
private theorem contact11ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact11) 40 8 = 586671611893 :=
  combineSlices (auxiliaryColumnSlice contact11) 40 4 4 314627036091 272044575802 contact11ColumnsSlice40 contact11ColumnsSlice44
private theorem contact11ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact11) 48 8 = 428980396568 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 4 4 232625634740 196354761828 contact11ColumnsSlice48 contact11ColumnsSlice52
private theorem contact11ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact11) 56 8 = 296476810149 :=
  combineSlices (auxiliaryColumnSlice contact11) 56 4 4 163229103732 133247706417 contact11ColumnsSlice56 contact11ColumnsSlice60
private theorem contact11ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact11) 64 8 = 189167377913 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 4 4 106417351077 82750026836 contact11ColumnsSlice64 contact11ColumnsSlice68
private theorem contact11ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact11) 72 8 = 107084512248 :=
  combineSlices (auxiliaryColumnSlice contact11) 72 4 4 62229828708 44854683540 contact11ColumnsSlice72 contact11ColumnsSlice76
private theorem contact11ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact11) 80 8 = 50147960152 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 4 4 30623920249 19524039903 contact11ColumnsSlice80 contact11ColumnsSlice84
private theorem contact11ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact11) 88 8 = 17389514740 :=
  combineSlices (auxiliaryColumnSlice contact11) 88 4 4 11417844301 5971670439 contact11ColumnsSlice88 contact11ColumnsSlice92
private theorem contact11ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact11) 0 16 = 3222724002002 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 8 8 1753208849322 1469515152680 contact11ColumnsJoin0_8 contact11ColumnsJoin8_8
private theorem contact11ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact11) 16 16 = 2188691404617 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 8 8 1211006707641 977684696976 contact11ColumnsJoin16_8 contact11ColumnsJoin24_8
private theorem contact11ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact11) 32 16 = 1356266029645 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 8 8 769594417752 586671611893 contact11ColumnsJoin32_8 contact11ColumnsJoin40_8
private theorem contact11ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact11) 48 16 = 725457206717 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 8 8 428980396568 296476810149 contact11ColumnsJoin48_8 contact11ColumnsJoin56_8
private theorem contact11ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact11) 64 16 = 296251890161 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 8 8 189167377913 107084512248 contact11ColumnsJoin64_8 contact11ColumnsJoin72_8
private theorem contact11ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact11) 80 16 = 67537474892 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 8 8 50147960152 17389514740 contact11ColumnsJoin80_8 contact11ColumnsJoin88_8
private theorem contact11ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact11) 0 32 = 5411415406619 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 16 16 3222724002002 2188691404617 contact11ColumnsJoin0_16 contact11ColumnsJoin16_16
private theorem contact11ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact11) 32 32 = 2081723236362 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 16 16 1356266029645 725457206717 contact11ColumnsJoin32_16 contact11ColumnsJoin48_16
private theorem contact11ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact11) 64 32 = 363789365053 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 16 16 296251890161 67537474892 contact11ColumnsJoin64_16 contact11ColumnsJoin80_16
private theorem contact11ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact11) 0 64 = 7493138642981 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 32 32 5411415406619 2081723236362 contact11ColumnsJoin0_32 contact11ColumnsJoin32_32
private theorem contact11ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact11) 64 33 = 364699547962 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 32 1 363789365053 910182909 contact11ColumnsJoin64_32 contact11ColumnsSlice96
private theorem contact11ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact11) 0 97 = 7857838190943 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 64 33 7493138642981 364699547962 contact11ColumnsJoin0_64 contact11ColumnsJoin64_33
private theorem contact11OrdinaryRanks : ordinaryRankBound contact11 = 816008003 := by decide +kernel
private theorem contact11RanksSlice0 : sliceWindow (auxiliaryRankSlice contact11) 0 4 = 3423580 :=
  contactRankWindow_of_rec contact11 0 4 3423580 (by decide +kernel)
private theorem contact11RanksSlice4 : sliceWindow (auxiliaryRankSlice contact11) 4 4 = 3061820 :=
  contactRankWindow_of_rec contact11 4 4 3061820 (by decide +kernel)
private theorem contact11RanksSlice8 : sliceWindow (auxiliaryRankSlice contact11) 8 4 = 2721820 :=
  contactRankWindow_of_rec contact11 8 4 2721820 (by decide +kernel)
private theorem contact11RanksSlice12 : sliceWindow (auxiliaryRankSlice contact11) 12 4 = 2403580 :=
  contactRankWindow_of_rec contact11 12 4 2403580 (by decide +kernel)
private theorem contact11RanksSlice16 : sliceWindow (auxiliaryRankSlice contact11) 16 4 = 2107100 :=
  contactRankWindow_of_rec contact11 16 4 2107100 (by decide +kernel)
private theorem contact11RanksSlice20 : sliceWindow (auxiliaryRankSlice contact11) 20 4 = 1832380 :=
  contactRankWindow_of_rec contact11 20 4 1832380 (by decide +kernel)
private theorem contact11RanksSlice24 : sliceWindow (auxiliaryRankSlice contact11) 24 4 = 1579420 :=
  contactRankWindow_of_rec contact11 24 4 1579420 (by decide +kernel)
private theorem contact11RanksSlice28 : sliceWindow (auxiliaryRankSlice contact11) 28 4 = 1348220 :=
  contactRankWindow_of_rec contact11 28 4 1348220 (by decide +kernel)
private theorem contact11RanksSlice32 : sliceWindow (auxiliaryRankSlice contact11) 32 4 = 1138763 :=
  contactRankWindow_of_rec contact11 32 4 1138763 (by decide +kernel)
private theorem contact11RanksSlice36 : sliceWindow (auxiliaryRankSlice contact11) 36 4 = 950687 :=
  contactRankWindow_of_rec contact11 36 4 950687 (by decide +kernel)
private theorem contact11RanksSlice40 : sliceWindow (auxiliaryRankSlice contact11) 40 4 = 783210 :=
  contactRankWindow_of_rec contact11 40 4 783210 (by decide +kernel)
private theorem contact11RanksSlice44 : sliceWindow (auxiliaryRankSlice contact11) 44 4 = 635320 :=
  contactRankWindow_of_rec contact11 44 4 635320 (by decide +kernel)
private theorem contact11RanksSlice48 : sliceWindow (auxiliaryRankSlice contact11) 48 4 = 505939 :=
  contactRankWindow_of_rec contact11 48 4 505939 (by decide +kernel)
private theorem contact11RanksSlice52 : sliceWindow (auxiliaryRankSlice contact11) 52 4 = 394094 :=
  contactRankWindow_of_rec contact11 52 4 394094 (by decide +kernel)
private theorem contact11RanksSlice56 : sliceWindow (auxiliaryRankSlice contact11) 56 4 = 298652 :=
  contactRankWindow_of_rec contact11 56 4 298652 (by decide +kernel)
private theorem contact11RanksSlice60 : sliceWindow (auxiliaryRankSlice contact11) 60 4 = 218535 :=
  contactRankWindow_of_rec contact11 60 4 218535 (by decide +kernel)
private theorem contact11RanksSlice64 : sliceWindow (auxiliaryRankSlice contact11) 64 4 = 152850 :=
  contactRankWindow_of_rec contact11 64 4 152850 (by decide +kernel)
private theorem contact11RanksSlice68 : sliceWindow (auxiliaryRankSlice contact11) 68 4 = 100384 :=
  contactRankWindow_of_rec contact11 68 4 100384 (by decide +kernel)
private theorem contact11RanksSlice72 : sliceWindow (auxiliaryRankSlice contact11) 72 4 = 60059 :=
  contactRankWindow_of_rec contact11 72 4 60059 (by decide +kernel)
private theorem contact11RanksSlice76 : sliceWindow (auxiliaryRankSlice contact11) 76 4 = 31062 :=
  contactRankWindow_of_rec contact11 76 4 31062 (by decide +kernel)
private theorem contact11RanksSlice80 : sliceWindow (auxiliaryRankSlice contact11) 80 4 = 12100 :=
  contactRankWindow_of_rec contact11 80 4 12100 (by decide +kernel)
private theorem contact11RanksSlice84 : sliceWindow (auxiliaryRankSlice contact11) 84 4 = 2100 :=
  contactRankWindow_of_rec contact11 84 4 2100 (by decide +kernel)
private theorem contact11RanksSlice88 : sliceWindow (auxiliaryRankSlice contact11) 88 9 = 0 :=
  contactRankWindow_of_rec contact11 88 9 0 (by decide +kernel)
private theorem contact11RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact11) 0 8 = 6485400 :=
  combineSlices (auxiliaryRankSlice contact11) 0 4 4 3423580 3061820 contact11RanksSlice0 contact11RanksSlice4
private theorem contact11RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact11) 8 8 = 5125400 :=
  combineSlices (auxiliaryRankSlice contact11) 8 4 4 2721820 2403580 contact11RanksSlice8 contact11RanksSlice12
private theorem contact11RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact11) 16 8 = 3939480 :=
  combineSlices (auxiliaryRankSlice contact11) 16 4 4 2107100 1832380 contact11RanksSlice16 contact11RanksSlice20
private theorem contact11RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact11) 24 8 = 2927640 :=
  combineSlices (auxiliaryRankSlice contact11) 24 4 4 1579420 1348220 contact11RanksSlice24 contact11RanksSlice28
private theorem contact11RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact11) 32 8 = 2089450 :=
  combineSlices (auxiliaryRankSlice contact11) 32 4 4 1138763 950687 contact11RanksSlice32 contact11RanksSlice36
private theorem contact11RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact11) 40 8 = 1418530 :=
  combineSlices (auxiliaryRankSlice contact11) 40 4 4 783210 635320 contact11RanksSlice40 contact11RanksSlice44
private theorem contact11RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact11) 48 8 = 900033 :=
  combineSlices (auxiliaryRankSlice contact11) 48 4 4 505939 394094 contact11RanksSlice48 contact11RanksSlice52
private theorem contact11RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact11) 56 8 = 517187 :=
  combineSlices (auxiliaryRankSlice contact11) 56 4 4 298652 218535 contact11RanksSlice56 contact11RanksSlice60
private theorem contact11RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact11) 64 8 = 253234 :=
  combineSlices (auxiliaryRankSlice contact11) 64 4 4 152850 100384 contact11RanksSlice64 contact11RanksSlice68
private theorem contact11RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact11) 72 8 = 91121 :=
  combineSlices (auxiliaryRankSlice contact11) 72 4 4 60059 31062 contact11RanksSlice72 contact11RanksSlice76
private theorem contact11RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact11) 80 8 = 14200 :=
  combineSlices (auxiliaryRankSlice contact11) 80 4 4 12100 2100 contact11RanksSlice80 contact11RanksSlice84
private theorem contact11RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact11) 0 16 = 11610800 :=
  combineSlices (auxiliaryRankSlice contact11) 0 8 8 6485400 5125400 contact11RanksJoin0_8 contact11RanksJoin8_8
private theorem contact11RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact11) 16 16 = 6867120 :=
  combineSlices (auxiliaryRankSlice contact11) 16 8 8 3939480 2927640 contact11RanksJoin16_8 contact11RanksJoin24_8
private theorem contact11RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact11) 32 16 = 3507980 :=
  combineSlices (auxiliaryRankSlice contact11) 32 8 8 2089450 1418530 contact11RanksJoin32_8 contact11RanksJoin40_8
private theorem contact11RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact11) 48 16 = 1417220 :=
  combineSlices (auxiliaryRankSlice contact11) 48 8 8 900033 517187 contact11RanksJoin48_8 contact11RanksJoin56_8
private theorem contact11RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact11) 64 16 = 344355 :=
  combineSlices (auxiliaryRankSlice contact11) 64 8 8 253234 91121 contact11RanksJoin64_8 contact11RanksJoin72_8
private theorem contact11RanksJoin80_17 : sliceWindow (auxiliaryRankSlice contact11) 80 17 = 14200 :=
  combineSlices (auxiliaryRankSlice contact11) 80 8 9 14200 0 contact11RanksJoin80_8 contact11RanksSlice88
private theorem contact11RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact11) 0 32 = 18477920 :=
  combineSlices (auxiliaryRankSlice contact11) 0 16 16 11610800 6867120 contact11RanksJoin0_16 contact11RanksJoin16_16
private theorem contact11RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact11) 32 32 = 4925200 :=
  combineSlices (auxiliaryRankSlice contact11) 32 16 16 3507980 1417220 contact11RanksJoin32_16 contact11RanksJoin48_16
private theorem contact11RanksJoin64_33 : sliceWindow (auxiliaryRankSlice contact11) 64 33 = 358555 :=
  combineSlices (auxiliaryRankSlice contact11) 64 16 17 344355 14200 contact11RanksJoin64_16 contact11RanksJoin80_17
private theorem contact11RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact11) 0 64 = 23403120 :=
  combineSlices (auxiliaryRankSlice contact11) 0 32 32 18477920 4925200 contact11RanksJoin0_32 contact11RanksJoin32_32
private theorem contact11RanksJoin0_97 : sliceWindow (auxiliaryRankSlice contact11) 0 97 = 23761675 :=
  combineSlices (auxiliaryRankSlice contact11) 0 64 33 23403120 358555 contact11RanksJoin0_64 contact11RanksJoin64_33
theorem contact11_margin : sourceMargin contact11 :=
  margin_of_checked_counts contact11 97 212282755866085 7857838190943 816008003 23761675 rfl contact11OrdinaryColumns contact11ColumnsJoin0_97 contact11OrdinaryRanks contact11RanksJoin0_97 (by decide +kernel)

private theorem contact13OrdinaryColumns : ordinaryColumnCount contact13 = 417151542841979 := by decide +kernel
private theorem contact13ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact13) 0 4 = 3650250210606 :=
  contactColumnsWindow_fast contact13 0 4 3650250210606 (by decide +kernel)
private theorem contact13ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact13) 4 4 = 3429290337972 :=
  contactColumnsWindow_fast contact13 4 4 3429290337972 (by decide +kernel)
private theorem contact13ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact13) 8 4 = 3215274400708 :=
  contactColumnsWindow_fast contact13 8 4 3215274400708 (by decide +kernel)
private theorem contact13ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact13) 12 4 = 3008194999124 :=
  contactColumnsWindow_fast contact13 12 4 3008194999124 (by decide +kernel)
private theorem contact13ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact13) 16 4 = 2808049992009 :=
  contactColumnsWindow_fast contact13 16 4 2808049992009 (by decide +kernel)
private theorem contact13ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact13) 20 4 = 2614848401978 :=
  contactColumnsWindow_fast contact13 20 4 2614848401978 (by decide +kernel)
private theorem contact13ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact13) 24 4 = 2428625281554 :=
  contactColumnsWindow_fast contact13 24 4 2428625281554 (by decide +kernel)
private theorem contact13ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact13) 28 4 = 2249347294108 :=
  contactColumnsWindow_fast contact13 28 4 2249347294108 (by decide +kernel)
private theorem contact13ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact13) 32 4 = 2077008391088 :=
  contactColumnsWindow_fast contact13 32 4 2077008391088 (by decide +kernel)
private theorem contact13ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact13) 36 4 = 1911607363323 :=
  contactColumnsWindow_fast contact13 36 4 1911607363323 (by decide +kernel)
private theorem contact13ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact13) 40 4 = 1753152261410 :=
  contactColumnsWindow_fast contact13 40 4 1753152261410 (by decide +kernel)
private theorem contact13ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact13) 44 4 = 1601675907240 :=
  contactColumnsWindow_fast contact13 44 4 1601675907240 (by decide +kernel)
private theorem contact13ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact13) 48 4 = 1457141994256 :=
  contactColumnsWindow_fast contact13 48 4 1457141994256 (by decide +kernel)
private theorem contact13ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact13) 52 4 = 1319547370052 :=
  contactColumnsWindow_fast contact13 52 4 1319547370052 (by decide +kernel)
private theorem contact13ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact13) 56 4 = 1188890321637 :=
  contactColumnsWindow_fast contact13 56 4 1188890321637 (by decide +kernel)
private theorem contact13ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact13) 60 4 = 1065182398707 :=
  contactColumnsWindow_fast contact13 60 4 1065182398707 (by decide +kernel)
private theorem contact13ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact13) 64 4 = 948452241372 :=
  contactColumnsWindow_fast contact13 64 4 948452241372 (by decide +kernel)
private theorem contact13ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact13) 68 4 = 838662292564 :=
  contactColumnsWindow_fast contact13 68 4 838662292564 (by decide +kernel)
private theorem contact13ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact13) 72 4 = 735811936016 :=
  contactColumnsWindow_fast contact13 72 4 735811936016 (by decide +kernel)
private theorem contact13ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact13) 76 4 = 639898951876 :=
  contactColumnsWindow_fast contact13 76 4 639898951876 (by decide +kernel)
private theorem contact13ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact13) 80 4 = 550938812973 :=
  contactColumnsWindow_fast contact13 80 4 550938812973 (by decide +kernel)
private theorem contact13ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact13) 84 4 = 468954162504 :=
  contactColumnsWindow_fast contact13 84 4 468954162504 (by decide +kernel)
private theorem contact13ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact13) 88 4 = 393908324971 :=
  contactColumnsWindow_fast contact13 88 4 393908324971 (by decide +kernel)
private theorem contact13ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact13) 92 4 = 325802088980 :=
  contactColumnsWindow_fast contact13 92 4 325802088980 (by decide +kernel)
private theorem contact13ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact13) 96 4 = 264633210640 :=
  contactColumnsWindow_fast contact13 96 4 264633210640 (by decide +kernel)
private theorem contact13ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact13) 100 4 = 210420871465 :=
  contactColumnsWindow_fast contact13 100 4 210420871465 (by decide +kernel)
private theorem contact13ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact13) 104 4 = 163181670636 :=
  contactColumnsWindow_fast contact13 104 4 163181670636 (by decide +kernel)
private theorem contact13ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact13) 108 4 = 122869485990 :=
  contactColumnsWindow_fast contact13 108 4 122869485990 (by decide +kernel)
private theorem contact13ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact13) 112 4 = 89371414321 :=
  contactColumnsWindow_fast contact13 112 4 89371414321 (by decide +kernel)
private theorem contact13ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact13) 116 4 = 62393668830 :=
  contactColumnsWindow_fast contact13 116 4 62393668830 (by decide +kernel)
private theorem contact13ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact13) 120 4 = 41500185057 :=
  contactColumnsWindow_fast contact13 120 4 41500185057 (by decide +kernel)
private theorem contact13ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact13) 124 4 = 26070352375 :=
  contactColumnsWindow_fast contact13 124 4 26070352375 (by decide +kernel)
private theorem contact13ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact13) 0 8 = 7079540548578 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 4 4 3650250210606 3429290337972 contact13ColumnsSlice0 contact13ColumnsSlice4
private theorem contact13ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact13) 8 8 = 6223469399832 :=
  combineSlices (auxiliaryColumnSlice contact13) 8 4 4 3215274400708 3008194999124 contact13ColumnsSlice8 contact13ColumnsSlice12
private theorem contact13ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact13) 16 8 = 5422898393987 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 4 4 2808049992009 2614848401978 contact13ColumnsSlice16 contact13ColumnsSlice20
private theorem contact13ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact13) 24 8 = 4677972575662 :=
  combineSlices (auxiliaryColumnSlice contact13) 24 4 4 2428625281554 2249347294108 contact13ColumnsSlice24 contact13ColumnsSlice28
private theorem contact13ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact13) 32 8 = 3988615754411 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 4 4 2077008391088 1911607363323 contact13ColumnsSlice32 contact13ColumnsSlice36
private theorem contact13ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact13) 40 8 = 3354828168650 :=
  combineSlices (auxiliaryColumnSlice contact13) 40 4 4 1753152261410 1601675907240 contact13ColumnsSlice40 contact13ColumnsSlice44
private theorem contact13ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact13) 48 8 = 2776689364308 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 4 4 1457141994256 1319547370052 contact13ColumnsSlice48 contact13ColumnsSlice52
private theorem contact13ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact13) 56 8 = 2254072720344 :=
  combineSlices (auxiliaryColumnSlice contact13) 56 4 4 1188890321637 1065182398707 contact13ColumnsSlice56 contact13ColumnsSlice60
private theorem contact13ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact13) 64 8 = 1787114533936 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 4 4 948452241372 838662292564 contact13ColumnsSlice64 contact13ColumnsSlice68
private theorem contact13ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact13) 72 8 = 1375710887892 :=
  combineSlices (auxiliaryColumnSlice contact13) 72 4 4 735811936016 639898951876 contact13ColumnsSlice72 contact13ColumnsSlice76
private theorem contact13ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact13) 80 8 = 1019892975477 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 4 4 550938812973 468954162504 contact13ColumnsSlice80 contact13ColumnsSlice84
private theorem contact13ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact13) 88 8 = 719710413951 :=
  combineSlices (auxiliaryColumnSlice contact13) 88 4 4 393908324971 325802088980 contact13ColumnsSlice88 contact13ColumnsSlice92
private theorem contact13ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact13) 96 8 = 475054082105 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 4 4 264633210640 210420871465 contact13ColumnsSlice96 contact13ColumnsSlice100
private theorem contact13ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact13) 104 8 = 286051156626 :=
  combineSlices (auxiliaryColumnSlice contact13) 104 4 4 163181670636 122869485990 contact13ColumnsSlice104 contact13ColumnsSlice108
private theorem contact13ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact13) 112 8 = 151765083151 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 4 4 89371414321 62393668830 contact13ColumnsSlice112 contact13ColumnsSlice116
private theorem contact13ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact13) 120 8 = 67570537432 :=
  combineSlices (auxiliaryColumnSlice contact13) 120 4 4 41500185057 26070352375 contact13ColumnsSlice120 contact13ColumnsSlice124
private theorem contact13ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact13) 0 16 = 13303009948410 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 8 8 7079540548578 6223469399832 contact13ColumnsJoin0_8 contact13ColumnsJoin8_8
private theorem contact13ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact13) 16 16 = 10100870969649 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 8 8 5422898393987 4677972575662 contact13ColumnsJoin16_8 contact13ColumnsJoin24_8
private theorem contact13ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact13) 32 16 = 7343443923061 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 8 8 3988615754411 3354828168650 contact13ColumnsJoin32_8 contact13ColumnsJoin40_8
private theorem contact13ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact13) 48 16 = 5030762084652 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 8 8 2776689364308 2254072720344 contact13ColumnsJoin48_8 contact13ColumnsJoin56_8
private theorem contact13ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact13) 64 16 = 3162825421828 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 8 8 1787114533936 1375710887892 contact13ColumnsJoin64_8 contact13ColumnsJoin72_8
private theorem contact13ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact13) 80 16 = 1739603389428 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 8 8 1019892975477 719710413951 contact13ColumnsJoin80_8 contact13ColumnsJoin88_8
private theorem contact13ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact13) 96 16 = 761105238731 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 8 8 475054082105 286051156626 contact13ColumnsJoin96_8 contact13ColumnsJoin104_8
private theorem contact13ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact13) 112 16 = 219335620583 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 8 8 151765083151 67570537432 contact13ColumnsJoin112_8 contact13ColumnsJoin120_8
private theorem contact13ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact13) 0 32 = 23403880918059 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 16 16 13303009948410 10100870969649 contact13ColumnsJoin0_16 contact13ColumnsJoin16_16
private theorem contact13ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact13) 32 32 = 12374206007713 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 16 16 7343443923061 5030762084652 contact13ColumnsJoin32_16 contact13ColumnsJoin48_16
private theorem contact13ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact13) 64 32 = 4902428811256 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 16 16 3162825421828 1739603389428 contact13ColumnsJoin64_16 contact13ColumnsJoin80_16
private theorem contact13ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact13) 96 32 = 980440859314 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 16 16 761105238731 219335620583 contact13ColumnsJoin96_16 contact13ColumnsJoin112_16
private theorem contact13ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact13) 0 64 = 35778086925772 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 32 32 23403880918059 12374206007713 contact13ColumnsJoin0_32 contact13ColumnsJoin32_32
private theorem contact13ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact13) 64 64 = 5882869670570 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 32 32 4902428811256 980440859314 contact13ColumnsJoin64_32 contact13ColumnsJoin96_32
private theorem contact13ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact13) 0 128 = 41660956596342 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 64 64 35778086925772 5882869670570 contact13ColumnsJoin0_64 contact13ColumnsJoin64_64
private theorem contact13OrdinaryRanks : ordinaryRankBound contact13 = 1622911107 := by decide +kernel
private theorem contact13RanksSlice0 : sliceWindow (auxiliaryRankSlice contact13) 0 4 = 13693114 :=
  contactRankWindow_of_rec contact13 0 4 13693114 (by decide +kernel)
private theorem contact13RanksSlice4 : sliceWindow (auxiliaryRankSlice contact13) 4 4 = 12619114 :=
  contactRankWindow_of_rec contact13 4 4 12619114 (by decide +kernel)
private theorem contact13RanksSlice8 : sliceWindow (auxiliaryRankSlice contact13) 8 4 = 11593114 :=
  contactRankWindow_of_rec contact13 8 4 11593114 (by decide +kernel)
private theorem contact13RanksSlice12 : sliceWindow (auxiliaryRankSlice contact13) 12 4 = 10615114 :=
  contactRankWindow_of_rec contact13 12 4 10615114 (by decide +kernel)
private theorem contact13RanksSlice16 : sliceWindow (auxiliaryRankSlice contact13) 16 4 = 9685114 :=
  contactRankWindow_of_rec contact13 16 4 9685114 (by decide +kernel)
private theorem contact13RanksSlice20 : sliceWindow (auxiliaryRankSlice contact13) 20 4 = 8803114 :=
  contactRankWindow_of_rec contact13 20 4 8803114 (by decide +kernel)
private theorem contact13RanksSlice24 : sliceWindow (auxiliaryRankSlice contact13) 24 4 = 7969114 :=
  contactRankWindow_of_rec contact13 24 4 7969114 (by decide +kernel)
private theorem contact13RanksSlice28 : sliceWindow (auxiliaryRankSlice contact13) 28 4 = 7183114 :=
  contactRankWindow_of_rec contact13 28 4 7183114 (by decide +kernel)
private theorem contact13RanksSlice32 : sliceWindow (auxiliaryRankSlice contact13) 32 4 = 6445114 :=
  contactRankWindow_of_rec contact13 32 4 6445114 (by decide +kernel)
private theorem contact13RanksSlice36 : sliceWindow (auxiliaryRankSlice contact13) 36 4 = 5755089 :=
  contactRankWindow_of_rec contact13 36 4 5755089 (by decide +kernel)
private theorem contact13RanksSlice40 : sliceWindow (auxiliaryRankSlice contact13) 40 4 = 5112509 :=
  contactRankWindow_of_rec contact13 40 4 5112509 (by decide +kernel)
private theorem contact13RanksSlice44 : sliceWindow (auxiliaryRankSlice contact13) 44 4 = 4516295 :=
  contactRankWindow_of_rec contact13 44 4 4516295 (by decide +kernel)
private theorem contact13RanksSlice48 : sliceWindow (auxiliaryRankSlice contact13) 48 4 = 3965258 :=
  contactRankWindow_of_rec contact13 48 4 3965258 (by decide +kernel)
private theorem contact13RanksSlice52 : sliceWindow (auxiliaryRankSlice contact13) 52 4 = 3457914 :=
  contactRankWindow_of_rec contact13 52 4 3457914 (by decide +kernel)
private theorem contact13RanksSlice56 : sliceWindow (auxiliaryRankSlice contact13) 56 4 = 2992639 :=
  contactRankWindow_of_rec contact13 56 4 2992639 (by decide +kernel)
private theorem contact13RanksSlice60 : sliceWindow (auxiliaryRankSlice contact13) 60 4 = 2567990 :=
  contactRankWindow_of_rec contact13 60 4 2567990 (by decide +kernel)
private theorem contact13RanksSlice64 : sliceWindow (auxiliaryRankSlice contact13) 64 4 = 2182298 :=
  contactRankWindow_of_rec contact13 64 4 2182298 (by decide +kernel)
private theorem contact13RanksSlice68 : sliceWindow (auxiliaryRankSlice contact13) 68 4 = 1833943 :=
  contactRankWindow_of_rec contact13 68 4 1833943 (by decide +kernel)
private theorem contact13RanksSlice72 : sliceWindow (auxiliaryRankSlice contact13) 72 4 = 1521602 :=
  contactRankWindow_of_rec contact13 72 4 1521602 (by decide +kernel)
private theorem contact13RanksSlice76 : sliceWindow (auxiliaryRankSlice contact13) 76 4 = 1243482 :=
  contactRankWindow_of_rec contact13 76 4 1243482 (by decide +kernel)
private theorem contact13RanksSlice80 : sliceWindow (auxiliaryRankSlice contact13) 80 4 = 997967 :=
  contactRankWindow_of_rec contact13 80 4 997967 (by decide +kernel)
private theorem contact13RanksSlice84 : sliceWindow (auxiliaryRankSlice contact13) 84 4 = 783854 :=
  contactRankWindow_of_rec contact13 84 4 783854 (by decide +kernel)
private theorem contact13RanksSlice88 : sliceWindow (auxiliaryRankSlice contact13) 88 4 = 599226 :=
  contactRankWindow_of_rec contact13 88 4 599226 (by decide +kernel)
private theorem contact13RanksSlice92 : sliceWindow (auxiliaryRankSlice contact13) 92 4 = 442471 :=
  contactRankWindow_of_rec contact13 92 4 442471 (by decide +kernel)
private theorem contact13RanksSlice96 : sliceWindow (auxiliaryRankSlice contact13) 96 4 = 312506 :=
  contactRankWindow_of_rec contact13 96 4 312506 (by decide +kernel)
private theorem contact13RanksSlice100 : sliceWindow (auxiliaryRankSlice contact13) 100 4 = 207290 :=
  contactRankWindow_of_rec contact13 100 4 207290 (by decide +kernel)
private theorem contact13RanksSlice104 : sliceWindow (auxiliaryRankSlice contact13) 104 4 = 125215 :=
  contactRankWindow_of_rec contact13 104 4 125215 (by decide +kernel)
private theorem contact13RanksSlice108 : sliceWindow (auxiliaryRankSlice contact13) 108 4 = 65318 :=
  contactRankWindow_of_rec contact13 108 4 65318 (by decide +kernel)
private theorem contact13RanksSlice112 : sliceWindow (auxiliaryRankSlice contact13) 112 4 = 25517 :=
  contactRankWindow_of_rec contact13 112 4 25517 (by decide +kernel)
private theorem contact13RanksSlice116 : sliceWindow (auxiliaryRankSlice contact13) 116 4 = 4420 :=
  contactRankWindow_of_rec contact13 116 4 4420 (by decide +kernel)
private theorem contact13RanksSlice120 : sliceWindow (auxiliaryRankSlice contact13) 120 8 = 0 :=
  contactRankWindow_of_rec contact13 120 8 0 (by decide +kernel)
private theorem contact13RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact13) 0 8 = 26312228 :=
  combineSlices (auxiliaryRankSlice contact13) 0 4 4 13693114 12619114 contact13RanksSlice0 contact13RanksSlice4
private theorem contact13RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact13) 8 8 = 22208228 :=
  combineSlices (auxiliaryRankSlice contact13) 8 4 4 11593114 10615114 contact13RanksSlice8 contact13RanksSlice12
private theorem contact13RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact13) 16 8 = 18488228 :=
  combineSlices (auxiliaryRankSlice contact13) 16 4 4 9685114 8803114 contact13RanksSlice16 contact13RanksSlice20
private theorem contact13RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact13) 24 8 = 15152228 :=
  combineSlices (auxiliaryRankSlice contact13) 24 4 4 7969114 7183114 contact13RanksSlice24 contact13RanksSlice28
private theorem contact13RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact13) 32 8 = 12200203 :=
  combineSlices (auxiliaryRankSlice contact13) 32 4 4 6445114 5755089 contact13RanksSlice32 contact13RanksSlice36
private theorem contact13RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact13) 40 8 = 9628804 :=
  combineSlices (auxiliaryRankSlice contact13) 40 4 4 5112509 4516295 contact13RanksSlice40 contact13RanksSlice44
private theorem contact13RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact13) 48 8 = 7423172 :=
  combineSlices (auxiliaryRankSlice contact13) 48 4 4 3965258 3457914 contact13RanksSlice48 contact13RanksSlice52
private theorem contact13RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact13) 56 8 = 5560629 :=
  combineSlices (auxiliaryRankSlice contact13) 56 4 4 2992639 2567990 contact13RanksSlice56 contact13RanksSlice60
private theorem contact13RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact13) 64 8 = 4016241 :=
  combineSlices (auxiliaryRankSlice contact13) 64 4 4 2182298 1833943 contact13RanksSlice64 contact13RanksSlice68
private theorem contact13RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact13) 72 8 = 2765084 :=
  combineSlices (auxiliaryRankSlice contact13) 72 4 4 1521602 1243482 contact13RanksSlice72 contact13RanksSlice76
private theorem contact13RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact13) 80 8 = 1781821 :=
  combineSlices (auxiliaryRankSlice contact13) 80 4 4 997967 783854 contact13RanksSlice80 contact13RanksSlice84
private theorem contact13RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact13) 88 8 = 1041697 :=
  combineSlices (auxiliaryRankSlice contact13) 88 4 4 599226 442471 contact13RanksSlice88 contact13RanksSlice92
private theorem contact13RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact13) 96 8 = 519796 :=
  combineSlices (auxiliaryRankSlice contact13) 96 4 4 312506 207290 contact13RanksSlice96 contact13RanksSlice100
private theorem contact13RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact13) 104 8 = 190533 :=
  combineSlices (auxiliaryRankSlice contact13) 104 4 4 125215 65318 contact13RanksSlice104 contact13RanksSlice108
private theorem contact13RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact13) 112 8 = 29937 :=
  combineSlices (auxiliaryRankSlice contact13) 112 4 4 25517 4420 contact13RanksSlice112 contact13RanksSlice116
private theorem contact13RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact13) 0 16 = 48520456 :=
  combineSlices (auxiliaryRankSlice contact13) 0 8 8 26312228 22208228 contact13RanksJoin0_8 contact13RanksJoin8_8
private theorem contact13RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact13) 16 16 = 33640456 :=
  combineSlices (auxiliaryRankSlice contact13) 16 8 8 18488228 15152228 contact13RanksJoin16_8 contact13RanksJoin24_8
private theorem contact13RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact13) 32 16 = 21829007 :=
  combineSlices (auxiliaryRankSlice contact13) 32 8 8 12200203 9628804 contact13RanksJoin32_8 contact13RanksJoin40_8
private theorem contact13RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact13) 48 16 = 12983801 :=
  combineSlices (auxiliaryRankSlice contact13) 48 8 8 7423172 5560629 contact13RanksJoin48_8 contact13RanksJoin56_8
private theorem contact13RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact13) 64 16 = 6781325 :=
  combineSlices (auxiliaryRankSlice contact13) 64 8 8 4016241 2765084 contact13RanksJoin64_8 contact13RanksJoin72_8
private theorem contact13RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact13) 80 16 = 2823518 :=
  combineSlices (auxiliaryRankSlice contact13) 80 8 8 1781821 1041697 contact13RanksJoin80_8 contact13RanksJoin88_8
private theorem contact13RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact13) 96 16 = 710329 :=
  combineSlices (auxiliaryRankSlice contact13) 96 8 8 519796 190533 contact13RanksJoin96_8 contact13RanksJoin104_8
private theorem contact13RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact13) 112 16 = 29937 :=
  combineSlices (auxiliaryRankSlice contact13) 112 8 8 29937 0 contact13RanksJoin112_8 contact13RanksSlice120
private theorem contact13RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact13) 0 32 = 82160912 :=
  combineSlices (auxiliaryRankSlice contact13) 0 16 16 48520456 33640456 contact13RanksJoin0_16 contact13RanksJoin16_16
private theorem contact13RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact13) 32 32 = 34812808 :=
  combineSlices (auxiliaryRankSlice contact13) 32 16 16 21829007 12983801 contact13RanksJoin32_16 contact13RanksJoin48_16
private theorem contact13RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact13) 64 32 = 9604843 :=
  combineSlices (auxiliaryRankSlice contact13) 64 16 16 6781325 2823518 contact13RanksJoin64_16 contact13RanksJoin80_16
private theorem contact13RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact13) 96 32 = 740266 :=
  combineSlices (auxiliaryRankSlice contact13) 96 16 16 710329 29937 contact13RanksJoin96_16 contact13RanksJoin112_16
private theorem contact13RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact13) 0 64 = 116973720 :=
  combineSlices (auxiliaryRankSlice contact13) 0 32 32 82160912 34812808 contact13RanksJoin0_32 contact13RanksJoin32_32
private theorem contact13RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact13) 64 64 = 10345109 :=
  combineSlices (auxiliaryRankSlice contact13) 64 32 32 9604843 740266 contact13RanksJoin64_32 contact13RanksJoin96_32
private theorem contact13RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact13) 0 128 = 127318829 :=
  combineSlices (auxiliaryRankSlice contact13) 0 64 64 116973720 10345109 contact13RanksJoin0_64 contact13RanksJoin64_64
theorem contact13_margin : sourceMargin contact13 :=
  margin_of_checked_counts contact13 128 417151542841979 41660956596342 1622911107 127318829 rfl contact13OrdinaryColumns contact13ColumnsJoin0_128 contact13OrdinaryRanks contact13RanksJoin0_128 (by decide +kernel)

private theorem contact15OrdinaryColumns : ordinaryColumnCount contact15 = 190530074520920 := by decide +kernel
private theorem contact15ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact15) 0 4 = 996253472656 :=
  contactColumnsWindow_fast contact15 0 4 996253472656 (by decide +kernel)
private theorem contact15ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact15) 4 4 = 914734092898 :=
  contactColumnsWindow_fast contact15 4 4 914734092898 (by decide +kernel)
private theorem contact15ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact15) 8 4 = 836730431092 :=
  contactColumnsWindow_fast contact15 8 4 836730431092 (by decide +kernel)
private theorem contact15ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact15) 12 4 = 762226392754 :=
  contactColumnsWindow_fast contact15 12 4 762226392754 (by decide +kernel)
private theorem contact15ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact15) 16 4 = 691219154608 :=
  contactColumnsWindow_fast contact15 16 4 691219154608 (by decide +kernel)
private theorem contact15ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact15) 20 4 = 623707226678 :=
  contactColumnsWindow_fast contact15 20 4 623707226678 (by decide +kernel)
private theorem contact15ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact15) 24 4 = 559695725830 :=
  contactColumnsWindow_fast contact15 24 4 559695725830 (by decide +kernel)
private theorem contact15ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact15) 28 4 = 499201438311 :=
  contactColumnsWindow_fast contact15 28 4 499201438311 (by decide +kernel)
private theorem contact15ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact15) 32 4 = 442208274243 :=
  contactColumnsWindow_fast contact15 32 4 442208274243 (by decide +kernel)
private theorem contact15ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact15) 36 4 = 388711978780 :=
  contactColumnsWindow_fast contact15 36 4 388711978780 (by decide +kernel)
private theorem contact15ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact15) 40 4 = 338711098382 :=
  contactColumnsWindow_fast contact15 40 4 338711098382 (by decide +kernel)
private theorem contact15ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact15) 44 4 = 292211828638 :=
  contactColumnsWindow_fast contact15 44 4 292211828638 (by decide +kernel)
private theorem contact15ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact15) 48 4 = 249229989796 :=
  contactColumnsWindow_fast contact15 48 4 249229989796 (by decide +kernel)
private theorem contact15ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact15) 52 4 = 209747933877 :=
  contactColumnsWindow_fast contact15 52 4 209747933877 (by decide +kernel)
private theorem contact15ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact15) 56 4 = 173762498800 :=
  contactColumnsWindow_fast contact15 56 4 173762498800 (by decide +kernel)
private theorem contact15ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact15) 60 4 = 141272665934 :=
  contactColumnsWindow_fast contact15 60 4 141272665934 (by decide +kernel)
private theorem contact15ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact15) 64 4 = 112286061609 :=
  contactColumnsWindow_fast contact15 64 4 112286061609 (by decide +kernel)
private theorem contact15ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact15) 68 4 = 86816312920 :=
  contactColumnsWindow_fast contact15 68 4 86816312920 (by decide +kernel)
private theorem contact15ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact15) 72 4 = 64845289359 :=
  contactColumnsWindow_fast contact15 72 4 64845289359 (by decide +kernel)
private theorem contact15ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact15) 76 4 = 46370714668 :=
  contactColumnsWindow_fast contact15 76 4 46370714668 (by decide +kernel)
private theorem contact15ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact15) 80 4 = 31388971736 :=
  contactColumnsWindow_fast contact15 80 4 31388971736 (by decide +kernel)
private theorem contact15ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact15) 84 4 = 19842739792 :=
  contactColumnsWindow_fast contact15 84 4 19842739792 (by decide +kernel)
private theorem contact15ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact15) 88 4 = 11512968197 :=
  contactColumnsWindow_fast contact15 88 4 11512968197 (by decide +kernel)
private theorem contact15ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact15) 92 4 = 5985953559 :=
  contactColumnsWindow_fast contact15 92 4 5985953559 (by decide +kernel)
private theorem contact15ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact15) 0 8 = 1910987565554 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 4 4 996253472656 914734092898 contact15ColumnsSlice0 contact15ColumnsSlice4
private theorem contact15ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact15) 8 8 = 1598956823846 :=
  combineSlices (auxiliaryColumnSlice contact15) 8 4 4 836730431092 762226392754 contact15ColumnsSlice8 contact15ColumnsSlice12
private theorem contact15ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact15) 16 8 = 1314926381286 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 4 4 691219154608 623707226678 contact15ColumnsSlice16 contact15ColumnsSlice20
private theorem contact15ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact15) 24 8 = 1058897164141 :=
  combineSlices (auxiliaryColumnSlice contact15) 24 4 4 559695725830 499201438311 contact15ColumnsSlice24 contact15ColumnsSlice28
private theorem contact15ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact15) 32 8 = 830920253023 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 4 4 442208274243 388711978780 contact15ColumnsSlice32 contact15ColumnsSlice36
private theorem contact15ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact15) 40 8 = 630922927020 :=
  combineSlices (auxiliaryColumnSlice contact15) 40 4 4 338711098382 292211828638 contact15ColumnsSlice40 contact15ColumnsSlice44
private theorem contact15ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact15) 48 8 = 458977923673 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 4 4 249229989796 209747933877 contact15ColumnsSlice48 contact15ColumnsSlice52
private theorem contact15ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact15) 56 8 = 315035164734 :=
  combineSlices (auxiliaryColumnSlice contact15) 56 4 4 173762498800 141272665934 contact15ColumnsSlice56 contact15ColumnsSlice60
private theorem contact15ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact15) 64 8 = 199102374529 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 4 4 112286061609 86816312920 contact15ColumnsSlice64 contact15ColumnsSlice68
private theorem contact15ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact15) 72 8 = 111216004027 :=
  combineSlices (auxiliaryColumnSlice contact15) 72 4 4 64845289359 46370714668 contact15ColumnsSlice72 contact15ColumnsSlice76
private theorem contact15ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact15) 80 8 = 51231711528 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 4 4 31388971736 19842739792 contact15ColumnsSlice80 contact15ColumnsSlice84
private theorem contact15ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact15) 88 8 = 17498921756 :=
  combineSlices (auxiliaryColumnSlice contact15) 88 4 4 11512968197 5985953559 contact15ColumnsSlice88 contact15ColumnsSlice92
private theorem contact15ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact15) 0 16 = 3509944389400 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 8 8 1910987565554 1598956823846 contact15ColumnsJoin0_8 contact15ColumnsJoin8_8
private theorem contact15ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact15) 16 16 = 2373823545427 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 8 8 1314926381286 1058897164141 contact15ColumnsJoin16_8 contact15ColumnsJoin24_8
private theorem contact15ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact15) 32 16 = 1461843180043 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 8 8 830920253023 630922927020 contact15ColumnsJoin32_8 contact15ColumnsJoin40_8
private theorem contact15ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact15) 48 16 = 774013088407 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 8 8 458977923673 315035164734 contact15ColumnsJoin48_8 contact15ColumnsJoin56_8
private theorem contact15ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact15) 64 16 = 310318378556 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 8 8 199102374529 111216004027 contact15ColumnsJoin64_8 contact15ColumnsJoin72_8
private theorem contact15ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact15) 80 16 = 68730633284 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 8 8 51231711528 17498921756 contact15ColumnsJoin80_8 contact15ColumnsJoin88_8
private theorem contact15ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact15) 0 32 = 5883767934827 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 16 16 3509944389400 2373823545427 contact15ColumnsJoin0_16 contact15ColumnsJoin16_16
private theorem contact15ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact15) 32 32 = 2235856268450 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 16 16 1461843180043 774013088407 contact15ColumnsJoin32_16 contact15ColumnsJoin48_16
private theorem contact15ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact15) 64 32 = 379049011840 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 16 16 310318378556 68730633284 contact15ColumnsJoin64_16 contact15ColumnsJoin80_16
private theorem contact15ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact15) 0 64 = 8119624203277 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 32 32 5883767934827 2235856268450 contact15ColumnsJoin0_32 contact15ColumnsJoin32_32
private theorem contact15ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact15) 0 96 = 8498673215117 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 64 32 8119624203277 379049011840 contact15ColumnsJoin0_64 contact15ColumnsJoin64_32
private theorem contact15OrdinaryRanks : ordinaryRankBound contact15 = 733343658 := by decide +kernel
private theorem contact15RanksSlice0 : sliceWindow (auxiliaryRankSlice contact15) 0 4 = 3732054 :=
  contactRankWindow_of_rec contact15 0 4 3732054 (by decide +kernel)
private theorem contact15RanksSlice4 : sliceWindow (auxiliaryRankSlice contact15) 4 4 = 3335910 :=
  contactRankWindow_of_rec contact15 4 4 3335910 (by decide +kernel)
private theorem contact15RanksSlice8 : sliceWindow (auxiliaryRankSlice contact15) 8 4 = 2963958 :=
  contactRankWindow_of_rec contact15 8 4 2963958 (by decide +kernel)
private theorem contact15RanksSlice12 : sliceWindow (auxiliaryRankSlice contact15) 12 4 = 2616198 :=
  contactRankWindow_of_rec contact15 12 4 2616198 (by decide +kernel)
private theorem contact15RanksSlice16 : sliceWindow (auxiliaryRankSlice contact15) 16 4 = 2292630 :=
  contactRankWindow_of_rec contact15 16 4 2292630 (by decide +kernel)
private theorem contact15RanksSlice20 : sliceWindow (auxiliaryRankSlice contact15) 20 4 = 1993254 :=
  contactRankWindow_of_rec contact15 20 4 1993254 (by decide +kernel)
private theorem contact15RanksSlice24 : sliceWindow (auxiliaryRankSlice contact15) 24 4 = 1718070 :=
  contactRankWindow_of_rec contact15 24 4 1718070 (by decide +kernel)
private theorem contact15RanksSlice28 : sliceWindow (auxiliaryRankSlice contact15) 28 4 = 1467078 :=
  contactRankWindow_of_rec contact15 28 4 1467078 (by decide +kernel)
private theorem contact15RanksSlice32 : sliceWindow (auxiliaryRankSlice contact15) 32 4 = 1240024 :=
  contactRankWindow_of_rec contact15 32 4 1240024 (by decide +kernel)
private theorem contact15RanksSlice36 : sliceWindow (auxiliaryRankSlice contact15) 36 4 = 1036163 :=
  contactRankWindow_of_rec contact15 36 4 1036163 (by decide +kernel)
private theorem contact15RanksSlice40 : sliceWindow (auxiliaryRankSlice contact15) 40 4 = 854492 :=
  contactRankWindow_of_rec contact15 40 4 854492 (by decide +kernel)
private theorem contact15RanksSlice44 : sliceWindow (auxiliaryRankSlice contact15) 44 4 = 693880 :=
  contactRankWindow_of_rec contact15 44 4 693880 (by decide +kernel)
private theorem contact15RanksSlice48 : sliceWindow (auxiliaryRankSlice contact15) 48 4 = 553191 :=
  contactRankWindow_of_rec contact15 48 4 553191 (by decide +kernel)
private theorem contact15RanksSlice52 : sliceWindow (auxiliaryRankSlice contact15) 52 4 = 431420 :=
  contactRankWindow_of_rec contact15 52 4 431420 (by decide +kernel)
private theorem contact15RanksSlice56 : sliceWindow (auxiliaryRankSlice contact15) 56 4 = 327352 :=
  contactRankWindow_of_rec contact15 56 4 327352 (by decide +kernel)
private theorem contact15RanksSlice60 : sliceWindow (auxiliaryRankSlice contact15) 60 4 = 239851 :=
  contactRankWindow_of_rec contact15 60 4 239851 (by decide +kernel)
private theorem contact15RanksSlice64 : sliceWindow (auxiliaryRankSlice contact15) 64 4 = 167996 :=
  contactRankWindow_of_rec contact15 64 4 167996 (by decide +kernel)
private theorem contact15RanksSlice68 : sliceWindow (auxiliaryRankSlice contact15) 68 4 = 110488 :=
  contactRankWindow_of_rec contact15 68 4 110488 (by decide +kernel)
private theorem contact15RanksSlice72 : sliceWindow (auxiliaryRankSlice contact15) 72 4 = 66191 :=
  contactRankWindow_of_rec contact15 72 4 66191 (by decide +kernel)
private theorem contact15RanksSlice76 : sliceWindow (auxiliaryRankSlice contact15) 76 4 = 34268 :=
  contactRankWindow_of_rec contact15 76 4 34268 (by decide +kernel)
private theorem contact15RanksSlice80 : sliceWindow (auxiliaryRankSlice contact15) 80 4 = 13336 :=
  contactRankWindow_of_rec contact15 80 4 13336 (by decide +kernel)
private theorem contact15RanksSlice84 : sliceWindow (auxiliaryRankSlice contact15) 84 4 = 2298 :=
  contactRankWindow_of_rec contact15 84 4 2298 (by decide +kernel)
private theorem contact15RanksSlice88 : sliceWindow (auxiliaryRankSlice contact15) 88 8 = 0 :=
  contactRankWindow_of_rec contact15 88 8 0 (by decide +kernel)
private theorem contact15RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact15) 0 8 = 7067964 :=
  combineSlices (auxiliaryRankSlice contact15) 0 4 4 3732054 3335910 contact15RanksSlice0 contact15RanksSlice4
private theorem contact15RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact15) 8 8 = 5580156 :=
  combineSlices (auxiliaryRankSlice contact15) 8 4 4 2963958 2616198 contact15RanksSlice8 contact15RanksSlice12
private theorem contact15RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact15) 16 8 = 4285884 :=
  combineSlices (auxiliaryRankSlice contact15) 16 4 4 2292630 1993254 contact15RanksSlice16 contact15RanksSlice20
private theorem contact15RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact15) 24 8 = 3185148 :=
  combineSlices (auxiliaryRankSlice contact15) 24 4 4 1718070 1467078 contact15RanksSlice24 contact15RanksSlice28
private theorem contact15RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact15) 32 8 = 2276187 :=
  combineSlices (auxiliaryRankSlice contact15) 32 4 4 1240024 1036163 contact15RanksSlice32 contact15RanksSlice36
private theorem contact15RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact15) 40 8 = 1548372 :=
  combineSlices (auxiliaryRankSlice contact15) 40 4 4 854492 693880 contact15RanksSlice40 contact15RanksSlice44
private theorem contact15RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact15) 48 8 = 984611 :=
  combineSlices (auxiliaryRankSlice contact15) 48 4 4 553191 431420 contact15RanksSlice48 contact15RanksSlice52
private theorem contact15RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact15) 56 8 = 567203 :=
  combineSlices (auxiliaryRankSlice contact15) 56 4 4 327352 239851 contact15RanksSlice56 contact15RanksSlice60
private theorem contact15RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact15) 64 8 = 278484 :=
  combineSlices (auxiliaryRankSlice contact15) 64 4 4 167996 110488 contact15RanksSlice64 contact15RanksSlice68
private theorem contact15RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact15) 72 8 = 100459 :=
  combineSlices (auxiliaryRankSlice contact15) 72 4 4 66191 34268 contact15RanksSlice72 contact15RanksSlice76
private theorem contact15RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact15) 80 8 = 15634 :=
  combineSlices (auxiliaryRankSlice contact15) 80 4 4 13336 2298 contact15RanksSlice80 contact15RanksSlice84
private theorem contact15RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact15) 0 16 = 12648120 :=
  combineSlices (auxiliaryRankSlice contact15) 0 8 8 7067964 5580156 contact15RanksJoin0_8 contact15RanksJoin8_8
private theorem contact15RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact15) 16 16 = 7471032 :=
  combineSlices (auxiliaryRankSlice contact15) 16 8 8 4285884 3185148 contact15RanksJoin16_8 contact15RanksJoin24_8
private theorem contact15RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact15) 32 16 = 3824559 :=
  combineSlices (auxiliaryRankSlice contact15) 32 8 8 2276187 1548372 contact15RanksJoin32_8 contact15RanksJoin40_8
private theorem contact15RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact15) 48 16 = 1551814 :=
  combineSlices (auxiliaryRankSlice contact15) 48 8 8 984611 567203 contact15RanksJoin48_8 contact15RanksJoin56_8
private theorem contact15RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact15) 64 16 = 378943 :=
  combineSlices (auxiliaryRankSlice contact15) 64 8 8 278484 100459 contact15RanksJoin64_8 contact15RanksJoin72_8
private theorem contact15RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact15) 80 16 = 15634 :=
  combineSlices (auxiliaryRankSlice contact15) 80 8 8 15634 0 contact15RanksJoin80_8 contact15RanksSlice88
private theorem contact15RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact15) 0 32 = 20119152 :=
  combineSlices (auxiliaryRankSlice contact15) 0 16 16 12648120 7471032 contact15RanksJoin0_16 contact15RanksJoin16_16
private theorem contact15RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact15) 32 32 = 5376373 :=
  combineSlices (auxiliaryRankSlice contact15) 32 16 16 3824559 1551814 contact15RanksJoin32_16 contact15RanksJoin48_16
private theorem contact15RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact15) 64 32 = 394577 :=
  combineSlices (auxiliaryRankSlice contact15) 64 16 16 378943 15634 contact15RanksJoin64_16 contact15RanksJoin80_16
private theorem contact15RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact15) 0 64 = 25495525 :=
  combineSlices (auxiliaryRankSlice contact15) 0 32 32 20119152 5376373 contact15RanksJoin0_32 contact15RanksJoin32_32
private theorem contact15RanksJoin0_96 : sliceWindow (auxiliaryRankSlice contact15) 0 96 = 25890102 :=
  combineSlices (auxiliaryRankSlice contact15) 0 64 32 25495525 394577 contact15RanksJoin0_64 contact15RanksJoin64_32
theorem contact15_margin : sourceMargin contact15 :=
  margin_of_checked_counts contact15 96 190530074520920 8498673215117 733343658 25890102 rfl contact15OrdinaryColumns contact15ColumnsJoin0_96 contact15OrdinaryRanks contact15RanksJoin0_96 (by decide +kernel)

private theorem contact17OrdinaryColumns : ordinaryColumnCount contact17 = 2691119401626463 := by decide +kernel
private theorem contact17ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact17) 0 4 = 6595192606488 :=
  contactColumnsWindow_fast contact17 0 4 6595192606488 (by decide +kernel)
private theorem contact17ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact17) 4 4 = 6259608089620 :=
  contactColumnsWindow_fast contact17 4 4 6259608089620 (by decide +kernel)
private theorem contact17ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact17) 8 4 = 5932826926552 :=
  contactColumnsWindow_fast contact17 8 4 5932826926552 (by decide +kernel)
private theorem contact17ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact17) 12 4 = 5614850862512 :=
  contactColumnsWindow_fast contact17 12 4 5614850862512 (by decide +kernel)
private theorem contact17ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact17) 16 4 = 5305716802460 :=
  contactColumnsWindow_fast contact17 16 4 5305716802460 (by decide +kernel)
private theorem contact17ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact17) 20 4 = 5005396785156 :=
  contactColumnsWindow_fast contact17 20 4 5005396785156 (by decide +kernel)
private theorem contact17ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact17) 24 4 = 4713882507019 :=
  contactColumnsWindow_fast contact17 24 4 4713882507019 (by decide +kernel)
private theorem contact17ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact17) 28 4 = 4431173627053 :=
  contactColumnsWindow_fast contact17 28 4 4431173627053 (by decide +kernel)
private theorem contact17ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact17) 32 4 = 4157276311336 :=
  contactColumnsWindow_fast contact17 32 4 4157276311336 (by decide +kernel)
private theorem contact17ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact17) 36 4 = 3892223237321 :=
  contactColumnsWindow_fast contact17 36 4 3892223237321 (by decide +kernel)
private theorem contact17ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact17) 40 4 = 3635985979230 :=
  contactColumnsWindow_fast contact17 40 4 3635985979230 (by decide +kernel)
private theorem contact17ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact17) 44 4 = 3388557002080 :=
  contactColumnsWindow_fast contact17 44 4 3388557002080 (by decide +kernel)
private theorem contact17ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact17) 48 4 = 3149937179932 :=
  contactColumnsWindow_fast contact17 48 4 3149937179932 (by decide +kernel)
private theorem contact17ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact17) 52 4 = 2920134507980 :=
  contactColumnsWindow_fast contact17 52 4 2920134507980 (by decide +kernel)
private theorem contact17ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact17) 56 4 = 2699179443971 :=
  contactColumnsWindow_fast contact17 56 4 2699179443971 (by decide +kernel)
private theorem contact17ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact17) 60 4 = 2487042049572 :=
  contactColumnsWindow_fast contact17 60 4 2487042049572 (by decide +kernel)
private theorem contact17ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact17) 64 4 = 2283715240486 :=
  contactColumnsWindow_fast contact17 64 4 2283715240486 (by decide +kernel)
private theorem contact17ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact17) 68 4 = 2089197300520 :=
  contactColumnsWindow_fast contact17 68 4 2089197300520 (by decide +kernel)
private theorem contact17ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact17) 72 4 = 1903499815128 :=
  contactColumnsWindow_fast contact17 72 4 1903499815128 (by decide +kernel)
private theorem contact17ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact17) 76 4 = 1726648920938 :=
  contactColumnsWindow_fast contact17 76 4 1726648920938 (by decide +kernel)
private theorem contact17ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact17) 80 4 = 1558613813493 :=
  contactColumnsWindow_fast contact17 80 4 1558613813493 (by decide +kernel)
private theorem contact17ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact17) 84 4 = 1399389165972 :=
  contactColumnsWindow_fast contact17 84 4 1399389165972 (by decide +kernel)
private theorem contact17ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact17) 88 4 = 1248973302608 :=
  contactColumnsWindow_fast contact17 88 4 1248973302608 (by decide +kernel)
private theorem contact17ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact17) 92 4 = 1107381497472 :=
  contactColumnsWindow_fast contact17 92 4 1107381497472 (by decide +kernel)
private theorem contact17ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact17) 96 4 = 974634076337 :=
  contactColumnsWindow_fast contact17 96 4 974634076337 (by decide +kernel)
private theorem contact17ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact17) 100 4 = 850701404376 :=
  contactColumnsWindow_fast contact17 100 4 850701404376 (by decide +kernel)
private theorem contact17ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact17) 104 4 = 735578880105 :=
  contactColumnsWindow_fast contact17 104 4 735578880105 (by decide +kernel)
private theorem contact17ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact17) 108 4 = 629265030563 :=
  contactColumnsWindow_fast contact17 108 4 629265030563 (by decide +kernel)
private theorem contact17ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact17) 112 4 = 531778915228 :=
  contactColumnsWindow_fast contact17 112 4 531778915228 (by decide +kernel)
private theorem contact17ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact17) 116 4 = 443135137819 :=
  contactColumnsWindow_fast contact17 116 4 443135137819 (by decide +kernel)
private theorem contact17ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact17) 120 4 = 363304798293 :=
  contactColumnsWindow_fast contact17 120 4 363304798293 (by decide +kernel)
private theorem contact17ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact17) 124 4 = 292284273411 :=
  contactColumnsWindow_fast contact17 124 4 292284273411 (by decide +kernel)
private theorem contact17ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact17) 128 4 = 230071826787 :=
  contactColumnsWindow_fast contact17 128 4 230071826787 (by decide +kernel)
private theorem contact17ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact17) 132 4 = 176650169368 :=
  contactColumnsWindow_fast contact17 132 4 176650169368 (by decide +kernel)
private theorem contact17ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact17) 136 4 = 131811391249 :=
  contactColumnsWindow_fast contact17 136 4 131811391249 (by decide +kernel)
private theorem contact17ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact17) 140 4 = 95129335082 :=
  contactColumnsWindow_fast contact17 140 4 95129335082 (by decide +kernel)
private theorem contact17ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact17) 144 4 = 66040736145 :=
  contactColumnsWindow_fast contact17 144 4 66040736145 (by decide +kernel)
private theorem contact17ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact17) 148 4 = 43823586873 :=
  contactColumnsWindow_fast contact17 148 4 43823586873 (by decide +kernel)
private theorem contact17ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact17) 152 4 = 27611411299 :=
  contactColumnsWindow_fast contact17 152 4 27611411299 (by decide +kernel)
private theorem contact17ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact17) 156 2 = 9321108224 :=
  contactColumnsWindow_fast contact17 156 2 9321108224 (by decide +kernel)
private theorem contact17ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact17) 0 8 = 12854800696108 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 4 4 6595192606488 6259608089620 contact17ColumnsSlice0 contact17ColumnsSlice4
private theorem contact17ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact17) 8 8 = 11547677789064 :=
  combineSlices (auxiliaryColumnSlice contact17) 8 4 4 5932826926552 5614850862512 contact17ColumnsSlice8 contact17ColumnsSlice12
private theorem contact17ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact17) 16 8 = 10311113587616 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 4 4 5305716802460 5005396785156 contact17ColumnsSlice16 contact17ColumnsSlice20
private theorem contact17ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact17) 24 8 = 9145056134072 :=
  combineSlices (auxiliaryColumnSlice contact17) 24 4 4 4713882507019 4431173627053 contact17ColumnsSlice24 contact17ColumnsSlice28
private theorem contact17ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact17) 32 8 = 8049499548657 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 4 4 4157276311336 3892223237321 contact17ColumnsSlice32 contact17ColumnsSlice36
private theorem contact17ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact17) 40 8 = 7024542981310 :=
  combineSlices (auxiliaryColumnSlice contact17) 40 4 4 3635985979230 3388557002080 contact17ColumnsSlice40 contact17ColumnsSlice44
private theorem contact17ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact17) 48 8 = 6070071687912 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 4 4 3149937179932 2920134507980 contact17ColumnsSlice48 contact17ColumnsSlice52
private theorem contact17ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact17) 56 8 = 5186221493543 :=
  combineSlices (auxiliaryColumnSlice contact17) 56 4 4 2699179443971 2487042049572 contact17ColumnsSlice56 contact17ColumnsSlice60
private theorem contact17ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact17) 64 8 = 4372912541006 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 4 4 2283715240486 2089197300520 contact17ColumnsSlice64 contact17ColumnsSlice68
private theorem contact17ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact17) 72 8 = 3630148736066 :=
  combineSlices (auxiliaryColumnSlice contact17) 72 4 4 1903499815128 1726648920938 contact17ColumnsSlice72 contact17ColumnsSlice76
private theorem contact17ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact17) 80 8 = 2958002979465 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 4 4 1558613813493 1399389165972 contact17ColumnsSlice80 contact17ColumnsSlice84
private theorem contact17ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact17) 88 8 = 2356354800080 :=
  combineSlices (auxiliaryColumnSlice contact17) 88 4 4 1248973302608 1107381497472 contact17ColumnsSlice88 contact17ColumnsSlice92
private theorem contact17ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact17) 96 8 = 1825335480713 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 4 4 974634076337 850701404376 contact17ColumnsSlice96 contact17ColumnsSlice100
private theorem contact17ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact17) 104 8 = 1364843910668 :=
  combineSlices (auxiliaryColumnSlice contact17) 104 4 4 735578880105 629265030563 contact17ColumnsSlice104 contact17ColumnsSlice108
private theorem contact17ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact17) 112 8 = 974914053047 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 4 4 531778915228 443135137819 contact17ColumnsSlice112 contact17ColumnsSlice116
private theorem contact17ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact17) 120 8 = 655589071704 :=
  combineSlices (auxiliaryColumnSlice contact17) 120 4 4 363304798293 292284273411 contact17ColumnsSlice120 contact17ColumnsSlice124
private theorem contact17ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact17) 128 8 = 406721996155 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 4 4 230071826787 176650169368 contact17ColumnsSlice128 contact17ColumnsSlice132
private theorem contact17ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact17) 136 8 = 226940726331 :=
  combineSlices (auxiliaryColumnSlice contact17) 136 4 4 131811391249 95129335082 contact17ColumnsSlice136 contact17ColumnsSlice140
private theorem contact17ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact17) 144 8 = 109864323018 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 4 4 66040736145 43823586873 contact17ColumnsSlice144 contact17ColumnsSlice148
private theorem contact17ColumnsJoin152_6 : sliceWindow (auxiliaryColumnSlice contact17) 152 6 = 36932519523 :=
  combineSlices (auxiliaryColumnSlice contact17) 152 4 2 27611411299 9321108224 contact17ColumnsSlice152 contact17ColumnsSlice156
private theorem contact17ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact17) 0 16 = 24402478485172 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 8 8 12854800696108 11547677789064 contact17ColumnsJoin0_8 contact17ColumnsJoin8_8
private theorem contact17ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact17) 16 16 = 19456169721688 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 8 8 10311113587616 9145056134072 contact17ColumnsJoin16_8 contact17ColumnsJoin24_8
private theorem contact17ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact17) 32 16 = 15074042529967 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 8 8 8049499548657 7024542981310 contact17ColumnsJoin32_8 contact17ColumnsJoin40_8
private theorem contact17ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact17) 48 16 = 11256293181455 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 8 8 6070071687912 5186221493543 contact17ColumnsJoin48_8 contact17ColumnsJoin56_8
private theorem contact17ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact17) 64 16 = 8003061277072 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 8 8 4372912541006 3630148736066 contact17ColumnsJoin64_8 contact17ColumnsJoin72_8
private theorem contact17ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact17) 80 16 = 5314357779545 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 8 8 2958002979465 2356354800080 contact17ColumnsJoin80_8 contact17ColumnsJoin88_8
private theorem contact17ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact17) 96 16 = 3190179391381 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 8 8 1825335480713 1364843910668 contact17ColumnsJoin96_8 contact17ColumnsJoin104_8
private theorem contact17ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact17) 112 16 = 1630503124751 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 8 8 974914053047 655589071704 contact17ColumnsJoin112_8 contact17ColumnsJoin120_8
private theorem contact17ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact17) 128 16 = 633662722486 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 8 8 406721996155 226940726331 contact17ColumnsJoin128_8 contact17ColumnsJoin136_8
private theorem contact17ColumnsJoin144_14 : sliceWindow (auxiliaryColumnSlice contact17) 144 14 = 146796842541 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 8 6 109864323018 36932519523 contact17ColumnsJoin144_8 contact17ColumnsJoin152_6
private theorem contact17ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact17) 0 32 = 43858648206860 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 16 16 24402478485172 19456169721688 contact17ColumnsJoin0_16 contact17ColumnsJoin16_16
private theorem contact17ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact17) 32 32 = 26330335711422 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 16 16 15074042529967 11256293181455 contact17ColumnsJoin32_16 contact17ColumnsJoin48_16
private theorem contact17ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact17) 64 32 = 13317419056617 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 16 16 8003061277072 5314357779545 contact17ColumnsJoin64_16 contact17ColumnsJoin80_16
private theorem contact17ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact17) 96 32 = 4820682516132 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 16 16 3190179391381 1630503124751 contact17ColumnsJoin96_16 contact17ColumnsJoin112_16
private theorem contact17ColumnsJoin128_30 : sliceWindow (auxiliaryColumnSlice contact17) 128 30 = 780459565027 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 16 14 633662722486 146796842541 contact17ColumnsJoin128_16 contact17ColumnsJoin144_14
private theorem contact17ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact17) 0 64 = 70188983918282 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 32 32 43858648206860 26330335711422 contact17ColumnsJoin0_32 contact17ColumnsJoin32_32
private theorem contact17ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact17) 64 64 = 18138101572749 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 32 32 13317419056617 4820682516132 contact17ColumnsJoin64_32 contact17ColumnsJoin96_32
private theorem contact17ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact17) 0 128 = 88327085491031 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 64 64 70188983918282 18138101572749 contact17ColumnsJoin0_64 contact17ColumnsJoin64_64
private theorem contact17ColumnsJoin0_158 : sliceWindow (auxiliaryColumnSlice contact17) 0 158 = 89107545056058 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 128 30 88327085491031 780459565027 contact17ColumnsJoin0_128 contact17ColumnsJoin128_30
private theorem contact17OrdinaryRanks : ordinaryRankBound contact17 = 10334038898 := by decide +kernel
private theorem contact17RanksSlice0 : sliceWindow (auxiliaryRankSlice contact17) 0 4 = 24869468 :=
  contactRankWindow_of_rec contact17 0 4 24869468 (by decide +kernel)
private theorem contact17RanksSlice4 : sliceWindow (auxiliaryRankSlice contact17) 4 4 = 23224412 :=
  contactRankWindow_of_rec contact17 4 4 23224412 (by decide +kernel)
private theorem contact17RanksSlice8 : sliceWindow (auxiliaryRankSlice contact17) 8 4 = 21640284 :=
  contactRankWindow_of_rec contact17 8 4 21640284 (by decide +kernel)
private theorem contact17RanksSlice12 : sliceWindow (auxiliaryRankSlice contact17) 12 4 = 20117084 :=
  contactRankWindow_of_rec contact17 12 4 20117084 (by decide +kernel)
private theorem contact17RanksSlice16 : sliceWindow (auxiliaryRankSlice contact17) 16 4 = 18654812 :=
  contactRankWindow_of_rec contact17 16 4 18654812 (by decide +kernel)
private theorem contact17RanksSlice20 : sliceWindow (auxiliaryRankSlice contact17) 20 4 = 17253468 :=
  contactRankWindow_of_rec contact17 20 4 17253468 (by decide +kernel)
private theorem contact17RanksSlice24 : sliceWindow (auxiliaryRankSlice contact17) 24 4 = 15913052 :=
  contactRankWindow_of_rec contact17 24 4 15913052 (by decide +kernel)
private theorem contact17RanksSlice28 : sliceWindow (auxiliaryRankSlice contact17) 28 4 = 14633564 :=
  contactRankWindow_of_rec contact17 28 4 14633564 (by decide +kernel)
private theorem contact17RanksSlice32 : sliceWindow (auxiliaryRankSlice contact17) 32 4 = 13415004 :=
  contactRankWindow_of_rec contact17 32 4 13415004 (by decide +kernel)
private theorem contact17RanksSlice36 : sliceWindow (auxiliaryRankSlice contact17) 36 4 = 12257372 :=
  contactRankWindow_of_rec contact17 36 4 12257372 (by decide +kernel)
private theorem contact17RanksSlice40 : sliceWindow (auxiliaryRankSlice contact17) 40 4 = 11160668 :=
  contactRankWindow_of_rec contact17 40 4 11160668 (by decide +kernel)
private theorem contact17RanksSlice44 : sliceWindow (auxiliaryRankSlice contact17) 44 4 = 10124892 :=
  contactRankWindow_of_rec contact17 44 4 10124892 (by decide +kernel)
private theorem contact17RanksSlice48 : sliceWindow (auxiliaryRankSlice contact17) 48 4 = 9149960 :=
  contactRankWindow_of_rec contact17 48 4 9149960 (by decide +kernel)
private theorem contact17RanksSlice52 : sliceWindow (auxiliaryRankSlice contact17) 52 4 = 8235050 :=
  contactRankWindow_of_rec contact17 52 4 8235050 (by decide +kernel)
private theorem contact17RanksSlice56 : sliceWindow (auxiliaryRankSlice contact17) 56 4 = 7378924 :=
  contactRankWindow_of_rec contact17 56 4 7378924 (by decide +kernel)
private theorem contact17RanksSlice60 : sliceWindow (auxiliaryRankSlice contact17) 60 4 = 6580306 :=
  contactRankWindow_of_rec contact17 60 4 6580306 (by decide +kernel)
private theorem contact17RanksSlice64 : sliceWindow (auxiliaryRankSlice contact17) 64 4 = 5837604 :=
  contactRankWindow_of_rec contact17 64 4 5837604 (by decide +kernel)
private theorem contact17RanksSlice68 : sliceWindow (auxiliaryRankSlice contact17) 68 4 = 5149020 :=
  contactRankWindow_of_rec contact17 68 4 5149020 (by decide +kernel)
private theorem contact17RanksSlice72 : sliceWindow (auxiliaryRankSlice contact17) 72 4 = 4512746 :=
  contactRankWindow_of_rec contact17 72 4 4512746 (by decide +kernel)
private theorem contact17RanksSlice76 : sliceWindow (auxiliaryRankSlice contact17) 76 4 = 3927188 :=
  contactRankWindow_of_rec contact17 76 4 3927188 (by decide +kernel)
private theorem contact17RanksSlice80 : sliceWindow (auxiliaryRankSlice contact17) 80 4 = 3390412 :=
  contactRankWindow_of_rec contact17 80 4 3390412 (by decide +kernel)
private theorem contact17RanksSlice84 : sliceWindow (auxiliaryRankSlice contact17) 84 4 = 2900610 :=
  contactRankWindow_of_rec contact17 84 4 2900610 (by decide +kernel)
private theorem contact17RanksSlice88 : sliceWindow (auxiliaryRankSlice contact17) 88 4 = 2456324 :=
  contactRankWindow_of_rec contact17 88 4 2456324 (by decide +kernel)
private theorem contact17RanksSlice92 : sliceWindow (auxiliaryRankSlice contact17) 92 4 = 2055484 :=
  contactRankWindow_of_rec contact17 92 4 2055484 (by decide +kernel)
private theorem contact17RanksSlice96 : sliceWindow (auxiliaryRankSlice contact17) 96 4 = 1696282 :=
  contactRankWindow_of_rec contact17 96 4 1696282 (by decide +kernel)
private theorem contact17RanksSlice100 : sliceWindow (auxiliaryRankSlice contact17) 100 4 = 1377396 :=
  contactRankWindow_of_rec contact17 100 4 1377396 (by decide +kernel)
private theorem contact17RanksSlice104 : sliceWindow (auxiliaryRankSlice contact17) 104 4 = 1096620 :=
  contactRankWindow_of_rec contact17 104 4 1096620 (by decide +kernel)
private theorem contact17RanksSlice108 : sliceWindow (auxiliaryRankSlice contact17) 108 4 = 852146 :=
  contactRankWindow_of_rec contact17 108 4 852146 (by decide +kernel)
private theorem contact17RanksSlice112 : sliceWindow (auxiliaryRankSlice contact17) 112 4 = 642788 :=
  contactRankWindow_of_rec contact17 112 4 642788 (by decide +kernel)
private theorem contact17RanksSlice116 : sliceWindow (auxiliaryRankSlice contact17) 116 4 = 466204 :=
  contactRankWindow_of_rec contact17 116 4 466204 (by decide +kernel)
private theorem contact17RanksSlice120 : sliceWindow (auxiliaryRankSlice contact17) 120 4 = 320586 :=
  contactRankWindow_of_rec contact17 120 4 320586 (by decide +kernel)
private theorem contact17RanksSlice124 : sliceWindow (auxiliaryRankSlice contact17) 124 4 = 204884 :=
  contactRankWindow_of_rec contact17 124 4 204884 (by decide +kernel)
private theorem contact17RanksSlice128 : sliceWindow (auxiliaryRankSlice contact17) 128 4 = 116620 :=
  contactRankWindow_of_rec contact17 128 4 116620 (by decide +kernel)
private theorem contact17RanksSlice132 : sliceWindow (auxiliaryRankSlice contact17) 132 4 = 54001 :=
  contactRankWindow_of_rec contact17 132 4 54001 (by decide +kernel)
private theorem contact17RanksSlice136 : sliceWindow (auxiliaryRankSlice contact17) 136 4 = 16315 :=
  contactRankWindow_of_rec contact17 136 4 16315 (by decide +kernel)
private theorem contact17RanksSlice140 : sliceWindow (auxiliaryRankSlice contact17) 140 4 = 916 :=
  contactRankWindow_of_rec contact17 140 4 916 (by decide +kernel)
private theorem contact17RanksSlice144 : sliceWindow (auxiliaryRankSlice contact17) 144 14 = 0 :=
  contactRankWindow_of_rec contact17 144 14 0 (by decide +kernel)
private theorem contact17RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact17) 0 8 = 48093880 :=
  combineSlices (auxiliaryRankSlice contact17) 0 4 4 24869468 23224412 contact17RanksSlice0 contact17RanksSlice4
private theorem contact17RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact17) 8 8 = 41757368 :=
  combineSlices (auxiliaryRankSlice contact17) 8 4 4 21640284 20117084 contact17RanksSlice8 contact17RanksSlice12
private theorem contact17RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact17) 16 8 = 35908280 :=
  combineSlices (auxiliaryRankSlice contact17) 16 4 4 18654812 17253468 contact17RanksSlice16 contact17RanksSlice20
private theorem contact17RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact17) 24 8 = 30546616 :=
  combineSlices (auxiliaryRankSlice contact17) 24 4 4 15913052 14633564 contact17RanksSlice24 contact17RanksSlice28
private theorem contact17RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact17) 32 8 = 25672376 :=
  combineSlices (auxiliaryRankSlice contact17) 32 4 4 13415004 12257372 contact17RanksSlice32 contact17RanksSlice36
private theorem contact17RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact17) 40 8 = 21285560 :=
  combineSlices (auxiliaryRankSlice contact17) 40 4 4 11160668 10124892 contact17RanksSlice40 contact17RanksSlice44
private theorem contact17RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact17) 48 8 = 17385010 :=
  combineSlices (auxiliaryRankSlice contact17) 48 4 4 9149960 8235050 contact17RanksSlice48 contact17RanksSlice52
private theorem contact17RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact17) 56 8 = 13959230 :=
  combineSlices (auxiliaryRankSlice contact17) 56 4 4 7378924 6580306 contact17RanksSlice56 contact17RanksSlice60
private theorem contact17RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact17) 64 8 = 10986624 :=
  combineSlices (auxiliaryRankSlice contact17) 64 4 4 5837604 5149020 contact17RanksSlice64 contact17RanksSlice68
private theorem contact17RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact17) 72 8 = 8439934 :=
  combineSlices (auxiliaryRankSlice contact17) 72 4 4 4512746 3927188 contact17RanksSlice72 contact17RanksSlice76
private theorem contact17RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact17) 80 8 = 6291022 :=
  combineSlices (auxiliaryRankSlice contact17) 80 4 4 3390412 2900610 contact17RanksSlice80 contact17RanksSlice84
private theorem contact17RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact17) 88 8 = 4511808 :=
  combineSlices (auxiliaryRankSlice contact17) 88 4 4 2456324 2055484 contact17RanksSlice88 contact17RanksSlice92
private theorem contact17RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact17) 96 8 = 3073678 :=
  combineSlices (auxiliaryRankSlice contact17) 96 4 4 1696282 1377396 contact17RanksSlice96 contact17RanksSlice100
private theorem contact17RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact17) 104 8 = 1948766 :=
  combineSlices (auxiliaryRankSlice contact17) 104 4 4 1096620 852146 contact17RanksSlice104 contact17RanksSlice108
private theorem contact17RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact17) 112 8 = 1108992 :=
  combineSlices (auxiliaryRankSlice contact17) 112 4 4 642788 466204 contact17RanksSlice112 contact17RanksSlice116
private theorem contact17RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact17) 120 8 = 525470 :=
  combineSlices (auxiliaryRankSlice contact17) 120 4 4 320586 204884 contact17RanksSlice120 contact17RanksSlice124
private theorem contact17RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact17) 128 8 = 170621 :=
  combineSlices (auxiliaryRankSlice contact17) 128 4 4 116620 54001 contact17RanksSlice128 contact17RanksSlice132
private theorem contact17RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact17) 136 8 = 17231 :=
  combineSlices (auxiliaryRankSlice contact17) 136 4 4 16315 916 contact17RanksSlice136 contact17RanksSlice140
private theorem contact17RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact17) 0 16 = 89851248 :=
  combineSlices (auxiliaryRankSlice contact17) 0 8 8 48093880 41757368 contact17RanksJoin0_8 contact17RanksJoin8_8
private theorem contact17RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact17) 16 16 = 66454896 :=
  combineSlices (auxiliaryRankSlice contact17) 16 8 8 35908280 30546616 contact17RanksJoin16_8 contact17RanksJoin24_8
private theorem contact17RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact17) 32 16 = 46957936 :=
  combineSlices (auxiliaryRankSlice contact17) 32 8 8 25672376 21285560 contact17RanksJoin32_8 contact17RanksJoin40_8
private theorem contact17RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact17) 48 16 = 31344240 :=
  combineSlices (auxiliaryRankSlice contact17) 48 8 8 17385010 13959230 contact17RanksJoin48_8 contact17RanksJoin56_8
private theorem contact17RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact17) 64 16 = 19426558 :=
  combineSlices (auxiliaryRankSlice contact17) 64 8 8 10986624 8439934 contact17RanksJoin64_8 contact17RanksJoin72_8
private theorem contact17RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact17) 80 16 = 10802830 :=
  combineSlices (auxiliaryRankSlice contact17) 80 8 8 6291022 4511808 contact17RanksJoin80_8 contact17RanksJoin88_8
private theorem contact17RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact17) 96 16 = 5022444 :=
  combineSlices (auxiliaryRankSlice contact17) 96 8 8 3073678 1948766 contact17RanksJoin96_8 contact17RanksJoin104_8
private theorem contact17RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact17) 112 16 = 1634462 :=
  combineSlices (auxiliaryRankSlice contact17) 112 8 8 1108992 525470 contact17RanksJoin112_8 contact17RanksJoin120_8
private theorem contact17RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact17) 128 16 = 187852 :=
  combineSlices (auxiliaryRankSlice contact17) 128 8 8 170621 17231 contact17RanksJoin128_8 contact17RanksJoin136_8
private theorem contact17RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact17) 0 32 = 156306144 :=
  combineSlices (auxiliaryRankSlice contact17) 0 16 16 89851248 66454896 contact17RanksJoin0_16 contact17RanksJoin16_16
private theorem contact17RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact17) 32 32 = 78302176 :=
  combineSlices (auxiliaryRankSlice contact17) 32 16 16 46957936 31344240 contact17RanksJoin32_16 contact17RanksJoin48_16
private theorem contact17RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact17) 64 32 = 30229388 :=
  combineSlices (auxiliaryRankSlice contact17) 64 16 16 19426558 10802830 contact17RanksJoin64_16 contact17RanksJoin80_16
private theorem contact17RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact17) 96 32 = 6656906 :=
  combineSlices (auxiliaryRankSlice contact17) 96 16 16 5022444 1634462 contact17RanksJoin96_16 contact17RanksJoin112_16
private theorem contact17RanksJoin128_30 : sliceWindow (auxiliaryRankSlice contact17) 128 30 = 187852 :=
  combineSlices (auxiliaryRankSlice contact17) 128 16 14 187852 0 contact17RanksJoin128_16 contact17RanksSlice144
private theorem contact17RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact17) 0 64 = 234608320 :=
  combineSlices (auxiliaryRankSlice contact17) 0 32 32 156306144 78302176 contact17RanksJoin0_32 contact17RanksJoin32_32
private theorem contact17RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact17) 64 64 = 36886294 :=
  combineSlices (auxiliaryRankSlice contact17) 64 32 32 30229388 6656906 contact17RanksJoin64_32 contact17RanksJoin96_32
private theorem contact17RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact17) 0 128 = 271494614 :=
  combineSlices (auxiliaryRankSlice contact17) 0 64 64 234608320 36886294 contact17RanksJoin0_64 contact17RanksJoin64_64
private theorem contact17RanksJoin0_158 : sliceWindow (auxiliaryRankSlice contact17) 0 158 = 271682466 :=
  combineSlices (auxiliaryRankSlice contact17) 0 128 30 271494614 187852 contact17RanksJoin0_128 contact17RanksJoin128_30
theorem contact17_margin : sourceMargin contact17 :=
  margin_of_checked_counts contact17 158 2691119401626463 89107545056058 10334038898 271682466 rfl contact17OrdinaryColumns contact17ColumnsJoin0_158 contact17OrdinaryRanks contact17RanksJoin0_158 (by decide +kernel)

private theorem contact19OrdinaryColumns : ordinaryColumnCount contact19 = 160527327333914 := by decide +kernel
private theorem contact19ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact19) 0 4 = 1313201840816 :=
  contactColumnsWindow_fast contact19 0 4 1313201840816 (by decide +kernel)
private theorem contact19ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact19) 4 4 = 1212448613504 :=
  contactColumnsWindow_fast contact19 4 4 1212448613504 (by decide +kernel)
private theorem contact19ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact19) 8 4 = 1115734832400 :=
  contactColumnsWindow_fast contact19 8 4 1115734832400 (by decide +kernel)
private theorem contact19ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact19) 12 4 = 1023077938304 :=
  contactColumnsWindow_fast contact19 12 4 1023077938304 (by decide +kernel)
private theorem contact19ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact19) 16 4 = 934477269124 :=
  contactColumnsWindow_fast contact19 16 4 934477269124 (by decide +kernel)
private theorem contact19ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact19) 20 4 = 849918553568 :=
  contactColumnsWindow_fast contact19 20 4 849918553568 (by decide +kernel)
private theorem contact19ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact19) 24 4 = 769400870899 :=
  contactColumnsWindow_fast contact19 24 4 769400870899 (by decide +kernel)
private theorem contact19ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact19) 28 4 = 692925554524 :=
  contactColumnsWindow_fast contact19 28 4 692925554524 (by decide +kernel)
private theorem contact19ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact19) 32 4 = 620511801568 :=
  contactColumnsWindow_fast contact19 32 4 620511801568 (by decide +kernel)
private theorem contact19ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact19) 36 4 = 552154416541 :=
  contactColumnsWindow_fast contact19 36 4 552154416541 (by decide +kernel)
private theorem contact19ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact19) 40 4 = 487839919304 :=
  contactColumnsWindow_fast contact19 40 4 487839919304 (by decide +kernel)
private theorem contact19ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact19) 44 4 = 427566272866 :=
  contactColumnsWindow_fast contact19 44 4 427566272866 (by decide +kernel)
private theorem contact19ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact19) 48 4 = 371335824744 :=
  contactColumnsWindow_fast contact19 48 4 371335824744 (by decide +kernel)
private theorem contact19ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact19) 52 4 = 319168819126 :=
  contactColumnsWindow_fast contact19 52 4 319168819126 (by decide +kernel)
private theorem contact19ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact19) 56 4 = 271055672650 :=
  contactColumnsWindow_fast contact19 56 4 271055672650 (by decide +kernel)
private theorem contact19ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact19) 60 4 = 226985393732 :=
  contactColumnsWindow_fast contact19 60 4 226985393732 (by decide +kernel)
private theorem contact19ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact19) 64 4 = 186955877710 :=
  contactColumnsWindow_fast contact19 64 4 186955877710 (by decide +kernel)
private theorem contact19ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact19) 68 4 = 150970378176 :=
  contactColumnsWindow_fast contact19 68 4 150970378176 (by decide +kernel)
private theorem contact19ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact19) 72 4 = 119049945376 :=
  contactColumnsWindow_fast contact19 72 4 119049945376 (by decide +kernel)
private theorem contact19ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact19) 76 4 = 91181088918 :=
  contactColumnsWindow_fast contact19 76 4 91181088918 (by decide +kernel)
private theorem contact19ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact19) 80 4 = 67354976852 :=
  contactColumnsWindow_fast contact19 80 4 67354976852 (by decide +kernel)
private theorem contact19ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact19) 84 4 = 47568867843 :=
  contactColumnsWindow_fast contact19 84 4 47568867843 (by decide +kernel)
private theorem contact19ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact19) 88 4 = 31788634419 :=
  contactColumnsWindow_fast contact19 88 4 31788634419 (by decide +kernel)
private theorem contact19ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact19) 92 4 = 19851273605 :=
  contactColumnsWindow_fast contact19 92 4 19851273605 (by decide +kernel)
private theorem contact19ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact19) 96 4 = 11384896071 :=
  contactColumnsWindow_fast contact19 96 4 11384896071 (by decide +kernel)
private theorem contact19ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact19) 0 8 = 2525650454320 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 4 4 1313201840816 1212448613504 contact19ColumnsSlice0 contact19ColumnsSlice4
private theorem contact19ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact19) 8 8 = 2138812770704 :=
  combineSlices (auxiliaryColumnSlice contact19) 8 4 4 1115734832400 1023077938304 contact19ColumnsSlice8 contact19ColumnsSlice12
private theorem contact19ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact19) 16 8 = 1784395822692 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 4 4 934477269124 849918553568 contact19ColumnsSlice16 contact19ColumnsSlice20
private theorem contact19ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact19) 24 8 = 1462326425423 :=
  combineSlices (auxiliaryColumnSlice contact19) 24 4 4 769400870899 692925554524 contact19ColumnsSlice24 contact19ColumnsSlice28
private theorem contact19ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact19) 32 8 = 1172666218109 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 4 4 620511801568 552154416541 contact19ColumnsSlice32 contact19ColumnsSlice36
private theorem contact19ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact19) 40 8 = 915406192170 :=
  combineSlices (auxiliaryColumnSlice contact19) 40 4 4 487839919304 427566272866 contact19ColumnsSlice40 contact19ColumnsSlice44
private theorem contact19ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact19) 48 8 = 690504643870 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 4 4 371335824744 319168819126 contact19ColumnsSlice48 contact19ColumnsSlice52
private theorem contact19ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact19) 56 8 = 498041066382 :=
  combineSlices (auxiliaryColumnSlice contact19) 56 4 4 271055672650 226985393732 contact19ColumnsSlice56 contact19ColumnsSlice60
private theorem contact19ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact19) 64 8 = 337926255886 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 4 4 186955877710 150970378176 contact19ColumnsSlice64 contact19ColumnsSlice68
private theorem contact19ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact19) 72 8 = 210231034294 :=
  combineSlices (auxiliaryColumnSlice contact19) 72 4 4 119049945376 91181088918 contact19ColumnsSlice72 contact19ColumnsSlice76
private theorem contact19ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact19) 80 8 = 114923844695 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 4 4 67354976852 47568867843 contact19ColumnsSlice80 contact19ColumnsSlice84
private theorem contact19ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact19) 88 8 = 51639908024 :=
  combineSlices (auxiliaryColumnSlice contact19) 88 4 4 31788634419 19851273605 contact19ColumnsSlice88 contact19ColumnsSlice92
private theorem contact19ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact19) 0 16 = 4664463225024 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 8 8 2525650454320 2138812770704 contact19ColumnsJoin0_8 contact19ColumnsJoin8_8
private theorem contact19ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact19) 16 16 = 3246722248115 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 8 8 1784395822692 1462326425423 contact19ColumnsJoin16_8 contact19ColumnsJoin24_8
private theorem contact19ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact19) 32 16 = 2088072410279 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 8 8 1172666218109 915406192170 contact19ColumnsJoin32_8 contact19ColumnsJoin40_8
private theorem contact19ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact19) 48 16 = 1188545710252 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 8 8 690504643870 498041066382 contact19ColumnsJoin48_8 contact19ColumnsJoin56_8
private theorem contact19ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact19) 64 16 = 548157290180 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 8 8 337926255886 210231034294 contact19ColumnsJoin64_8 contact19ColumnsJoin72_8
private theorem contact19ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact19) 80 16 = 166563752719 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 8 8 114923844695 51639908024 contact19ColumnsJoin80_8 contact19ColumnsJoin88_8
private theorem contact19ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact19) 0 32 = 7911185473139 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 16 16 4664463225024 3246722248115 contact19ColumnsJoin0_16 contact19ColumnsJoin16_16
private theorem contact19ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact19) 32 32 = 3276618120531 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 16 16 2088072410279 1188545710252 contact19ColumnsJoin32_16 contact19ColumnsJoin48_16
private theorem contact19ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact19) 64 32 = 714721042899 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 16 16 548157290180 166563752719 contact19ColumnsJoin64_16 contact19ColumnsJoin80_16
private theorem contact19ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact19) 0 64 = 11187803593670 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 32 32 7911185473139 3276618120531 contact19ColumnsJoin0_32 contact19ColumnsJoin32_32
private theorem contact19ColumnsJoin64_36 : sliceWindow (auxiliaryColumnSlice contact19) 64 36 = 726105938970 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 32 4 714721042899 11384896071 contact19ColumnsJoin64_32 contact19ColumnsSlice96
private theorem contact19ColumnsJoin0_100 : sliceWindow (auxiliaryColumnSlice contact19) 0 100 = 11913909532640 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 64 36 11187803593670 726105938970 contact19ColumnsJoin0_64 contact19ColumnsJoin64_36
private theorem contact19OrdinaryRanks : ordinaryRankBound contact19 = 621528024 := by decide +kernel
private theorem contact19RanksSlice0 : sliceWindow (auxiliaryRankSlice contact19) 0 4 = 4916474 :=
  contactRankWindow_of_rec contact19 0 4 4916474 (by decide +kernel)
private theorem contact19RanksSlice4 : sliceWindow (auxiliaryRankSlice contact19) 4 4 = 4427034 :=
  contactRankWindow_of_rec contact19 4 4 4427034 (by decide +kernel)
private theorem contact19RanksSlice8 : sliceWindow (auxiliaryRankSlice contact19) 8 4 = 3965562 :=
  contactRankWindow_of_rec contact19 8 4 3965562 (by decide +kernel)
private theorem contact19RanksSlice12 : sliceWindow (auxiliaryRankSlice contact19) 12 4 = 3532058 :=
  contactRankWindow_of_rec contact19 12 4 3532058 (by decide +kernel)
private theorem contact19RanksSlice16 : sliceWindow (auxiliaryRankSlice contact19) 16 4 = 3126522 :=
  contactRankWindow_of_rec contact19 16 4 3126522 (by decide +kernel)
private theorem contact19RanksSlice20 : sliceWindow (auxiliaryRankSlice contact19) 20 4 = 2748954 :=
  contactRankWindow_of_rec contact19 20 4 2748954 (by decide +kernel)
private theorem contact19RanksSlice24 : sliceWindow (auxiliaryRankSlice contact19) 24 4 = 2399354 :=
  contactRankWindow_of_rec contact19 24 4 2399354 (by decide +kernel)
private theorem contact19RanksSlice28 : sliceWindow (auxiliaryRankSlice contact19) 28 4 = 2077722 :=
  contactRankWindow_of_rec contact19 28 4 2077722 (by decide +kernel)
private theorem contact19RanksSlice32 : sliceWindow (auxiliaryRankSlice contact19) 32 4 = 1783924 :=
  contactRankWindow_of_rec contact19 32 4 1783924 (by decide +kernel)
private theorem contact19RanksSlice36 : sliceWindow (auxiliaryRankSlice contact19) 36 4 = 1517262 :=
  contactRankWindow_of_rec contact19 36 4 1517262 (by decide +kernel)
private theorem contact19RanksSlice40 : sliceWindow (auxiliaryRankSlice contact19) 40 4 = 1276849 :=
  contactRankWindow_of_rec contact19 40 4 1276849 (by decide +kernel)
private theorem contact19RanksSlice44 : sliceWindow (auxiliaryRankSlice contact19) 44 4 = 1061535 :=
  contactRankWindow_of_rec contact19 44 4 1061535 (by decide +kernel)
private theorem contact19RanksSlice48 : sliceWindow (auxiliaryRankSlice contact19) 48 4 = 870082 :=
  contactRankWindow_of_rec contact19 48 4 870082 (by decide +kernel)
private theorem contact19RanksSlice52 : sliceWindow (auxiliaryRankSlice contact19) 52 4 = 701401 :=
  contactRankWindow_of_rec contact19 52 4 701401 (by decide +kernel)
private theorem contact19RanksSlice56 : sliceWindow (auxiliaryRankSlice contact19) 56 4 = 554203 :=
  contactRankWindow_of_rec contact19 56 4 554203 (by decide +kernel)
private theorem contact19RanksSlice60 : sliceWindow (auxiliaryRankSlice contact19) 60 4 = 427254 :=
  contactRankWindow_of_rec contact19 60 4 427254 (by decide +kernel)
private theorem contact19RanksSlice64 : sliceWindow (auxiliaryRankSlice contact19) 64 4 = 319553 :=
  contactRankWindow_of_rec contact19 64 4 319553 (by decide +kernel)
private theorem contact19RanksSlice68 : sliceWindow (auxiliaryRankSlice contact19) 68 4 = 229719 :=
  contactRankWindow_of_rec contact19 68 4 229719 (by decide +kernel)
private theorem contact19RanksSlice72 : sliceWindow (auxiliaryRankSlice contact19) 72 4 = 156522 :=
  contactRankWindow_of_rec contact19 72 4 156522 (by decide +kernel)
private theorem contact19RanksSlice76 : sliceWindow (auxiliaryRankSlice contact19) 76 4 = 99049 :=
  contactRankWindow_of_rec contact19 76 4 99049 (by decide +kernel)
private theorem contact19RanksSlice80 : sliceWindow (auxiliaryRankSlice contact19) 80 4 = 55827 :=
  contactRankWindow_of_rec contact19 80 4 55827 (by decide +kernel)
private theorem contact19RanksSlice84 : sliceWindow (auxiliaryRankSlice contact19) 84 4 = 25630 :=
  contactRankWindow_of_rec contact19 84 4 25630 (by decide +kernel)
private theorem contact19RanksSlice88 : sliceWindow (auxiliaryRankSlice contact19) 88 4 = 7657 :=
  contactRankWindow_of_rec contact19 88 4 7657 (by decide +kernel)
private theorem contact19RanksSlice92 : sliceWindow (auxiliaryRankSlice contact19) 92 4 = 422 :=
  contactRankWindow_of_rec contact19 92 4 422 (by decide +kernel)
private theorem contact19RanksSlice96 : sliceWindow (auxiliaryRankSlice contact19) 96 4 = 0 :=
  contactRankWindow_of_rec contact19 96 4 0 (by decide +kernel)
private theorem contact19RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact19) 0 8 = 9343508 :=
  combineSlices (auxiliaryRankSlice contact19) 0 4 4 4916474 4427034 contact19RanksSlice0 contact19RanksSlice4
private theorem contact19RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact19) 8 8 = 7497620 :=
  combineSlices (auxiliaryRankSlice contact19) 8 4 4 3965562 3532058 contact19RanksSlice8 contact19RanksSlice12
private theorem contact19RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact19) 16 8 = 5875476 :=
  combineSlices (auxiliaryRankSlice contact19) 16 4 4 3126522 2748954 contact19RanksSlice16 contact19RanksSlice20
private theorem contact19RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact19) 24 8 = 4477076 :=
  combineSlices (auxiliaryRankSlice contact19) 24 4 4 2399354 2077722 contact19RanksSlice24 contact19RanksSlice28
private theorem contact19RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact19) 32 8 = 3301186 :=
  combineSlices (auxiliaryRankSlice contact19) 32 4 4 1783924 1517262 contact19RanksSlice32 contact19RanksSlice36
private theorem contact19RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact19) 40 8 = 2338384 :=
  combineSlices (auxiliaryRankSlice contact19) 40 4 4 1276849 1061535 contact19RanksSlice40 contact19RanksSlice44
private theorem contact19RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact19) 48 8 = 1571483 :=
  combineSlices (auxiliaryRankSlice contact19) 48 4 4 870082 701401 contact19RanksSlice48 contact19RanksSlice52
private theorem contact19RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact19) 56 8 = 981457 :=
  combineSlices (auxiliaryRankSlice contact19) 56 4 4 554203 427254 contact19RanksSlice56 contact19RanksSlice60
private theorem contact19RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact19) 64 8 = 549272 :=
  combineSlices (auxiliaryRankSlice contact19) 64 4 4 319553 229719 contact19RanksSlice64 contact19RanksSlice68
private theorem contact19RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact19) 72 8 = 255571 :=
  combineSlices (auxiliaryRankSlice contact19) 72 4 4 156522 99049 contact19RanksSlice72 contact19RanksSlice76
private theorem contact19RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact19) 80 8 = 81457 :=
  combineSlices (auxiliaryRankSlice contact19) 80 4 4 55827 25630 contact19RanksSlice80 contact19RanksSlice84
private theorem contact19RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact19) 88 8 = 8079 :=
  combineSlices (auxiliaryRankSlice contact19) 88 4 4 7657 422 contact19RanksSlice88 contact19RanksSlice92
private theorem contact19RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact19) 0 16 = 16841128 :=
  combineSlices (auxiliaryRankSlice contact19) 0 8 8 9343508 7497620 contact19RanksJoin0_8 contact19RanksJoin8_8
private theorem contact19RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact19) 16 16 = 10352552 :=
  combineSlices (auxiliaryRankSlice contact19) 16 8 8 5875476 4477076 contact19RanksJoin16_8 contact19RanksJoin24_8
private theorem contact19RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact19) 32 16 = 5639570 :=
  combineSlices (auxiliaryRankSlice contact19) 32 8 8 3301186 2338384 contact19RanksJoin32_8 contact19RanksJoin40_8
private theorem contact19RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact19) 48 16 = 2552940 :=
  combineSlices (auxiliaryRankSlice contact19) 48 8 8 1571483 981457 contact19RanksJoin48_8 contact19RanksJoin56_8
private theorem contact19RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact19) 64 16 = 804843 :=
  combineSlices (auxiliaryRankSlice contact19) 64 8 8 549272 255571 contact19RanksJoin64_8 contact19RanksJoin72_8
private theorem contact19RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact19) 80 16 = 89536 :=
  combineSlices (auxiliaryRankSlice contact19) 80 8 8 81457 8079 contact19RanksJoin80_8 contact19RanksJoin88_8
private theorem contact19RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact19) 0 32 = 27193680 :=
  combineSlices (auxiliaryRankSlice contact19) 0 16 16 16841128 10352552 contact19RanksJoin0_16 contact19RanksJoin16_16
private theorem contact19RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact19) 32 32 = 8192510 :=
  combineSlices (auxiliaryRankSlice contact19) 32 16 16 5639570 2552940 contact19RanksJoin32_16 contact19RanksJoin48_16
private theorem contact19RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact19) 64 32 = 894379 :=
  combineSlices (auxiliaryRankSlice contact19) 64 16 16 804843 89536 contact19RanksJoin64_16 contact19RanksJoin80_16
private theorem contact19RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact19) 0 64 = 35386190 :=
  combineSlices (auxiliaryRankSlice contact19) 0 32 32 27193680 8192510 contact19RanksJoin0_32 contact19RanksJoin32_32
private theorem contact19RanksJoin64_36 : sliceWindow (auxiliaryRankSlice contact19) 64 36 = 894379 :=
  combineSlices (auxiliaryRankSlice contact19) 64 32 4 894379 0 contact19RanksJoin64_32 contact19RanksSlice96
private theorem contact19RanksJoin0_100 : sliceWindow (auxiliaryRankSlice contact19) 0 100 = 36280569 :=
  combineSlices (auxiliaryRankSlice contact19) 0 64 36 35386190 894379 contact19RanksJoin0_64 contact19RanksJoin64_36
theorem contact19_margin : sourceMargin contact19 :=
  margin_of_checked_counts contact19 100 160527327333914 11913909532640 621528024 36280569 rfl contact19OrdinaryColumns contact19ColumnsJoin0_100 contact19OrdinaryRanks contact19RanksJoin0_100 (by decide +kernel)

private theorem contact21OrdinaryColumns : ordinaryColumnCount contact21 = 52185024205836 := by decide +kernel
private theorem contact21ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact21) 0 4 = 510912914179 :=
  contactColumnsWindow_fast contact21 0 4 510912914179 (by decide +kernel)
private theorem contact21ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact21) 4 4 = 463105178708 :=
  contactColumnsWindow_fast contact21 4 4 463105178708 (by decide +kernel)
private theorem contact21ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact21) 8 4 = 417659683492 :=
  contactColumnsWindow_fast contact21 8 4 417659683492 (by decide +kernel)
private theorem contact21ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact21) 12 4 = 374573626836 :=
  contactColumnsWindow_fast contact21 12 4 374573626836 (by decide +kernel)
private theorem contact21ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact21) 16 4 = 333845700642 :=
  contactColumnsWindow_fast contact21 16 4 333845700642 (by decide +kernel)
private theorem contact21ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact21) 20 4 = 295479056516 :=
  contactColumnsWindow_fast contact21 20 4 295479056516 (by decide +kernel)
private theorem contact21ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact21) 24 4 = 259485434216 :=
  contactColumnsWindow_fast contact21 24 4 259485434216 (by decide +kernel)
private theorem contact21ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact21) 28 4 = 225852909682 :=
  contactColumnsWindow_fast contact21 28 4 225852909682 (by decide +kernel)
private theorem contact21ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact21) 32 4 = 194579823708 :=
  contactColumnsWindow_fast contact21 32 4 194579823708 (by decide +kernel)
private theorem contact21ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact21) 36 4 = 165664921898 :=
  contactColumnsWindow_fast contact21 36 4 165664921898 (by decide +kernel)
private theorem contact21ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact21) 40 4 = 139112201294 :=
  contactColumnsWindow_fast contact21 40 4 139112201294 (by decide +kernel)
private theorem contact21ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact21) 44 4 = 114932389304 :=
  contactColumnsWindow_fast contact21 44 4 114932389304 (by decide +kernel)
private theorem contact21ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact21) 48 4 = 93112846530 :=
  contactColumnsWindow_fast contact21 48 4 93112846530 (by decide +kernel)
private theorem contact21ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact21) 52 4 = 73652720160 :=
  contactColumnsWindow_fast contact21 52 4 73652720160 (by decide +kernel)
private theorem contact21ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact21) 56 4 = 56550877547 :=
  contactColumnsWindow_fast contact21 56 4 56550877547 (by decide +kernel)
private theorem contact21ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact21) 60 4 = 41812045652 :=
  contactColumnsWindow_fast contact21 60 4 41812045652 (by decide +kernel)
private theorem contact21ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact21) 64 4 = 29446043972 :=
  contactColumnsWindow_fast contact21 64 4 29446043972 (by decide +kernel)
private theorem contact21ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact21) 68 4 = 19439545221 :=
  contactColumnsWindow_fast contact21 68 4 19439545221 (by decide +kernel)
private theorem contact21ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact21) 72 4 = 11783102365 :=
  contactColumnsWindow_fast contact21 72 4 11783102365 (by decide +kernel)
private theorem contact21ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact21) 76 4 = 6377244548 :=
  contactColumnsWindow_fast contact21 76 4 6377244548 (by decide +kernel)
private theorem contact21ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact21) 80 2 = 1798779372 :=
  contactColumnsWindow_fast contact21 80 2 1798779372 (by decide +kernel)
private theorem contact21ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact21) 0 8 = 974018092887 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 4 4 510912914179 463105178708 contact21ColumnsSlice0 contact21ColumnsSlice4
private theorem contact21ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact21) 8 8 = 792233310328 :=
  combineSlices (auxiliaryColumnSlice contact21) 8 4 4 417659683492 374573626836 contact21ColumnsSlice8 contact21ColumnsSlice12
private theorem contact21ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact21) 16 8 = 629324757158 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 4 4 333845700642 295479056516 contact21ColumnsSlice16 contact21ColumnsSlice20
private theorem contact21ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact21) 24 8 = 485338343898 :=
  combineSlices (auxiliaryColumnSlice contact21) 24 4 4 259485434216 225852909682 contact21ColumnsSlice24 contact21ColumnsSlice28
private theorem contact21ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact21) 32 8 = 360244745606 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 4 4 194579823708 165664921898 contact21ColumnsSlice32 contact21ColumnsSlice36
private theorem contact21ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact21) 40 8 = 254044590598 :=
  combineSlices (auxiliaryColumnSlice contact21) 40 4 4 139112201294 114932389304 contact21ColumnsSlice40 contact21ColumnsSlice44
private theorem contact21ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact21) 48 8 = 166765566690 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 4 4 93112846530 73652720160 contact21ColumnsSlice48 contact21ColumnsSlice52
private theorem contact21ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact21) 56 8 = 98362923199 :=
  combineSlices (auxiliaryColumnSlice contact21) 56 4 4 56550877547 41812045652 contact21ColumnsSlice56 contact21ColumnsSlice60
private theorem contact21ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact21) 64 8 = 48885589193 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 4 4 29446043972 19439545221 contact21ColumnsSlice64 contact21ColumnsSlice68
private theorem contact21ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact21) 72 8 = 18160346913 :=
  combineSlices (auxiliaryColumnSlice contact21) 72 4 4 11783102365 6377244548 contact21ColumnsSlice72 contact21ColumnsSlice76
private theorem contact21ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact21) 0 16 = 1766251403215 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 8 8 974018092887 792233310328 contact21ColumnsJoin0_8 contact21ColumnsJoin8_8
private theorem contact21ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact21) 16 16 = 1114663101056 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 8 8 629324757158 485338343898 contact21ColumnsJoin16_8 contact21ColumnsJoin24_8
private theorem contact21ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact21) 32 16 = 614289336204 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 8 8 360244745606 254044590598 contact21ColumnsJoin32_8 contact21ColumnsJoin40_8
private theorem contact21ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact21) 48 16 = 265128489889 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 8 8 166765566690 98362923199 contact21ColumnsJoin48_8 contact21ColumnsJoin56_8
private theorem contact21ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact21) 64 16 = 67045936106 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 8 8 48885589193 18160346913 contact21ColumnsJoin64_8 contact21ColumnsJoin72_8
private theorem contact21ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact21) 0 32 = 2880914504271 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 16 16 1766251403215 1114663101056 contact21ColumnsJoin0_16 contact21ColumnsJoin16_16
private theorem contact21ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact21) 32 32 = 879417826093 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 16 16 614289336204 265128489889 contact21ColumnsJoin32_16 contact21ColumnsJoin48_16
private theorem contact21ColumnsJoin64_18 : sliceWindow (auxiliaryColumnSlice contact21) 64 18 = 68844715478 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 16 2 67045936106 1798779372 contact21ColumnsJoin64_16 contact21ColumnsSlice80
private theorem contact21ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact21) 0 64 = 3760332330364 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 32 32 2880914504271 879417826093 contact21ColumnsJoin0_32 contact21ColumnsJoin32_32
private theorem contact21ColumnsJoin0_82 : sliceWindow (auxiliaryColumnSlice contact21) 0 82 = 3829177045842 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 64 18 3760332330364 68844715478 contact21ColumnsJoin0_64 contact21ColumnsJoin64_18
private theorem contact21OrdinaryRanks : ordinaryRankBound contact21 = 202137126 := by decide +kernel
private theorem contact21RanksSlice0 : sliceWindow (auxiliaryRankSlice contact21) 0 4 = 1905896 :=
  contactRankWindow_of_rec contact21 0 4 1905896 (by decide +kernel)
private theorem contact21RanksSlice4 : sliceWindow (auxiliaryRankSlice contact21) 4 4 = 1673336 :=
  contactRankWindow_of_rec contact21 4 4 1673336 (by decide +kernel)
private theorem contact21RanksSlice8 : sliceWindow (auxiliaryRankSlice contact21) 8 4 = 1457096 :=
  contactRankWindow_of_rec contact21 8 4 1457096 (by decide +kernel)
private theorem contact21RanksSlice12 : sliceWindow (auxiliaryRankSlice contact21) 12 4 = 1257176 :=
  contactRankWindow_of_rec contact21 12 4 1257176 (by decide +kernel)
private theorem contact21RanksSlice16 : sliceWindow (auxiliaryRankSlice contact21) 16 4 = 1073576 :=
  contactRankWindow_of_rec contact21 16 4 1073576 (by decide +kernel)
private theorem contact21RanksSlice20 : sliceWindow (auxiliaryRankSlice contact21) 20 4 = 906296 :=
  contactRankWindow_of_rec contact21 20 4 906296 (by decide +kernel)
private theorem contact21RanksSlice24 : sliceWindow (auxiliaryRankSlice contact21) 24 4 = 755336 :=
  contactRankWindow_of_rec contact21 24 4 755336 (by decide +kernel)
private theorem contact21RanksSlice28 : sliceWindow (auxiliaryRankSlice contact21) 28 4 = 620681 :=
  contactRankWindow_of_rec contact21 28 4 620681 (by decide +kernel)
private theorem contact21RanksSlice32 : sliceWindow (auxiliaryRankSlice contact21) 32 4 = 502011 :=
  contactRankWindow_of_rec contact21 32 4 502011 (by decide +kernel)
private theorem contact21RanksSlice36 : sliceWindow (auxiliaryRankSlice contact21) 36 4 = 398536 :=
  contactRankWindow_of_rec contact21 36 4 398536 (by decide +kernel)
private theorem contact21RanksSlice40 : sliceWindow (auxiliaryRankSlice contact21) 40 4 = 309381 :=
  contactRankWindow_of_rec contact21 40 4 309381 (by decide +kernel)
private theorem contact21RanksSlice44 : sliceWindow (auxiliaryRankSlice contact21) 44 4 = 233611 :=
  contactRankWindow_of_rec contact21 44 4 233611 (by decide +kernel)
private theorem contact21RanksSlice48 : sliceWindow (auxiliaryRankSlice contact21) 48 4 = 170284 :=
  contactRankWindow_of_rec contact21 48 4 170284 (by decide +kernel)
private theorem contact21RanksSlice52 : sliceWindow (auxiliaryRankSlice contact21) 52 4 = 118593 :=
  contactRankWindow_of_rec contact21 52 4 118593 (by decide +kernel)
private theorem contact21RanksSlice56 : sliceWindow (auxiliaryRankSlice contact21) 56 4 = 77531 :=
  contactRankWindow_of_rec contact21 56 4 77531 (by decide +kernel)
private theorem contact21RanksSlice60 : sliceWindow (auxiliaryRankSlice contact21) 60 4 = 46160 :=
  contactRankWindow_of_rec contact21 60 4 46160 (by decide +kernel)
private theorem contact21RanksSlice64 : sliceWindow (auxiliaryRankSlice contact21) 64 4 = 23741 :=
  contactRankWindow_of_rec contact21 64 4 23741 (by decide +kernel)
private theorem contact21RanksSlice68 : sliceWindow (auxiliaryRankSlice contact21) 68 4 = 9195 :=
  contactRankWindow_of_rec contact21 68 4 9195 (by decide +kernel)
private theorem contact21RanksSlice72 : sliceWindow (auxiliaryRankSlice contact21) 72 4 = 1589 :=
  contactRankWindow_of_rec contact21 72 4 1589 (by decide +kernel)
private theorem contact21RanksSlice76 : sliceWindow (auxiliaryRankSlice contact21) 76 6 = 0 :=
  contactRankWindow_of_rec contact21 76 6 0 (by decide +kernel)
private theorem contact21RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact21) 0 8 = 3579232 :=
  combineSlices (auxiliaryRankSlice contact21) 0 4 4 1905896 1673336 contact21RanksSlice0 contact21RanksSlice4
private theorem contact21RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact21) 8 8 = 2714272 :=
  combineSlices (auxiliaryRankSlice contact21) 8 4 4 1457096 1257176 contact21RanksSlice8 contact21RanksSlice12
private theorem contact21RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact21) 16 8 = 1979872 :=
  combineSlices (auxiliaryRankSlice contact21) 16 4 4 1073576 906296 contact21RanksSlice16 contact21RanksSlice20
private theorem contact21RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact21) 24 8 = 1376017 :=
  combineSlices (auxiliaryRankSlice contact21) 24 4 4 755336 620681 contact21RanksSlice24 contact21RanksSlice28
private theorem contact21RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact21) 32 8 = 900547 :=
  combineSlices (auxiliaryRankSlice contact21) 32 4 4 502011 398536 contact21RanksSlice32 contact21RanksSlice36
private theorem contact21RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact21) 40 8 = 542992 :=
  combineSlices (auxiliaryRankSlice contact21) 40 4 4 309381 233611 contact21RanksSlice40 contact21RanksSlice44
private theorem contact21RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact21) 48 8 = 288877 :=
  combineSlices (auxiliaryRankSlice contact21) 48 4 4 170284 118593 contact21RanksSlice48 contact21RanksSlice52
private theorem contact21RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact21) 56 8 = 123691 :=
  combineSlices (auxiliaryRankSlice contact21) 56 4 4 77531 46160 contact21RanksSlice56 contact21RanksSlice60
private theorem contact21RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact21) 64 8 = 32936 :=
  combineSlices (auxiliaryRankSlice contact21) 64 4 4 23741 9195 contact21RanksSlice64 contact21RanksSlice68
private theorem contact21RanksJoin72_10 : sliceWindow (auxiliaryRankSlice contact21) 72 10 = 1589 :=
  combineSlices (auxiliaryRankSlice contact21) 72 4 6 1589 0 contact21RanksSlice72 contact21RanksSlice76
private theorem contact21RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact21) 0 16 = 6293504 :=
  combineSlices (auxiliaryRankSlice contact21) 0 8 8 3579232 2714272 contact21RanksJoin0_8 contact21RanksJoin8_8
private theorem contact21RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact21) 16 16 = 3355889 :=
  combineSlices (auxiliaryRankSlice contact21) 16 8 8 1979872 1376017 contact21RanksJoin16_8 contact21RanksJoin24_8
private theorem contact21RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact21) 32 16 = 1443539 :=
  combineSlices (auxiliaryRankSlice contact21) 32 8 8 900547 542992 contact21RanksJoin32_8 contact21RanksJoin40_8
private theorem contact21RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact21) 48 16 = 412568 :=
  combineSlices (auxiliaryRankSlice contact21) 48 8 8 288877 123691 contact21RanksJoin48_8 contact21RanksJoin56_8
private theorem contact21RanksJoin64_18 : sliceWindow (auxiliaryRankSlice contact21) 64 18 = 34525 :=
  combineSlices (auxiliaryRankSlice contact21) 64 8 10 32936 1589 contact21RanksJoin64_8 contact21RanksJoin72_10
private theorem contact21RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact21) 0 32 = 9649393 :=
  combineSlices (auxiliaryRankSlice contact21) 0 16 16 6293504 3355889 contact21RanksJoin0_16 contact21RanksJoin16_16
private theorem contact21RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact21) 32 32 = 1856107 :=
  combineSlices (auxiliaryRankSlice contact21) 32 16 16 1443539 412568 contact21RanksJoin32_16 contact21RanksJoin48_16
private theorem contact21RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact21) 0 64 = 11505500 :=
  combineSlices (auxiliaryRankSlice contact21) 0 32 32 9649393 1856107 contact21RanksJoin0_32 contact21RanksJoin32_32
private theorem contact21RanksJoin0_82 : sliceWindow (auxiliaryRankSlice contact21) 0 82 = 11540025 :=
  combineSlices (auxiliaryRankSlice contact21) 0 64 18 11505500 34525 contact21RanksJoin0_64 contact21RanksJoin64_18
theorem contact21_margin : sourceMargin contact21 :=
  margin_of_checked_counts contact21 82 52185024205836 3829177045842 202137126 11540025 rfl contact21OrdinaryColumns contact21ColumnsJoin0_82 contact21OrdinaryRanks contact21RanksJoin0_82 (by decide +kernel)

private theorem contact23OrdinaryColumns : ordinaryColumnCount contact23 = 2312877254950217 := by decide +kernel
private theorem contact23ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact23) 0 4 = 7258351071776 :=
  contactColumnsWindow_fast contact23 0 4 7258351071776 (by decide +kernel)
private theorem contact23ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact23) 4 4 = 6899933034176 :=
  contactColumnsWindow_fast contact23 4 4 6899933034176 (by decide +kernel)
private theorem contact23ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact23) 8 4 = 6550629926778 :=
  contactColumnsWindow_fast contact23 8 4 6550629926778 (by decide +kernel)
private theorem contact23ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact23) 12 4 = 6210444680564 :=
  contactColumnsWindow_fast contact23 12 4 6210444680564 (by decide +kernel)
private theorem contact23ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact23) 16 4 = 5879375295484 :=
  contactColumnsWindow_fast contact23 16 4 5879375295484 (by decide +kernel)
private theorem contact23ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact23) 20 4 = 5557423763476 :=
  contactColumnsWindow_fast contact23 20 4 5557423763476 (by decide +kernel)
private theorem contact23ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact23) 24 4 = 5244606406331 :=
  contactColumnsWindow_fast contact23 24 4 5244606406331 (by decide +kernel)
private theorem contact23ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact23) 28 4 = 4940942505249 :=
  contactColumnsWindow_fast contact23 28 4 4940942505249 (by decide +kernel)
private theorem contact23ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact23) 32 4 = 4646399695644 :=
  contactColumnsWindow_fast contact23 32 4 4646399695644 (by decide +kernel)
private theorem contact23ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact23) 36 4 = 4360975932340 :=
  contactColumnsWindow_fast contact23 36 4 4360975932340 (by decide +kernel)
private theorem contact23ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact23) 40 4 = 4084673182080 :=
  contactColumnsWindow_fast contact23 40 4 4084673182080 (by decide +kernel)
private theorem contact23ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact23) 44 4 = 3817511804024 :=
  contactColumnsWindow_fast contact23 44 4 3817511804024 (by decide +kernel)
private theorem contact23ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact23) 48 4 = 3559504219551 :=
  contactColumnsWindow_fast contact23 48 4 3559504219551 (by decide +kernel)
private theorem contact23ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact23) 52 4 = 3310619423963 :=
  contactColumnsWindow_fast contact23 52 4 3310619423963 (by decide +kernel)
private theorem contact23ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact23) 56 4 = 3070858077203 :=
  contactColumnsWindow_fast contact23 56 4 3070858077203 (by decide +kernel)
private theorem contact23ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact23) 60 4 = 2840219880924 :=
  contactColumnsWindow_fast contact23 60 4 2840219880924 (by decide +kernel)
private theorem contact23ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact23) 64 4 = 2618732996032 :=
  contactColumnsWindow_fast contact23 64 4 2618732996032 (by decide +kernel)
private theorem contact23ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact23) 68 4 = 2406397071477 :=
  contactColumnsWindow_fast contact23 68 4 2406397071477 (by decide +kernel)
private theorem contact23ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact23) 72 4 = 2203188979310 :=
  contactColumnsWindow_fast contact23 72 4 2203188979310 (by decide +kernel)
private theorem contact23ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact23) 76 4 = 2009104831037 :=
  contactColumnsWindow_fast contact23 76 4 2009104831037 (by decide +kernel)
private theorem contact23ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact23) 80 4 = 1824143600736 :=
  contactColumnsWindow_fast contact23 80 4 1824143600736 (by decide +kernel)
private theorem contact23ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact23) 84 4 = 1648339032680 :=
  contactColumnsWindow_fast contact23 84 4 1648339032680 (by decide +kernel)
private theorem contact23ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact23) 88 4 = 1481680751035 :=
  contactColumnsWindow_fast contact23 88 4 1481680751035 (by decide +kernel)
private theorem contact23ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact23) 92 4 = 1324149803222 :=
  contactColumnsWindow_fast contact23 92 4 1324149803222 (by decide +kernel)
private theorem contact23ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact23) 96 4 = 1175742823247 :=
  contactColumnsWindow_fast contact23 96 4 1175742823247 (by decide +kernel)
private theorem contact23ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact23) 100 4 = 1036459773559 :=
  contactColumnsWindow_fast contact23 100 4 1036459773559 (by decide +kernel)
private theorem contact23ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact23) 104 4 = 906336394196 :=
  contactColumnsWindow_fast contact23 104 4 906336394196 (by decide +kernel)
private theorem contact23ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact23) 108 4 = 785355715837 :=
  contactColumnsWindow_fast contact23 108 4 785355715837 (by decide +kernel)
private theorem contact23ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact23) 112 4 = 673501937823 :=
  contactColumnsWindow_fast contact23 112 4 673501937823 (by decide +kernel)
private theorem contact23ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact23) 116 4 = 570772188266 :=
  contactColumnsWindow_fast contact23 116 4 570772188266 (by decide +kernel)
private theorem contact23ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact23) 120 4 = 477167512813 :=
  contactColumnsWindow_fast contact23 120 4 477167512813 (by decide +kernel)
private theorem contact23ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact23) 124 4 = 392724994829 :=
  contactColumnsWindow_fast contact23 124 4 392724994829 (by decide +kernel)
private theorem contact23ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact23) 128 4 = 317422045596 :=
  contactColumnsWindow_fast contact23 128 4 317422045596 (by decide +kernel)
private theorem contact23ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact23) 132 4 = 251245078324 :=
  contactColumnsWindow_fast contact23 132 4 251245078324 (by decide +kernel)
private theorem contact23ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact23) 136 4 = 194157831992 :=
  contactColumnsWindow_fast contact23 136 4 194157831992 (by decide +kernel)
private theorem contact23ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact23) 140 4 = 145965786367 :=
  contactColumnsWindow_fast contact23 140 4 145965786367 (by decide +kernel)
private theorem contact23ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact23) 144 4 = 106318241050 :=
  contactColumnsWindow_fast contact23 144 4 106318241050 (by decide +kernel)
private theorem contact23ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact23) 148 4 = 74637186887 :=
  contactColumnsWindow_fast contact23 148 4 74637186887 (by decide +kernel)
private theorem contact23ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact23) 152 4 = 50201237722 :=
  contactColumnsWindow_fast contact23 152 4 50201237722 (by decide +kernel)
private theorem contact23ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact23) 156 4 = 32136609459 :=
  contactColumnsWindow_fast contact23 156 4 32136609459 (by decide +kernel)
private theorem contact23ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact23) 160 1 = 5862093927 :=
  contactColumnsWindow_fast contact23 160 1 5862093927 (by decide +kernel)
private theorem contact23ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact23) 0 8 = 14158284105952 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 4 4 7258351071776 6899933034176 contact23ColumnsSlice0 contact23ColumnsSlice4
private theorem contact23ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact23) 8 8 = 12761074607342 :=
  combineSlices (auxiliaryColumnSlice contact23) 8 4 4 6550629926778 6210444680564 contact23ColumnsSlice8 contact23ColumnsSlice12
private theorem contact23ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact23) 16 8 = 11436799058960 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 4 4 5879375295484 5557423763476 contact23ColumnsSlice16 contact23ColumnsSlice20
private theorem contact23ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact23) 24 8 = 10185548911580 :=
  combineSlices (auxiliaryColumnSlice contact23) 24 4 4 5244606406331 4940942505249 contact23ColumnsSlice24 contact23ColumnsSlice28
private theorem contact23ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact23) 32 8 = 9007375627984 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 4 4 4646399695644 4360975932340 contact23ColumnsSlice32 contact23ColumnsSlice36
private theorem contact23ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact23) 40 8 = 7902184986104 :=
  combineSlices (auxiliaryColumnSlice contact23) 40 4 4 4084673182080 3817511804024 contact23ColumnsSlice40 contact23ColumnsSlice44
private theorem contact23ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact23) 48 8 = 6870123643514 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 4 4 3559504219551 3310619423963 contact23ColumnsSlice48 contact23ColumnsSlice52
private theorem contact23ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact23) 56 8 = 5911077958127 :=
  combineSlices (auxiliaryColumnSlice contact23) 56 4 4 3070858077203 2840219880924 contact23ColumnsSlice56 contact23ColumnsSlice60
private theorem contact23ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact23) 64 8 = 5025130067509 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 4 4 2618732996032 2406397071477 contact23ColumnsSlice64 contact23ColumnsSlice68
private theorem contact23ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact23) 72 8 = 4212293810347 :=
  combineSlices (auxiliaryColumnSlice contact23) 72 4 4 2203188979310 2009104831037 contact23ColumnsSlice72 contact23ColumnsSlice76
private theorem contact23ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact23) 80 8 = 3472482633416 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 4 4 1824143600736 1648339032680 contact23ColumnsSlice80 contact23ColumnsSlice84
private theorem contact23ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact23) 88 8 = 2805830554257 :=
  combineSlices (auxiliaryColumnSlice contact23) 88 4 4 1481680751035 1324149803222 contact23ColumnsSlice88 contact23ColumnsSlice92
private theorem contact23ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact23) 96 8 = 2212202596806 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 4 4 1175742823247 1036459773559 contact23ColumnsSlice96 contact23ColumnsSlice100
private theorem contact23ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact23) 104 8 = 1691692110033 :=
  combineSlices (auxiliaryColumnSlice contact23) 104 4 4 906336394196 785355715837 contact23ColumnsSlice104 contact23ColumnsSlice108
private theorem contact23ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact23) 112 8 = 1244274126089 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 4 4 673501937823 570772188266 contact23ColumnsSlice112 contact23ColumnsSlice116
private theorem contact23ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact23) 120 8 = 869892507642 :=
  combineSlices (auxiliaryColumnSlice contact23) 120 4 4 477167512813 392724994829 contact23ColumnsSlice120 contact23ColumnsSlice124
private theorem contact23ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact23) 128 8 = 568667123920 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 4 4 317422045596 251245078324 contact23ColumnsSlice128 contact23ColumnsSlice132
private theorem contact23ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact23) 136 8 = 340123618359 :=
  combineSlices (auxiliaryColumnSlice contact23) 136 4 4 194157831992 145965786367 contact23ColumnsSlice136 contact23ColumnsSlice140
private theorem contact23ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact23) 144 8 = 180955427937 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 4 4 106318241050 74637186887 contact23ColumnsSlice144 contact23ColumnsSlice148
private theorem contact23ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact23) 152 8 = 82337847181 :=
  combineSlices (auxiliaryColumnSlice contact23) 152 4 4 50201237722 32136609459 contact23ColumnsSlice152 contact23ColumnsSlice156
private theorem contact23ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact23) 0 16 = 26919358713294 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 8 8 14158284105952 12761074607342 contact23ColumnsJoin0_8 contact23ColumnsJoin8_8
private theorem contact23ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact23) 16 16 = 21622347970540 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 8 8 11436799058960 10185548911580 contact23ColumnsJoin16_8 contact23ColumnsJoin24_8
private theorem contact23ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact23) 32 16 = 16909560614088 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 8 8 9007375627984 7902184986104 contact23ColumnsJoin32_8 contact23ColumnsJoin40_8
private theorem contact23ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact23) 48 16 = 12781201601641 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 8 8 6870123643514 5911077958127 contact23ColumnsJoin48_8 contact23ColumnsJoin56_8
private theorem contact23ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact23) 64 16 = 9237423877856 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 8 8 5025130067509 4212293810347 contact23ColumnsJoin64_8 contact23ColumnsJoin72_8
private theorem contact23ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact23) 80 16 = 6278313187673 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 8 8 3472482633416 2805830554257 contact23ColumnsJoin80_8 contact23ColumnsJoin88_8
private theorem contact23ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact23) 96 16 = 3903894706839 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 8 8 2212202596806 1691692110033 contact23ColumnsJoin96_8 contact23ColumnsJoin104_8
private theorem contact23ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact23) 112 16 = 2114166633731 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 8 8 1244274126089 869892507642 contact23ColumnsJoin112_8 contact23ColumnsJoin120_8
private theorem contact23ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact23) 128 16 = 908790742279 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 8 8 568667123920 340123618359 contact23ColumnsJoin128_8 contact23ColumnsJoin136_8
private theorem contact23ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact23) 144 16 = 263293275118 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 8 8 180955427937 82337847181 contact23ColumnsJoin144_8 contact23ColumnsJoin152_8
private theorem contact23ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact23) 0 32 = 48541706683834 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 16 16 26919358713294 21622347970540 contact23ColumnsJoin0_16 contact23ColumnsJoin16_16
private theorem contact23ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact23) 32 32 = 29690762215729 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 16 16 16909560614088 12781201601641 contact23ColumnsJoin32_16 contact23ColumnsJoin48_16
private theorem contact23ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact23) 64 32 = 15515737065529 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 16 16 9237423877856 6278313187673 contact23ColumnsJoin64_16 contact23ColumnsJoin80_16
private theorem contact23ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact23) 96 32 = 6018061340570 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 16 16 3903894706839 2114166633731 contact23ColumnsJoin96_16 contact23ColumnsJoin112_16
private theorem contact23ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact23) 128 32 = 1172084017397 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 16 16 908790742279 263293275118 contact23ColumnsJoin128_16 contact23ColumnsJoin144_16
private theorem contact23ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact23) 0 64 = 78232468899563 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 32 32 48541706683834 29690762215729 contact23ColumnsJoin0_32 contact23ColumnsJoin32_32
private theorem contact23ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact23) 64 64 = 21533798406099 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 32 32 15515737065529 6018061340570 contact23ColumnsJoin64_32 contact23ColumnsJoin96_32
private theorem contact23ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact23) 128 33 = 1177946111324 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 32 1 1172084017397 5862093927 contact23ColumnsJoin128_32 contact23ColumnsSlice160
private theorem contact23ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact23) 0 128 = 99766267305662 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 64 64 78232468899563 21533798406099 contact23ColumnsJoin0_64 contact23ColumnsJoin64_64
private theorem contact23ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact23) 0 161 = 100944213416986 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 128 33 99766267305662 1177946111324 contact23ColumnsJoin0_128 contact23ColumnsJoin128_33
private theorem contact23OrdinaryRanks : ordinaryRankBound contact23 = 8900968487 := by decide +kernel
private theorem contact23RanksSlice0 : sliceWindow (auxiliaryRankSlice contact23) 0 4 = 27361038 :=
  contactRankWindow_of_rec contact23 0 4 27361038 (by decide +kernel)
private theorem contact23RanksSlice4 : sliceWindow (auxiliaryRankSlice contact23) 4 4 = 25602014 :=
  contactRankWindow_of_rec contact23 4 4 25602014 (by decide +kernel)
private theorem contact23RanksSlice8 : sliceWindow (auxiliaryRankSlice contact23) 8 4 = 23906094 :=
  contactRankWindow_of_rec contact23 8 4 23906094 (by decide +kernel)
private theorem contact23RanksSlice12 : sliceWindow (auxiliaryRankSlice contact23) 12 4 = 22273278 :=
  contactRankWindow_of_rec contact23 12 4 22273278 (by decide +kernel)
private theorem contact23RanksSlice16 : sliceWindow (auxiliaryRankSlice contact23) 16 4 = 20703566 :=
  contactRankWindow_of_rec contact23 16 4 20703566 (by decide +kernel)
private theorem contact23RanksSlice20 : sliceWindow (auxiliaryRankSlice contact23) 20 4 = 19196958 :=
  contactRankWindow_of_rec contact23 20 4 19196958 (by decide +kernel)
private theorem contact23RanksSlice24 : sliceWindow (auxiliaryRankSlice contact23) 24 4 = 17753454 :=
  contactRankWindow_of_rec contact23 24 4 17753454 (by decide +kernel)
private theorem contact23RanksSlice28 : sliceWindow (auxiliaryRankSlice contact23) 28 4 = 16373054 :=
  contactRankWindow_of_rec contact23 28 4 16373054 (by decide +kernel)
private theorem contact23RanksSlice32 : sliceWindow (auxiliaryRankSlice contact23) 32 4 = 15055758 :=
  contactRankWindow_of_rec contact23 32 4 15055758 (by decide +kernel)
private theorem contact23RanksSlice36 : sliceWindow (auxiliaryRankSlice contact23) 36 4 = 13801566 :=
  contactRankWindow_of_rec contact23 36 4 13801566 (by decide +kernel)
private theorem contact23RanksSlice40 : sliceWindow (auxiliaryRankSlice contact23) 40 4 = 12610478 :=
  contactRankWindow_of_rec contact23 40 4 12610478 (by decide +kernel)
private theorem contact23RanksSlice44 : sliceWindow (auxiliaryRankSlice contact23) 44 4 = 11482494 :=
  contactRankWindow_of_rec contact23 44 4 11482494 (by decide +kernel)
private theorem contact23RanksSlice48 : sliceWindow (auxiliaryRankSlice contact23) 48 4 = 10417614 :=
  contactRankWindow_of_rec contact23 48 4 10417614 (by decide +kernel)
private theorem contact23RanksSlice52 : sliceWindow (auxiliaryRankSlice contact23) 52 4 = 9415634 :=
  contactRankWindow_of_rec contact23 52 4 9415634 (by decide +kernel)
private theorem contact23RanksSlice56 : sliceWindow (auxiliaryRankSlice contact23) 56 4 = 8475496 :=
  contactRankWindow_of_rec contact23 56 4 8475496 (by decide +kernel)
private theorem contact23RanksSlice60 : sliceWindow (auxiliaryRankSlice contact23) 60 4 = 7595938 :=
  contactRankWindow_of_rec contact23 60 4 7595938 (by decide +kernel)
private theorem contact23RanksSlice64 : sliceWindow (auxiliaryRankSlice contact23) 64 4 = 6775375 :=
  contactRankWindow_of_rec contact23 64 4 6775375 (by decide +kernel)
private theorem contact23RanksSlice68 : sliceWindow (auxiliaryRankSlice contact23) 68 4 = 6012084 :=
  contactRankWindow_of_rec contact23 68 4 6012084 (by decide +kernel)
private theorem contact23RanksSlice72 : sliceWindow (auxiliaryRankSlice contact23) 72 4 = 5304226 :=
  contactRankWindow_of_rec contact23 72 4 5304226 (by decide +kernel)
private theorem contact23RanksSlice76 : sliceWindow (auxiliaryRankSlice contact23) 76 4 = 4649943 :=
  contactRankWindow_of_rec contact23 76 4 4649943 (by decide +kernel)
private theorem contact23RanksSlice80 : sliceWindow (auxiliaryRankSlice contact23) 80 4 = 4047648 :=
  contactRankWindow_of_rec contact23 80 4 4047648 (by decide +kernel)
private theorem contact23RanksSlice84 : sliceWindow (auxiliaryRankSlice contact23) 84 4 = 3495362 :=
  contactRankWindow_of_rec contact23 84 4 3495362 (by decide +kernel)
private theorem contact23RanksSlice88 : sliceWindow (auxiliaryRankSlice contact23) 88 4 = 2991231 :=
  contactRankWindow_of_rec contact23 88 4 2991231 (by decide +kernel)
private theorem contact23RanksSlice92 : sliceWindow (auxiliaryRankSlice contact23) 92 4 = 2533804 :=
  contactRankWindow_of_rec contact23 92 4 2533804 (by decide +kernel)
private theorem contact23RanksSlice96 : sliceWindow (auxiliaryRankSlice contact23) 96 4 = 2120962 :=
  contactRankWindow_of_rec contact23 96 4 2120962 (by decide +kernel)
private theorem contact23RanksSlice100 : sliceWindow (auxiliaryRankSlice contact23) 100 4 = 1750855 :=
  contactRankWindow_of_rec contact23 100 4 1750855 (by decide +kernel)
private theorem contact23RanksSlice104 : sliceWindow (auxiliaryRankSlice contact23) 104 4 = 1422168 :=
  contactRankWindow_of_rec contact23 104 4 1422168 (by decide +kernel)
private theorem contact23RanksSlice108 : sliceWindow (auxiliaryRankSlice contact23) 108 4 = 1132642 :=
  contactRankWindow_of_rec contact23 108 4 1132642 (by decide +kernel)
private theorem contact23RanksSlice112 : sliceWindow (auxiliaryRankSlice contact23) 112 4 = 880431 :=
  contactRankWindow_of_rec contact23 112 4 880431 (by decide +kernel)
private theorem contact23RanksSlice116 : sliceWindow (auxiliaryRankSlice contact23) 116 4 = 664356 :=
  contactRankWindow_of_rec contact23 116 4 664356 (by decide +kernel)
private theorem contact23RanksSlice120 : sliceWindow (auxiliaryRankSlice contact23) 120 4 = 482018 :=
  contactRankWindow_of_rec contact23 120 4 482018 (by decide +kernel)
private theorem contact23RanksSlice124 : sliceWindow (auxiliaryRankSlice contact23) 124 4 = 331575 :=
  contactRankWindow_of_rec contact23 124 4 331575 (by decide +kernel)
private theorem contact23RanksSlice128 : sliceWindow (auxiliaryRankSlice contact23) 128 4 = 211984 :=
  contactRankWindow_of_rec contact23 128 4 211984 (by decide +kernel)
private theorem contact23RanksSlice132 : sliceWindow (auxiliaryRankSlice contact23) 132 4 = 120706 :=
  contactRankWindow_of_rec contact23 132 4 120706 (by decide +kernel)
private theorem contact23RanksSlice136 : sliceWindow (auxiliaryRankSlice contact23) 136 4 = 55918 :=
  contactRankWindow_of_rec contact23 136 4 55918 (by decide +kernel)
private theorem contact23RanksSlice140 : sliceWindow (auxiliaryRankSlice contact23) 140 4 = 16907 :=
  contactRankWindow_of_rec contact23 140 4 16907 (by decide +kernel)
private theorem contact23RanksSlice144 : sliceWindow (auxiliaryRankSlice contact23) 144 4 = 950 :=
  contactRankWindow_of_rec contact23 144 4 950 (by decide +kernel)
private theorem contact23RanksSlice148 : sliceWindow (auxiliaryRankSlice contact23) 148 13 = 0 :=
  contactRankWindow_of_rec contact23 148 13 0 (by decide +kernel)
private theorem contact23RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact23) 0 8 = 52963052 :=
  combineSlices (auxiliaryRankSlice contact23) 0 4 4 27361038 25602014 contact23RanksSlice0 contact23RanksSlice4
private theorem contact23RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact23) 8 8 = 46179372 :=
  combineSlices (auxiliaryRankSlice contact23) 8 4 4 23906094 22273278 contact23RanksSlice8 contact23RanksSlice12
private theorem contact23RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact23) 16 8 = 39900524 :=
  combineSlices (auxiliaryRankSlice contact23) 16 4 4 20703566 19196958 contact23RanksSlice16 contact23RanksSlice20
private theorem contact23RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact23) 24 8 = 34126508 :=
  combineSlices (auxiliaryRankSlice contact23) 24 4 4 17753454 16373054 contact23RanksSlice24 contact23RanksSlice28
private theorem contact23RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact23) 32 8 = 28857324 :=
  combineSlices (auxiliaryRankSlice contact23) 32 4 4 15055758 13801566 contact23RanksSlice32 contact23RanksSlice36
private theorem contact23RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact23) 40 8 = 24092972 :=
  combineSlices (auxiliaryRankSlice contact23) 40 4 4 12610478 11482494 contact23RanksSlice40 contact23RanksSlice44
private theorem contact23RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact23) 48 8 = 19833248 :=
  combineSlices (auxiliaryRankSlice contact23) 48 4 4 10417614 9415634 contact23RanksSlice48 contact23RanksSlice52
private theorem contact23RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact23) 56 8 = 16071434 :=
  combineSlices (auxiliaryRankSlice contact23) 56 4 4 8475496 7595938 contact23RanksSlice56 contact23RanksSlice60
private theorem contact23RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact23) 64 8 = 12787459 :=
  combineSlices (auxiliaryRankSlice contact23) 64 4 4 6775375 6012084 contact23RanksSlice64 contact23RanksSlice68
private theorem contact23RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact23) 72 8 = 9954169 :=
  combineSlices (auxiliaryRankSlice contact23) 72 4 4 5304226 4649943 contact23RanksSlice72 contact23RanksSlice76
private theorem contact23RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact23) 80 8 = 7543010 :=
  combineSlices (auxiliaryRankSlice contact23) 80 4 4 4047648 3495362 contact23RanksSlice80 contact23RanksSlice84
private theorem contact23RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact23) 88 8 = 5525035 :=
  combineSlices (auxiliaryRankSlice contact23) 88 4 4 2991231 2533804 contact23RanksSlice88 contact23RanksSlice92
private theorem contact23RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact23) 96 8 = 3871817 :=
  combineSlices (auxiliaryRankSlice contact23) 96 4 4 2120962 1750855 contact23RanksSlice96 contact23RanksSlice100
private theorem contact23RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact23) 104 8 = 2554810 :=
  combineSlices (auxiliaryRankSlice contact23) 104 4 4 1422168 1132642 contact23RanksSlice104 contact23RanksSlice108
private theorem contact23RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact23) 112 8 = 1544787 :=
  combineSlices (auxiliaryRankSlice contact23) 112 4 4 880431 664356 contact23RanksSlice112 contact23RanksSlice116
private theorem contact23RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact23) 120 8 = 813593 :=
  combineSlices (auxiliaryRankSlice contact23) 120 4 4 482018 331575 contact23RanksSlice120 contact23RanksSlice124
private theorem contact23RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact23) 128 8 = 332690 :=
  combineSlices (auxiliaryRankSlice contact23) 128 4 4 211984 120706 contact23RanksSlice128 contact23RanksSlice132
private theorem contact23RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact23) 136 8 = 72825 :=
  combineSlices (auxiliaryRankSlice contact23) 136 4 4 55918 16907 contact23RanksSlice136 contact23RanksSlice140
private theorem contact23RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact23) 144 17 = 950 :=
  combineSlices (auxiliaryRankSlice contact23) 144 4 13 950 0 contact23RanksSlice144 contact23RanksSlice148
private theorem contact23RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact23) 0 16 = 99142424 :=
  combineSlices (auxiliaryRankSlice contact23) 0 8 8 52963052 46179372 contact23RanksJoin0_8 contact23RanksJoin8_8
private theorem contact23RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact23) 16 16 = 74027032 :=
  combineSlices (auxiliaryRankSlice contact23) 16 8 8 39900524 34126508 contact23RanksJoin16_8 contact23RanksJoin24_8
private theorem contact23RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact23) 32 16 = 52950296 :=
  combineSlices (auxiliaryRankSlice contact23) 32 8 8 28857324 24092972 contact23RanksJoin32_8 contact23RanksJoin40_8
private theorem contact23RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact23) 48 16 = 35904682 :=
  combineSlices (auxiliaryRankSlice contact23) 48 8 8 19833248 16071434 contact23RanksJoin48_8 contact23RanksJoin56_8
private theorem contact23RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact23) 64 16 = 22741628 :=
  combineSlices (auxiliaryRankSlice contact23) 64 8 8 12787459 9954169 contact23RanksJoin64_8 contact23RanksJoin72_8
private theorem contact23RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact23) 80 16 = 13068045 :=
  combineSlices (auxiliaryRankSlice contact23) 80 8 8 7543010 5525035 contact23RanksJoin80_8 contact23RanksJoin88_8
private theorem contact23RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact23) 96 16 = 6426627 :=
  combineSlices (auxiliaryRankSlice contact23) 96 8 8 3871817 2554810 contact23RanksJoin96_8 contact23RanksJoin104_8
private theorem contact23RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact23) 112 16 = 2358380 :=
  combineSlices (auxiliaryRankSlice contact23) 112 8 8 1544787 813593 contact23RanksJoin112_8 contact23RanksJoin120_8
private theorem contact23RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact23) 128 16 = 405515 :=
  combineSlices (auxiliaryRankSlice contact23) 128 8 8 332690 72825 contact23RanksJoin128_8 contact23RanksJoin136_8
private theorem contact23RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact23) 0 32 = 173169456 :=
  combineSlices (auxiliaryRankSlice contact23) 0 16 16 99142424 74027032 contact23RanksJoin0_16 contact23RanksJoin16_16
private theorem contact23RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact23) 32 32 = 88854978 :=
  combineSlices (auxiliaryRankSlice contact23) 32 16 16 52950296 35904682 contact23RanksJoin32_16 contact23RanksJoin48_16
private theorem contact23RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact23) 64 32 = 35809673 :=
  combineSlices (auxiliaryRankSlice contact23) 64 16 16 22741628 13068045 contact23RanksJoin64_16 contact23RanksJoin80_16
private theorem contact23RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact23) 96 32 = 8785007 :=
  combineSlices (auxiliaryRankSlice contact23) 96 16 16 6426627 2358380 contact23RanksJoin96_16 contact23RanksJoin112_16
private theorem contact23RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact23) 128 33 = 406465 :=
  combineSlices (auxiliaryRankSlice contact23) 128 16 17 405515 950 contact23RanksJoin128_16 contact23RanksJoin144_17
private theorem contact23RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact23) 0 64 = 262024434 :=
  combineSlices (auxiliaryRankSlice contact23) 0 32 32 173169456 88854978 contact23RanksJoin0_32 contact23RanksJoin32_32
private theorem contact23RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact23) 64 64 = 44594680 :=
  combineSlices (auxiliaryRankSlice contact23) 64 32 32 35809673 8785007 contact23RanksJoin64_32 contact23RanksJoin96_32
private theorem contact23RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact23) 0 128 = 306619114 :=
  combineSlices (auxiliaryRankSlice contact23) 0 64 64 262024434 44594680 contact23RanksJoin0_64 contact23RanksJoin64_64
private theorem contact23RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact23) 0 161 = 307025579 :=
  combineSlices (auxiliaryRankSlice contact23) 0 128 33 306619114 406465 contact23RanksJoin0_128 contact23RanksJoin128_33
theorem contact23_margin : sourceMargin contact23 :=
  margin_of_checked_counts contact23 161 2312877254950217 100944213416986 8900968487 307025579 rfl contact23OrdinaryColumns contact23ColumnsJoin0_161 contact23OrdinaryRanks contact23RanksJoin0_161 (by decide +kernel)

private theorem contact25OrdinaryColumns : ordinaryColumnCount contact25 = 2296478716050185 := by decide +kernel
private theorem contact25ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact25) 0 4 = 7596399618000 :=
  contactColumnsWindow_fast contact25 0 4 7596399618000 (by decide +kernel)
private theorem contact25ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact25) 4 4 = 7219221676240 :=
  contactColumnsWindow_fast contact25 4 4 7219221676240 (by decide +kernel)
private theorem contact25ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact25) 8 4 = 6851694825344 :=
  contactColumnsWindow_fast contact25 8 4 6851694825344 (by decide +kernel)
private theorem contact25ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact25) 12 4 = 6493822123824 :=
  contactColumnsWindow_fast contact25 12 4 6493822123824 (by decide +kernel)
private theorem contact25ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact25) 16 4 = 6145601482417 :=
  contactColumnsWindow_fast contact25 16 4 6145601482417 (by decide +kernel)
private theorem contact25ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact25) 20 4 = 5807034975356 :=
  contactColumnsWindow_fast contact25 20 4 5807034975356 (by decide +kernel)
private theorem contact25ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact25) 24 4 = 5478140288080 :=
  contactColumnsWindow_fast contact25 24 4 5478140288080 (by decide +kernel)
private theorem contact25ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact25) 28 4 = 5158938152132 :=
  contactColumnsWindow_fast contact25 28 4 5158938152132 (by decide +kernel)
private theorem contact25ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact25) 32 4 = 4849393549152 :=
  contactColumnsWindow_fast contact25 32 4 4849393549152 (by decide +kernel)
private theorem contact25ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact25) 36 4 = 4549504314295 :=
  contactColumnsWindow_fast contact25 36 4 4549504314295 (by decide +kernel)
private theorem contact25ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact25) 40 4 = 4259272489444 :=
  contactColumnsWindow_fast contact25 40 4 4259272489444 (by decide +kernel)
private theorem contact25ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact25) 44 4 = 3978720135907 :=
  contactColumnsWindow_fast contact25 44 4 3978720135907 (by decide +kernel)
private theorem contact25ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact25) 48 4 = 3707860522904 :=
  contactColumnsWindow_fast contact25 48 4 3707860522904 (by decide +kernel)
private theorem contact25ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact25) 52 4 = 3446660168610 :=
  contactColumnsWindow_fast contact25 52 4 3446660168610 (by decide +kernel)
private theorem contact25ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact25) 56 4 = 3195119736292 :=
  contactColumnsWindow_fast contact25 56 4 3195119736292 (by decide +kernel)
private theorem contact25ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact25) 60 4 = 2953238923634 :=
  contactColumnsWindow_fast contact25 60 4 2953238923634 (by decide +kernel)
private theorem contact25ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact25) 64 4 = 2721048089757 :=
  contactColumnsWindow_fast contact25 64 4 2721048089757 (by decide +kernel)
private theorem contact25ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact25) 68 4 = 2498546832297 :=
  contactColumnsWindow_fast contact25 68 4 2498546832297 (by decide +kernel)
private theorem contact25ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact25) 72 4 = 2285710039200 :=
  contactColumnsWindow_fast contact25 72 4 2285710039200 (by decide +kernel)
private theorem contact25ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact25) 76 4 = 2082533680276 :=
  contactColumnsWindow_fast contact25 76 4 2082533680276 (by decide +kernel)
private theorem contact25ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact25) 80 4 = 1889016697286 :=
  contactColumnsWindow_fast contact25 80 4 1889016697286 (by decide +kernel)
private theorem contact25ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact25) 84 4 = 1705195460602 :=
  contactColumnsWindow_fast contact25 84 4 1705195460602 (by decide +kernel)
private theorem contact25ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact25) 88 4 = 1531058736095 :=
  contactColumnsWindow_fast contact25 88 4 1531058736095 (by decide +kernel)
private theorem contact25ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact25) 92 4 = 1366585958184 :=
  contactColumnsWindow_fast contact25 92 4 1366585958184 (by decide +kernel)
private theorem contact25ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact25) 96 4 = 1211773641364 :=
  contactColumnsWindow_fast contact25 96 4 1211773641364 (by decide +kernel)
private theorem contact25ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact25) 100 4 = 1066621791011 :=
  contactColumnsWindow_fast contact25 100 4 1066621791011 (by decide +kernel)
private theorem contact25ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact25) 104 4 = 931168938190 :=
  contactColumnsWindow_fast contact25 104 4 931168938190 (by decide +kernel)
private theorem contact25ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact25) 108 4 = 805396705949 :=
  contactColumnsWindow_fast contact25 108 4 805396705949 (by decide +kernel)
private theorem contact25ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact25) 112 4 = 689287969327 :=
  contactColumnsWindow_fast contact25 112 4 689287969327 (by decide +kernel)
private theorem contact25ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact25) 116 4 = 582839758912 :=
  contactColumnsWindow_fast contact25 116 4 582839758912 (by decide +kernel)
private theorem contact25ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact25) 120 4 = 486053252837 :=
  contactColumnsWindow_fast contact25 120 4 486053252837 (by decide +kernel)
private theorem contact25ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact25) 124 4 = 398968433623 :=
  contactColumnsWindow_fast contact25 124 4 398968433623 (by decide +kernel)
private theorem contact25ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact25) 128 4 = 321560823926 :=
  contactColumnsWindow_fast contact25 128 4 321560823926 (by decide +kernel)
private theorem contact25ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact25) 132 4 = 253810463596 :=
  contactColumnsWindow_fast contact25 132 4 253810463596 (by decide +kernel)
private theorem contact25ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact25) 136 4 = 195619254185 :=
  contactColumnsWindow_fast contact25 136 4 195619254185 (by decide +kernel)
private theorem contact25ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact25) 140 4 = 146695915644 :=
  contactColumnsWindow_fast contact25 140 4 146695915644 (by decide +kernel)
private theorem contact25ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact25) 144 4 = 106615629990 :=
  contactColumnsWindow_fast contact25 144 4 106615629990 (by decide +kernel)
private theorem contact25ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact25) 148 4 = 74720440427 :=
  contactColumnsWindow_fast contact25 148 4 74720440427 (by decide +kernel)
private theorem contact25ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact25) 152 4 = 50210932182 :=
  contactColumnsWindow_fast contact25 152 4 50210932182 (by decide +kernel)
private theorem contact25ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact25) 156 4 = 32136646594 :=
  contactColumnsWindow_fast contact25 156 4 32136646594 (by decide +kernel)
private theorem contact25ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact25) 160 1 = 5862093927 :=
  contactColumnsWindow_fast contact25 160 1 5862093927 (by decide +kernel)
private theorem contact25ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact25) 0 8 = 14815621294240 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 4 4 7596399618000 7219221676240 contact25ColumnsSlice0 contact25ColumnsSlice4
private theorem contact25ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact25) 8 8 = 13345516949168 :=
  combineSlices (auxiliaryColumnSlice contact25) 8 4 4 6851694825344 6493822123824 contact25ColumnsSlice8 contact25ColumnsSlice12
private theorem contact25ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact25) 16 8 = 11952636457773 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 4 4 6145601482417 5807034975356 contact25ColumnsSlice16 contact25ColumnsSlice20
private theorem contact25ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact25) 24 8 = 10637078440212 :=
  combineSlices (auxiliaryColumnSlice contact25) 24 4 4 5478140288080 5158938152132 contact25ColumnsSlice24 contact25ColumnsSlice28
private theorem contact25ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact25) 32 8 = 9398897863447 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 4 4 4849393549152 4549504314295 contact25ColumnsSlice32 contact25ColumnsSlice36
private theorem contact25ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact25) 40 8 = 8237992625351 :=
  combineSlices (auxiliaryColumnSlice contact25) 40 4 4 4259272489444 3978720135907 contact25ColumnsSlice40 contact25ColumnsSlice44
private theorem contact25ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact25) 48 8 = 7154520691514 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 4 4 3707860522904 3446660168610 contact25ColumnsSlice48 contact25ColumnsSlice52
private theorem contact25ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact25) 56 8 = 6148358659926 :=
  combineSlices (auxiliaryColumnSlice contact25) 56 4 4 3195119736292 2953238923634 contact25ColumnsSlice56 contact25ColumnsSlice60
private theorem contact25ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact25) 64 8 = 5219594922054 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 4 4 2721048089757 2498546832297 contact25ColumnsSlice64 contact25ColumnsSlice68
private theorem contact25ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact25) 72 8 = 4368243719476 :=
  combineSlices (auxiliaryColumnSlice contact25) 72 4 4 2285710039200 2082533680276 contact25ColumnsSlice72 contact25ColumnsSlice76
private theorem contact25ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact25) 80 8 = 3594212157888 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 4 4 1889016697286 1705195460602 contact25ColumnsSlice80 contact25ColumnsSlice84
private theorem contact25ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact25) 88 8 = 2897644694279 :=
  combineSlices (auxiliaryColumnSlice contact25) 88 4 4 1531058736095 1366585958184 contact25ColumnsSlice88 contact25ColumnsSlice92
private theorem contact25ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact25) 96 8 = 2278395432375 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 4 4 1211773641364 1066621791011 contact25ColumnsSlice96 contact25ColumnsSlice100
private theorem contact25ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact25) 104 8 = 1736565644139 :=
  combineSlices (auxiliaryColumnSlice contact25) 104 4 4 931168938190 805396705949 contact25ColumnsSlice104 contact25ColumnsSlice108
private theorem contact25ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact25) 112 8 = 1272127728239 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 4 4 689287969327 582839758912 contact25ColumnsSlice112 contact25ColumnsSlice116
private theorem contact25ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact25) 120 8 = 885021686460 :=
  combineSlices (auxiliaryColumnSlice contact25) 120 4 4 486053252837 398968433623 contact25ColumnsSlice120 contact25ColumnsSlice124
private theorem contact25ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact25) 128 8 = 575371287522 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 4 4 321560823926 253810463596 contact25ColumnsSlice128 contact25ColumnsSlice132
private theorem contact25ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact25) 136 8 = 342315169829 :=
  combineSlices (auxiliaryColumnSlice contact25) 136 4 4 195619254185 146695915644 contact25ColumnsSlice136 contact25ColumnsSlice140
private theorem contact25ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact25) 144 8 = 181336070417 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 4 4 106615629990 74720440427 contact25ColumnsSlice144 contact25ColumnsSlice148
private theorem contact25ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact25) 152 8 = 82347578776 :=
  combineSlices (auxiliaryColumnSlice contact25) 152 4 4 50210932182 32136646594 contact25ColumnsSlice152 contact25ColumnsSlice156
private theorem contact25ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact25) 0 16 = 28161138243408 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 8 8 14815621294240 13345516949168 contact25ColumnsJoin0_8 contact25ColumnsJoin8_8
private theorem contact25ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact25) 16 16 = 22589714897985 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 8 8 11952636457773 10637078440212 contact25ColumnsJoin16_8 contact25ColumnsJoin24_8
private theorem contact25ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact25) 32 16 = 17636890488798 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 8 8 9398897863447 8237992625351 contact25ColumnsJoin32_8 contact25ColumnsJoin40_8
private theorem contact25ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact25) 48 16 = 13302879351440 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 8 8 7154520691514 6148358659926 contact25ColumnsJoin48_8 contact25ColumnsJoin56_8
private theorem contact25ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact25) 64 16 = 9587838641530 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 8 8 5219594922054 4368243719476 contact25ColumnsJoin64_8 contact25ColumnsJoin72_8
private theorem contact25ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact25) 80 16 = 6491856852167 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 8 8 3594212157888 2897644694279 contact25ColumnsJoin80_8 contact25ColumnsJoin88_8
private theorem contact25ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact25) 96 16 = 4014961076514 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 8 8 2278395432375 1736565644139 contact25ColumnsJoin96_8 contact25ColumnsJoin104_8
private theorem contact25ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact25) 112 16 = 2157149414699 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 8 8 1272127728239 885021686460 contact25ColumnsJoin112_8 contact25ColumnsJoin120_8
private theorem contact25ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact25) 128 16 = 917686457351 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 8 8 575371287522 342315169829 contact25ColumnsJoin128_8 contact25ColumnsJoin136_8
private theorem contact25ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact25) 144 16 = 263683649193 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 8 8 181336070417 82347578776 contact25ColumnsJoin144_8 contact25ColumnsJoin152_8
private theorem contact25ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact25) 0 32 = 50750853141393 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 16 16 28161138243408 22589714897985 contact25ColumnsJoin0_16 contact25ColumnsJoin16_16
private theorem contact25ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact25) 32 32 = 30939769840238 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 16 16 17636890488798 13302879351440 contact25ColumnsJoin32_16 contact25ColumnsJoin48_16
private theorem contact25ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact25) 64 32 = 16079695493697 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 16 16 9587838641530 6491856852167 contact25ColumnsJoin64_16 contact25ColumnsJoin80_16
private theorem contact25ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact25) 96 32 = 6172110491213 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 16 16 4014961076514 2157149414699 contact25ColumnsJoin96_16 contact25ColumnsJoin112_16
private theorem contact25ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact25) 128 32 = 1181370106544 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 16 16 917686457351 263683649193 contact25ColumnsJoin128_16 contact25ColumnsJoin144_16
private theorem contact25ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact25) 0 64 = 81690622981631 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 32 32 50750853141393 30939769840238 contact25ColumnsJoin0_32 contact25ColumnsJoin32_32
private theorem contact25ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact25) 64 64 = 22251805984910 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 32 32 16079695493697 6172110491213 contact25ColumnsJoin64_32 contact25ColumnsJoin96_32
private theorem contact25ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact25) 128 33 = 1187232200471 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 32 1 1181370106544 5862093927 contact25ColumnsJoin128_32 contact25ColumnsSlice160
private theorem contact25ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact25) 0 128 = 103942428966541 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 64 64 81690622981631 22251805984910 contact25ColumnsJoin0_64 contact25ColumnsJoin64_64
private theorem contact25ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact25) 0 161 = 105129661167012 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 128 33 103942428966541 1187232200471 contact25ColumnsJoin0_128 contact25ColumnsJoin128_33
private theorem contact25OrdinaryRanks : ordinaryRankBound contact25 = 8840200495 := by decide +kernel
private theorem contact25RanksSlice0 : sliceWindow (auxiliaryRankSlice contact25) 0 4 = 28633648 :=
  contactRankWindow_of_rec contact25 0 4 28633648 (by decide +kernel)
private theorem contact25RanksSlice4 : sliceWindow (auxiliaryRankSlice contact25) 4 4 = 26787856 :=
  contactRankWindow_of_rec contact25 4 4 26787856 (by decide +kernel)
private theorem contact25RanksSlice8 : sliceWindow (auxiliaryRankSlice contact25) 8 4 = 25008880 :=
  contactRankWindow_of_rec contact25 8 4 25008880 (by decide +kernel)
private theorem contact25RanksSlice12 : sliceWindow (auxiliaryRankSlice contact25) 12 4 = 23296720 :=
  contactRankWindow_of_rec contact25 12 4 23296720 (by decide +kernel)
private theorem contact25RanksSlice16 : sliceWindow (auxiliaryRankSlice contact25) 16 4 = 21651376 :=
  contactRankWindow_of_rec contact25 16 4 21651376 (by decide +kernel)
private theorem contact25RanksSlice20 : sliceWindow (auxiliaryRankSlice contact25) 20 4 = 20072848 :=
  contactRankWindow_of_rec contact25 20 4 20072848 (by decide +kernel)
private theorem contact25RanksSlice24 : sliceWindow (auxiliaryRankSlice contact25) 24 4 = 18561136 :=
  contactRankWindow_of_rec contact25 24 4 18561136 (by decide +kernel)
private theorem contact25RanksSlice28 : sliceWindow (auxiliaryRankSlice contact25) 28 4 = 17116240 :=
  contactRankWindow_of_rec contact25 28 4 17116240 (by decide +kernel)
private theorem contact25RanksSlice32 : sliceWindow (auxiliaryRankSlice contact25) 32 4 = 15738160 :=
  contactRankWindow_of_rec contact25 32 4 15738160 (by decide +kernel)
private theorem contact25RanksSlice36 : sliceWindow (auxiliaryRankSlice contact25) 36 4 = 14426896 :=
  contactRankWindow_of_rec contact25 36 4 14426896 (by decide +kernel)
private theorem contact25RanksSlice40 : sliceWindow (auxiliaryRankSlice contact25) 40 4 = 13182448 :=
  contactRankWindow_of_rec contact25 40 4 13182448 (by decide +kernel)
private theorem contact25RanksSlice44 : sliceWindow (auxiliaryRankSlice contact25) 44 4 = 12004816 :=
  contactRankWindow_of_rec contact25 44 4 12004816 (by decide +kernel)
private theorem contact25RanksSlice48 : sliceWindow (auxiliaryRankSlice contact25) 48 4 = 10893796 :=
  contactRankWindow_of_rec contact25 48 4 10893796 (by decide +kernel)
private theorem contact25RanksSlice52 : sliceWindow (auxiliaryRankSlice contact25) 52 4 = 9848330 :=
  contactRankWindow_of_rec contact25 52 4 9848330 (by decide +kernel)
private theorem contact25RanksSlice56 : sliceWindow (auxiliaryRankSlice contact25) 56 4 = 8867156 :=
  contactRankWindow_of_rec contact25 56 4 8867156 (by decide +kernel)
private theorem contact25RanksSlice60 : sliceWindow (auxiliaryRankSlice contact25) 60 4 = 7948956 :=
  contactRankWindow_of_rec contact25 60 4 7948956 (by decide +kernel)
private theorem contact25RanksSlice64 : sliceWindow (auxiliaryRankSlice contact25) 64 4 = 7092103 :=
  contactRankWindow_of_rec contact25 64 4 7092103 (by decide +kernel)
private theorem contact25RanksSlice68 : sliceWindow (auxiliaryRankSlice contact25) 68 4 = 6294844 :=
  contactRankWindow_of_rec contact25 68 4 6294844 (by decide +kernel)
private theorem contact25RanksSlice72 : sliceWindow (auxiliaryRankSlice contact25) 72 4 = 5555256 :=
  contactRankWindow_of_rec contact25 72 4 5555256 (by decide +kernel)
private theorem contact25RanksSlice76 : sliceWindow (auxiliaryRankSlice contact25) 76 4 = 4871423 :=
  contactRankWindow_of_rec contact25 76 4 4871423 (by decide +kernel)
private theorem contact25RanksSlice80 : sliceWindow (auxiliaryRankSlice contact25) 80 4 = 4241732 :=
  contactRankWindow_of_rec contact25 80 4 4241732 (by decide +kernel)
private theorem contact25RanksSlice84 : sliceWindow (auxiliaryRankSlice contact25) 84 4 = 3664116 :=
  contactRankWindow_of_rec contact25 84 4 3664116 (by decide +kernel)
private theorem contact25RanksSlice88 : sliceWindow (auxiliaryRankSlice contact25) 88 4 = 3136663 :=
  contactRankWindow_of_rec contact25 88 4 3136663 (by decide +kernel)
private theorem contact25RanksSlice92 : sliceWindow (auxiliaryRankSlice contact25) 92 4 = 2657900 :=
  contactRankWindow_of_rec contact25 92 4 2657900 (by decide +kernel)
private theorem contact25RanksSlice96 : sliceWindow (auxiliaryRankSlice contact25) 96 4 = 2225616 :=
  contactRankWindow_of_rec contact25 96 4 2225616 (by decide +kernel)
private theorem contact25RanksSlice100 : sliceWindow (auxiliaryRankSlice contact25) 100 4 = 1837903 :=
  contactRankWindow_of_rec contact25 100 4 1837903 (by decide +kernel)
private theorem contact25RanksSlice104 : sliceWindow (auxiliaryRankSlice contact25) 104 4 = 1493428 :=
  contactRankWindow_of_rec contact25 104 4 1493428 (by decide +kernel)
private theorem contact25RanksSlice108 : sliceWindow (auxiliaryRankSlice contact25) 108 4 = 1189836 :=
  contactRankWindow_of_rec contact25 108 4 1189836 (by decide +kernel)
private theorem contact25RanksSlice112 : sliceWindow (auxiliaryRankSlice contact25) 112 4 = 925223 :=
  contactRankWindow_of_rec contact25 112 4 925223 (by decide +kernel)
private theorem contact25RanksSlice116 : sliceWindow (auxiliaryRankSlice contact25) 116 4 = 698396 :=
  contactRankWindow_of_rec contact25 116 4 698396 (by decide +kernel)
private theorem contact25RanksSlice120 : sliceWindow (auxiliaryRankSlice contact25) 120 4 = 506856 :=
  contactRankWindow_of_rec contact25 120 4 506856 (by decide +kernel)
private theorem contact25RanksSlice124 : sliceWindow (auxiliaryRankSlice contact25) 124 4 = 348703 :=
  contactRankWindow_of_rec contact25 124 4 348703 (by decide +kernel)
private theorem contact25RanksSlice128 : sliceWindow (auxiliaryRankSlice contact25) 128 4 = 222884 :=
  contactRankWindow_of_rec contact25 128 4 222884 (by decide +kernel)
private theorem contact25RanksSlice132 : sliceWindow (auxiliaryRankSlice contact25) 132 4 = 126756 :=
  contactRankWindow_of_rec contact25 132 4 126756 (by decide +kernel)
private theorem contact25RanksSlice136 : sliceWindow (auxiliaryRankSlice contact25) 136 4 = 58534 :=
  contactRankWindow_of_rec contact25 136 4 58534 (by decide +kernel)
private theorem contact25RanksSlice140 : sliceWindow (auxiliaryRankSlice contact25) 140 4 = 17638 :=
  contactRankWindow_of_rec contact25 140 4 17638 (by decide +kernel)
private theorem contact25RanksSlice144 : sliceWindow (auxiliaryRankSlice contact25) 144 4 = 989 :=
  contactRankWindow_of_rec contact25 144 4 989 (by decide +kernel)
private theorem contact25RanksSlice148 : sliceWindow (auxiliaryRankSlice contact25) 148 13 = 0 :=
  contactRankWindow_of_rec contact25 148 13 0 (by decide +kernel)
private theorem contact25RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact25) 0 8 = 55421504 :=
  combineSlices (auxiliaryRankSlice contact25) 0 4 4 28633648 26787856 contact25RanksSlice0 contact25RanksSlice4
private theorem contact25RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact25) 8 8 = 48305600 :=
  combineSlices (auxiliaryRankSlice contact25) 8 4 4 25008880 23296720 contact25RanksSlice8 contact25RanksSlice12
private theorem contact25RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact25) 16 8 = 41724224 :=
  combineSlices (auxiliaryRankSlice contact25) 16 4 4 21651376 20072848 contact25RanksSlice16 contact25RanksSlice20
private theorem contact25RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact25) 24 8 = 35677376 :=
  combineSlices (auxiliaryRankSlice contact25) 24 4 4 18561136 17116240 contact25RanksSlice24 contact25RanksSlice28
private theorem contact25RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact25) 32 8 = 30165056 :=
  combineSlices (auxiliaryRankSlice contact25) 32 4 4 15738160 14426896 contact25RanksSlice32 contact25RanksSlice36
private theorem contact25RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact25) 40 8 = 25187264 :=
  combineSlices (auxiliaryRankSlice contact25) 40 4 4 13182448 12004816 contact25RanksSlice40 contact25RanksSlice44
private theorem contact25RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact25) 48 8 = 20742126 :=
  combineSlices (auxiliaryRankSlice contact25) 48 4 4 10893796 9848330 contact25RanksSlice48 contact25RanksSlice52
private theorem contact25RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact25) 56 8 = 16816112 :=
  combineSlices (auxiliaryRankSlice contact25) 56 4 4 8867156 7948956 contact25RanksSlice56 contact25RanksSlice60
private theorem contact25RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact25) 64 8 = 13386947 :=
  combineSlices (auxiliaryRankSlice contact25) 64 4 4 7092103 6294844 contact25RanksSlice64 contact25RanksSlice68
private theorem contact25RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact25) 72 8 = 10426679 :=
  combineSlices (auxiliaryRankSlice contact25) 72 4 4 5555256 4871423 contact25RanksSlice72 contact25RanksSlice76
private theorem contact25RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact25) 80 8 = 7905848 :=
  combineSlices (auxiliaryRankSlice contact25) 80 4 4 4241732 3664116 contact25RanksSlice80 contact25RanksSlice84
private theorem contact25RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact25) 88 8 = 5794563 :=
  combineSlices (auxiliaryRankSlice contact25) 88 4 4 3136663 2657900 contact25RanksSlice88 contact25RanksSlice92
private theorem contact25RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact25) 96 8 = 4063519 :=
  combineSlices (auxiliaryRankSlice contact25) 96 4 4 2225616 1837903 contact25RanksSlice96 contact25RanksSlice100
private theorem contact25RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact25) 104 8 = 2683264 :=
  combineSlices (auxiliaryRankSlice contact25) 104 4 4 1493428 1189836 contact25RanksSlice104 contact25RanksSlice108
private theorem contact25RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact25) 112 8 = 1623619 :=
  combineSlices (auxiliaryRankSlice contact25) 112 4 4 925223 698396 contact25RanksSlice112 contact25RanksSlice116
private theorem contact25RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact25) 120 8 = 855559 :=
  combineSlices (auxiliaryRankSlice contact25) 120 4 4 506856 348703 contact25RanksSlice120 contact25RanksSlice124
private theorem contact25RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact25) 128 8 = 349640 :=
  combineSlices (auxiliaryRankSlice contact25) 128 4 4 222884 126756 contact25RanksSlice128 contact25RanksSlice132
private theorem contact25RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact25) 136 8 = 76172 :=
  combineSlices (auxiliaryRankSlice contact25) 136 4 4 58534 17638 contact25RanksSlice136 contact25RanksSlice140
private theorem contact25RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact25) 144 17 = 989 :=
  combineSlices (auxiliaryRankSlice contact25) 144 4 13 989 0 contact25RanksSlice144 contact25RanksSlice148
private theorem contact25RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact25) 0 16 = 103727104 :=
  combineSlices (auxiliaryRankSlice contact25) 0 8 8 55421504 48305600 contact25RanksJoin0_8 contact25RanksJoin8_8
private theorem contact25RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact25) 16 16 = 77401600 :=
  combineSlices (auxiliaryRankSlice contact25) 16 8 8 41724224 35677376 contact25RanksJoin16_8 contact25RanksJoin24_8
private theorem contact25RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact25) 32 16 = 55352320 :=
  combineSlices (auxiliaryRankSlice contact25) 32 8 8 30165056 25187264 contact25RanksJoin32_8 contact25RanksJoin40_8
private theorem contact25RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact25) 48 16 = 37558238 :=
  combineSlices (auxiliaryRankSlice contact25) 48 8 8 20742126 16816112 contact25RanksJoin48_8 contact25RanksJoin56_8
private theorem contact25RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact25) 64 16 = 23813626 :=
  combineSlices (auxiliaryRankSlice contact25) 64 8 8 13386947 10426679 contact25RanksJoin64_8 contact25RanksJoin72_8
private theorem contact25RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact25) 80 16 = 13700411 :=
  combineSlices (auxiliaryRankSlice contact25) 80 8 8 7905848 5794563 contact25RanksJoin80_8 contact25RanksJoin88_8
private theorem contact25RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact25) 96 16 = 6746783 :=
  combineSlices (auxiliaryRankSlice contact25) 96 8 8 4063519 2683264 contact25RanksJoin96_8 contact25RanksJoin104_8
private theorem contact25RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact25) 112 16 = 2479178 :=
  combineSlices (auxiliaryRankSlice contact25) 112 8 8 1623619 855559 contact25RanksJoin112_8 contact25RanksJoin120_8
private theorem contact25RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact25) 128 16 = 425812 :=
  combineSlices (auxiliaryRankSlice contact25) 128 8 8 349640 76172 contact25RanksJoin128_8 contact25RanksJoin136_8
private theorem contact25RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact25) 0 32 = 181128704 :=
  combineSlices (auxiliaryRankSlice contact25) 0 16 16 103727104 77401600 contact25RanksJoin0_16 contact25RanksJoin16_16
private theorem contact25RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact25) 32 32 = 92910558 :=
  combineSlices (auxiliaryRankSlice contact25) 32 16 16 55352320 37558238 contact25RanksJoin32_16 contact25RanksJoin48_16
private theorem contact25RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact25) 64 32 = 37514037 :=
  combineSlices (auxiliaryRankSlice contact25) 64 16 16 23813626 13700411 contact25RanksJoin64_16 contact25RanksJoin80_16
private theorem contact25RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact25) 96 32 = 9225961 :=
  combineSlices (auxiliaryRankSlice contact25) 96 16 16 6746783 2479178 contact25RanksJoin96_16 contact25RanksJoin112_16
private theorem contact25RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact25) 128 33 = 426801 :=
  combineSlices (auxiliaryRankSlice contact25) 128 16 17 425812 989 contact25RanksJoin128_16 contact25RanksJoin144_17
private theorem contact25RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact25) 0 64 = 274039262 :=
  combineSlices (auxiliaryRankSlice contact25) 0 32 32 181128704 92910558 contact25RanksJoin0_32 contact25RanksJoin32_32
private theorem contact25RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact25) 64 64 = 46739998 :=
  combineSlices (auxiliaryRankSlice contact25) 64 32 32 37514037 9225961 contact25RanksJoin64_32 contact25RanksJoin96_32
private theorem contact25RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact25) 0 128 = 320779260 :=
  combineSlices (auxiliaryRankSlice contact25) 0 64 64 274039262 46739998 contact25RanksJoin0_64 contact25RanksJoin64_64
private theorem contact25RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact25) 0 161 = 321206061 :=
  combineSlices (auxiliaryRankSlice contact25) 0 128 33 320779260 426801 contact25RanksJoin0_128 contact25RanksJoin128_33
theorem contact25_margin : sourceMargin contact25 :=
  margin_of_checked_counts contact25 161 2296478716050185 105129661167012 8840200495 321206061 rfl contact25OrdinaryColumns contact25ColumnsJoin0_161 contact25OrdinaryRanks contact25RanksJoin0_161 (by decide +kernel)

private theorem contact27OrdinaryColumns : ordinaryColumnCount contact27 = 2286299000566185 := by decide +kernel
private theorem contact27ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact27) 0 4 = 7428507243190 :=
  contactColumnsWindow_fast contact27 0 4 7428507243190 (by decide +kernel)
private theorem contact27ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact27) 4 4 = 7060677295510 :=
  contactColumnsWindow_fast contact27 4 4 7060677295510 (by decide +kernel)
private theorem contact27ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact27) 8 4 = 6702230358364 :=
  contactColumnsWindow_fast contact27 8 4 6702230358364 (by decide +kernel)
private theorem contact27ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact27) 12 4 = 6353169426498 :=
  contactColumnsWindow_fast contact27 12 4 6353169426498 (by decide +kernel)
private theorem contact27ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact27) 16 4 = 6013492455256 :=
  contactColumnsWindow_fast contact27 16 4 6013492455256 (by decide +kernel)
private theorem contact27ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact27) 20 4 = 5683201477722 :=
  contactColumnsWindow_fast contact27 20 4 5683201477722 (by decide +kernel)
private theorem contact27ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact27) 24 4 = 5362313497543 :=
  contactColumnsWindow_fast contact27 24 4 5362313497543 (by decide +kernel)
private theorem contact27ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact27) 28 4 = 5050848521040 :=
  contactColumnsWindow_fast contact27 28 4 5050848521040 (by decide +kernel)
private theorem contact27ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact27) 32 4 = 4748772856750 :=
  contactColumnsWindow_fast contact27 32 4 4748772856750 (by decide +kernel)
private theorem contact27ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact27) 36 4 = 4456084399671 :=
  contactColumnsWindow_fast contact27 36 4 4456084399671 (by decide +kernel)
private theorem contact27ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact27) 40 4 = 4172785154118 :=
  contactColumnsWindow_fast contact27 40 4 4172785154118 (by decide +kernel)
private theorem contact27ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact27) 44 4 = 3898896330364 :=
  contactColumnsWindow_fast contact27 44 4 3898896330364 (by decide +kernel)
private theorem contact27ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact27) 48 4 = 3634430773629 :=
  contactColumnsWindow_fast contact27 48 4 3634430773629 (by decide +kernel)
private theorem contact27ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact27) 52 4 = 3379356240691 :=
  contactColumnsWindow_fast contact27 52 4 3379356240691 (by decide +kernel)
private theorem contact27ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact27) 56 4 = 3133673393156 :=
  contactColumnsWindow_fast contact27 56 4 3133673393156 (by decide +kernel)
private theorem contact27ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact27) 60 4 = 2897381930690 :=
  contactColumnsWindow_fast contact27 60 4 2897381930690 (by decide +kernel)
private theorem contact27ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact27) 64 4 = 2670511113349 :=
  contactColumnsWindow_fast contact27 64 4 2670511113349 (by decide +kernel)
private theorem contact27ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact27) 68 4 = 2453060564346 :=
  contactColumnsWindow_fast contact27 68 4 2453060564346 (by decide +kernel)
private theorem contact27ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact27) 72 4 = 2245006163718 :=
  contactColumnsWindow_fast contact27 72 4 2245006163718 (by decide +kernel)
private theorem contact27ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact27) 76 4 = 2046343952123 :=
  contactColumnsWindow_fast contact27 76 4 2046343952123 (by decide +kernel)
private theorem contact27ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact27) 80 4 = 1857072887480 :=
  contactColumnsWindow_fast contact27 80 4 1857072887480 (by decide +kernel)
private theorem contact27ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact27) 84 4 = 1677228027154 :=
  contactColumnsWindow_fast contact27 84 4 1677228027154 (by decide +kernel)
private theorem contact27ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact27) 88 4 = 1506798566083 :=
  contactColumnsWindow_fast contact27 88 4 1506798566083 (by decide +kernel)
private theorem contact27ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact27) 92 4 = 1345764745224 :=
  contactColumnsWindow_fast contact27 92 4 1345764745224 (by decide +kernel)
private theorem contact27ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact27) 96 4 = 1194123138830 :=
  contactColumnsWindow_fast contact27 96 4 1194123138830 (by decide +kernel)
private theorem contact27ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact27) 100 4 = 1051873730823 :=
  contactColumnsWindow_fast contact27 100 4 1051873730823 (by decide +kernel)
private theorem contact27ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact27) 104 4 = 919053656764 :=
  contactColumnsWindow_fast contact27 104 4 919053656764 (by decide +kernel)
private theorem contact27ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact27) 108 4 = 795645243469 :=
  contactColumnsWindow_fast contact27 108 4 795645243469 (by decide +kernel)
private theorem contact27ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact27) 112 4 = 681632028155 :=
  contactColumnsWindow_fast contact27 112 4 681632028155 (by decide +kernel)
private theorem contact27ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact27) 116 4 = 577011090172 :=
  contactColumnsWindow_fast contact27 116 4 577011090172 (by decide +kernel)
private theorem contact27ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact27) 120 4 = 481783541421 :=
  contactColumnsWindow_fast contact27 120 4 481783541421 (by decide +kernel)
private theorem contact27ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact27) 124 4 = 395987914855 :=
  contactColumnsWindow_fast contact27 124 4 395987914855 (by decide +kernel)
private theorem contact27ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact27) 128 4 = 319600677396 :=
  contactColumnsWindow_fast contact27 128 4 319600677396 (by decide +kernel)
private theorem contact27ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact27) 132 4 = 252606271285 :=
  contactColumnsWindow_fast contact27 132 4 252606271285 (by decide +kernel)
private theorem contact27ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact27) 136 4 = 194942248051 :=
  contactColumnsWindow_fast contact27 136 4 194942248051 (by decide +kernel)
private theorem contact27ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact27) 140 4 = 146364652958 :=
  contactColumnsWindow_fast contact27 140 4 146364652958 (by decide +kernel)
private theorem contact27ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact27) 144 4 = 106485410085 :=
  contactColumnsWindow_fast contact27 144 4 106485410085 (by decide +kernel)
private theorem contact27ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact27) 148 4 = 74686592182 :=
  contactColumnsWindow_fast contact27 148 4 74686592182 (by decide +kernel)
private theorem contact27ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact27) 152 4 = 50207789197 :=
  contactColumnsWindow_fast contact27 152 4 50207789197 (by decide +kernel)
private theorem contact27ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact27) 156 3 = 25485013453 :=
  contactColumnsWindow_fast contact27 156 3 25485013453 (by decide +kernel)
private theorem contact27ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact27) 0 8 = 14489184538700 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 4 4 7428507243190 7060677295510 contact27ColumnsSlice0 contact27ColumnsSlice4
private theorem contact27ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact27) 8 8 = 13055399784862 :=
  combineSlices (auxiliaryColumnSlice contact27) 8 4 4 6702230358364 6353169426498 contact27ColumnsSlice8 contact27ColumnsSlice12
private theorem contact27ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact27) 16 8 = 11696693932978 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 4 4 6013492455256 5683201477722 contact27ColumnsSlice16 contact27ColumnsSlice20
private theorem contact27ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact27) 24 8 = 10413162018583 :=
  combineSlices (auxiliaryColumnSlice contact27) 24 4 4 5362313497543 5050848521040 contact27ColumnsSlice24 contact27ColumnsSlice28
private theorem contact27ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact27) 32 8 = 9204857256421 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 4 4 4748772856750 4456084399671 contact27ColumnsSlice32 contact27ColumnsSlice36
private theorem contact27ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact27) 40 8 = 8071681484482 :=
  combineSlices (auxiliaryColumnSlice contact27) 40 4 4 4172785154118 3898896330364 contact27ColumnsSlice40 contact27ColumnsSlice44
private theorem contact27ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact27) 48 8 = 7013787014320 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 4 4 3634430773629 3379356240691 contact27ColumnsSlice48 contact27ColumnsSlice52
private theorem contact27ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact27) 56 8 = 6031055323846 :=
  combineSlices (auxiliaryColumnSlice contact27) 56 4 4 3133673393156 2897381930690 contact27ColumnsSlice56 contact27ColumnsSlice60
private theorem contact27ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact27) 64 8 = 5123571677695 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 4 4 2670511113349 2453060564346 contact27ColumnsSlice64 contact27ColumnsSlice68
private theorem contact27ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact27) 72 8 = 4291350115841 :=
  combineSlices (auxiliaryColumnSlice contact27) 72 4 4 2245006163718 2046343952123 contact27ColumnsSlice72 contact27ColumnsSlice76
private theorem contact27ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact27) 80 8 = 3534300914634 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 4 4 1857072887480 1677228027154 contact27ColumnsSlice80 contact27ColumnsSlice84
private theorem contact27ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact27) 88 8 = 2852563311307 :=
  combineSlices (auxiliaryColumnSlice contact27) 88 4 4 1506798566083 1345764745224 contact27ColumnsSlice88 contact27ColumnsSlice92
private theorem contact27ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact27) 96 8 = 2245996869653 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 4 4 1194123138830 1051873730823 contact27ColumnsSlice96 contact27ColumnsSlice100
private theorem contact27ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact27) 104 8 = 1714698900233 :=
  combineSlices (auxiliaryColumnSlice contact27) 104 4 4 919053656764 795645243469 contact27ColumnsSlice104 contact27ColumnsSlice108
private theorem contact27ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact27) 112 8 = 1258643118327 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 4 4 681632028155 577011090172 contact27ColumnsSlice112 contact27ColumnsSlice116
private theorem contact27ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact27) 120 8 = 877771456276 :=
  combineSlices (auxiliaryColumnSlice contact27) 120 4 4 481783541421 395987914855 contact27ColumnsSlice120 contact27ColumnsSlice124
private theorem contact27ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact27) 128 8 = 572206948681 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 4 4 319600677396 252606271285 contact27ColumnsSlice128 contact27ColumnsSlice132
private theorem contact27ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact27) 136 8 = 341306901009 :=
  combineSlices (auxiliaryColumnSlice contact27) 136 4 4 194942248051 146364652958 contact27ColumnsSlice136 contact27ColumnsSlice140
private theorem contact27ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact27) 144 8 = 181172002267 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 4 4 106485410085 74686592182 contact27ColumnsSlice144 contact27ColumnsSlice148
private theorem contact27ColumnsJoin152_7 : sliceWindow (auxiliaryColumnSlice contact27) 152 7 = 75692802650 :=
  combineSlices (auxiliaryColumnSlice contact27) 152 4 3 50207789197 25485013453 contact27ColumnsSlice152 contact27ColumnsSlice156
private theorem contact27ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact27) 0 16 = 27544584323562 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 8 8 14489184538700 13055399784862 contact27ColumnsJoin0_8 contact27ColumnsJoin8_8
private theorem contact27ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact27) 16 16 = 22109855951561 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 8 8 11696693932978 10413162018583 contact27ColumnsJoin16_8 contact27ColumnsJoin24_8
private theorem contact27ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact27) 32 16 = 17276538740903 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 8 8 9204857256421 8071681484482 contact27ColumnsJoin32_8 contact27ColumnsJoin40_8
private theorem contact27ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact27) 48 16 = 13044842338166 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 8 8 7013787014320 6031055323846 contact27ColumnsJoin48_8 contact27ColumnsJoin56_8
private theorem contact27ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact27) 64 16 = 9414921793536 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 8 8 5123571677695 4291350115841 contact27ColumnsJoin64_8 contact27ColumnsJoin72_8
private theorem contact27ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact27) 80 16 = 6386864225941 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 8 8 3534300914634 2852563311307 contact27ColumnsJoin80_8 contact27ColumnsJoin88_8
private theorem contact27ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact27) 96 16 = 3960695769886 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 8 8 2245996869653 1714698900233 contact27ColumnsJoin96_8 contact27ColumnsJoin104_8
private theorem contact27ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact27) 112 16 = 2136414574603 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 8 8 1258643118327 877771456276 contact27ColumnsJoin112_8 contact27ColumnsJoin120_8
private theorem contact27ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact27) 128 16 = 913513849690 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 8 8 572206948681 341306901009 contact27ColumnsJoin128_8 contact27ColumnsJoin136_8
private theorem contact27ColumnsJoin144_15 : sliceWindow (auxiliaryColumnSlice contact27) 144 15 = 256864804917 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 8 7 181172002267 75692802650 contact27ColumnsJoin144_8 contact27ColumnsJoin152_7
private theorem contact27ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact27) 0 32 = 49654440275123 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 16 16 27544584323562 22109855951561 contact27ColumnsJoin0_16 contact27ColumnsJoin16_16
private theorem contact27ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact27) 32 32 = 30321381079069 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 16 16 17276538740903 13044842338166 contact27ColumnsJoin32_16 contact27ColumnsJoin48_16
private theorem contact27ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact27) 64 32 = 15801786019477 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 16 16 9414921793536 6386864225941 contact27ColumnsJoin64_16 contact27ColumnsJoin80_16
private theorem contact27ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact27) 96 32 = 6097110344489 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 16 16 3960695769886 2136414574603 contact27ColumnsJoin96_16 contact27ColumnsJoin112_16
private theorem contact27ColumnsJoin128_31 : sliceWindow (auxiliaryColumnSlice contact27) 128 31 = 1170378654607 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 16 15 913513849690 256864804917 contact27ColumnsJoin128_16 contact27ColumnsJoin144_15
private theorem contact27ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact27) 0 64 = 79975821354192 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 32 32 49654440275123 30321381079069 contact27ColumnsJoin0_32 contact27ColumnsJoin32_32
private theorem contact27ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact27) 64 64 = 21898896363966 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 32 32 15801786019477 6097110344489 contact27ColumnsJoin64_32 contact27ColumnsJoin96_32
private theorem contact27ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact27) 0 128 = 101874717718158 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 64 64 79975821354192 21898896363966 contact27ColumnsJoin0_64 contact27ColumnsJoin64_64
private theorem contact27ColumnsJoin0_159 : sliceWindow (auxiliaryColumnSlice contact27) 0 159 = 103045096372765 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 128 31 101874717718158 1170378654607 contact27ColumnsJoin0_128 contact27ColumnsJoin128_31
private theorem contact27OrdinaryRanks : ordinaryRankBound contact27 = 8800472855 := by decide +kernel
private theorem contact27RanksSlice0 : sliceWindow (auxiliaryRankSlice contact27) 0 4 = 28000896 :=
  contactRankWindow_of_rec contact27 0 4 28000896 (by decide +kernel)
private theorem contact27RanksSlice4 : sliceWindow (auxiliaryRankSlice contact27) 4 4 = 26198256 :=
  contactRankWindow_of_rec contact27 4 4 26198256 (by decide +kernel)
private theorem contact27RanksSlice8 : sliceWindow (auxiliaryRankSlice contact27) 8 4 = 24460576 :=
  contactRankWindow_of_rec contact27 8 4 24460576 (by decide +kernel)
private theorem contact27RanksSlice12 : sliceWindow (auxiliaryRankSlice contact27) 12 4 = 22787856 :=
  contactRankWindow_of_rec contact27 12 4 22787856 (by decide +kernel)
private theorem contact27RanksSlice16 : sliceWindow (auxiliaryRankSlice contact27) 16 4 = 21180096 :=
  contactRankWindow_of_rec contact27 16 4 21180096 (by decide +kernel)
private theorem contact27RanksSlice20 : sliceWindow (auxiliaryRankSlice contact27) 20 4 = 19637296 :=
  contactRankWindow_of_rec contact27 20 4 19637296 (by decide +kernel)
private theorem contact27RanksSlice24 : sliceWindow (auxiliaryRankSlice contact27) 24 4 = 18159456 :=
  contactRankWindow_of_rec contact27 24 4 18159456 (by decide +kernel)
private theorem contact27RanksSlice28 : sliceWindow (auxiliaryRankSlice contact27) 28 4 = 16746576 :=
  contactRankWindow_of_rec contact27 28 4 16746576 (by decide +kernel)
private theorem contact27RanksSlice32 : sliceWindow (auxiliaryRankSlice contact27) 32 4 = 15398656 :=
  contactRankWindow_of_rec contact27 32 4 15398656 (by decide +kernel)
private theorem contact27RanksSlice36 : sliceWindow (auxiliaryRankSlice contact27) 36 4 = 14115696 :=
  contactRankWindow_of_rec contact27 36 4 14115696 (by decide +kernel)
private theorem contact27RanksSlice40 : sliceWindow (auxiliaryRankSlice contact27) 40 4 = 12897696 :=
  contactRankWindow_of_rec contact27 40 4 12897696 (by decide +kernel)
private theorem contact27RanksSlice44 : sliceWindow (auxiliaryRankSlice contact27) 44 4 = 11744656 :=
  contactRankWindow_of_rec contact27 44 4 11744656 (by decide +kernel)
private theorem contact27RanksSlice48 : sliceWindow (auxiliaryRankSlice contact27) 48 4 = 10656547 :=
  contactRankWindow_of_rec contact27 48 4 10656547 (by decide +kernel)
private theorem contact27RanksSlice52 : sliceWindow (auxiliaryRankSlice contact27) 52 4 = 9632755 :=
  contactRankWindow_of_rec contact27 52 4 9632755 (by decide +kernel)
private theorem contact27RanksSlice56 : sliceWindow (auxiliaryRankSlice contact27) 56 4 = 8672033 :=
  contactRankWindow_of_rec contact27 56 4 8672033 (by decide +kernel)
private theorem contact27RanksSlice60 : sliceWindow (auxiliaryRankSlice contact27) 60 4 = 7773079 :=
  contactRankWindow_of_rec contact27 60 4 7773079 (by decide +kernel)
private theorem contact27RanksSlice64 : sliceWindow (auxiliaryRankSlice contact27) 64 4 = 6934312 :=
  contactRankWindow_of_rec contact27 64 4 6934312 (by decide +kernel)
private theorem contact27RanksSlice68 : sliceWindow (auxiliaryRankSlice contact27) 68 4 = 6153981 :=
  contactRankWindow_of_rec contact27 68 4 6153981 (by decide +kernel)
private theorem contact27RanksSlice72 : sliceWindow (auxiliaryRankSlice contact27) 72 4 = 5430195 :=
  contactRankWindow_of_rec contact27 72 4 5430195 (by decide +kernel)
private theorem contact27RanksSlice76 : sliceWindow (auxiliaryRankSlice contact27) 76 4 = 4761088 :=
  contactRankWindow_of_rec contact27 76 4 4761088 (by decide +kernel)
private theorem contact27RanksSlice80 : sliceWindow (auxiliaryRankSlice contact27) 80 4 = 4145049 :=
  contactRankWindow_of_rec contact27 80 4 4145049 (by decide +kernel)
private theorem contact27RanksSlice84 : sliceWindow (auxiliaryRankSlice contact27) 84 4 = 3580047 :=
  contactRankWindow_of_rec contact27 84 4 3580047 (by decide +kernel)
private theorem contact27RanksSlice88 : sliceWindow (auxiliaryRankSlice contact27) 88 4 = 3064216 :=
  contactRankWindow_of_rec contact27 88 4 3064216 (by decide +kernel)
private theorem contact27RanksSlice92 : sliceWindow (auxiliaryRankSlice contact27) 92 4 = 2596085 :=
  contactRankWindow_of_rec contact27 92 4 2596085 (by decide +kernel)
private theorem contact27RanksSlice96 : sliceWindow (auxiliaryRankSlice contact27) 96 4 = 2173483 :=
  contactRankWindow_of_rec contact27 96 4 2173483 (by decide +kernel)
private theorem contact27RanksSlice100 : sliceWindow (auxiliaryRankSlice contact27) 100 4 = 1794544 :=
  contactRankWindow_of_rec contact27 100 4 1794544 (by decide +kernel)
private theorem contact27RanksSlice104 : sliceWindow (auxiliaryRankSlice contact27) 104 4 = 1457937 :=
  contactRankWindow_of_rec contact27 104 4 1457937 (by decide +kernel)
private theorem contact27RanksSlice108 : sliceWindow (auxiliaryRankSlice contact27) 108 4 = 1161351 :=
  contactRankWindow_of_rec contact27 108 4 1161351 (by decide +kernel)
private theorem contact27RanksSlice112 : sliceWindow (auxiliaryRankSlice contact27) 112 4 = 902920 :=
  contactRankWindow_of_rec contact27 112 4 902920 (by decide +kernel)
private theorem contact27RanksSlice116 : sliceWindow (auxiliaryRankSlice contact27) 116 4 = 681453 :=
  contactRankWindow_of_rec contact27 116 4 681453 (by decide +kernel)
private theorem contact27RanksSlice120 : sliceWindow (auxiliaryRankSlice contact27) 120 4 = 494499 :=
  contactRankWindow_of_rec contact27 120 4 494499 (by decide +kernel)
private theorem contact27RanksSlice124 : sliceWindow (auxiliaryRankSlice contact27) 124 4 = 340192 :=
  contactRankWindow_of_rec contact27 124 4 340192 (by decide +kernel)
private theorem contact27RanksSlice128 : sliceWindow (auxiliaryRankSlice contact27) 128 4 = 217481 :=
  contactRankWindow_of_rec contact27 128 4 217481 (by decide +kernel)
private theorem contact27RanksSlice132 : sliceWindow (auxiliaryRankSlice contact27) 132 4 = 123775 :=
  contactRankWindow_of_rec contact27 132 4 123775 (by decide +kernel)
private theorem contact27RanksSlice136 : sliceWindow (auxiliaryRankSlice contact27) 136 4 = 57253 :=
  contactRankWindow_of_rec contact27 136 4 57253 (by decide +kernel)
private theorem contact27RanksSlice140 : sliceWindow (auxiliaryRankSlice contact27) 140 4 = 17281 :=
  contactRankWindow_of_rec contact27 140 4 17281 (by decide +kernel)
private theorem contact27RanksSlice144 : sliceWindow (auxiliaryRankSlice contact27) 144 4 = 970 :=
  contactRankWindow_of_rec contact27 144 4 970 (by decide +kernel)
private theorem contact27RanksSlice148 : sliceWindow (auxiliaryRankSlice contact27) 148 11 = 0 :=
  contactRankWindow_of_rec contact27 148 11 0 (by decide +kernel)
private theorem contact27RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact27) 0 8 = 54199152 :=
  combineSlices (auxiliaryRankSlice contact27) 0 4 4 28000896 26198256 contact27RanksSlice0 contact27RanksSlice4
private theorem contact27RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact27) 8 8 = 47248432 :=
  combineSlices (auxiliaryRankSlice contact27) 8 4 4 24460576 22787856 contact27RanksSlice8 contact27RanksSlice12
private theorem contact27RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact27) 16 8 = 40817392 :=
  combineSlices (auxiliaryRankSlice contact27) 16 4 4 21180096 19637296 contact27RanksSlice16 contact27RanksSlice20
private theorem contact27RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact27) 24 8 = 34906032 :=
  combineSlices (auxiliaryRankSlice contact27) 24 4 4 18159456 16746576 contact27RanksSlice24 contact27RanksSlice28
private theorem contact27RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact27) 32 8 = 29514352 :=
  combineSlices (auxiliaryRankSlice contact27) 32 4 4 15398656 14115696 contact27RanksSlice32 contact27RanksSlice36
private theorem contact27RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact27) 40 8 = 24642352 :=
  combineSlices (auxiliaryRankSlice contact27) 40 4 4 12897696 11744656 contact27RanksSlice40 contact27RanksSlice44
private theorem contact27RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact27) 48 8 = 20289302 :=
  combineSlices (auxiliaryRankSlice contact27) 48 4 4 10656547 9632755 contact27RanksSlice48 contact27RanksSlice52
private theorem contact27RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact27) 56 8 = 16445112 :=
  combineSlices (auxiliaryRankSlice contact27) 56 4 4 8672033 7773079 contact27RanksSlice56 contact27RanksSlice60
private theorem contact27RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact27) 64 8 = 13088293 :=
  combineSlices (auxiliaryRankSlice contact27) 64 4 4 6934312 6153981 contact27RanksSlice64 contact27RanksSlice68
private theorem contact27RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact27) 72 8 = 10191283 :=
  combineSlices (auxiliaryRankSlice contact27) 72 4 4 5430195 4761088 contact27RanksSlice72 contact27RanksSlice76
private theorem contact27RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact27) 80 8 = 7725096 :=
  combineSlices (auxiliaryRankSlice contact27) 80 4 4 4145049 3580047 contact27RanksSlice80 contact27RanksSlice84
private theorem contact27RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact27) 88 8 = 5660301 :=
  combineSlices (auxiliaryRankSlice contact27) 88 4 4 3064216 2596085 contact27RanksSlice88 contact27RanksSlice92
private theorem contact27RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact27) 96 8 = 3968027 :=
  combineSlices (auxiliaryRankSlice contact27) 96 4 4 2173483 1794544 contact27RanksSlice96 contact27RanksSlice100
private theorem contact27RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact27) 104 8 = 2619288 :=
  combineSlices (auxiliaryRankSlice contact27) 104 4 4 1457937 1161351 contact27RanksSlice104 contact27RanksSlice108
private theorem contact27RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact27) 112 8 = 1584373 :=
  combineSlices (auxiliaryRankSlice contact27) 112 4 4 902920 681453 contact27RanksSlice112 contact27RanksSlice116
private theorem contact27RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact27) 120 8 = 834691 :=
  combineSlices (auxiliaryRankSlice contact27) 120 4 4 494499 340192 contact27RanksSlice120 contact27RanksSlice124
private theorem contact27RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact27) 128 8 = 341256 :=
  combineSlices (auxiliaryRankSlice contact27) 128 4 4 217481 123775 contact27RanksSlice128 contact27RanksSlice132
private theorem contact27RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact27) 136 8 = 74534 :=
  combineSlices (auxiliaryRankSlice contact27) 136 4 4 57253 17281 contact27RanksSlice136 contact27RanksSlice140
private theorem contact27RanksJoin144_15 : sliceWindow (auxiliaryRankSlice contact27) 144 15 = 970 :=
  combineSlices (auxiliaryRankSlice contact27) 144 4 11 970 0 contact27RanksSlice144 contact27RanksSlice148
private theorem contact27RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact27) 0 16 = 101447584 :=
  combineSlices (auxiliaryRankSlice contact27) 0 8 8 54199152 47248432 contact27RanksJoin0_8 contact27RanksJoin8_8
private theorem contact27RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact27) 16 16 = 75723424 :=
  combineSlices (auxiliaryRankSlice contact27) 16 8 8 40817392 34906032 contact27RanksJoin16_8 contact27RanksJoin24_8
private theorem contact27RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact27) 32 16 = 54156704 :=
  combineSlices (auxiliaryRankSlice contact27) 32 8 8 29514352 24642352 contact27RanksJoin32_8 contact27RanksJoin40_8
private theorem contact27RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact27) 48 16 = 36734414 :=
  combineSlices (auxiliaryRankSlice contact27) 48 8 8 20289302 16445112 contact27RanksJoin48_8 contact27RanksJoin56_8
private theorem contact27RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact27) 64 16 = 23279576 :=
  combineSlices (auxiliaryRankSlice contact27) 64 8 8 13088293 10191283 contact27RanksJoin64_8 contact27RanksJoin72_8
private theorem contact27RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact27) 80 16 = 13385397 :=
  combineSlices (auxiliaryRankSlice contact27) 80 8 8 7725096 5660301 contact27RanksJoin80_8 contact27RanksJoin88_8
private theorem contact27RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact27) 96 16 = 6587315 :=
  combineSlices (auxiliaryRankSlice contact27) 96 8 8 3968027 2619288 contact27RanksJoin96_8 contact27RanksJoin104_8
private theorem contact27RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact27) 112 16 = 2419064 :=
  combineSlices (auxiliaryRankSlice contact27) 112 8 8 1584373 834691 contact27RanksJoin112_8 contact27RanksJoin120_8
private theorem contact27RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact27) 128 16 = 415790 :=
  combineSlices (auxiliaryRankSlice contact27) 128 8 8 341256 74534 contact27RanksJoin128_8 contact27RanksJoin136_8
private theorem contact27RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact27) 0 32 = 177171008 :=
  combineSlices (auxiliaryRankSlice contact27) 0 16 16 101447584 75723424 contact27RanksJoin0_16 contact27RanksJoin16_16
private theorem contact27RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact27) 32 32 = 90891118 :=
  combineSlices (auxiliaryRankSlice contact27) 32 16 16 54156704 36734414 contact27RanksJoin32_16 contact27RanksJoin48_16
private theorem contact27RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact27) 64 32 = 36664973 :=
  combineSlices (auxiliaryRankSlice contact27) 64 16 16 23279576 13385397 contact27RanksJoin64_16 contact27RanksJoin80_16
private theorem contact27RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact27) 96 32 = 9006379 :=
  combineSlices (auxiliaryRankSlice contact27) 96 16 16 6587315 2419064 contact27RanksJoin96_16 contact27RanksJoin112_16
private theorem contact27RanksJoin128_31 : sliceWindow (auxiliaryRankSlice contact27) 128 31 = 416760 :=
  combineSlices (auxiliaryRankSlice contact27) 128 16 15 415790 970 contact27RanksJoin128_16 contact27RanksJoin144_15
private theorem contact27RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact27) 0 64 = 268062126 :=
  combineSlices (auxiliaryRankSlice contact27) 0 32 32 177171008 90891118 contact27RanksJoin0_32 contact27RanksJoin32_32
private theorem contact27RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact27) 64 64 = 45671352 :=
  combineSlices (auxiliaryRankSlice contact27) 64 32 32 36664973 9006379 contact27RanksJoin64_32 contact27RanksJoin96_32
private theorem contact27RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact27) 0 128 = 313733478 :=
  combineSlices (auxiliaryRankSlice contact27) 0 64 64 268062126 45671352 contact27RanksJoin0_64 contact27RanksJoin64_64
private theorem contact27RanksJoin0_159 : sliceWindow (auxiliaryRankSlice contact27) 0 159 = 314150238 :=
  combineSlices (auxiliaryRankSlice contact27) 0 128 31 313733478 416760 contact27RanksJoin0_128 contact27RanksJoin128_31
theorem contact27_margin : sourceMargin contact27 :=
  margin_of_checked_counts contact27 159 2286299000566185 103045096372765 8800472855 314150238 rfl contact27OrdinaryColumns contact27ColumnsJoin0_159 contact27OrdinaryRanks contact27RanksJoin0_159 (by decide +kernel)

private theorem contact29OrdinaryColumns : ordinaryColumnCount contact29 = 194382442013409 := by decide +kernel
private theorem contact29ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact29) 0 4 = 1033628095226 :=
  contactColumnsWindow_fast contact29 0 4 1033628095226 (by decide +kernel)
private theorem contact29ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact29) 4 4 = 948666821408 :=
  contactColumnsWindow_fast contact29 4 4 948666821408 (by decide +kernel)
private theorem contact29ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact29) 8 4 = 867388852454 :=
  contactColumnsWindow_fast contact29 8 4 867388852454 (by decide +kernel)
private theorem contact29ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact29) 12 4 = 789777186544 :=
  contactColumnsWindow_fast contact29 12 4 789777186544 (by decide +kernel)
private theorem contact29ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact29) 16 4 = 715828785498 :=
  contactColumnsWindow_fast contact29 16 4 715828785498 (by decide +kernel)
private theorem contact29ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact29) 20 4 = 645542114118 :=
  contactColumnsWindow_fast contact29 20 4 645542114118 (by decide +kernel)
private theorem contact29ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact29) 24 4 = 578922529034 :=
  contactColumnsWindow_fast contact29 24 4 578922529034 (by decide +kernel)
private theorem contact29ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact29) 28 4 = 515987783795 :=
  contactColumnsWindow_fast contact29 28 4 515987783795 (by decide +kernel)
private theorem contact29ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact29) 32 4 = 456720841690 :=
  contactColumnsWindow_fast contact29 32 4 456720841690 (by decide +kernel)
private theorem contact29ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact29) 36 4 = 401117234694 :=
  contactColumnsWindow_fast contact29 36 4 401117234694 (by decide +kernel)
private theorem contact29ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact29) 40 4 = 349175464833 :=
  contactColumnsWindow_fast contact29 40 4 349175464833 (by decide +kernel)
private theorem contact29ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact29) 44 4 = 300902035652 :=
  contactColumnsWindow_fast contact29 44 4 300902035652 (by decide +kernel)
private theorem contact29ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact29) 48 4 = 256313669462 :=
  contactColumnsWindow_fast contact29 48 4 256313669462 (by decide +kernel)
private theorem contact29ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact29) 52 4 = 215391691507 :=
  contactColumnsWindow_fast contact29 52 4 215391691507 (by decide +kernel)
private theorem contact29ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact29) 56 4 = 178132793826 :=
  contactColumnsWindow_fast contact29 56 4 178132793826 (by decide +kernel)
private theorem contact29ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact29) 60 4 = 144535925484 :=
  contactColumnsWindow_fast contact29 60 4 144535925484 (by decide +kernel)
private theorem contact29ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact29) 64 4 = 114609110476 :=
  contactColumnsWindow_fast contact29 64 4 114609110476 (by decide +kernel)
private theorem contact29ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact29) 68 4 = 88366742870 :=
  contactColumnsWindow_fast contact29 68 4 88366742870 (by decide +kernel)
private theorem contact29ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact29) 72 4 = 65789651260 :=
  contactColumnsWindow_fast contact29 72 4 65789651260 (by decide +kernel)
private theorem contact29ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact29) 76 4 = 46875462894 :=
  contactColumnsWindow_fast contact29 76 4 46875462894 (by decide +kernel)
private theorem contact29ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact29) 80 4 = 31615258627 :=
  contactColumnsWindow_fast contact29 80 4 31615258627 (by decide +kernel)
private theorem contact29ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact29) 84 4 = 19919044881 :=
  contactColumnsWindow_fast contact29 84 4 19919044881 (by decide +kernel)
private theorem contact29ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact29) 88 4 = 11527217116 :=
  contactColumnsWindow_fast contact29 88 4 11527217116 (by decide +kernel)
private theorem contact29ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact29) 92 4 = 5986398690 :=
  contactColumnsWindow_fast contact29 92 4 5986398690 (by decide +kernel)
private theorem contact29ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact29) 96 1 = 910474364 :=
  contactColumnsWindow_fast contact29 96 1 910474364 (by decide +kernel)
private theorem contact29ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact29) 0 8 = 1982294916634 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 4 4 1033628095226 948666821408 contact29ColumnsSlice0 contact29ColumnsSlice4
private theorem contact29ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact29) 8 8 = 1657166038998 :=
  combineSlices (auxiliaryColumnSlice contact29) 8 4 4 867388852454 789777186544 contact29ColumnsSlice8 contact29ColumnsSlice12
private theorem contact29ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact29) 16 8 = 1361370899616 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 4 4 715828785498 645542114118 contact29ColumnsSlice16 contact29ColumnsSlice20
private theorem contact29ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact29) 24 8 = 1094910312829 :=
  combineSlices (auxiliaryColumnSlice contact29) 24 4 4 578922529034 515987783795 contact29ColumnsSlice24 contact29ColumnsSlice28
private theorem contact29ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact29) 32 8 = 857838076384 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 4 4 456720841690 401117234694 contact29ColumnsSlice32 contact29ColumnsSlice36
private theorem contact29ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact29) 40 8 = 650077500485 :=
  combineSlices (auxiliaryColumnSlice contact29) 40 4 4 349175464833 300902035652 contact29ColumnsSlice40 contact29ColumnsSlice44
private theorem contact29ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact29) 48 8 = 471705360969 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 4 4 256313669462 215391691507 contact29ColumnsSlice48 contact29ColumnsSlice52
private theorem contact29ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact29) 56 8 = 322668719310 :=
  combineSlices (auxiliaryColumnSlice contact29) 56 4 4 178132793826 144535925484 contact29ColumnsSlice56 contact29ColumnsSlice60
private theorem contact29ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact29) 64 8 = 202975853346 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 4 4 114609110476 88366742870 contact29ColumnsSlice64 contact29ColumnsSlice68
private theorem contact29ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact29) 72 8 = 112665114154 :=
  combineSlices (auxiliaryColumnSlice contact29) 72 4 4 65789651260 46875462894 contact29ColumnsSlice72 contact29ColumnsSlice76
private theorem contact29ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact29) 80 8 = 51534303508 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 4 4 31615258627 19919044881 contact29ColumnsSlice80 contact29ColumnsSlice84
private theorem contact29ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact29) 88 8 = 17513615806 :=
  combineSlices (auxiliaryColumnSlice contact29) 88 4 4 11527217116 5986398690 contact29ColumnsSlice88 contact29ColumnsSlice92
private theorem contact29ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact29) 0 16 = 3639460955632 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 8 8 1982294916634 1657166038998 contact29ColumnsJoin0_8 contact29ColumnsJoin8_8
private theorem contact29ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact29) 16 16 = 2456281212445 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 8 8 1361370899616 1094910312829 contact29ColumnsJoin16_8 contact29ColumnsJoin24_8
private theorem contact29ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact29) 32 16 = 1507915576869 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 8 8 857838076384 650077500485 contact29ColumnsJoin32_8 contact29ColumnsJoin40_8
private theorem contact29ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact29) 48 16 = 794374080279 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 8 8 471705360969 322668719310 contact29ColumnsJoin48_8 contact29ColumnsJoin56_8
private theorem contact29ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact29) 64 16 = 315640967500 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 8 8 202975853346 112665114154 contact29ColumnsJoin64_8 contact29ColumnsJoin72_8
private theorem contact29ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact29) 80 16 = 69047919314 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 8 8 51534303508 17513615806 contact29ColumnsJoin80_8 contact29ColumnsJoin88_8
private theorem contact29ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact29) 0 32 = 6095742168077 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 16 16 3639460955632 2456281212445 contact29ColumnsJoin0_16 contact29ColumnsJoin16_16
private theorem contact29ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact29) 32 32 = 2302289657148 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 16 16 1507915576869 794374080279 contact29ColumnsJoin32_16 contact29ColumnsJoin48_16
private theorem contact29ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact29) 64 32 = 384688886814 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 16 16 315640967500 69047919314 contact29ColumnsJoin64_16 contact29ColumnsJoin80_16
private theorem contact29ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact29) 0 64 = 8398031825225 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 32 32 6095742168077 2302289657148 contact29ColumnsJoin0_32 contact29ColumnsJoin32_32
private theorem contact29ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact29) 64 33 = 385599361178 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 32 1 384688886814 910474364 contact29ColumnsJoin64_32 contact29ColumnsSlice96
private theorem contact29ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact29) 0 97 = 8783631186403 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 64 33 8398031825225 385599361178 contact29ColumnsJoin0_64 contact29ColumnsJoin64_33
private theorem contact29OrdinaryRanks : ordinaryRankBound contact29 = 748156758 := by decide +kernel
private theorem contact29RanksSlice0 : sliceWindow (auxiliaryRankSlice contact29) 0 4 = 3872292 :=
  contactRankWindow_of_rec contact29 0 4 3872292 (by decide +kernel)
private theorem contact29RanksSlice4 : sliceWindow (auxiliaryRankSlice contact29) 4 4 = 3460452 :=
  contactRankWindow_of_rec contact29 4 4 3460452 (by decide +kernel)
private theorem contact29RanksSlice8 : sliceWindow (auxiliaryRankSlice contact29) 8 4 = 3073956 :=
  contactRankWindow_of_rec contact29 8 4 3073956 (by decide +kernel)
private theorem contact29RanksSlice12 : sliceWindow (auxiliaryRankSlice contact29) 12 4 = 2712804 :=
  contactRankWindow_of_rec contact29 12 4 2712804 (by decide +kernel)
private theorem contact29RanksSlice16 : sliceWindow (auxiliaryRankSlice contact29) 16 4 = 2376996 :=
  contactRankWindow_of_rec contact29 16 4 2376996 (by decide +kernel)
private theorem contact29RanksSlice20 : sliceWindow (auxiliaryRankSlice contact29) 20 4 = 2066532 :=
  contactRankWindow_of_rec contact29 20 4 2066532 (by decide +kernel)
private theorem contact29RanksSlice24 : sliceWindow (auxiliaryRankSlice contact29) 24 4 = 1781412 :=
  contactRankWindow_of_rec contact29 24 4 1781412 (by decide +kernel)
private theorem contact29RanksSlice28 : sliceWindow (auxiliaryRankSlice contact29) 28 4 = 1521582 :=
  contactRankWindow_of_rec contact29 28 4 1521582 (by decide +kernel)
private theorem contact29RanksSlice32 : sliceWindow (auxiliaryRankSlice contact29) 32 4 = 1286510 :=
  contactRankWindow_of_rec contact29 32 4 1286510 (by decide +kernel)
private theorem contact29RanksSlice36 : sliceWindow (auxiliaryRankSlice contact29) 36 4 = 1075366 :=
  contactRankWindow_of_rec contact29 36 4 1075366 (by decide +kernel)
private theorem contact29RanksSlice40 : sliceWindow (auxiliaryRankSlice contact29) 40 4 = 887140 :=
  contactRankWindow_of_rec contact29 40 4 887140 (by decide +kernel)
private theorem contact29RanksSlice44 : sliceWindow (auxiliaryRankSlice contact29) 44 4 = 720670 :=
  contactRankWindow_of_rec contact29 44 4 720670 (by decide +kernel)
private theorem contact29RanksSlice48 : sliceWindow (auxiliaryRankSlice contact29) 48 4 = 574778 :=
  contactRankWindow_of_rec contact29 48 4 574778 (by decide +kernel)
private theorem contact29RanksSlice52 : sliceWindow (auxiliaryRankSlice contact29) 52 4 = 448448 :=
  contactRankWindow_of_rec contact29 52 4 448448 (by decide +kernel)
private theorem contact29RanksSlice56 : sliceWindow (auxiliaryRankSlice contact29) 56 4 = 340430 :=
  contactRankWindow_of_rec contact29 56 4 340430 (by decide +kernel)
private theorem contact29RanksSlice60 : sliceWindow (auxiliaryRankSlice contact29) 60 4 = 249550 :=
  contactRankWindow_of_rec contact29 60 4 249550 (by decide +kernel)
private theorem contact29RanksSlice64 : sliceWindow (auxiliaryRankSlice contact29) 64 4 = 174876 :=
  contactRankWindow_of_rec contact29 64 4 174876 (by decide +kernel)
private theorem contact29RanksSlice68 : sliceWindow (auxiliaryRankSlice contact29) 68 4 = 115070 :=
  contactRankWindow_of_rec contact29 68 4 115070 (by decide +kernel)
private theorem contact29RanksSlice72 : sliceWindow (auxiliaryRankSlice contact29) 72 4 = 68962 :=
  contactRankWindow_of_rec contact29 72 4 68962 (by decide +kernel)
private theorem contact29RanksSlice76 : sliceWindow (auxiliaryRankSlice contact29) 76 4 = 35704 :=
  contactRankWindow_of_rec contact29 76 4 35704 (by decide +kernel)
private theorem contact29RanksSlice80 : sliceWindow (auxiliaryRankSlice contact29) 80 4 = 13872 :=
  contactRankWindow_of_rec contact29 80 4 13872 (by decide +kernel)
private theorem contact29RanksSlice84 : sliceWindow (auxiliaryRankSlice contact29) 84 4 = 2381 :=
  contactRankWindow_of_rec contact29 84 4 2381 (by decide +kernel)
private theorem contact29RanksSlice88 : sliceWindow (auxiliaryRankSlice contact29) 88 9 = 0 :=
  contactRankWindow_of_rec contact29 88 9 0 (by decide +kernel)
private theorem contact29RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact29) 0 8 = 7332744 :=
  combineSlices (auxiliaryRankSlice contact29) 0 4 4 3872292 3460452 contact29RanksSlice0 contact29RanksSlice4
private theorem contact29RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact29) 8 8 = 5786760 :=
  combineSlices (auxiliaryRankSlice contact29) 8 4 4 3073956 2712804 contact29RanksSlice8 contact29RanksSlice12
private theorem contact29RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact29) 16 8 = 4443528 :=
  combineSlices (auxiliaryRankSlice contact29) 16 4 4 2376996 2066532 contact29RanksSlice16 contact29RanksSlice20
private theorem contact29RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact29) 24 8 = 3302994 :=
  combineSlices (auxiliaryRankSlice contact29) 24 4 4 1781412 1521582 contact29RanksSlice24 contact29RanksSlice28
private theorem contact29RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact29) 32 8 = 2361876 :=
  combineSlices (auxiliaryRankSlice contact29) 32 4 4 1286510 1075366 contact29RanksSlice32 contact29RanksSlice36
private theorem contact29RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact29) 40 8 = 1607810 :=
  combineSlices (auxiliaryRankSlice contact29) 40 4 4 887140 720670 contact29RanksSlice40 contact29RanksSlice44
private theorem contact29RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact29) 48 8 = 1023226 :=
  combineSlices (auxiliaryRankSlice contact29) 48 4 4 574778 448448 contact29RanksSlice48 contact29RanksSlice52
private theorem contact29RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact29) 56 8 = 589980 :=
  combineSlices (auxiliaryRankSlice contact29) 56 4 4 340430 249550 contact29RanksSlice56 contact29RanksSlice60
private theorem contact29RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact29) 64 8 = 289946 :=
  combineSlices (auxiliaryRankSlice contact29) 64 4 4 174876 115070 contact29RanksSlice64 contact29RanksSlice68
private theorem contact29RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact29) 72 8 = 104666 :=
  combineSlices (auxiliaryRankSlice contact29) 72 4 4 68962 35704 contact29RanksSlice72 contact29RanksSlice76
private theorem contact29RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact29) 80 8 = 16253 :=
  combineSlices (auxiliaryRankSlice contact29) 80 4 4 13872 2381 contact29RanksSlice80 contact29RanksSlice84
private theorem contact29RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact29) 0 16 = 13119504 :=
  combineSlices (auxiliaryRankSlice contact29) 0 8 8 7332744 5786760 contact29RanksJoin0_8 contact29RanksJoin8_8
private theorem contact29RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact29) 16 16 = 7746522 :=
  combineSlices (auxiliaryRankSlice contact29) 16 8 8 4443528 3302994 contact29RanksJoin16_8 contact29RanksJoin24_8
private theorem contact29RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact29) 32 16 = 3969686 :=
  combineSlices (auxiliaryRankSlice contact29) 32 8 8 2361876 1607810 contact29RanksJoin32_8 contact29RanksJoin40_8
private theorem contact29RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact29) 48 16 = 1613206 :=
  combineSlices (auxiliaryRankSlice contact29) 48 8 8 1023226 589980 contact29RanksJoin48_8 contact29RanksJoin56_8
private theorem contact29RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact29) 64 16 = 394612 :=
  combineSlices (auxiliaryRankSlice contact29) 64 8 8 289946 104666 contact29RanksJoin64_8 contact29RanksJoin72_8
private theorem contact29RanksJoin80_17 : sliceWindow (auxiliaryRankSlice contact29) 80 17 = 16253 :=
  combineSlices (auxiliaryRankSlice contact29) 80 8 9 16253 0 contact29RanksJoin80_8 contact29RanksSlice88
private theorem contact29RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact29) 0 32 = 20866026 :=
  combineSlices (auxiliaryRankSlice contact29) 0 16 16 13119504 7746522 contact29RanksJoin0_16 contact29RanksJoin16_16
private theorem contact29RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact29) 32 32 = 5582892 :=
  combineSlices (auxiliaryRankSlice contact29) 32 16 16 3969686 1613206 contact29RanksJoin32_16 contact29RanksJoin48_16
private theorem contact29RanksJoin64_33 : sliceWindow (auxiliaryRankSlice contact29) 64 33 = 410865 :=
  combineSlices (auxiliaryRankSlice contact29) 64 16 17 394612 16253 contact29RanksJoin64_16 contact29RanksJoin80_17
private theorem contact29RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact29) 0 64 = 26448918 :=
  combineSlices (auxiliaryRankSlice contact29) 0 32 32 20866026 5582892 contact29RanksJoin0_32 contact29RanksJoin32_32
private theorem contact29RanksJoin0_97 : sliceWindow (auxiliaryRankSlice contact29) 0 97 = 26859783 :=
  combineSlices (auxiliaryRankSlice contact29) 0 64 33 26448918 410865 contact29RanksJoin0_64 contact29RanksJoin64_33
theorem contact29_margin : sourceMargin contact29 :=
  margin_of_checked_counts contact29 97 194382442013409 8783631186403 748156758 26859783 rfl contact29OrdinaryColumns contact29ColumnsJoin0_97 contact29OrdinaryRanks contact29RanksJoin0_97 (by decide +kernel)

private theorem contact31OrdinaryColumns : ordinaryColumnCount contact31 = 55344872441854 := by decide +kernel
private theorem contact31ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact31) 0 4 = 469390848948 :=
  contactColumnsWindow_fast contact31 0 4 469390848948 (by decide +kernel)
private theorem contact31ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact31) 4 4 = 422353426036 :=
  contactColumnsWindow_fast contact31 4 4 422353426036 (by decide +kernel)
private theorem contact31ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact31) 8 4 = 377811770804 :=
  contactColumnsWindow_fast contact31 8 4 377811770804 (by decide +kernel)
private theorem contact31ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact31) 12 4 = 335776423236 :=
  contactColumnsWindow_fast contact31 12 4 335776423236 (by decide +kernel)
private theorem contact31ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact31) 16 4 = 296248534404 :=
  contactColumnsWindow_fast contact31 16 4 296248534404 (by decide +kernel)
private theorem contact31ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact31) 20 4 = 259218360312 :=
  contactColumnsWindow_fast contact31 20 4 259218360312 (by decide +kernel)
private theorem contact31ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact31) 24 4 = 224685311752 :=
  contactColumnsWindow_fast contact31 24 4 224685311752 (by decide +kernel)
private theorem contact31ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact31) 28 4 = 192650365496 :=
  contactColumnsWindow_fast contact31 28 4 192650365496 (by decide +kernel)
private theorem contact31ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact31) 32 4 = 163124818056 :=
  contactColumnsWindow_fast contact31 32 4 163124818056 (by decide +kernel)
private theorem contact31ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact31) 36 4 = 136104686859 :=
  contactColumnsWindow_fast contact31 36 4 136104686859 (by decide +kernel)
private theorem contact31ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact31) 40 4 = 111582450612 :=
  contactColumnsWindow_fast contact31 40 4 111582450612 (by decide +kernel)
private theorem contact31ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact31) 44 4 = 89557178980 :=
  contactColumnsWindow_fast contact31 44 4 89557178980 (by decide +kernel)
private theorem contact31ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact31) 48 4 = 70030384968 :=
  contactColumnsWindow_fast contact31 48 4 70030384968 (by decide +kernel)
private theorem contact31ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact31) 52 4 = 53014424196 :=
  contactColumnsWindow_fast contact31 52 4 53014424196 (by decide +kernel)
private theorem contact31ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact31) 56 4 = 38502064869 :=
  contactColumnsWindow_fast contact31 56 4 38502064869 (by decide +kernel)
private theorem contact31ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact31) 60 4 = 26487752232 :=
  contactColumnsWindow_fast contact31 60 4 26487752232 (by decide +kernel)
private theorem contact31ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact31) 64 4 = 16969131402 :=
  contactColumnsWindow_fast contact31 64 4 16969131402 (by decide +kernel)
private theorem contact31ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact31) 68 4 = 9904579884 :=
  contactColumnsWindow_fast contact31 68 4 9904579884 (by decide +kernel)
private theorem contact31ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact31) 72 4 = 5119041904 :=
  contactColumnsWindow_fast contact31 72 4 5119041904 (by decide +kernel)
private theorem contact31ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact31) 76 1 = 766844579 :=
  contactColumnsWindow_fast contact31 76 1 766844579 (by decide +kernel)
private theorem contact31ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact31) 0 8 = 891744274984 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 4 4 469390848948 422353426036 contact31ColumnsSlice0 contact31ColumnsSlice4
private theorem contact31ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact31) 8 8 = 713588194040 :=
  combineSlices (auxiliaryColumnSlice contact31) 8 4 4 377811770804 335776423236 contact31ColumnsSlice8 contact31ColumnsSlice12
private theorem contact31ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact31) 16 8 = 555466894716 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 4 4 296248534404 259218360312 contact31ColumnsSlice16 contact31ColumnsSlice20
private theorem contact31ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact31) 24 8 = 417335677248 :=
  combineSlices (auxiliaryColumnSlice contact31) 24 4 4 224685311752 192650365496 contact31ColumnsSlice24 contact31ColumnsSlice28
private theorem contact31ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact31) 32 8 = 299229504915 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 4 4 163124818056 136104686859 contact31ColumnsSlice32 contact31ColumnsSlice36
private theorem contact31ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact31) 40 8 = 201139629592 :=
  combineSlices (auxiliaryColumnSlice contact31) 40 4 4 111582450612 89557178980 contact31ColumnsSlice40 contact31ColumnsSlice44
private theorem contact31ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact31) 48 8 = 123044809164 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 4 4 70030384968 53014424196 contact31ColumnsSlice48 contact31ColumnsSlice52
private theorem contact31ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact31) 56 8 = 64989817101 :=
  combineSlices (auxiliaryColumnSlice contact31) 56 4 4 38502064869 26487752232 contact31ColumnsSlice56 contact31ColumnsSlice60
private theorem contact31ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact31) 64 8 = 26873711286 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 4 4 16969131402 9904579884 contact31ColumnsSlice64 contact31ColumnsSlice68
private theorem contact31ColumnsJoin72_5 : sliceWindow (auxiliaryColumnSlice contact31) 72 5 = 5885886483 :=
  combineSlices (auxiliaryColumnSlice contact31) 72 4 1 5119041904 766844579 contact31ColumnsSlice72 contact31ColumnsSlice76
private theorem contact31ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact31) 0 16 = 1605332469024 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 8 8 891744274984 713588194040 contact31ColumnsJoin0_8 contact31ColumnsJoin8_8
private theorem contact31ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact31) 16 16 = 972802571964 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 8 8 555466894716 417335677248 contact31ColumnsJoin16_8 contact31ColumnsJoin24_8
private theorem contact31ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact31) 32 16 = 500369134507 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 8 8 299229504915 201139629592 contact31ColumnsJoin32_8 contact31ColumnsJoin40_8
private theorem contact31ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact31) 48 16 = 188034626265 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 8 8 123044809164 64989817101 contact31ColumnsJoin48_8 contact31ColumnsJoin56_8
private theorem contact31ColumnsJoin64_13 : sliceWindow (auxiliaryColumnSlice contact31) 64 13 = 32759597769 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 8 5 26873711286 5885886483 contact31ColumnsJoin64_8 contact31ColumnsJoin72_5
private theorem contact31ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact31) 0 32 = 2578135040988 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 16 16 1605332469024 972802571964 contact31ColumnsJoin0_16 contact31ColumnsJoin16_16
private theorem contact31ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact31) 32 32 = 688403760772 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 16 16 500369134507 188034626265 contact31ColumnsJoin32_16 contact31ColumnsJoin48_16
private theorem contact31ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact31) 0 64 = 3266538801760 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 32 32 2578135040988 688403760772 contact31ColumnsJoin0_32 contact31ColumnsJoin32_32
private theorem contact31ColumnsJoin0_77 : sliceWindow (auxiliaryColumnSlice contact31) 0 77 = 3299298399529 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 64 13 3266538801760 32759597769 contact31ColumnsJoin0_64 contact31ColumnsJoin64_13
private theorem contact31OrdinaryRanks : ordinaryRankBound contact31 = 213629514 := by decide +kernel
private theorem contact31RanksSlice0 : sliceWindow (auxiliaryRankSlice contact31) 0 4 = 1750986 :=
  contactRankWindow_of_rec contact31 0 4 1750986 (by decide +kernel)
private theorem contact31RanksSlice4 : sliceWindow (auxiliaryRankSlice contact31) 4 4 = 1524186 :=
  contactRankWindow_of_rec contact31 4 4 1524186 (by decide +kernel)
private theorem contact31RanksSlice8 : sliceWindow (auxiliaryRankSlice contact31) 8 4 = 1314666 :=
  contactRankWindow_of_rec contact31 8 4 1314666 (by decide +kernel)
private theorem contact31RanksSlice12 : sliceWindow (auxiliaryRankSlice contact31) 12 4 = 1122426 :=
  contactRankWindow_of_rec contact31 12 4 1122426 (by decide +kernel)
private theorem contact31RanksSlice16 : sliceWindow (auxiliaryRankSlice contact31) 16 4 = 947466 :=
  contactRankWindow_of_rec contact31 16 4 947466 (by decide +kernel)
private theorem contact31RanksSlice20 : sliceWindow (auxiliaryRankSlice contact31) 20 4 = 789786 :=
  contactRankWindow_of_rec contact31 20 4 789786 (by decide +kernel)
private theorem contact31RanksSlice24 : sliceWindow (auxiliaryRankSlice contact31) 24 4 = 649280 :=
  contactRankWindow_of_rec contact31 24 4 649280 (by decide +kernel)
private theorem contact31RanksSlice28 : sliceWindow (auxiliaryRankSlice contact31) 28 4 = 525394 :=
  contactRankWindow_of_rec contact31 28 4 525394 (by decide +kernel)
private theorem contact31RanksSlice32 : sliceWindow (auxiliaryRankSlice contact31) 32 4 = 417315 :=
  contactRankWindow_of_rec contact31 32 4 417315 (by decide +kernel)
private theorem contact31RanksSlice36 : sliceWindow (auxiliaryRankSlice contact31) 36 4 = 324140 :=
  contactRankWindow_of_rec contact31 36 4 324140 (by decide +kernel)
private theorem contact31RanksSlice40 : sliceWindow (auxiliaryRankSlice contact31) 40 4 = 244894 :=
  contactRankWindow_of_rec contact31 40 4 244894 (by decide +kernel)
private theorem contact31RanksSlice44 : sliceWindow (auxiliaryRankSlice contact31) 44 4 = 178615 :=
  contactRankWindow_of_rec contact31 44 4 178615 (by decide +kernel)
private theorem contact31RanksSlice48 : sliceWindow (auxiliaryRankSlice contact31) 48 4 = 124472 :=
  contactRankWindow_of_rec contact31 48 4 124472 (by decide +kernel)
private theorem contact31RanksSlice52 : sliceWindow (auxiliaryRankSlice contact31) 52 4 = 81418 :=
  contactRankWindow_of_rec contact31 52 4 81418 (by decide +kernel)
private theorem contact31RanksSlice56 : sliceWindow (auxiliaryRankSlice contact31) 56 4 = 48491 :=
  contactRankWindow_of_rec contact31 56 4 48491 (by decide +kernel)
private theorem contact31RanksSlice60 : sliceWindow (auxiliaryRankSlice contact31) 60 4 = 24932 :=
  contactRankWindow_of_rec contact31 60 4 24932 (by decide +kernel)
private theorem contact31RanksSlice64 : sliceWindow (auxiliaryRankSlice contact31) 64 4 = 9622 :=
  contactRankWindow_of_rec contact31 64 4 9622 (by decide +kernel)
private theorem contact31RanksSlice68 : sliceWindow (auxiliaryRankSlice contact31) 68 4 = 1638 :=
  contactRankWindow_of_rec contact31 68 4 1638 (by decide +kernel)
private theorem contact31RanksSlice72 : sliceWindow (auxiliaryRankSlice contact31) 72 5 = 0 :=
  contactRankWindow_of_rec contact31 72 5 0 (by decide +kernel)
private theorem contact31RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact31) 0 8 = 3275172 :=
  combineSlices (auxiliaryRankSlice contact31) 0 4 4 1750986 1524186 contact31RanksSlice0 contact31RanksSlice4
private theorem contact31RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact31) 8 8 = 2437092 :=
  combineSlices (auxiliaryRankSlice contact31) 8 4 4 1314666 1122426 contact31RanksSlice8 contact31RanksSlice12
private theorem contact31RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact31) 16 8 = 1737252 :=
  combineSlices (auxiliaryRankSlice contact31) 16 4 4 947466 789786 contact31RanksSlice16 contact31RanksSlice20
private theorem contact31RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact31) 24 8 = 1174674 :=
  combineSlices (auxiliaryRankSlice contact31) 24 4 4 649280 525394 contact31RanksSlice24 contact31RanksSlice28
private theorem contact31RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact31) 32 8 = 741455 :=
  combineSlices (auxiliaryRankSlice contact31) 32 4 4 417315 324140 contact31RanksSlice32 contact31RanksSlice36
private theorem contact31RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact31) 40 8 = 423509 :=
  combineSlices (auxiliaryRankSlice contact31) 40 4 4 244894 178615 contact31RanksSlice40 contact31RanksSlice44
private theorem contact31RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact31) 48 8 = 205890 :=
  combineSlices (auxiliaryRankSlice contact31) 48 4 4 124472 81418 contact31RanksSlice48 contact31RanksSlice52
private theorem contact31RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact31) 56 8 = 73423 :=
  combineSlices (auxiliaryRankSlice contact31) 56 4 4 48491 24932 contact31RanksSlice56 contact31RanksSlice60
private theorem contact31RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact31) 64 8 = 11260 :=
  combineSlices (auxiliaryRankSlice contact31) 64 4 4 9622 1638 contact31RanksSlice64 contact31RanksSlice68
private theorem contact31RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact31) 0 16 = 5712264 :=
  combineSlices (auxiliaryRankSlice contact31) 0 8 8 3275172 2437092 contact31RanksJoin0_8 contact31RanksJoin8_8
private theorem contact31RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact31) 16 16 = 2911926 :=
  combineSlices (auxiliaryRankSlice contact31) 16 8 8 1737252 1174674 contact31RanksJoin16_8 contact31RanksJoin24_8
private theorem contact31RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact31) 32 16 = 1164964 :=
  combineSlices (auxiliaryRankSlice contact31) 32 8 8 741455 423509 contact31RanksJoin32_8 contact31RanksJoin40_8
private theorem contact31RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact31) 48 16 = 279313 :=
  combineSlices (auxiliaryRankSlice contact31) 48 8 8 205890 73423 contact31RanksJoin48_8 contact31RanksJoin56_8
private theorem contact31RanksJoin64_13 : sliceWindow (auxiliaryRankSlice contact31) 64 13 = 11260 :=
  combineSlices (auxiliaryRankSlice contact31) 64 8 5 11260 0 contact31RanksJoin64_8 contact31RanksSlice72
private theorem contact31RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact31) 0 32 = 8624190 :=
  combineSlices (auxiliaryRankSlice contact31) 0 16 16 5712264 2911926 contact31RanksJoin0_16 contact31RanksJoin16_16
private theorem contact31RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact31) 32 32 = 1444277 :=
  combineSlices (auxiliaryRankSlice contact31) 32 16 16 1164964 279313 contact31RanksJoin32_16 contact31RanksJoin48_16
private theorem contact31RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact31) 0 64 = 10068467 :=
  combineSlices (auxiliaryRankSlice contact31) 0 32 32 8624190 1444277 contact31RanksJoin0_32 contact31RanksJoin32_32
private theorem contact31RanksJoin0_77 : sliceWindow (auxiliaryRankSlice contact31) 0 77 = 10079727 :=
  combineSlices (auxiliaryRankSlice contact31) 0 64 13 10068467 11260 contact31RanksJoin0_64 contact31RanksJoin64_13
theorem contact31_margin : sourceMargin contact31 :=
  margin_of_checked_counts contact31 77 55344872441854 3299298399529 213629514 10079727 rfl contact31OrdinaryColumns contact31ColumnsJoin0_77 contact31OrdinaryRanks contact31RanksJoin0_77 (by decide +kernel)

private theorem contact33OrdinaryColumns : ordinaryColumnCount contact33 = 224664250201406 := by decide +kernel
private theorem contact33ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact33) 0 4 = 942314314588 :=
  contactColumnsWindow_fast contact33 0 4 942314314588 (by decide +kernel)
private theorem contact33ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact33) 4 4 = 863102810172 :=
  contactColumnsWindow_fast contact33 4 4 863102810172 (by decide +kernel)
private theorem contact33ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact33) 8 4 = 787386137203 :=
  contactColumnsWindow_fast contact33 8 4 787386137203 (by decide +kernel)
private theorem contact33ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact33) 12 4 = 715183088376 :=
  contactColumnsWindow_fast contact33 12 4 715183088376 (by decide +kernel)
private theorem contact33ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact33) 16 4 = 646482882073 :=
  contactColumnsWindow_fast contact33 16 4 646482882073 (by decide +kernel)
private theorem contact33ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact33) 20 4 = 581279454236 :=
  contactColumnsWindow_fast contact33 20 4 581279454236 (by decide +kernel)
private theorem contact33ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact33) 24 4 = 519571288392 :=
  contactColumnsWindow_fast contact33 24 4 519571288392 (by decide +kernel)
private theorem contact33ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact33) 28 4 = 461361522585 :=
  contactColumnsWindow_fast contact33 28 4 461361522585 (by decide +kernel)
private theorem contact33ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact33) 32 4 = 406668008869 :=
  contactColumnsWindow_fast contact33 32 4 406668008869 (by decide +kernel)
private theorem contact33ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact33) 36 4 = 355478488282 :=
  contactColumnsWindow_fast contact33 36 4 355478488282 (by decide +kernel)
private theorem contact33ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact33) 40 4 = 307786017680 :=
  contactColumnsWindow_fast contact33 40 4 307786017680 (by decide +kernel)
private theorem contact33ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact33) 44 4 = 263588808324 :=
  contactColumnsWindow_fast contact33 44 4 263588808324 (by decide +kernel)
private theorem contact33ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact33) 48 4 = 222891000590 :=
  contactColumnsWindow_fast contact33 48 4 222891000590 (by decide +kernel)
private theorem contact33ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact33) 52 4 = 185710279315 :=
  contactColumnsWindow_fast contact33 52 4 185710279315 (by decide +kernel)
private theorem contact33ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact33) 56 4 = 152031801202 :=
  contactColumnsWindow_fast contact33 56 4 152031801202 (by decide +kernel)
private theorem contact33ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact33) 60 4 = 121850276972 :=
  contactColumnsWindow_fast contact33 60 4 121850276972 (by decide +kernel)
private theorem contact33ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact33) 64 4 = 95164082118 :=
  contactColumnsWindow_fast contact33 64 4 95164082118 (by decide +kernel)
private theorem contact33ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact33) 68 4 = 71978538518 :=
  contactColumnsWindow_fast contact33 68 4 71978538518 (by decide +kernel)
private theorem contact33ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact33) 72 4 = 52310245609 :=
  contactColumnsWindow_fast contact33 72 4 52310245609 (by decide +kernel)
private theorem contact33ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact33) 76 4 = 36142415604 :=
  contactColumnsWindow_fast contact33 76 4 36142415604 (by decide +kernel)
private theorem contact33ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact33) 80 4 = 23439734525 :=
  contactColumnsWindow_fast contact33 80 4 23439734525 (by decide +kernel)
private theorem contact33ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact33) 84 4 = 14032520089 :=
  contactColumnsWindow_fast contact33 84 4 14032520089 (by decide +kernel)
private theorem contact33ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact33) 88 4 = 7588698525 :=
  contactColumnsWindow_fast contact33 88 4 7588698525 (by decide +kernel)
private theorem contact33ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact33) 92 3 = 2973035898 :=
  contactColumnsWindow_fast contact33 92 3 2973035898 (by decide +kernel)
private theorem contact33ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact33) 0 8 = 1805417124760 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 4 4 942314314588 863102810172 contact33ColumnsSlice0 contact33ColumnsSlice4
private theorem contact33ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact33) 8 8 = 1502569225579 :=
  combineSlices (auxiliaryColumnSlice contact33) 8 4 4 787386137203 715183088376 contact33ColumnsSlice8 contact33ColumnsSlice12
private theorem contact33ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact33) 16 8 = 1227762336309 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 4 4 646482882073 581279454236 contact33ColumnsSlice16 contact33ColumnsSlice20
private theorem contact33ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact33) 24 8 = 980932810977 :=
  combineSlices (auxiliaryColumnSlice contact33) 24 4 4 519571288392 461361522585 contact33ColumnsSlice24 contact33ColumnsSlice28
private theorem contact33ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact33) 32 8 = 762146497151 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 4 4 406668008869 355478488282 contact33ColumnsSlice32 contact33ColumnsSlice36
private theorem contact33ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact33) 40 8 = 571374826004 :=
  combineSlices (auxiliaryColumnSlice contact33) 40 4 4 307786017680 263588808324 contact33ColumnsSlice40 contact33ColumnsSlice44
private theorem contact33ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact33) 48 8 = 408601279905 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 4 4 222891000590 185710279315 contact33ColumnsSlice48 contact33ColumnsSlice52
private theorem contact33ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact33) 56 8 = 273882078174 :=
  combineSlices (auxiliaryColumnSlice contact33) 56 4 4 152031801202 121850276972 contact33ColumnsSlice56 contact33ColumnsSlice60
private theorem contact33ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact33) 64 8 = 167142620636 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 4 4 95164082118 71978538518 contact33ColumnsSlice64 contact33ColumnsSlice68
private theorem contact33ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact33) 72 8 = 88452661213 :=
  combineSlices (auxiliaryColumnSlice contact33) 72 4 4 52310245609 36142415604 contact33ColumnsSlice72 contact33ColumnsSlice76
private theorem contact33ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact33) 80 8 = 37472254614 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 4 4 23439734525 14032520089 contact33ColumnsSlice80 contact33ColumnsSlice84
private theorem contact33ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact33) 88 7 = 10561734423 :=
  combineSlices (auxiliaryColumnSlice contact33) 88 4 3 7588698525 2973035898 contact33ColumnsSlice88 contact33ColumnsSlice92
private theorem contact33ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact33) 0 16 = 3307986350339 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 8 8 1805417124760 1502569225579 contact33ColumnsJoin0_8 contact33ColumnsJoin8_8
private theorem contact33ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact33) 16 16 = 2208695147286 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 8 8 1227762336309 980932810977 contact33ColumnsJoin16_8 contact33ColumnsJoin24_8
private theorem contact33ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact33) 32 16 = 1333521323155 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 8 8 762146497151 571374826004 contact33ColumnsJoin32_8 contact33ColumnsJoin40_8
private theorem contact33ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact33) 48 16 = 682483358079 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 8 8 408601279905 273882078174 contact33ColumnsJoin48_8 contact33ColumnsJoin56_8
private theorem contact33ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact33) 64 16 = 255595281849 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 8 8 167142620636 88452661213 contact33ColumnsJoin64_8 contact33ColumnsJoin72_8
private theorem contact33ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact33) 80 15 = 48033989037 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 8 7 37472254614 10561734423 contact33ColumnsJoin80_8 contact33ColumnsJoin88_7
private theorem contact33ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact33) 0 32 = 5516681497625 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 16 16 3307986350339 2208695147286 contact33ColumnsJoin0_16 contact33ColumnsJoin16_16
private theorem contact33ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact33) 32 32 = 2016004681234 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 16 16 1333521323155 682483358079 contact33ColumnsJoin32_16 contact33ColumnsJoin48_16
private theorem contact33ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact33) 64 31 = 303629270886 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 16 15 255595281849 48033989037 contact33ColumnsJoin64_16 contact33ColumnsJoin80_15
private theorem contact33ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact33) 0 64 = 7532686178859 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 32 32 5516681497625 2016004681234 contact33ColumnsJoin0_32 contact33ColumnsJoin32_32
private theorem contact33ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact33) 0 95 = 7836315449745 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 64 31 7532686178859 303629270886 contact33ColumnsJoin0_64 contact33ColumnsJoin64_31
private theorem contact33OrdinaryRanks : ordinaryRankBound contact33 = 862947036 := by decide +kernel
private theorem contact33RanksSlice0 : sliceWindow (auxiliaryRankSlice contact33) 0 4 = 3530886 :=
  contactRankWindow_of_rec contact33 0 4 3530886 (by decide +kernel)
private theorem contact33RanksSlice4 : sliceWindow (auxiliaryRankSlice contact33) 4 4 = 3146838 :=
  contactRankWindow_of_rec contact33 4 4 3146838 (by decide +kernel)
private theorem contact33RanksSlice8 : sliceWindow (auxiliaryRankSlice contact33) 8 4 = 2786982 :=
  contactRankWindow_of_rec contact33 8 4 2786982 (by decide +kernel)
private theorem contact33RanksSlice12 : sliceWindow (auxiliaryRankSlice contact33) 12 4 = 2451318 :=
  contactRankWindow_of_rec contact33 12 4 2451318 (by decide +kernel)
private theorem contact33RanksSlice16 : sliceWindow (auxiliaryRankSlice contact33) 16 4 = 2139846 :=
  contactRankWindow_of_rec contact33 16 4 2139846 (by decide +kernel)
private theorem contact33RanksSlice20 : sliceWindow (auxiliaryRankSlice contact33) 20 4 = 1852566 :=
  contactRankWindow_of_rec contact33 20 4 1852566 (by decide +kernel)
private theorem contact33RanksSlice24 : sliceWindow (auxiliaryRankSlice contact33) 24 4 = 1589478 :=
  contactRankWindow_of_rec contact33 24 4 1589478 (by decide +kernel)
private theorem contact33RanksSlice28 : sliceWindow (auxiliaryRankSlice contact33) 28 4 = 1350528 :=
  contactRankWindow_of_rec contact33 28 4 1350528 (by decide +kernel)
private theorem contact33RanksSlice32 : sliceWindow (auxiliaryRankSlice contact33) 32 4 = 1135184 :=
  contactRankWindow_of_rec contact33 32 4 1135184 (by decide +kernel)
private theorem contact33RanksSlice36 : sliceWindow (auxiliaryRankSlice contact33) 36 4 = 942556 :=
  contactRankWindow_of_rec contact33 36 4 942556 (by decide +kernel)
private theorem contact33RanksSlice40 : sliceWindow (auxiliaryRankSlice contact33) 40 4 = 771529 :=
  contactRankWindow_of_rec contact33 40 4 771529 (by decide +kernel)
private theorem contact33RanksSlice44 : sliceWindow (auxiliaryRankSlice contact33) 44 4 = 621056 :=
  contactRankWindow_of_rec contact33 44 4 621056 (by decide +kernel)
private theorem contact33RanksSlice48 : sliceWindow (auxiliaryRankSlice contact33) 48 4 = 489964 :=
  contactRankWindow_of_rec contact33 48 4 489964 (by decide +kernel)
private theorem contact33RanksSlice52 : sliceWindow (auxiliaryRankSlice contact33) 52 4 = 377117 :=
  contactRankWindow_of_rec contact33 52 4 377117 (by decide +kernel)
private theorem contact33RanksSlice56 : sliceWindow (auxiliaryRankSlice contact33) 56 4 = 281552 :=
  contactRankWindow_of_rec contact33 56 4 281552 (by decide +kernel)
private theorem contact33RanksSlice60 : sliceWindow (auxiliaryRankSlice contact33) 60 4 = 202012 :=
  contactRankWindow_of_rec contact33 60 4 202012 (by decide +kernel)
private theorem contact33RanksSlice64 : sliceWindow (auxiliaryRankSlice contact33) 64 4 = 137361 :=
  contactRankWindow_of_rec contact33 64 4 137361 (by decide +kernel)
private theorem contact33RanksSlice68 : sliceWindow (auxiliaryRankSlice contact33) 68 4 = 86720 :=
  contactRankWindow_of_rec contact33 68 4 86720 (by decide +kernel)
private theorem contact33RanksSlice72 : sliceWindow (auxiliaryRankSlice contact33) 72 4 = 48748 :=
  contactRankWindow_of_rec contact33 72 4 48748 (by decide +kernel)
private theorem contact33RanksSlice76 : sliceWindow (auxiliaryRankSlice contact33) 76 4 = 22309 :=
  contactRankWindow_of_rec contact33 76 4 22309 (by decide +kernel)
private theorem contact33RanksSlice80 : sliceWindow (auxiliaryRankSlice contact33) 80 4 = 6632 :=
  contactRankWindow_of_rec contact33 80 4 6632 (by decide +kernel)
private theorem contact33RanksSlice84 : sliceWindow (auxiliaryRankSlice contact33) 84 4 = 363 :=
  contactRankWindow_of_rec contact33 84 4 363 (by decide +kernel)
private theorem contact33RanksSlice88 : sliceWindow (auxiliaryRankSlice contact33) 88 7 = 0 :=
  contactRankWindow_of_rec contact33 88 7 0 (by decide +kernel)
private theorem contact33RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact33) 0 8 = 6677724 :=
  combineSlices (auxiliaryRankSlice contact33) 0 4 4 3530886 3146838 contact33RanksSlice0 contact33RanksSlice4
private theorem contact33RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact33) 8 8 = 5238300 :=
  combineSlices (auxiliaryRankSlice contact33) 8 4 4 2786982 2451318 contact33RanksSlice8 contact33RanksSlice12
private theorem contact33RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact33) 16 8 = 3992412 :=
  combineSlices (auxiliaryRankSlice contact33) 16 4 4 2139846 1852566 contact33RanksSlice16 contact33RanksSlice20
private theorem contact33RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact33) 24 8 = 2940006 :=
  combineSlices (auxiliaryRankSlice contact33) 24 4 4 1589478 1350528 contact33RanksSlice24 contact33RanksSlice28
private theorem contact33RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact33) 32 8 = 2077740 :=
  combineSlices (auxiliaryRankSlice contact33) 32 4 4 1135184 942556 contact33RanksSlice32 contact33RanksSlice36
private theorem contact33RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact33) 40 8 = 1392585 :=
  combineSlices (auxiliaryRankSlice contact33) 40 4 4 771529 621056 contact33RanksSlice40 contact33RanksSlice44
private theorem contact33RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact33) 48 8 = 867081 :=
  combineSlices (auxiliaryRankSlice contact33) 48 4 4 489964 377117 contact33RanksSlice48 contact33RanksSlice52
private theorem contact33RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact33) 56 8 = 483564 :=
  combineSlices (auxiliaryRankSlice contact33) 56 4 4 281552 202012 contact33RanksSlice56 contact33RanksSlice60
private theorem contact33RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact33) 64 8 = 224081 :=
  combineSlices (auxiliaryRankSlice contact33) 64 4 4 137361 86720 contact33RanksSlice64 contact33RanksSlice68
private theorem contact33RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact33) 72 8 = 71057 :=
  combineSlices (auxiliaryRankSlice contact33) 72 4 4 48748 22309 contact33RanksSlice72 contact33RanksSlice76
private theorem contact33RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact33) 80 8 = 6995 :=
  combineSlices (auxiliaryRankSlice contact33) 80 4 4 6632 363 contact33RanksSlice80 contact33RanksSlice84
private theorem contact33RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact33) 0 16 = 11916024 :=
  combineSlices (auxiliaryRankSlice contact33) 0 8 8 6677724 5238300 contact33RanksJoin0_8 contact33RanksJoin8_8
private theorem contact33RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact33) 16 16 = 6932418 :=
  combineSlices (auxiliaryRankSlice contact33) 16 8 8 3992412 2940006 contact33RanksJoin16_8 contact33RanksJoin24_8
private theorem contact33RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact33) 32 16 = 3470325 :=
  combineSlices (auxiliaryRankSlice contact33) 32 8 8 2077740 1392585 contact33RanksJoin32_8 contact33RanksJoin40_8
private theorem contact33RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact33) 48 16 = 1350645 :=
  combineSlices (auxiliaryRankSlice contact33) 48 8 8 867081 483564 contact33RanksJoin48_8 contact33RanksJoin56_8
private theorem contact33RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact33) 64 16 = 295138 :=
  combineSlices (auxiliaryRankSlice contact33) 64 8 8 224081 71057 contact33RanksJoin64_8 contact33RanksJoin72_8
private theorem contact33RanksJoin80_15 : sliceWindow (auxiliaryRankSlice contact33) 80 15 = 6995 :=
  combineSlices (auxiliaryRankSlice contact33) 80 8 7 6995 0 contact33RanksJoin80_8 contact33RanksSlice88
private theorem contact33RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact33) 0 32 = 18848442 :=
  combineSlices (auxiliaryRankSlice contact33) 0 16 16 11916024 6932418 contact33RanksJoin0_16 contact33RanksJoin16_16
private theorem contact33RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact33) 32 32 = 4820970 :=
  combineSlices (auxiliaryRankSlice contact33) 32 16 16 3470325 1350645 contact33RanksJoin32_16 contact33RanksJoin48_16
private theorem contact33RanksJoin64_31 : sliceWindow (auxiliaryRankSlice contact33) 64 31 = 302133 :=
  combineSlices (auxiliaryRankSlice contact33) 64 16 15 295138 6995 contact33RanksJoin64_16 contact33RanksJoin80_15
private theorem contact33RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact33) 0 64 = 23669412 :=
  combineSlices (auxiliaryRankSlice contact33) 0 32 32 18848442 4820970 contact33RanksJoin0_32 contact33RanksJoin32_32
private theorem contact33RanksJoin0_95 : sliceWindow (auxiliaryRankSlice contact33) 0 95 = 23971545 :=
  combineSlices (auxiliaryRankSlice contact33) 0 64 31 23669412 302133 contact33RanksJoin0_64 contact33RanksJoin64_31
theorem contact33_margin : sourceMargin contact33 :=
  margin_of_checked_counts contact33 95 224664250201406 7836315449745 862947036 23971545 rfl contact33OrdinaryColumns contact33ColumnsJoin0_95 contact33OrdinaryRanks contact33RanksJoin0_95 (by decide +kernel)

private theorem contact35OrdinaryColumns : ordinaryColumnCount contact35 = 6712498102238338 := by decide +kernel
private theorem contact35ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact35) 0 4 = 21184223387740 :=
  contactColumnsWindow_fast contact35 0 4 21184223387740 (by decide +kernel)
private theorem contact35ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact35) 4 4 = 20401711090636 :=
  contactColumnsWindow_fast contact35 4 4 20401711090636 (by decide +kernel)
private theorem contact35ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact35) 8 4 = 19633979284348 :=
  contactColumnsWindow_fast contact35 8 4 19633979284348 (by decide +kernel)
private theorem contact35ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact35) 12 4 = 18881030612080 :=
  contactColumnsWindow_fast contact35 12 4 18881030612080 (by decide +kernel)
private theorem contact35ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact35) 16 4 = 18142865879584 :=
  contactColumnsWindow_fast contact35 16 4 18142865879584 (by decide +kernel)
private theorem contact35ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact35) 20 4 = 17419485212360 :=
  contactColumnsWindow_fast contact35 20 4 17419485212360 (by decide +kernel)
private theorem contact35ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact35) 24 4 = 16710887889355 :=
  contactColumnsWindow_fast contact35 24 4 16710887889355 (by decide +kernel)
private theorem contact35ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact35) 28 4 = 16017075375844 :=
  contactColumnsWindow_fast contact35 28 4 16017075375844 (by decide +kernel)
private theorem contact35ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact35) 32 4 = 15338053338985 :=
  contactColumnsWindow_fast contact35 32 4 15338053338985 (by decide +kernel)
private theorem contact35ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact35) 36 4 = 14673880609525 :=
  contactColumnsWindow_fast contact35 36 4 14673880609525 (by decide +kernel)
private theorem contact35ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact35) 40 4 = 14024513023390 :=
  contactColumnsWindow_fast contact35 40 4 14024513023390 (by decide +kernel)
private theorem contact35ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact35) 44 4 = 13389933606824 :=
  contactColumnsWindow_fast contact35 44 4 13389933606824 (by decide +kernel)
private theorem contact35ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact35) 48 4 = 12770141544252 :=
  contactColumnsWindow_fast contact35 48 4 12770141544252 (by decide +kernel)
private theorem contact35ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact35) 52 4 = 12165148757602 :=
  contactColumnsWindow_fast contact35 52 4 12165148757602 (by decide +kernel)
private theorem contact35ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact35) 56 4 = 11575009294141 :=
  contactColumnsWindow_fast contact35 56 4 11575009294141 (by decide +kernel)
private theorem contact35ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact35) 60 4 = 10999675495408 :=
  contactColumnsWindow_fast contact35 60 4 10999675495408 (by decide +kernel)
private theorem contact35ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact35) 64 4 = 10439132646970 :=
  contactColumnsWindow_fast contact35 64 4 10439132646970 (by decide +kernel)
private theorem contact35ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact35) 68 4 = 9893382470947 :=
  contactColumnsWindow_fast contact35 68 4 9893382470947 (by decide +kernel)
private theorem contact35ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact35) 72 4 = 9362439361498 :=
  contactColumnsWindow_fast contact35 72 4 9362439361498 (by decide +kernel)
private theorem contact35ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact35) 76 4 = 8846353526989 :=
  contactColumnsWindow_fast contact35 76 4 8846353526989 (by decide +kernel)
private theorem contact35ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact35) 80 4 = 8345074441025 :=
  contactColumnsWindow_fast contact35 80 4 8345074441025 (by decide +kernel)
private theorem contact35ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact35) 84 4 = 7858589843391 :=
  contactColumnsWindow_fast contact35 84 4 7858589843391 (by decide +kernel)
private theorem contact35ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact35) 88 4 = 7386903328897 :=
  contactColumnsWindow_fast contact35 88 4 7386903328897 (by decide +kernel)
private theorem contact35ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact35) 92 4 = 6930031369294 :=
  contactColumnsWindow_fast contact35 92 4 6930031369294 (by decide +kernel)
private theorem contact35ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact35) 96 4 = 6488022735129 :=
  contactColumnsWindow_fast contact35 96 4 6488022735129 (by decide +kernel)
private theorem contact35ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact35) 100 4 = 6060818492840 :=
  contactColumnsWindow_fast contact35 100 4 6060818492840 (by decide +kernel)
private theorem contact35ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact35) 104 4 = 5648408636298 :=
  contactColumnsWindow_fast contact35 104 4 5648408636298 (by decide +kernel)
private theorem contact35ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact35) 108 4 = 5250797205679 :=
  contactColumnsWindow_fast contact35 108 4 5250797205679 (by decide +kernel)
private theorem contact35ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact35) 112 4 = 4868006379373 :=
  contactColumnsWindow_fast contact35 112 4 4868006379373 (by decide +kernel)
private theorem contact35ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact35) 116 4 = 4500075022626 :=
  contactColumnsWindow_fast contact35 116 4 4500075022626 (by decide +kernel)
private theorem contact35ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact35) 120 4 = 4146945540940 :=
  contactColumnsWindow_fast contact35 120 4 4146945540940 (by decide +kernel)
private theorem contact35ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact35) 124 4 = 3808610619250 :=
  contactColumnsWindow_fast contact35 124 4 3808610619250 (by decide +kernel)
private theorem contact35ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact35) 128 4 = 3485074348702 :=
  contactColumnsWindow_fast contact35 128 4 3485074348702 (by decide +kernel)
private theorem contact35ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact35) 132 4 = 3176364537937 :=
  contactColumnsWindow_fast contact35 132 4 3176364537937 (by decide +kernel)
private theorem contact35ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact35) 136 4 = 2882510356222 :=
  contactColumnsWindow_fast contact35 136 4 2882510356222 (by decide +kernel)
private theorem contact35ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact35) 140 4 = 2603455786432 :=
  contactColumnsWindow_fast contact35 140 4 2603455786432 (by decide +kernel)
private theorem contact35ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact35) 144 4 = 2339195664127 :=
  contactColumnsWindow_fast contact35 144 4 2339195664127 (by decide +kernel)
private theorem contact35ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact35) 148 4 = 2089734445624 :=
  contactColumnsWindow_fast contact35 148 4 2089734445624 (by decide +kernel)
private theorem contact35ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact35) 152 4 = 1855106482847 :=
  contactColumnsWindow_fast contact35 152 4 1855106482847 (by decide +kernel)
private theorem contact35ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact35) 156 4 = 1635328885573 :=
  contactColumnsWindow_fast contact35 156 4 1635328885573 (by decide +kernel)
private theorem contact35ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact35) 160 4 = 1430349036643 :=
  contactColumnsWindow_fast contact35 160 4 1430349036643 (by decide +kernel)
private theorem contact35ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact35) 164 4 = 1240163770335 :=
  contactColumnsWindow_fast contact35 164 4 1240163770335 (by decide +kernel)
private theorem contact35ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact35) 168 4 = 1064777776831 :=
  contactColumnsWindow_fast contact35 168 4 1064777776831 (by decide +kernel)
private theorem contact35ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact35) 172 4 = 904233058205 :=
  contactColumnsWindow_fast contact35 172 4 904233058205 (by decide +kernel)
private theorem contact35ColumnsSlice176 : sliceWindow (auxiliaryColumnSlice contact35) 176 4 = 758530372128 :=
  contactColumnsWindow_fast contact35 176 4 758530372128 (by decide +kernel)
private theorem contact35ColumnsSlice180 : sliceWindow (auxiliaryColumnSlice contact35) 180 4 = 627623030957 :=
  contactColumnsWindow_fast contact35 180 4 627623030957 (by decide +kernel)
private theorem contact35ColumnsSlice184 : sliceWindow (auxiliaryColumnSlice contact35) 184 4 = 511442590656 :=
  contactColumnsWindow_fast contact35 184 4 511442590656 (by decide +kernel)
private theorem contact35ColumnsSlice188 : sliceWindow (auxiliaryColumnSlice contact35) 188 4 = 409722486645 :=
  contactColumnsWindow_fast contact35 188 4 409722486645 (by decide +kernel)
private theorem contact35ColumnsSlice192 : sliceWindow (auxiliaryColumnSlice contact35) 192 4 = 322042723676 :=
  contactColumnsWindow_fast contact35 192 4 322042723676 (by decide +kernel)
private theorem contact35ColumnsSlice196 : sliceWindow (auxiliaryColumnSlice contact35) 196 4 = 247761261900 :=
  contactColumnsWindow_fast contact35 196 4 247761261900 (by decide +kernel)
private theorem contact35ColumnsSlice200 : sliceWindow (auxiliaryColumnSlice contact35) 200 4 = 186054771796 :=
  contactColumnsWindow_fast contact35 200 4 186054771796 (by decide +kernel)
private theorem contact35ColumnsSlice204 : sliceWindow (auxiliaryColumnSlice contact35) 204 4 = 135973960240 :=
  contactColumnsWindow_fast contact35 204 4 135973960240 (by decide +kernel)
private theorem contact35ColumnsSlice208 : sliceWindow (auxiliaryColumnSlice contact35) 208 4 = 96412160506 :=
  contactColumnsWindow_fast contact35 208 4 96412160506 (by decide +kernel)
private theorem contact35ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact35) 0 8 = 41585934478376 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 4 4 21184223387740 20401711090636 contact35ColumnsSlice0 contact35ColumnsSlice4
private theorem contact35ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact35) 8 8 = 38515009896428 :=
  combineSlices (auxiliaryColumnSlice contact35) 8 4 4 19633979284348 18881030612080 contact35ColumnsSlice8 contact35ColumnsSlice12
private theorem contact35ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact35) 16 8 = 35562351091944 :=
  combineSlices (auxiliaryColumnSlice contact35) 16 4 4 18142865879584 17419485212360 contact35ColumnsSlice16 contact35ColumnsSlice20
private theorem contact35ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact35) 24 8 = 32727963265199 :=
  combineSlices (auxiliaryColumnSlice contact35) 24 4 4 16710887889355 16017075375844 contact35ColumnsSlice24 contact35ColumnsSlice28
private theorem contact35ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact35) 32 8 = 30011933948510 :=
  combineSlices (auxiliaryColumnSlice contact35) 32 4 4 15338053338985 14673880609525 contact35ColumnsSlice32 contact35ColumnsSlice36
private theorem contact35ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact35) 40 8 = 27414446630214 :=
  combineSlices (auxiliaryColumnSlice contact35) 40 4 4 14024513023390 13389933606824 contact35ColumnsSlice40 contact35ColumnsSlice44
private theorem contact35ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact35) 48 8 = 24935290301854 :=
  combineSlices (auxiliaryColumnSlice contact35) 48 4 4 12770141544252 12165148757602 contact35ColumnsSlice48 contact35ColumnsSlice52
private theorem contact35ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact35) 56 8 = 22574684789549 :=
  combineSlices (auxiliaryColumnSlice contact35) 56 4 4 11575009294141 10999675495408 contact35ColumnsSlice56 contact35ColumnsSlice60
private theorem contact35ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact35) 64 8 = 20332515117917 :=
  combineSlices (auxiliaryColumnSlice contact35) 64 4 4 10439132646970 9893382470947 contact35ColumnsSlice64 contact35ColumnsSlice68
private theorem contact35ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact35) 72 8 = 18208792888487 :=
  combineSlices (auxiliaryColumnSlice contact35) 72 4 4 9362439361498 8846353526989 contact35ColumnsSlice72 contact35ColumnsSlice76
private theorem contact35ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact35) 80 8 = 16203664284416 :=
  combineSlices (auxiliaryColumnSlice contact35) 80 4 4 8345074441025 7858589843391 contact35ColumnsSlice80 contact35ColumnsSlice84
private theorem contact35ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact35) 88 8 = 14316934698191 :=
  combineSlices (auxiliaryColumnSlice contact35) 88 4 4 7386903328897 6930031369294 contact35ColumnsSlice88 contact35ColumnsSlice92
private theorem contact35ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact35) 96 8 = 12548841227969 :=
  combineSlices (auxiliaryColumnSlice contact35) 96 4 4 6488022735129 6060818492840 contact35ColumnsSlice96 contact35ColumnsSlice100
private theorem contact35ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact35) 104 8 = 10899205841977 :=
  combineSlices (auxiliaryColumnSlice contact35) 104 4 4 5648408636298 5250797205679 contact35ColumnsSlice104 contact35ColumnsSlice108
private theorem contact35ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact35) 112 8 = 9368081401999 :=
  combineSlices (auxiliaryColumnSlice contact35) 112 4 4 4868006379373 4500075022626 contact35ColumnsSlice112 contact35ColumnsSlice116
private theorem contact35ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact35) 120 8 = 7955556160190 :=
  combineSlices (auxiliaryColumnSlice contact35) 120 4 4 4146945540940 3808610619250 contact35ColumnsSlice120 contact35ColumnsSlice124
private theorem contact35ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact35) 128 8 = 6661438886639 :=
  combineSlices (auxiliaryColumnSlice contact35) 128 4 4 3485074348702 3176364537937 contact35ColumnsSlice128 contact35ColumnsSlice132
private theorem contact35ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact35) 136 8 = 5485966142654 :=
  combineSlices (auxiliaryColumnSlice contact35) 136 4 4 2882510356222 2603455786432 contact35ColumnsSlice136 contact35ColumnsSlice140
private theorem contact35ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact35) 144 8 = 4428930109751 :=
  combineSlices (auxiliaryColumnSlice contact35) 144 4 4 2339195664127 2089734445624 contact35ColumnsSlice144 contact35ColumnsSlice148
private theorem contact35ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact35) 152 8 = 3490435368420 :=
  combineSlices (auxiliaryColumnSlice contact35) 152 4 4 1855106482847 1635328885573 contact35ColumnsSlice152 contact35ColumnsSlice156
private theorem contact35ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact35) 160 8 = 2670512806978 :=
  combineSlices (auxiliaryColumnSlice contact35) 160 4 4 1430349036643 1240163770335 contact35ColumnsSlice160 contact35ColumnsSlice164
private theorem contact35ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact35) 168 8 = 1969010835036 :=
  combineSlices (auxiliaryColumnSlice contact35) 168 4 4 1064777776831 904233058205 contact35ColumnsSlice168 contact35ColumnsSlice172
private theorem contact35ColumnsJoin176_8 : sliceWindow (auxiliaryColumnSlice contact35) 176 8 = 1386153403085 :=
  combineSlices (auxiliaryColumnSlice contact35) 176 4 4 758530372128 627623030957 contact35ColumnsSlice176 contact35ColumnsSlice180
private theorem contact35ColumnsJoin184_8 : sliceWindow (auxiliaryColumnSlice contact35) 184 8 = 921165077301 :=
  combineSlices (auxiliaryColumnSlice contact35) 184 4 4 511442590656 409722486645 contact35ColumnsSlice184 contact35ColumnsSlice188
private theorem contact35ColumnsJoin192_8 : sliceWindow (auxiliaryColumnSlice contact35) 192 8 = 569803985576 :=
  combineSlices (auxiliaryColumnSlice contact35) 192 4 4 322042723676 247761261900 contact35ColumnsSlice192 contact35ColumnsSlice196
private theorem contact35ColumnsJoin200_8 : sliceWindow (auxiliaryColumnSlice contact35) 200 8 = 322028732036 :=
  combineSlices (auxiliaryColumnSlice contact35) 200 4 4 186054771796 135973960240 contact35ColumnsSlice200 contact35ColumnsSlice204
private theorem contact35ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact35) 0 16 = 80100944374804 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 8 8 41585934478376 38515009896428 contact35ColumnsJoin0_8 contact35ColumnsJoin8_8
private theorem contact35ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact35) 16 16 = 68290314357143 :=
  combineSlices (auxiliaryColumnSlice contact35) 16 8 8 35562351091944 32727963265199 contact35ColumnsJoin16_8 contact35ColumnsJoin24_8
private theorem contact35ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact35) 32 16 = 57426380578724 :=
  combineSlices (auxiliaryColumnSlice contact35) 32 8 8 30011933948510 27414446630214 contact35ColumnsJoin32_8 contact35ColumnsJoin40_8
private theorem contact35ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact35) 48 16 = 47509975091403 :=
  combineSlices (auxiliaryColumnSlice contact35) 48 8 8 24935290301854 22574684789549 contact35ColumnsJoin48_8 contact35ColumnsJoin56_8
private theorem contact35ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact35) 64 16 = 38541308006404 :=
  combineSlices (auxiliaryColumnSlice contact35) 64 8 8 20332515117917 18208792888487 contact35ColumnsJoin64_8 contact35ColumnsJoin72_8
private theorem contact35ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact35) 80 16 = 30520598982607 :=
  combineSlices (auxiliaryColumnSlice contact35) 80 8 8 16203664284416 14316934698191 contact35ColumnsJoin80_8 contact35ColumnsJoin88_8
private theorem contact35ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact35) 96 16 = 23448047069946 :=
  combineSlices (auxiliaryColumnSlice contact35) 96 8 8 12548841227969 10899205841977 contact35ColumnsJoin96_8 contact35ColumnsJoin104_8
private theorem contact35ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact35) 112 16 = 17323637562189 :=
  combineSlices (auxiliaryColumnSlice contact35) 112 8 8 9368081401999 7955556160190 contact35ColumnsJoin112_8 contact35ColumnsJoin120_8
private theorem contact35ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact35) 128 16 = 12147405029293 :=
  combineSlices (auxiliaryColumnSlice contact35) 128 8 8 6661438886639 5485966142654 contact35ColumnsJoin128_8 contact35ColumnsJoin136_8
private theorem contact35ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact35) 144 16 = 7919365478171 :=
  combineSlices (auxiliaryColumnSlice contact35) 144 8 8 4428930109751 3490435368420 contact35ColumnsJoin144_8 contact35ColumnsJoin152_8
private theorem contact35ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact35) 160 16 = 4639523642014 :=
  combineSlices (auxiliaryColumnSlice contact35) 160 8 8 2670512806978 1969010835036 contact35ColumnsJoin160_8 contact35ColumnsJoin168_8
private theorem contact35ColumnsJoin176_16 : sliceWindow (auxiliaryColumnSlice contact35) 176 16 = 2307318480386 :=
  combineSlices (auxiliaryColumnSlice contact35) 176 8 8 1386153403085 921165077301 contact35ColumnsJoin176_8 contact35ColumnsJoin184_8
private theorem contact35ColumnsJoin192_16 : sliceWindow (auxiliaryColumnSlice contact35) 192 16 = 891832717612 :=
  combineSlices (auxiliaryColumnSlice contact35) 192 8 8 569803985576 322028732036 contact35ColumnsJoin192_8 contact35ColumnsJoin200_8
private theorem contact35ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact35) 0 32 = 148391258731947 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 16 16 80100944374804 68290314357143 contact35ColumnsJoin0_16 contact35ColumnsJoin16_16
private theorem contact35ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact35) 32 32 = 104936355670127 :=
  combineSlices (auxiliaryColumnSlice contact35) 32 16 16 57426380578724 47509975091403 contact35ColumnsJoin32_16 contact35ColumnsJoin48_16
private theorem contact35ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact35) 64 32 = 69061906989011 :=
  combineSlices (auxiliaryColumnSlice contact35) 64 16 16 38541308006404 30520598982607 contact35ColumnsJoin64_16 contact35ColumnsJoin80_16
private theorem contact35ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact35) 96 32 = 40771684632135 :=
  combineSlices (auxiliaryColumnSlice contact35) 96 16 16 23448047069946 17323637562189 contact35ColumnsJoin96_16 contact35ColumnsJoin112_16
private theorem contact35ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact35) 128 32 = 20066770507464 :=
  combineSlices (auxiliaryColumnSlice contact35) 128 16 16 12147405029293 7919365478171 contact35ColumnsJoin128_16 contact35ColumnsJoin144_16
private theorem contact35ColumnsJoin160_32 : sliceWindow (auxiliaryColumnSlice contact35) 160 32 = 6946842122400 :=
  combineSlices (auxiliaryColumnSlice contact35) 160 16 16 4639523642014 2307318480386 contact35ColumnsJoin160_16 contact35ColumnsJoin176_16
private theorem contact35ColumnsJoin192_20 : sliceWindow (auxiliaryColumnSlice contact35) 192 20 = 988244878118 :=
  combineSlices (auxiliaryColumnSlice contact35) 192 16 4 891832717612 96412160506 contact35ColumnsJoin192_16 contact35ColumnsSlice208
private theorem contact35ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact35) 0 64 = 253327614402074 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 32 32 148391258731947 104936355670127 contact35ColumnsJoin0_32 contact35ColumnsJoin32_32
private theorem contact35ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact35) 64 64 = 109833591621146 :=
  combineSlices (auxiliaryColumnSlice contact35) 64 32 32 69061906989011 40771684632135 contact35ColumnsJoin64_32 contact35ColumnsJoin96_32
private theorem contact35ColumnsJoin128_64 : sliceWindow (auxiliaryColumnSlice contact35) 128 64 = 27013612629864 :=
  combineSlices (auxiliaryColumnSlice contact35) 128 32 32 20066770507464 6946842122400 contact35ColumnsJoin128_32 contact35ColumnsJoin160_32
private theorem contact35ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact35) 0 128 = 363161206023220 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 64 64 253327614402074 109833591621146 contact35ColumnsJoin0_64 contact35ColumnsJoin64_64
private theorem contact35ColumnsJoin128_84 : sliceWindow (auxiliaryColumnSlice contact35) 128 84 = 28001857507982 :=
  combineSlices (auxiliaryColumnSlice contact35) 128 64 20 27013612629864 988244878118 contact35ColumnsJoin128_64 contact35ColumnsJoin192_20
private theorem contact35ColumnsJoin0_212 : sliceWindow (auxiliaryColumnSlice contact35) 0 212 = 391163063531202 :=
  combineSlices (auxiliaryColumnSlice contact35) 0 128 84 363161206023220 28001857507982 contact35ColumnsJoin0_128 contact35ColumnsJoin128_84
private theorem contact35OrdinaryRanks : ordinaryRankBound contact35 = 25916359093 := by decide +kernel
private theorem contact35RanksSlice0 : sliceWindow (auxiliaryRankSlice contact35) 0 4 = 79978224 :=
  contactRankWindow_of_rec contact35 0 4 79978224 (by decide +kernel)
private theorem contact35RanksSlice4 : sliceWindow (auxiliaryRankSlice contact35) 4 4 = 76115040 :=
  contactRankWindow_of_rec contact35 4 4 76115040 (by decide +kernel)
private theorem contact35RanksSlice8 : sliceWindow (auxiliaryRankSlice contact35) 8 4 = 72354192 :=
  contactRankWindow_of_rec contact35 8 4 72354192 (by decide +kernel)
private theorem contact35RanksSlice12 : sliceWindow (auxiliaryRankSlice contact35) 12 4 = 68695680 :=
  contactRankWindow_of_rec contact35 12 4 68695680 (by decide +kernel)
private theorem contact35RanksSlice16 : sliceWindow (auxiliaryRankSlice contact35) 16 4 = 65139504 :=
  contactRankWindow_of_rec contact35 16 4 65139504 (by decide +kernel)
private theorem contact35RanksSlice20 : sliceWindow (auxiliaryRankSlice contact35) 20 4 = 61685664 :=
  contactRankWindow_of_rec contact35 20 4 61685664 (by decide +kernel)
private theorem contact35RanksSlice24 : sliceWindow (auxiliaryRankSlice contact35) 24 4 = 58334160 :=
  contactRankWindow_of_rec contact35 24 4 58334160 (by decide +kernel)
private theorem contact35RanksSlice28 : sliceWindow (auxiliaryRankSlice contact35) 28 4 = 55084992 :=
  contactRankWindow_of_rec contact35 28 4 55084992 (by decide +kernel)
private theorem contact35RanksSlice32 : sliceWindow (auxiliaryRankSlice contact35) 32 4 = 51938160 :=
  contactRankWindow_of_rec contact35 32 4 51938160 (by decide +kernel)
private theorem contact35RanksSlice36 : sliceWindow (auxiliaryRankSlice contact35) 36 4 = 48893664 :=
  contactRankWindow_of_rec contact35 36 4 48893664 (by decide +kernel)
private theorem contact35RanksSlice40 : sliceWindow (auxiliaryRankSlice contact35) 40 4 = 45951504 :=
  contactRankWindow_of_rec contact35 40 4 45951504 (by decide +kernel)
private theorem contact35RanksSlice44 : sliceWindow (auxiliaryRankSlice contact35) 44 4 = 43111680 :=
  contactRankWindow_of_rec contact35 44 4 43111680 (by decide +kernel)
private theorem contact35RanksSlice48 : sliceWindow (auxiliaryRankSlice contact35) 48 4 = 40374192 :=
  contactRankWindow_of_rec contact35 48 4 40374192 (by decide +kernel)
private theorem contact35RanksSlice52 : sliceWindow (auxiliaryRankSlice contact35) 52 4 = 37739040 :=
  contactRankWindow_of_rec contact35 52 4 37739040 (by decide +kernel)
private theorem contact35RanksSlice56 : sliceWindow (auxiliaryRankSlice contact35) 56 4 = 35206224 :=
  contactRankWindow_of_rec contact35 56 4 35206224 (by decide +kernel)
private theorem contact35RanksSlice60 : sliceWindow (auxiliaryRankSlice contact35) 60 4 = 32775744 :=
  contactRankWindow_of_rec contact35 60 4 32775744 (by decide +kernel)
private theorem contact35RanksSlice64 : sliceWindow (auxiliaryRankSlice contact35) 64 4 = 30447600 :=
  contactRankWindow_of_rec contact35 64 4 30447600 (by decide +kernel)
private theorem contact35RanksSlice68 : sliceWindow (auxiliaryRankSlice contact35) 68 4 = 28221792 :=
  contactRankWindow_of_rec contact35 68 4 28221792 (by decide +kernel)
private theorem contact35RanksSlice72 : sliceWindow (auxiliaryRankSlice contact35) 72 4 = 26098320 :=
  contactRankWindow_of_rec contact35 72 4 26098320 (by decide +kernel)
private theorem contact35RanksSlice76 : sliceWindow (auxiliaryRankSlice contact35) 76 4 = 24076910 :=
  contactRankWindow_of_rec contact35 76 4 24076910 (by decide +kernel)
private theorem contact35RanksSlice80 : sliceWindow (auxiliaryRankSlice contact35) 80 4 = 22156063 :=
  contactRankWindow_of_rec contact35 80 4 22156063 (by decide +kernel)
private theorem contact35RanksSlice84 : sliceWindow (auxiliaryRankSlice contact35) 84 4 = 20333619 :=
  contactRankWindow_of_rec contact35 84 4 20333619 (by decide +kernel)
private theorem contact35RanksSlice88 : sliceWindow (auxiliaryRankSlice contact35) 88 4 = 18607218 :=
  contactRankWindow_of_rec contact35 88 4 18607218 (by decide +kernel)
private theorem contact35RanksSlice92 : sliceWindow (auxiliaryRankSlice contact35) 92 4 = 16974747 :=
  contactRankWindow_of_rec contact35 92 4 16974747 (by decide +kernel)
private theorem contact35RanksSlice96 : sliceWindow (auxiliaryRankSlice contact35) 96 4 = 15433795 :=
  contactRankWindow_of_rec contact35 96 4 15433795 (by decide +kernel)
private theorem contact35RanksSlice100 : sliceWindow (auxiliaryRankSlice contact35) 100 4 = 13982006 :=
  contactRankWindow_of_rec contact35 100 4 13982006 (by decide +kernel)
private theorem contact35RanksSlice104 : sliceWindow (auxiliaryRankSlice contact35) 104 4 = 12617431 :=
  contactRankWindow_of_rec contact35 104 4 12617431 (by decide +kernel)
private theorem contact35RanksSlice108 : sliceWindow (auxiliaryRankSlice contact35) 108 4 = 11337491 :=
  contactRankWindow_of_rec contact35 108 4 11337491 (by decide +kernel)
private theorem contact35RanksSlice112 : sliceWindow (auxiliaryRankSlice contact35) 112 4 = 10139834 :=
  contactRankWindow_of_rec contact35 112 4 10139834 (by decide +kernel)
private theorem contact35RanksSlice116 : sliceWindow (auxiliaryRankSlice contact35) 116 4 = 9022675 :=
  contactRankWindow_of_rec contact35 116 4 9022675 (by decide +kernel)
private theorem contact35RanksSlice120 : sliceWindow (auxiliaryRankSlice contact35) 120 4 = 7983267 :=
  contactRankWindow_of_rec contact35 120 4 7983267 (by decide +kernel)
private theorem contact35RanksSlice124 : sliceWindow (auxiliaryRankSlice contact35) 124 4 = 7019262 :=
  contactRankWindow_of_rec contact35 124 4 7019262 (by decide +kernel)
private theorem contact35RanksSlice128 : sliceWindow (auxiliaryRankSlice contact35) 128 4 = 6129039 :=
  contactRankWindow_of_rec contact35 128 4 6129039 (by decide +kernel)
private theorem contact35RanksSlice132 : sliceWindow (auxiliaryRankSlice contact35) 132 4 = 5309683 :=
  contactRankWindow_of_rec contact35 132 4 5309683 (by decide +kernel)
private theorem contact35RanksSlice136 : sliceWindow (auxiliaryRankSlice contact35) 136 4 = 4558850 :=
  contactRankWindow_of_rec contact35 136 4 4558850 (by decide +kernel)
private theorem contact35RanksSlice140 : sliceWindow (auxiliaryRankSlice contact35) 140 4 = 3875083 :=
  contactRankWindow_of_rec contact35 140 4 3875083 (by decide +kernel)
private theorem contact35RanksSlice144 : sliceWindow (auxiliaryRankSlice contact35) 144 4 = 3255299 :=
  contactRankWindow_of_rec contact35 144 4 3255299 (by decide +kernel)
private theorem contact35RanksSlice148 : sliceWindow (auxiliaryRankSlice contact35) 148 4 = 2697158 :=
  contactRankWindow_of_rec contact35 148 4 2697158 (by decide +kernel)
private theorem contact35RanksSlice152 : sliceWindow (auxiliaryRankSlice contact35) 152 4 = 2199367 :=
  contactRankWindow_of_rec contact35 152 4 2199367 (by decide +kernel)
private theorem contact35RanksSlice156 : sliceWindow (auxiliaryRankSlice contact35) 156 4 = 1758675 :=
  contactRankWindow_of_rec contact35 156 4 1758675 (by decide +kernel)
private theorem contact35RanksSlice160 : sliceWindow (auxiliaryRankSlice contact35) 160 4 = 1372746 :=
  contactRankWindow_of_rec contact35 160 4 1372746 (by decide +kernel)
private theorem contact35RanksSlice164 : sliceWindow (auxiliaryRankSlice contact35) 164 4 = 1040451 :=
  contactRankWindow_of_rec contact35 164 4 1040451 (by decide +kernel)
private theorem contact35RanksSlice168 : sliceWindow (auxiliaryRankSlice contact35) 168 4 = 758371 :=
  contactRankWindow_of_rec contact35 168 4 758371 (by decide +kernel)
private theorem contact35RanksSlice172 : sliceWindow (auxiliaryRankSlice contact35) 172 4 = 524174 :=
  contactRankWindow_of_rec contact35 172 4 524174 (by decide +kernel)
private theorem contact35RanksSlice176 : sliceWindow (auxiliaryRankSlice contact35) 176 4 = 336895 :=
  contactRankWindow_of_rec contact35 176 4 336895 (by decide +kernel)
private theorem contact35RanksSlice180 : sliceWindow (auxiliaryRankSlice contact35) 180 4 = 192947 :=
  contactRankWindow_of_rec contact35 180 4 192947 (by decide +kernel)
private theorem contact35RanksSlice184 : sliceWindow (auxiliaryRankSlice contact35) 184 4 = 90017 :=
  contactRankWindow_of_rec contact35 184 4 90017 (by decide +kernel)
private theorem contact35RanksSlice188 : sliceWindow (auxiliaryRankSlice contact35) 188 4 = 27496 :=
  contactRankWindow_of_rec contact35 188 4 27496 (by decide +kernel)
private theorem contact35RanksSlice192 : sliceWindow (auxiliaryRankSlice contact35) 192 4 = 1563 :=
  contactRankWindow_of_rec contact35 192 4 1563 (by decide +kernel)
private theorem contact35RanksSlice196 : sliceWindow (auxiliaryRankSlice contact35) 196 16 = 0 :=
  contactRankWindow_of_rec contact35 196 16 0 (by decide +kernel)
private theorem contact35RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact35) 0 8 = 156093264 :=
  combineSlices (auxiliaryRankSlice contact35) 0 4 4 79978224 76115040 contact35RanksSlice0 contact35RanksSlice4
private theorem contact35RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact35) 8 8 = 141049872 :=
  combineSlices (auxiliaryRankSlice contact35) 8 4 4 72354192 68695680 contact35RanksSlice8 contact35RanksSlice12
private theorem contact35RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact35) 16 8 = 126825168 :=
  combineSlices (auxiliaryRankSlice contact35) 16 4 4 65139504 61685664 contact35RanksSlice16 contact35RanksSlice20
private theorem contact35RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact35) 24 8 = 113419152 :=
  combineSlices (auxiliaryRankSlice contact35) 24 4 4 58334160 55084992 contact35RanksSlice24 contact35RanksSlice28
private theorem contact35RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact35) 32 8 = 100831824 :=
  combineSlices (auxiliaryRankSlice contact35) 32 4 4 51938160 48893664 contact35RanksSlice32 contact35RanksSlice36
private theorem contact35RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact35) 40 8 = 89063184 :=
  combineSlices (auxiliaryRankSlice contact35) 40 4 4 45951504 43111680 contact35RanksSlice40 contact35RanksSlice44
private theorem contact35RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact35) 48 8 = 78113232 :=
  combineSlices (auxiliaryRankSlice contact35) 48 4 4 40374192 37739040 contact35RanksSlice48 contact35RanksSlice52
private theorem contact35RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact35) 56 8 = 67981968 :=
  combineSlices (auxiliaryRankSlice contact35) 56 4 4 35206224 32775744 contact35RanksSlice56 contact35RanksSlice60
private theorem contact35RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact35) 64 8 = 58669392 :=
  combineSlices (auxiliaryRankSlice contact35) 64 4 4 30447600 28221792 contact35RanksSlice64 contact35RanksSlice68
private theorem contact35RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact35) 72 8 = 50175230 :=
  combineSlices (auxiliaryRankSlice contact35) 72 4 4 26098320 24076910 contact35RanksSlice72 contact35RanksSlice76
private theorem contact35RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact35) 80 8 = 42489682 :=
  combineSlices (auxiliaryRankSlice contact35) 80 4 4 22156063 20333619 contact35RanksSlice80 contact35RanksSlice84
private theorem contact35RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact35) 88 8 = 35581965 :=
  combineSlices (auxiliaryRankSlice contact35) 88 4 4 18607218 16974747 contact35RanksSlice88 contact35RanksSlice92
private theorem contact35RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact35) 96 8 = 29415801 :=
  combineSlices (auxiliaryRankSlice contact35) 96 4 4 15433795 13982006 contact35RanksSlice96 contact35RanksSlice100
private theorem contact35RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact35) 104 8 = 23954922 :=
  combineSlices (auxiliaryRankSlice contact35) 104 4 4 12617431 11337491 contact35RanksSlice104 contact35RanksSlice108
private theorem contact35RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact35) 112 8 = 19162509 :=
  combineSlices (auxiliaryRankSlice contact35) 112 4 4 10139834 9022675 contact35RanksSlice112 contact35RanksSlice116
private theorem contact35RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact35) 120 8 = 15002529 :=
  combineSlices (auxiliaryRankSlice contact35) 120 4 4 7983267 7019262 contact35RanksSlice120 contact35RanksSlice124
private theorem contact35RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact35) 128 8 = 11438722 :=
  combineSlices (auxiliaryRankSlice contact35) 128 4 4 6129039 5309683 contact35RanksSlice128 contact35RanksSlice132
private theorem contact35RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact35) 136 8 = 8433933 :=
  combineSlices (auxiliaryRankSlice contact35) 136 4 4 4558850 3875083 contact35RanksSlice136 contact35RanksSlice140
private theorem contact35RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact35) 144 8 = 5952457 :=
  combineSlices (auxiliaryRankSlice contact35) 144 4 4 3255299 2697158 contact35RanksSlice144 contact35RanksSlice148
private theorem contact35RanksJoin152_8 : sliceWindow (auxiliaryRankSlice contact35) 152 8 = 3958042 :=
  combineSlices (auxiliaryRankSlice contact35) 152 4 4 2199367 1758675 contact35RanksSlice152 contact35RanksSlice156
private theorem contact35RanksJoin160_8 : sliceWindow (auxiliaryRankSlice contact35) 160 8 = 2413197 :=
  combineSlices (auxiliaryRankSlice contact35) 160 4 4 1372746 1040451 contact35RanksSlice160 contact35RanksSlice164
private theorem contact35RanksJoin168_8 : sliceWindow (auxiliaryRankSlice contact35) 168 8 = 1282545 :=
  combineSlices (auxiliaryRankSlice contact35) 168 4 4 758371 524174 contact35RanksSlice168 contact35RanksSlice172
private theorem contact35RanksJoin176_8 : sliceWindow (auxiliaryRankSlice contact35) 176 8 = 529842 :=
  combineSlices (auxiliaryRankSlice contact35) 176 4 4 336895 192947 contact35RanksSlice176 contact35RanksSlice180
private theorem contact35RanksJoin184_8 : sliceWindow (auxiliaryRankSlice contact35) 184 8 = 117513 :=
  combineSlices (auxiliaryRankSlice contact35) 184 4 4 90017 27496 contact35RanksSlice184 contact35RanksSlice188
private theorem contact35RanksJoin192_20 : sliceWindow (auxiliaryRankSlice contact35) 192 20 = 1563 :=
  combineSlices (auxiliaryRankSlice contact35) 192 4 16 1563 0 contact35RanksSlice192 contact35RanksSlice196
private theorem contact35RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact35) 0 16 = 297143136 :=
  combineSlices (auxiliaryRankSlice contact35) 0 8 8 156093264 141049872 contact35RanksJoin0_8 contact35RanksJoin8_8
private theorem contact35RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact35) 16 16 = 240244320 :=
  combineSlices (auxiliaryRankSlice contact35) 16 8 8 126825168 113419152 contact35RanksJoin16_8 contact35RanksJoin24_8
private theorem contact35RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact35) 32 16 = 189895008 :=
  combineSlices (auxiliaryRankSlice contact35) 32 8 8 100831824 89063184 contact35RanksJoin32_8 contact35RanksJoin40_8
private theorem contact35RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact35) 48 16 = 146095200 :=
  combineSlices (auxiliaryRankSlice contact35) 48 8 8 78113232 67981968 contact35RanksJoin48_8 contact35RanksJoin56_8
private theorem contact35RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact35) 64 16 = 108844622 :=
  combineSlices (auxiliaryRankSlice contact35) 64 8 8 58669392 50175230 contact35RanksJoin64_8 contact35RanksJoin72_8
private theorem contact35RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact35) 80 16 = 78071647 :=
  combineSlices (auxiliaryRankSlice contact35) 80 8 8 42489682 35581965 contact35RanksJoin80_8 contact35RanksJoin88_8
private theorem contact35RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact35) 96 16 = 53370723 :=
  combineSlices (auxiliaryRankSlice contact35) 96 8 8 29415801 23954922 contact35RanksJoin96_8 contact35RanksJoin104_8
private theorem contact35RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact35) 112 16 = 34165038 :=
  combineSlices (auxiliaryRankSlice contact35) 112 8 8 19162509 15002529 contact35RanksJoin112_8 contact35RanksJoin120_8
private theorem contact35RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact35) 128 16 = 19872655 :=
  combineSlices (auxiliaryRankSlice contact35) 128 8 8 11438722 8433933 contact35RanksJoin128_8 contact35RanksJoin136_8
private theorem contact35RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact35) 144 16 = 9910499 :=
  combineSlices (auxiliaryRankSlice contact35) 144 8 8 5952457 3958042 contact35RanksJoin144_8 contact35RanksJoin152_8
private theorem contact35RanksJoin160_16 : sliceWindow (auxiliaryRankSlice contact35) 160 16 = 3695742 :=
  combineSlices (auxiliaryRankSlice contact35) 160 8 8 2413197 1282545 contact35RanksJoin160_8 contact35RanksJoin168_8
private theorem contact35RanksJoin176_16 : sliceWindow (auxiliaryRankSlice contact35) 176 16 = 647355 :=
  combineSlices (auxiliaryRankSlice contact35) 176 8 8 529842 117513 contact35RanksJoin176_8 contact35RanksJoin184_8
private theorem contact35RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact35) 0 32 = 537387456 :=
  combineSlices (auxiliaryRankSlice contact35) 0 16 16 297143136 240244320 contact35RanksJoin0_16 contact35RanksJoin16_16
private theorem contact35RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact35) 32 32 = 335990208 :=
  combineSlices (auxiliaryRankSlice contact35) 32 16 16 189895008 146095200 contact35RanksJoin32_16 contact35RanksJoin48_16
private theorem contact35RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact35) 64 32 = 186916269 :=
  combineSlices (auxiliaryRankSlice contact35) 64 16 16 108844622 78071647 contact35RanksJoin64_16 contact35RanksJoin80_16
private theorem contact35RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact35) 96 32 = 87535761 :=
  combineSlices (auxiliaryRankSlice contact35) 96 16 16 53370723 34165038 contact35RanksJoin96_16 contact35RanksJoin112_16
private theorem contact35RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact35) 128 32 = 29783154 :=
  combineSlices (auxiliaryRankSlice contact35) 128 16 16 19872655 9910499 contact35RanksJoin128_16 contact35RanksJoin144_16
private theorem contact35RanksJoin160_32 : sliceWindow (auxiliaryRankSlice contact35) 160 32 = 4343097 :=
  combineSlices (auxiliaryRankSlice contact35) 160 16 16 3695742 647355 contact35RanksJoin160_16 contact35RanksJoin176_16
private theorem contact35RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact35) 0 64 = 873377664 :=
  combineSlices (auxiliaryRankSlice contact35) 0 32 32 537387456 335990208 contact35RanksJoin0_32 contact35RanksJoin32_32
private theorem contact35RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact35) 64 64 = 274452030 :=
  combineSlices (auxiliaryRankSlice contact35) 64 32 32 186916269 87535761 contact35RanksJoin64_32 contact35RanksJoin96_32
private theorem contact35RanksJoin128_64 : sliceWindow (auxiliaryRankSlice contact35) 128 64 = 34126251 :=
  combineSlices (auxiliaryRankSlice contact35) 128 32 32 29783154 4343097 contact35RanksJoin128_32 contact35RanksJoin160_32
private theorem contact35RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact35) 0 128 = 1147829694 :=
  combineSlices (auxiliaryRankSlice contact35) 0 64 64 873377664 274452030 contact35RanksJoin0_64 contact35RanksJoin64_64
private theorem contact35RanksJoin128_84 : sliceWindow (auxiliaryRankSlice contact35) 128 84 = 34127814 :=
  combineSlices (auxiliaryRankSlice contact35) 128 64 20 34126251 1563 contact35RanksJoin128_64 contact35RanksJoin192_20
private theorem contact35RanksJoin0_212 : sliceWindow (auxiliaryRankSlice contact35) 0 212 = 1181957508 :=
  combineSlices (auxiliaryRankSlice contact35) 0 128 84 1147829694 34127814 contact35RanksJoin0_128 contact35RanksJoin128_84
theorem contact35_margin : sourceMargin contact35 :=
  margin_of_checked_counts contact35 212 6712498102238338 391163063531202 25916359093 1181957508 rfl contact35OrdinaryColumns contact35ColumnsJoin0_212 contact35OrdinaryRanks contact35RanksJoin0_212 (by decide +kernel)

private theorem contact37OrdinaryColumns : ordinaryColumnCount contact37 = 8949733668999943 := by decide +kernel
private theorem contact37ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact37) 0 4 = 28390100354176 :=
  contactColumnsWindow_fast contact37 0 4 28390100354176 (by decide +kernel)
private theorem contact37ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact37) 4 4 = 27382832335936 :=
  contactColumnsWindow_fast contact37 4 4 27382832335936 (by decide +kernel)
private theorem contact37ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact37) 8 4 = 26393848126848 :=
  contactColumnsWindow_fast contact37 8 4 26393848126848 (by decide +kernel)
private theorem contact37ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact37) 12 4 = 25423147726912 :=
  contactColumnsWindow_fast contact37 12 4 25423147726912 (by decide +kernel)
private theorem contact37ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact37) 16 4 = 24470731136128 :=
  contactColumnsWindow_fast contact37 16 4 24470731136128 (by decide +kernel)
private theorem contact37ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact37) 20 4 = 23536598354496 :=
  contactColumnsWindow_fast contact37 20 4 23536598354496 (by decide +kernel)
private theorem contact37ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact37) 24 4 = 22620749382016 :=
  contactColumnsWindow_fast contact37 24 4 22620749382016 (by decide +kernel)
private theorem contact37ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact37) 28 4 = 21723184218688 :=
  contactColumnsWindow_fast contact37 28 4 21723184218688 (by decide +kernel)
private theorem contact37ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact37) 32 4 = 20843902864512 :=
  contactColumnsWindow_fast contact37 32 4 20843902864512 (by decide +kernel)
private theorem contact37ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact37) 36 4 = 19982905319488 :=
  contactColumnsWindow_fast contact37 36 4 19982905319488 (by decide +kernel)
private theorem contact37ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact37) 40 4 = 19140191583616 :=
  contactColumnsWindow_fast contact37 40 4 19140191583616 (by decide +kernel)
private theorem contact37ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact37) 44 4 = 18315761656896 :=
  contactColumnsWindow_fast contact37 44 4 18315761656896 (by decide +kernel)
private theorem contact37ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact37) 48 4 = 17509615539328 :=
  contactColumnsWindow_fast contact37 48 4 17509615539328 (by decide +kernel)
private theorem contact37ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact37) 52 4 = 16721753230912 :=
  contactColumnsWindow_fast contact37 52 4 16721753230912 (by decide +kernel)
private theorem contact37ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact37) 56 4 = 15952174731648 :=
  contactColumnsWindow_fast contact37 56 4 15952174731648 (by decide +kernel)
private theorem contact37ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact37) 60 4 = 15200887269001 :=
  contactColumnsWindow_fast contact37 60 4 15200887269001 (by decide +kernel)
private theorem contact37ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact37) 64 4 = 14467982104836 :=
  contactColumnsWindow_fast contact37 64 4 14467982104836 (by decide +kernel)
private theorem contact37ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact37) 68 4 = 13753390347676 :=
  contactColumnsWindow_fast contact37 68 4 13753390347676 (by decide +kernel)
private theorem contact37ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact37) 72 4 = 13057088171188 :=
  contactColumnsWindow_fast contact37 72 4 13057088171188 (by decide +kernel)
private theorem contact37ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact37) 76 4 = 12379072277414 :=
  contactColumnsWindow_fast contact37 76 4 12379072277414 (by decide +kernel)
private theorem contact37ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact37) 80 4 = 11719358539086 :=
  contactColumnsWindow_fast contact37 80 4 11719358539086 (by decide +kernel)
private theorem contact37ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact37) 84 4 = 11078032238834 :=
  contactColumnsWindow_fast contact37 84 4 11078032238834 (by decide +kernel)
private theorem contact37ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact37) 88 4 = 10455017798548 :=
  contactColumnsWindow_fast contact37 88 4 10455017798548 (by decide +kernel)
private theorem contact37ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact37) 92 4 = 9850296323905 :=
  contactColumnsWindow_fast contact37 92 4 9850296323905 (by decide +kernel)
private theorem contact37ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact37) 96 4 = 9263866513977 :=
  contactColumnsWindow_fast contact37 96 4 9263866513977 (by decide +kernel)
private theorem contact37ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact37) 100 4 = 8695749247854 :=
  contactColumnsWindow_fast contact37 100 4 8695749247854 (by decide +kernel)
private theorem contact37ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact37) 104 4 = 8146024031447 :=
  contactColumnsWindow_fast contact37 104 4 8146024031447 (by decide +kernel)
private theorem contact37ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact37) 108 4 = 7614609900088 :=
  contactColumnsWindow_fast contact37 108 4 7614609900088 (by decide +kernel)
private theorem contact37ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact37) 112 4 = 7101492708142 :=
  contactColumnsWindow_fast contact37 112 4 7101492708142 (by decide +kernel)
private theorem contact37ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact37) 116 4 = 6606672940479 :=
  contactColumnsWindow_fast contact37 116 4 6606672940479 (by decide +kernel)
private theorem contact37ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact37) 120 4 = 6130175600367 :=
  contactColumnsWindow_fast contact37 120 4 6130175600367 (by decide +kernel)
private theorem contact37ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact37) 124 4 = 5672077099011 :=
  contactColumnsWindow_fast contact37 124 4 5672077099011 (by decide +kernel)
private theorem contact37ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact37) 128 4 = 5232286618804 :=
  contactColumnsWindow_fast contact37 128 4 5232286618804 (by decide +kernel)
private theorem contact37ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact37) 132 4 = 4810800064006 :=
  contactColumnsWindow_fast contact37 132 4 4810800064006 (by decide +kernel)
private theorem contact37ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact37) 136 4 = 4407612128552 :=
  contactColumnsWindow_fast contact37 136 4 4407612128552 (by decide +kernel)
private theorem contact37ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact37) 140 4 = 4022756004053 :=
  contactColumnsWindow_fast contact37 140 4 4022756004053 (by decide +kernel)
private theorem contact37ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact37) 144 4 = 3656292585345 :=
  contactColumnsWindow_fast contact37 144 4 3656292585345 (by decide +kernel)
private theorem contact37ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact37) 148 4 = 3308134254269 :=
  contactColumnsWindow_fast contact37 148 4 3308134254269 (by decide +kernel)
private theorem contact37ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact37) 152 4 = 2978279893300 :=
  contactColumnsWindow_fast contact37 152 4 2978279893300 (by decide +kernel)
private theorem contact37ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact37) 156 4 = 2666723808476 :=
  contactColumnsWindow_fast contact37 156 4 2666723808476 (by decide +kernel)
private theorem contact37ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact37) 160 4 = 2373508724771 :=
  contactColumnsWindow_fast contact37 160 4 2373508724771 (by decide +kernel)
private theorem contact37ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact37) 164 4 = 2098680456570 :=
  contactColumnsWindow_fast contact37 164 4 2098680456570 (by decide +kernel)
private theorem contact37ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact37) 168 4 = 1842154647611 :=
  contactColumnsWindow_fast contact37 168 4 1842154647611 (by decide +kernel)
private theorem contact37ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact37) 172 4 = 1603932024496 :=
  contactColumnsWindow_fast contact37 172 4 1603932024496 (by decide +kernel)
private theorem contact37ColumnsSlice176 : sliceWindow (auxiliaryColumnSlice contact37) 176 4 = 1384007788848 :=
  contactColumnsWindow_fast contact37 176 4 1384007788848 (by decide +kernel)
private theorem contact37ColumnsSlice180 : sliceWindow (auxiliaryColumnSlice contact37) 180 4 = 1182435155977 :=
  contactColumnsWindow_fast contact37 180 4 1182435155977 (by decide +kernel)
private theorem contact37ColumnsSlice184 : sliceWindow (auxiliaryColumnSlice contact37) 184 4 = 999239703819 :=
  contactColumnsWindow_fast contact37 184 4 999239703819 (by decide +kernel)
private theorem contact37ColumnsSlice188 : sliceWindow (auxiliaryColumnSlice contact37) 188 4 = 834296728387 :=
  contactColumnsWindow_fast contact37 188 4 834296728387 (by decide +kernel)
private theorem contact37ColumnsSlice192 : sliceWindow (auxiliaryColumnSlice contact37) 192 4 = 687372797465 :=
  contactColumnsWindow_fast contact37 192 4 687372797465 (by decide +kernel)
private theorem contact37ColumnsSlice196 : sliceWindow (auxiliaryColumnSlice contact37) 196 4 = 558019313089 :=
  contactColumnsWindow_fast contact37 196 4 558019313089 (by decide +kernel)
private theorem contact37ColumnsSlice200 : sliceWindow (auxiliaryColumnSlice contact37) 200 4 = 445685552704 :=
  contactColumnsWindow_fast contact37 200 4 445685552704 (by decide +kernel)
private theorem contact37ColumnsSlice204 : sliceWindow (auxiliaryColumnSlice contact37) 204 4 = 349590356097 :=
  contactColumnsWindow_fast contact37 204 4 349590356097 (by decide +kernel)
private theorem contact37ColumnsSlice208 : sliceWindow (auxiliaryColumnSlice contact37) 208 4 = 268731078065 :=
  contactColumnsWindow_fast contact37 208 4 268731078065 (by decide +kernel)
private theorem contact37ColumnsSlice212 : sliceWindow (auxiliaryColumnSlice contact37) 212 4 = 202005361070 :=
  contactColumnsWindow_fast contact37 212 4 202005361070 (by decide +kernel)
private theorem contact37ColumnsSlice216 : sliceWindow (auxiliaryColumnSlice contact37) 216 4 = 148147284708 :=
  contactColumnsWindow_fast contact37 216 4 148147284708 (by decide +kernel)
private theorem contact37ColumnsSlice220 : sliceWindow (auxiliaryColumnSlice contact37) 220 2 = 57525581762 :=
  contactColumnsWindow_fast contact37 220 2 57525581762 (by decide +kernel)
private theorem contact37ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact37) 0 8 = 55772932690112 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 4 4 28390100354176 27382832335936 contact37ColumnsSlice0 contact37ColumnsSlice4
private theorem contact37ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact37) 8 8 = 51816995853760 :=
  combineSlices (auxiliaryColumnSlice contact37) 8 4 4 26393848126848 25423147726912 contact37ColumnsSlice8 contact37ColumnsSlice12
private theorem contact37ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact37) 16 8 = 48007329490624 :=
  combineSlices (auxiliaryColumnSlice contact37) 16 4 4 24470731136128 23536598354496 contact37ColumnsSlice16 contact37ColumnsSlice20
private theorem contact37ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact37) 24 8 = 44343933600704 :=
  combineSlices (auxiliaryColumnSlice contact37) 24 4 4 22620749382016 21723184218688 contact37ColumnsSlice24 contact37ColumnsSlice28
private theorem contact37ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact37) 32 8 = 40826808184000 :=
  combineSlices (auxiliaryColumnSlice contact37) 32 4 4 20843902864512 19982905319488 contact37ColumnsSlice32 contact37ColumnsSlice36
private theorem contact37ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact37) 40 8 = 37455953240512 :=
  combineSlices (auxiliaryColumnSlice contact37) 40 4 4 19140191583616 18315761656896 contact37ColumnsSlice40 contact37ColumnsSlice44
private theorem contact37ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact37) 48 8 = 34231368770240 :=
  combineSlices (auxiliaryColumnSlice contact37) 48 4 4 17509615539328 16721753230912 contact37ColumnsSlice48 contact37ColumnsSlice52
private theorem contact37ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact37) 56 8 = 31153062000649 :=
  combineSlices (auxiliaryColumnSlice contact37) 56 4 4 15952174731648 15200887269001 contact37ColumnsSlice56 contact37ColumnsSlice60
private theorem contact37ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact37) 64 8 = 28221372452512 :=
  combineSlices (auxiliaryColumnSlice contact37) 64 4 4 14467982104836 13753390347676 contact37ColumnsSlice64 contact37ColumnsSlice68
private theorem contact37ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact37) 72 8 = 25436160448602 :=
  combineSlices (auxiliaryColumnSlice contact37) 72 4 4 13057088171188 12379072277414 contact37ColumnsSlice72 contact37ColumnsSlice76
private theorem contact37ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact37) 80 8 = 22797390777920 :=
  combineSlices (auxiliaryColumnSlice contact37) 80 4 4 11719358539086 11078032238834 contact37ColumnsSlice80 contact37ColumnsSlice84
private theorem contact37ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact37) 88 8 = 20305314122453 :=
  combineSlices (auxiliaryColumnSlice contact37) 88 4 4 10455017798548 9850296323905 contact37ColumnsSlice88 contact37ColumnsSlice92
private theorem contact37ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact37) 96 8 = 17959615761831 :=
  combineSlices (auxiliaryColumnSlice contact37) 96 4 4 9263866513977 8695749247854 contact37ColumnsSlice96 contact37ColumnsSlice100
private theorem contact37ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact37) 104 8 = 15760633931535 :=
  combineSlices (auxiliaryColumnSlice contact37) 104 4 4 8146024031447 7614609900088 contact37ColumnsSlice104 contact37ColumnsSlice108
private theorem contact37ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact37) 112 8 = 13708165648621 :=
  combineSlices (auxiliaryColumnSlice contact37) 112 4 4 7101492708142 6606672940479 contact37ColumnsSlice112 contact37ColumnsSlice116
private theorem contact37ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact37) 120 8 = 11802252699378 :=
  combineSlices (auxiliaryColumnSlice contact37) 120 4 4 6130175600367 5672077099011 contact37ColumnsSlice120 contact37ColumnsSlice124
private theorem contact37ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact37) 128 8 = 10043086682810 :=
  combineSlices (auxiliaryColumnSlice contact37) 128 4 4 5232286618804 4810800064006 contact37ColumnsSlice128 contact37ColumnsSlice132
private theorem contact37ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact37) 136 8 = 8430368132605 :=
  combineSlices (auxiliaryColumnSlice contact37) 136 4 4 4407612128552 4022756004053 contact37ColumnsSlice136 contact37ColumnsSlice140
private theorem contact37ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact37) 144 8 = 6964426839614 :=
  combineSlices (auxiliaryColumnSlice contact37) 144 4 4 3656292585345 3308134254269 contact37ColumnsSlice144 contact37ColumnsSlice148
private theorem contact37ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact37) 152 8 = 5645003701776 :=
  combineSlices (auxiliaryColumnSlice contact37) 152 4 4 2978279893300 2666723808476 contact37ColumnsSlice152 contact37ColumnsSlice156
private theorem contact37ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact37) 160 8 = 4472189181341 :=
  combineSlices (auxiliaryColumnSlice contact37) 160 4 4 2373508724771 2098680456570 contact37ColumnsSlice160 contact37ColumnsSlice164
private theorem contact37ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact37) 168 8 = 3446086672107 :=
  combineSlices (auxiliaryColumnSlice contact37) 168 4 4 1842154647611 1603932024496 contact37ColumnsSlice168 contact37ColumnsSlice172
private theorem contact37ColumnsJoin176_8 : sliceWindow (auxiliaryColumnSlice contact37) 176 8 = 2566442944825 :=
  combineSlices (auxiliaryColumnSlice contact37) 176 4 4 1384007788848 1182435155977 contact37ColumnsSlice176 contact37ColumnsSlice180
private theorem contact37ColumnsJoin184_8 : sliceWindow (auxiliaryColumnSlice contact37) 184 8 = 1833536432206 :=
  combineSlices (auxiliaryColumnSlice contact37) 184 4 4 999239703819 834296728387 contact37ColumnsSlice184 contact37ColumnsSlice188
private theorem contact37ColumnsJoin192_8 : sliceWindow (auxiliaryColumnSlice contact37) 192 8 = 1245392110554 :=
  combineSlices (auxiliaryColumnSlice contact37) 192 4 4 687372797465 558019313089 contact37ColumnsSlice192 contact37ColumnsSlice196
private theorem contact37ColumnsJoin200_8 : sliceWindow (auxiliaryColumnSlice contact37) 200 8 = 795275908801 :=
  combineSlices (auxiliaryColumnSlice contact37) 200 4 4 445685552704 349590356097 contact37ColumnsSlice200 contact37ColumnsSlice204
private theorem contact37ColumnsJoin208_8 : sliceWindow (auxiliaryColumnSlice contact37) 208 8 = 470736439135 :=
  combineSlices (auxiliaryColumnSlice contact37) 208 4 4 268731078065 202005361070 contact37ColumnsSlice208 contact37ColumnsSlice212
private theorem contact37ColumnsJoin216_6 : sliceWindow (auxiliaryColumnSlice contact37) 216 6 = 205672866470 :=
  combineSlices (auxiliaryColumnSlice contact37) 216 4 2 148147284708 57525581762 contact37ColumnsSlice216 contact37ColumnsSlice220
private theorem contact37ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact37) 0 16 = 107589928543872 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 8 8 55772932690112 51816995853760 contact37ColumnsJoin0_8 contact37ColumnsJoin8_8
private theorem contact37ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact37) 16 16 = 92351263091328 :=
  combineSlices (auxiliaryColumnSlice contact37) 16 8 8 48007329490624 44343933600704 contact37ColumnsJoin16_8 contact37ColumnsJoin24_8
private theorem contact37ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact37) 32 16 = 78282761424512 :=
  combineSlices (auxiliaryColumnSlice contact37) 32 8 8 40826808184000 37455953240512 contact37ColumnsJoin32_8 contact37ColumnsJoin40_8
private theorem contact37ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact37) 48 16 = 65384430770889 :=
  combineSlices (auxiliaryColumnSlice contact37) 48 8 8 34231368770240 31153062000649 contact37ColumnsJoin48_8 contact37ColumnsJoin56_8
private theorem contact37ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact37) 64 16 = 53657532901114 :=
  combineSlices (auxiliaryColumnSlice contact37) 64 8 8 28221372452512 25436160448602 contact37ColumnsJoin64_8 contact37ColumnsJoin72_8
private theorem contact37ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact37) 80 16 = 43102704900373 :=
  combineSlices (auxiliaryColumnSlice contact37) 80 8 8 22797390777920 20305314122453 contact37ColumnsJoin80_8 contact37ColumnsJoin88_8
private theorem contact37ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact37) 96 16 = 33720249693366 :=
  combineSlices (auxiliaryColumnSlice contact37) 96 8 8 17959615761831 15760633931535 contact37ColumnsJoin96_8 contact37ColumnsJoin104_8
private theorem contact37ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact37) 112 16 = 25510418347999 :=
  combineSlices (auxiliaryColumnSlice contact37) 112 8 8 13708165648621 11802252699378 contact37ColumnsJoin112_8 contact37ColumnsJoin120_8
private theorem contact37ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact37) 128 16 = 18473454815415 :=
  combineSlices (auxiliaryColumnSlice contact37) 128 8 8 10043086682810 8430368132605 contact37ColumnsJoin128_8 contact37ColumnsJoin136_8
private theorem contact37ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact37) 144 16 = 12609430541390 :=
  combineSlices (auxiliaryColumnSlice contact37) 144 8 8 6964426839614 5645003701776 contact37ColumnsJoin144_8 contact37ColumnsJoin152_8
private theorem contact37ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact37) 160 16 = 7918275853448 :=
  combineSlices (auxiliaryColumnSlice contact37) 160 8 8 4472189181341 3446086672107 contact37ColumnsJoin160_8 contact37ColumnsJoin168_8
private theorem contact37ColumnsJoin176_16 : sliceWindow (auxiliaryColumnSlice contact37) 176 16 = 4399979377031 :=
  combineSlices (auxiliaryColumnSlice contact37) 176 8 8 2566442944825 1833536432206 contact37ColumnsJoin176_8 contact37ColumnsJoin184_8
private theorem contact37ColumnsJoin192_16 : sliceWindow (auxiliaryColumnSlice contact37) 192 16 = 2040668019355 :=
  combineSlices (auxiliaryColumnSlice contact37) 192 8 8 1245392110554 795275908801 contact37ColumnsJoin192_8 contact37ColumnsJoin200_8
private theorem contact37ColumnsJoin208_14 : sliceWindow (auxiliaryColumnSlice contact37) 208 14 = 676409305605 :=
  combineSlices (auxiliaryColumnSlice contact37) 208 8 6 470736439135 205672866470 contact37ColumnsJoin208_8 contact37ColumnsJoin216_6
private theorem contact37ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact37) 0 32 = 199941191635200 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 16 16 107589928543872 92351263091328 contact37ColumnsJoin0_16 contact37ColumnsJoin16_16
private theorem contact37ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact37) 32 32 = 143667192195401 :=
  combineSlices (auxiliaryColumnSlice contact37) 32 16 16 78282761424512 65384430770889 contact37ColumnsJoin32_16 contact37ColumnsJoin48_16
private theorem contact37ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact37) 64 32 = 96760237801487 :=
  combineSlices (auxiliaryColumnSlice contact37) 64 16 16 53657532901114 43102704900373 contact37ColumnsJoin64_16 contact37ColumnsJoin80_16
private theorem contact37ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact37) 96 32 = 59230668041365 :=
  combineSlices (auxiliaryColumnSlice contact37) 96 16 16 33720249693366 25510418347999 contact37ColumnsJoin96_16 contact37ColumnsJoin112_16
private theorem contact37ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact37) 128 32 = 31082885356805 :=
  combineSlices (auxiliaryColumnSlice contact37) 128 16 16 18473454815415 12609430541390 contact37ColumnsJoin128_16 contact37ColumnsJoin144_16
private theorem contact37ColumnsJoin160_32 : sliceWindow (auxiliaryColumnSlice contact37) 160 32 = 12318255230479 :=
  combineSlices (auxiliaryColumnSlice contact37) 160 16 16 7918275853448 4399979377031 contact37ColumnsJoin160_16 contact37ColumnsJoin176_16
private theorem contact37ColumnsJoin192_30 : sliceWindow (auxiliaryColumnSlice contact37) 192 30 = 2717077324960 :=
  combineSlices (auxiliaryColumnSlice contact37) 192 16 14 2040668019355 676409305605 contact37ColumnsJoin192_16 contact37ColumnsJoin208_14
private theorem contact37ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact37) 0 64 = 343608383830601 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 32 32 199941191635200 143667192195401 contact37ColumnsJoin0_32 contact37ColumnsJoin32_32
private theorem contact37ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact37) 64 64 = 155990905842852 :=
  combineSlices (auxiliaryColumnSlice contact37) 64 32 32 96760237801487 59230668041365 contact37ColumnsJoin64_32 contact37ColumnsJoin96_32
private theorem contact37ColumnsJoin128_64 : sliceWindow (auxiliaryColumnSlice contact37) 128 64 = 43401140587284 :=
  combineSlices (auxiliaryColumnSlice contact37) 128 32 32 31082885356805 12318255230479 contact37ColumnsJoin128_32 contact37ColumnsJoin160_32
private theorem contact37ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact37) 0 128 = 499599289673453 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 64 64 343608383830601 155990905842852 contact37ColumnsJoin0_64 contact37ColumnsJoin64_64
private theorem contact37ColumnsJoin128_94 : sliceWindow (auxiliaryColumnSlice contact37) 128 94 = 46118217912244 :=
  combineSlices (auxiliaryColumnSlice contact37) 128 64 30 43401140587284 2717077324960 contact37ColumnsJoin128_64 contact37ColumnsJoin192_30
private theorem contact37ColumnsJoin0_222 : sliceWindow (auxiliaryColumnSlice contact37) 0 222 = 545717507585697 :=
  combineSlices (auxiliaryColumnSlice contact37) 0 128 94 499599289673453 46118217912244 contact37ColumnsJoin0_128 contact37ColumnsJoin128_94
private theorem contact37OrdinaryRanks : ordinaryRankBound contact37 = 34559928814 := by decide +kernel
private theorem contact37RanksSlice0 : sliceWindow (auxiliaryRankSlice contact37) 0 4 = 107212734 :=
  contactRankWindow_of_rec contact37 0 4 107212734 (by decide +kernel)
private theorem contact37RanksSlice4 : sliceWindow (auxiliaryRankSlice contact37) 4 4 = 102259822 :=
  contactRankWindow_of_rec contact37 4 4 102259822 (by decide +kernel)
private theorem contact37RanksSlice8 : sliceWindow (auxiliaryRankSlice contact37) 8 4 = 97433502 :=
  contactRankWindow_of_rec contact37 8 4 97433502 (by decide +kernel)
private theorem contact37RanksSlice12 : sliceWindow (auxiliaryRankSlice contact37) 12 4 = 92733774 :=
  contactRankWindow_of_rec contact37 12 4 92733774 (by decide +kernel)
private theorem contact37RanksSlice16 : sliceWindow (auxiliaryRankSlice contact37) 16 4 = 88160638 :=
  contactRankWindow_of_rec contact37 16 4 88160638 (by decide +kernel)
private theorem contact37RanksSlice20 : sliceWindow (auxiliaryRankSlice contact37) 20 4 = 83714094 :=
  contactRankWindow_of_rec contact37 20 4 83714094 (by decide +kernel)
private theorem contact37RanksSlice24 : sliceWindow (auxiliaryRankSlice contact37) 24 4 = 79394142 :=
  contactRankWindow_of_rec contact37 24 4 79394142 (by decide +kernel)
private theorem contact37RanksSlice28 : sliceWindow (auxiliaryRankSlice contact37) 28 4 = 75200782 :=
  contactRankWindow_of_rec contact37 28 4 75200782 (by decide +kernel)
private theorem contact37RanksSlice32 : sliceWindow (auxiliaryRankSlice contact37) 32 4 = 71134014 :=
  contactRankWindow_of_rec contact37 32 4 71134014 (by decide +kernel)
private theorem contact37RanksSlice36 : sliceWindow (auxiliaryRankSlice contact37) 36 4 = 67193838 :=
  contactRankWindow_of_rec contact37 36 4 67193838 (by decide +kernel)
private theorem contact37RanksSlice40 : sliceWindow (auxiliaryRankSlice contact37) 40 4 = 63380254 :=
  contactRankWindow_of_rec contact37 40 4 63380254 (by decide +kernel)
private theorem contact37RanksSlice44 : sliceWindow (auxiliaryRankSlice contact37) 44 4 = 59693262 :=
  contactRankWindow_of_rec contact37 44 4 59693262 (by decide +kernel)
private theorem contact37RanksSlice48 : sliceWindow (auxiliaryRankSlice contact37) 48 4 = 56132862 :=
  contactRankWindow_of_rec contact37 48 4 56132862 (by decide +kernel)
private theorem contact37RanksSlice52 : sliceWindow (auxiliaryRankSlice contact37) 52 4 = 52699054 :=
  contactRankWindow_of_rec contact37 52 4 52699054 (by decide +kernel)
private theorem contact37RanksSlice56 : sliceWindow (auxiliaryRankSlice contact37) 56 4 = 49391838 :=
  contactRankWindow_of_rec contact37 56 4 49391838 (by decide +kernel)
private theorem contact37RanksSlice60 : sliceWindow (auxiliaryRankSlice contact37) 60 4 = 46211214 :=
  contactRankWindow_of_rec contact37 60 4 46211214 (by decide +kernel)
private theorem contact37RanksSlice64 : sliceWindow (auxiliaryRankSlice contact37) 64 4 = 43157182 :=
  contactRankWindow_of_rec contact37 64 4 43157182 (by decide +kernel)
private theorem contact37RanksSlice68 : sliceWindow (auxiliaryRankSlice contact37) 68 4 = 40229742 :=
  contactRankWindow_of_rec contact37 68 4 40229742 (by decide +kernel)
private theorem contact37RanksSlice72 : sliceWindow (auxiliaryRankSlice contact37) 72 4 = 37428592 :=
  contactRankWindow_of_rec contact37 72 4 37428592 (by decide +kernel)
private theorem contact37RanksSlice76 : sliceWindow (auxiliaryRankSlice contact37) 76 4 = 34752170 :=
  contactRankWindow_of_rec contact37 76 4 34752170 (by decide +kernel)
private theorem contact37RanksSlice80 : sliceWindow (auxiliaryRankSlice contact37) 80 4 = 32198263 :=
  contactRankWindow_of_rec contact37 80 4 32198263 (by decide +kernel)
private theorem contact37RanksSlice84 : sliceWindow (auxiliaryRankSlice contact37) 84 4 = 29764428 :=
  contactRankWindow_of_rec contact37 84 4 29764428 (by decide +kernel)
private theorem contact37RanksSlice88 : sliceWindow (auxiliaryRankSlice contact37) 88 4 = 27448038 :=
  contactRankWindow_of_rec contact37 88 4 27448038 (by decide +kernel)
private theorem contact37RanksSlice92 : sliceWindow (auxiliaryRankSlice contact37) 92 4 = 25246507 :=
  contactRankWindow_of_rec contact37 92 4 25246507 (by decide +kernel)
private theorem contact37RanksSlice96 : sliceWindow (auxiliaryRankSlice contact37) 96 4 = 23157576 :=
  contactRankWindow_of_rec contact37 96 4 23157576 (by decide +kernel)
private theorem contact37RanksSlice100 : sliceWindow (auxiliaryRankSlice contact37) 100 4 = 21178434 :=
  contactRankWindow_of_rec contact37 100 4 21178434 (by decide +kernel)
private theorem contact37RanksSlice104 : sliceWindow (auxiliaryRankSlice contact37) 104 4 = 19306495 :=
  contactRankWindow_of_rec contact37 104 4 19306495 (by decide +kernel)
private theorem contact37RanksSlice108 : sliceWindow (auxiliaryRankSlice contact37) 108 4 = 17539684 :=
  contactRankWindow_of_rec contact37 108 4 17539684 (by decide +kernel)
private theorem contact37RanksSlice112 : sliceWindow (auxiliaryRankSlice contact37) 112 4 = 15875006 :=
  contactRankWindow_of_rec contact37 112 4 15875006 (by decide +kernel)
private theorem contact37RanksSlice116 : sliceWindow (auxiliaryRankSlice contact37) 116 4 = 14309875 :=
  contactRankWindow_of_rec contact37 116 4 14309875 (by decide +kernel)
private theorem contact37RanksSlice120 : sliceWindow (auxiliaryRankSlice contact37) 120 4 = 12842400 :=
  contactRankWindow_of_rec contact37 120 4 12842400 (by decide +kernel)
private theorem contact37RanksSlice124 : sliceWindow (auxiliaryRankSlice contact37) 124 4 = 11469402 :=
  contactRankWindow_of_rec contact37 124 4 11469402 (by decide +kernel)
private theorem contact37RanksSlice128 : sliceWindow (auxiliaryRankSlice contact37) 128 4 = 10188295 :=
  contactRankWindow_of_rec contact37 128 4 10188295 (by decide +kernel)
private theorem contact37RanksSlice132 : sliceWindow (auxiliaryRankSlice contact37) 132 4 = 8997372 :=
  contactRankWindow_of_rec contact37 132 4 8997372 (by decide +kernel)
private theorem contact37RanksSlice136 : sliceWindow (auxiliaryRankSlice contact37) 136 4 = 7893270 :=
  contactRankWindow_of_rec contact37 136 4 7893270 (by decide +kernel)
private theorem contact37RanksSlice140 : sliceWindow (auxiliaryRankSlice contact37) 140 4 = 6873403 :=
  contactRankWindow_of_rec contact37 140 4 6873403 (by decide +kernel)
private theorem contact37RanksSlice144 : sliceWindow (auxiliaryRankSlice contact37) 144 4 = 5936248 :=
  contactRankWindow_of_rec contact37 144 4 5936248 (by decide +kernel)
private theorem contact37RanksSlice148 : sliceWindow (auxiliaryRankSlice contact37) 148 4 = 5078258 :=
  contactRankWindow_of_rec contact37 148 4 5078258 (by decide +kernel)
private theorem contact37RanksSlice152 : sliceWindow (auxiliaryRankSlice contact37) 152 4 = 4296847 :=
  contactRankWindow_of_rec contact37 152 4 4296847 (by decide +kernel)
private theorem contact37RanksSlice156 : sliceWindow (auxiliaryRankSlice contact37) 156 4 = 3590676 :=
  contactRankWindow_of_rec contact37 156 4 3590676 (by decide +kernel)
private theorem contact37RanksSlice160 : sliceWindow (auxiliaryRankSlice contact37) 160 4 = 2956014 :=
  contactRankWindow_of_rec contact37 160 4 2956014 (by decide +kernel)
private theorem contact37RanksSlice164 : sliceWindow (auxiliaryRankSlice contact37) 164 4 = 2390275 :=
  contactRankWindow_of_rec contact37 164 4 2390275 (by decide +kernel)
private theorem contact37RanksSlice168 : sliceWindow (auxiliaryRankSlice contact37) 168 4 = 1892304 :=
  contactRankWindow_of_rec contact37 168 4 1892304 (by decide +kernel)
private theorem contact37RanksSlice172 : sliceWindow (auxiliaryRankSlice contact37) 172 4 = 1458186 :=
  contactRankWindow_of_rec contact37 172 4 1458186 (by decide +kernel)
private theorem contact37RanksSlice176 : sliceWindow (auxiliaryRankSlice contact37) 176 4 = 1085335 :=
  contactRankWindow_of_rec contact37 176 4 1085335 (by decide +kernel)
private theorem contact37RanksSlice180 : sliceWindow (auxiliaryRankSlice contact37) 180 4 = 772780 :=
  contactRankWindow_of_rec contact37 180 4 772780 (by decide +kernel)
private theorem contact37RanksSlice184 : sliceWindow (auxiliaryRankSlice contact37) 184 4 = 516422 :=
  contactRankWindow_of_rec contact37 184 4 516422 (by decide +kernel)
private theorem contact37RanksSlice188 : sliceWindow (auxiliaryRankSlice contact37) 188 4 = 313750 :=
  contactRankWindow_of_rec contact37 188 4 313750 (by decide +kernel)
private theorem contact37RanksSlice192 : sliceWindow (auxiliaryRankSlice contact37) 192 4 = 164544 :=
  contactRankWindow_of_rec contact37 192 4 164544 (by decide +kernel)
private theorem contact37RanksSlice196 : sliceWindow (auxiliaryRankSlice contact37) 196 4 = 64831 :=
  contactRankWindow_of_rec contact37 196 4 64831 (by decide +kernel)
private theorem contact37RanksSlice200 : sliceWindow (auxiliaryRankSlice contact37) 200 4 = 11382 :=
  contactRankWindow_of_rec contact37 200 4 11382 (by decide +kernel)
private theorem contact37RanksSlice204 : sliceWindow (auxiliaryRankSlice contact37) 204 18 = 0 :=
  contactRankWindow_of_rec contact37 204 18 0 (by decide +kernel)
private theorem contact37RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact37) 0 8 = 209472556 :=
  combineSlices (auxiliaryRankSlice contact37) 0 4 4 107212734 102259822 contact37RanksSlice0 contact37RanksSlice4
private theorem contact37RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact37) 8 8 = 190167276 :=
  combineSlices (auxiliaryRankSlice contact37) 8 4 4 97433502 92733774 contact37RanksSlice8 contact37RanksSlice12
private theorem contact37RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact37) 16 8 = 171874732 :=
  combineSlices (auxiliaryRankSlice contact37) 16 4 4 88160638 83714094 contact37RanksSlice16 contact37RanksSlice20
private theorem contact37RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact37) 24 8 = 154594924 :=
  combineSlices (auxiliaryRankSlice contact37) 24 4 4 79394142 75200782 contact37RanksSlice24 contact37RanksSlice28
private theorem contact37RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact37) 32 8 = 138327852 :=
  combineSlices (auxiliaryRankSlice contact37) 32 4 4 71134014 67193838 contact37RanksSlice32 contact37RanksSlice36
private theorem contact37RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact37) 40 8 = 123073516 :=
  combineSlices (auxiliaryRankSlice contact37) 40 4 4 63380254 59693262 contact37RanksSlice40 contact37RanksSlice44
private theorem contact37RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact37) 48 8 = 108831916 :=
  combineSlices (auxiliaryRankSlice contact37) 48 4 4 56132862 52699054 contact37RanksSlice48 contact37RanksSlice52
private theorem contact37RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact37) 56 8 = 95603052 :=
  combineSlices (auxiliaryRankSlice contact37) 56 4 4 49391838 46211214 contact37RanksSlice56 contact37RanksSlice60
private theorem contact37RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact37) 64 8 = 83386924 :=
  combineSlices (auxiliaryRankSlice contact37) 64 4 4 43157182 40229742 contact37RanksSlice64 contact37RanksSlice68
private theorem contact37RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact37) 72 8 = 72180762 :=
  combineSlices (auxiliaryRankSlice contact37) 72 4 4 37428592 34752170 contact37RanksSlice72 contact37RanksSlice76
private theorem contact37RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact37) 80 8 = 61962691 :=
  combineSlices (auxiliaryRankSlice contact37) 80 4 4 32198263 29764428 contact37RanksSlice80 contact37RanksSlice84
private theorem contact37RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact37) 88 8 = 52694545 :=
  combineSlices (auxiliaryRankSlice contact37) 88 4 4 27448038 25246507 contact37RanksSlice88 contact37RanksSlice92
private theorem contact37RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact37) 96 8 = 44336010 :=
  combineSlices (auxiliaryRankSlice contact37) 96 4 4 23157576 21178434 contact37RanksSlice96 contact37RanksSlice100
private theorem contact37RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact37) 104 8 = 36846179 :=
  combineSlices (auxiliaryRankSlice contact37) 104 4 4 19306495 17539684 contact37RanksSlice104 contact37RanksSlice108
private theorem contact37RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact37) 112 8 = 30184881 :=
  combineSlices (auxiliaryRankSlice contact37) 112 4 4 15875006 14309875 contact37RanksSlice112 contact37RanksSlice116
private theorem contact37RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact37) 120 8 = 24311802 :=
  combineSlices (auxiliaryRankSlice contact37) 120 4 4 12842400 11469402 contact37RanksSlice120 contact37RanksSlice124
private theorem contact37RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact37) 128 8 = 19185667 :=
  combineSlices (auxiliaryRankSlice contact37) 128 4 4 10188295 8997372 contact37RanksSlice128 contact37RanksSlice132
private theorem contact37RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact37) 136 8 = 14766673 :=
  combineSlices (auxiliaryRankSlice contact37) 136 4 4 7893270 6873403 contact37RanksSlice136 contact37RanksSlice140
private theorem contact37RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact37) 144 8 = 11014506 :=
  combineSlices (auxiliaryRankSlice contact37) 144 4 4 5936248 5078258 contact37RanksSlice144 contact37RanksSlice148
private theorem contact37RanksJoin152_8 : sliceWindow (auxiliaryRankSlice contact37) 152 8 = 7887523 :=
  combineSlices (auxiliaryRankSlice contact37) 152 4 4 4296847 3590676 contact37RanksSlice152 contact37RanksSlice156
private theorem contact37RanksJoin160_8 : sliceWindow (auxiliaryRankSlice contact37) 160 8 = 5346289 :=
  combineSlices (auxiliaryRankSlice contact37) 160 4 4 2956014 2390275 contact37RanksSlice160 contact37RanksSlice164
private theorem contact37RanksJoin168_8 : sliceWindow (auxiliaryRankSlice contact37) 168 8 = 3350490 :=
  combineSlices (auxiliaryRankSlice contact37) 168 4 4 1892304 1458186 contact37RanksSlice168 contact37RanksSlice172
private theorem contact37RanksJoin176_8 : sliceWindow (auxiliaryRankSlice contact37) 176 8 = 1858115 :=
  combineSlices (auxiliaryRankSlice contact37) 176 4 4 1085335 772780 contact37RanksSlice176 contact37RanksSlice180
private theorem contact37RanksJoin184_8 : sliceWindow (auxiliaryRankSlice contact37) 184 8 = 830172 :=
  combineSlices (auxiliaryRankSlice contact37) 184 4 4 516422 313750 contact37RanksSlice184 contact37RanksSlice188
private theorem contact37RanksJoin192_8 : sliceWindow (auxiliaryRankSlice contact37) 192 8 = 229375 :=
  combineSlices (auxiliaryRankSlice contact37) 192 4 4 164544 64831 contact37RanksSlice192 contact37RanksSlice196
private theorem contact37RanksJoin200_22 : sliceWindow (auxiliaryRankSlice contact37) 200 22 = 11382 :=
  combineSlices (auxiliaryRankSlice contact37) 200 4 18 11382 0 contact37RanksSlice200 contact37RanksSlice204
private theorem contact37RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact37) 0 16 = 399639832 :=
  combineSlices (auxiliaryRankSlice contact37) 0 8 8 209472556 190167276 contact37RanksJoin0_8 contact37RanksJoin8_8
private theorem contact37RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact37) 16 16 = 326469656 :=
  combineSlices (auxiliaryRankSlice contact37) 16 8 8 171874732 154594924 contact37RanksJoin16_8 contact37RanksJoin24_8
private theorem contact37RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact37) 32 16 = 261401368 :=
  combineSlices (auxiliaryRankSlice contact37) 32 8 8 138327852 123073516 contact37RanksJoin32_8 contact37RanksJoin40_8
private theorem contact37RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact37) 48 16 = 204434968 :=
  combineSlices (auxiliaryRankSlice contact37) 48 8 8 108831916 95603052 contact37RanksJoin48_8 contact37RanksJoin56_8
private theorem contact37RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact37) 64 16 = 155567686 :=
  combineSlices (auxiliaryRankSlice contact37) 64 8 8 83386924 72180762 contact37RanksJoin64_8 contact37RanksJoin72_8
private theorem contact37RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact37) 80 16 = 114657236 :=
  combineSlices (auxiliaryRankSlice contact37) 80 8 8 61962691 52694545 contact37RanksJoin80_8 contact37RanksJoin88_8
private theorem contact37RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact37) 96 16 = 81182189 :=
  combineSlices (auxiliaryRankSlice contact37) 96 8 8 44336010 36846179 contact37RanksJoin96_8 contact37RanksJoin104_8
private theorem contact37RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact37) 112 16 = 54496683 :=
  combineSlices (auxiliaryRankSlice contact37) 112 8 8 30184881 24311802 contact37RanksJoin112_8 contact37RanksJoin120_8
private theorem contact37RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact37) 128 16 = 33952340 :=
  combineSlices (auxiliaryRankSlice contact37) 128 8 8 19185667 14766673 contact37RanksJoin128_8 contact37RanksJoin136_8
private theorem contact37RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact37) 144 16 = 18902029 :=
  combineSlices (auxiliaryRankSlice contact37) 144 8 8 11014506 7887523 contact37RanksJoin144_8 contact37RanksJoin152_8
private theorem contact37RanksJoin160_16 : sliceWindow (auxiliaryRankSlice contact37) 160 16 = 8696779 :=
  combineSlices (auxiliaryRankSlice contact37) 160 8 8 5346289 3350490 contact37RanksJoin160_8 contact37RanksJoin168_8
private theorem contact37RanksJoin176_16 : sliceWindow (auxiliaryRankSlice contact37) 176 16 = 2688287 :=
  combineSlices (auxiliaryRankSlice contact37) 176 8 8 1858115 830172 contact37RanksJoin176_8 contact37RanksJoin184_8
private theorem contact37RanksJoin192_30 : sliceWindow (auxiliaryRankSlice contact37) 192 30 = 240757 :=
  combineSlices (auxiliaryRankSlice contact37) 192 8 22 229375 11382 contact37RanksJoin192_8 contact37RanksJoin200_22
private theorem contact37RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact37) 0 32 = 726109488 :=
  combineSlices (auxiliaryRankSlice contact37) 0 16 16 399639832 326469656 contact37RanksJoin0_16 contact37RanksJoin16_16
private theorem contact37RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact37) 32 32 = 465836336 :=
  combineSlices (auxiliaryRankSlice contact37) 32 16 16 261401368 204434968 contact37RanksJoin32_16 contact37RanksJoin48_16
private theorem contact37RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact37) 64 32 = 270224922 :=
  combineSlices (auxiliaryRankSlice contact37) 64 16 16 155567686 114657236 contact37RanksJoin64_16 contact37RanksJoin80_16
private theorem contact37RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact37) 96 32 = 135678872 :=
  combineSlices (auxiliaryRankSlice contact37) 96 16 16 81182189 54496683 contact37RanksJoin96_16 contact37RanksJoin112_16
private theorem contact37RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact37) 128 32 = 52854369 :=
  combineSlices (auxiliaryRankSlice contact37) 128 16 16 33952340 18902029 contact37RanksJoin128_16 contact37RanksJoin144_16
private theorem contact37RanksJoin160_32 : sliceWindow (auxiliaryRankSlice contact37) 160 32 = 11385066 :=
  combineSlices (auxiliaryRankSlice contact37) 160 16 16 8696779 2688287 contact37RanksJoin160_16 contact37RanksJoin176_16
private theorem contact37RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact37) 0 64 = 1191945824 :=
  combineSlices (auxiliaryRankSlice contact37) 0 32 32 726109488 465836336 contact37RanksJoin0_32 contact37RanksJoin32_32
private theorem contact37RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact37) 64 64 = 405903794 :=
  combineSlices (auxiliaryRankSlice contact37) 64 32 32 270224922 135678872 contact37RanksJoin64_32 contact37RanksJoin96_32
private theorem contact37RanksJoin128_64 : sliceWindow (auxiliaryRankSlice contact37) 128 64 = 64239435 :=
  combineSlices (auxiliaryRankSlice contact37) 128 32 32 52854369 11385066 contact37RanksJoin128_32 contact37RanksJoin160_32
private theorem contact37RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact37) 0 128 = 1597849618 :=
  combineSlices (auxiliaryRankSlice contact37) 0 64 64 1191945824 405903794 contact37RanksJoin0_64 contact37RanksJoin64_64
private theorem contact37RanksJoin128_94 : sliceWindow (auxiliaryRankSlice contact37) 128 94 = 64480192 :=
  combineSlices (auxiliaryRankSlice contact37) 128 64 30 64239435 240757 contact37RanksJoin128_64 contact37RanksJoin192_30
private theorem contact37RanksJoin0_222 : sliceWindow (auxiliaryRankSlice contact37) 0 222 = 1662329810 :=
  combineSlices (auxiliaryRankSlice contact37) 0 128 94 1597849618 64480192 contact37RanksJoin0_128 contact37RanksJoin128_94
theorem contact37_margin : sourceMargin contact37 :=
  margin_of_checked_counts contact37 222 8949733668999943 545717507585697 34559928814 1662329810 rfl contact37OrdinaryColumns contact37ColumnsJoin0_222 contact37OrdinaryRanks contact37RanksJoin0_222 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

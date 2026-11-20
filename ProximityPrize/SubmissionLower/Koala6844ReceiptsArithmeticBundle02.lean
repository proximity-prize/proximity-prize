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

private theorem contact01OrdinaryColumns : ordinaryColumnCount contact01 = 2418554595580809 := by decide +kernel
private theorem contact01ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact01) 0 4 = 7339082412620 :=
  contactColumnsWindow_fast contact01 0 4 7339082412620 (by decide +kernel)
private theorem contact01ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact01) 4 4 = 6989850654700 :=
  contactColumnsWindow_fast contact01 4 4 6989850654700 (by decide +kernel)
private theorem contact01ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact01) 8 4 = 6649162444524 :=
  contactColumnsWindow_fast contact01 8 4 6649162444524 (by decide +kernel)
private theorem contact01ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact01) 12 4 = 6317017981740 :=
  contactColumnsWindow_fast contact01 12 4 6317017981740 (by decide +kernel)
private theorem contact01ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact01) 16 4 = 5993449079868 :=
  contactColumnsWindow_fast contact01 16 4 5993449079868 (by decide +kernel)
private theorem contact01ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact01) 20 4 = 5678442434489 :=
  contactColumnsWindow_fast contact01 20 4 5678442434489 (by decide +kernel)
private theorem contact01ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact01) 24 4 = 5371982933580 :=
  contactColumnsWindow_fast contact01 24 4 5371982933580 (by decide +kernel)
private theorem contact01ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact01) 28 4 = 5074069260476 :=
  contactColumnsWindow_fast contact01 28 4 5074069260476 (by decide +kernel)
private theorem contact01ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact01) 32 4 = 4784704305340 :=
  contactColumnsWindow_fast contact01 32 4 4784704305340 (by decide +kernel)
private theorem contact01ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact01) 36 4 = 4503919230952 :=
  contactColumnsWindow_fast contact01 36 4 4503919230952 (by decide +kernel)
private theorem contact01ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact01) 40 4 = 4231697530500 :=
  contactColumnsWindow_fast contact01 40 4 4231697530500 (by decide +kernel)
private theorem contact01ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact01) 44 4 = 3968024834487 :=
  contactColumnsWindow_fast contact01 44 4 3968024834487 (by decide +kernel)
private theorem contact01ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact01) 48 4 = 3712902396524 :=
  contactColumnsWindow_fast contact01 48 4 3712902396524 (by decide +kernel)
private theorem contact01ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact01) 52 4 = 3466331951789 :=
  contactColumnsWindow_fast contact01 52 4 3466331951789 (by decide +kernel)
private theorem contact01ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact01) 56 4 = 3228348060063 :=
  contactColumnsWindow_fast contact01 56 4 3228348060063 (by decide +kernel)
private theorem contact01ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact01) 60 4 = 2998927246008 :=
  contactColumnsWindow_fast contact01 60 4 2998927246008 (by decide +kernel)
private theorem contact01ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact01) 64 4 = 2778058846877 :=
  contactColumnsWindow_fast contact01 64 4 2778058846877 (by decide +kernel)
private theorem contact01ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact01) 68 4 = 2565740665652 :=
  contactColumnsWindow_fast contact01 68 4 2565740665652 (by decide +kernel)
private theorem contact01ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact01) 72 4 = 2361976658140 :=
  contactColumnsWindow_fast contact01 72 4 2361976658140 (by decide +kernel)
private theorem contact01ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact01) 76 4 = 2166799765325 :=
  contactColumnsWindow_fast contact01 76 4 2166799765325 (by decide +kernel)
private theorem contact01ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact01) 80 4 = 1980183780060 :=
  contactColumnsWindow_fast contact01 80 4 1980183780060 (by decide +kernel)
private theorem contact01ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact01) 84 4 = 1802119718544 :=
  contactColumnsWindow_fast contact01 84 4 1802119718544 (by decide +kernel)
private theorem contact01ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact01) 88 4 = 1632605867906 :=
  contactColumnsWindow_fast contact01 88 4 1632605867906 (by decide +kernel)
private theorem contact01ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact01) 92 4 = 1471648626964 :=
  contactColumnsWindow_fast contact01 92 4 1471648626964 (by decide +kernel)
private theorem contact01ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact01) 96 4 = 1319278319881 :=
  contactColumnsWindow_fast contact01 96 4 1319278319881 (by decide +kernel)
private theorem contact01ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact01) 100 4 = 1175467191081 :=
  contactColumnsWindow_fast contact01 100 4 1175467191081 (by decide +kernel)
private theorem contact01ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact01) 104 4 = 1040207623940 :=
  contactColumnsWindow_fast contact01 104 4 1040207623940 (by decide +kernel)
private theorem contact01ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact01) 108 4 = 913497904590 :=
  contactColumnsWindow_fast contact01 108 4 913497904590 (by decide +kernel)
private theorem contact01ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact01) 112 4 = 795347477284 :=
  contactColumnsWindow_fast contact01 112 4 795347477284 (by decide +kernel)
private theorem contact01ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact01) 116 4 = 685783996230 :=
  contactColumnsWindow_fast contact01 116 4 685783996230 (by decide +kernel)
private theorem contact01ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact01) 120 4 = 584777487671 :=
  contactColumnsWindow_fast contact01 120 4 584777487671 (by decide +kernel)
private theorem contact01ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact01) 124 4 = 492322347880 :=
  contactColumnsWindow_fast contact01 124 4 492322347880 (by decide +kernel)
private theorem contact01ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact01) 128 4 = 408416903245 :=
  contactColumnsWindow_fast contact01 128 4 408416903245 (by decide +kernel)
private theorem contact01ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact01) 132 4 = 333074347732 :=
  contactColumnsWindow_fast contact01 132 4 333074347732 (by decide +kernel)
private theorem contact01ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact01) 136 4 = 266316553546 :=
  contactColumnsWindow_fast contact01 136 4 266316553546 (by decide +kernel)
private theorem contact01ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact01) 140 4 = 208113074480 :=
  contactColumnsWindow_fast contact01 140 4 208113074480 (by decide +kernel)
private theorem contact01ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact01) 144 4 = 158402848910 :=
  contactColumnsWindow_fast contact01 144 4 158402848910 (by decide +kernel)
private theorem contact01ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact01) 148 4 = 116943051462 :=
  contactColumnsWindow_fast contact01 148 4 116943051462 (by decide +kernel)
private theorem contact01ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact01) 152 4 = 83328542148 :=
  contactColumnsWindow_fast contact01 152 4 83328542148 (by decide +kernel)
private theorem contact01ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact01) 156 4 = 56990600319 :=
  contactColumnsWindow_fast contact01 156 4 56990600319 (by decide +kernel)
private theorem contact01ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact01) 160 4 = 37154900131 :=
  contactColumnsWindow_fast contact01 160 4 37154900131 (by decide +kernel)
private theorem contact01ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact01) 164 1 = 6866951855 :=
  contactColumnsWindow_fast contact01 164 1 6866951855 (by decide +kernel)
private theorem contact01ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact01) 0 8 = 14328933067320 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 4 4 7339082412620 6989850654700 contact01ColumnsSlice0 contact01ColumnsSlice4
private theorem contact01ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact01) 8 8 = 12966180426264 :=
  combineSlices (auxiliaryColumnSlice contact01) 8 4 4 6649162444524 6317017981740 contact01ColumnsSlice8 contact01ColumnsSlice12
private theorem contact01ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact01) 16 8 = 11671891514357 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 4 4 5993449079868 5678442434489 contact01ColumnsSlice16 contact01ColumnsSlice20
private theorem contact01ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact01) 24 8 = 10446052194056 :=
  combineSlices (auxiliaryColumnSlice contact01) 24 4 4 5371982933580 5074069260476 contact01ColumnsSlice24 contact01ColumnsSlice28
private theorem contact01ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact01) 32 8 = 9288623536292 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 4 4 4784704305340 4503919230952 contact01ColumnsSlice32 contact01ColumnsSlice36
private theorem contact01ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact01) 40 8 = 8199722364987 :=
  combineSlices (auxiliaryColumnSlice contact01) 40 4 4 4231697530500 3968024834487 contact01ColumnsSlice40 contact01ColumnsSlice44
private theorem contact01ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact01) 48 8 = 7179234348313 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 4 4 3712902396524 3466331951789 contact01ColumnsSlice48 contact01ColumnsSlice52
private theorem contact01ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact01) 56 8 = 6227275306071 :=
  combineSlices (auxiliaryColumnSlice contact01) 56 4 4 3228348060063 2998927246008 contact01ColumnsSlice56 contact01ColumnsSlice60
private theorem contact01ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact01) 64 8 = 5343799512529 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 4 4 2778058846877 2565740665652 contact01ColumnsSlice64 contact01ColumnsSlice68
private theorem contact01ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact01) 72 8 = 4528776423465 :=
  combineSlices (auxiliaryColumnSlice contact01) 72 4 4 2361976658140 2166799765325 contact01ColumnsSlice72 contact01ColumnsSlice76
private theorem contact01ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact01) 80 8 = 3782303498604 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 4 4 1980183780060 1802119718544 contact01ColumnsSlice80 contact01ColumnsSlice84
private theorem contact01ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact01) 88 8 = 3104254494870 :=
  combineSlices (auxiliaryColumnSlice contact01) 88 4 4 1632605867906 1471648626964 contact01ColumnsSlice88 contact01ColumnsSlice92
private theorem contact01ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact01) 96 8 = 2494745510962 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 4 4 1319278319881 1175467191081 contact01ColumnsSlice96 contact01ColumnsSlice100
private theorem contact01ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact01) 104 8 = 1953705528530 :=
  combineSlices (auxiliaryColumnSlice contact01) 104 4 4 1040207623940 913497904590 contact01ColumnsSlice104 contact01ColumnsSlice108
private theorem contact01ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact01) 112 8 = 1481131473514 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 4 4 795347477284 685783996230 contact01ColumnsSlice112 contact01ColumnsSlice116
private theorem contact01ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact01) 120 8 = 1077099835551 :=
  combineSlices (auxiliaryColumnSlice contact01) 120 4 4 584777487671 492322347880 contact01ColumnsSlice120 contact01ColumnsSlice124
private theorem contact01ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact01) 128 8 = 741491250977 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 4 4 408416903245 333074347732 contact01ColumnsSlice128 contact01ColumnsSlice132
private theorem contact01ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact01) 136 8 = 474429628026 :=
  combineSlices (auxiliaryColumnSlice contact01) 136 4 4 266316553546 208113074480 contact01ColumnsSlice136 contact01ColumnsSlice140
private theorem contact01ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact01) 144 8 = 275345900372 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 4 4 158402848910 116943051462 contact01ColumnsSlice144 contact01ColumnsSlice148
private theorem contact01ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact01) 152 8 = 140319142467 :=
  combineSlices (auxiliaryColumnSlice contact01) 152 4 4 83328542148 56990600319 contact01ColumnsSlice152 contact01ColumnsSlice156
private theorem contact01ColumnsJoin160_5 : sliceWindow (auxiliaryColumnSlice contact01) 160 5 = 44021851986 :=
  combineSlices (auxiliaryColumnSlice contact01) 160 4 1 37154900131 6866951855 contact01ColumnsSlice160 contact01ColumnsSlice164
private theorem contact01ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact01) 0 16 = 27295113493584 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 8 8 14328933067320 12966180426264 contact01ColumnsJoin0_8 contact01ColumnsJoin8_8
private theorem contact01ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact01) 16 16 = 22117943708413 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 8 8 11671891514357 10446052194056 contact01ColumnsJoin16_8 contact01ColumnsJoin24_8
private theorem contact01ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact01) 32 16 = 17488345901279 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 8 8 9288623536292 8199722364987 contact01ColumnsJoin32_8 contact01ColumnsJoin40_8
private theorem contact01ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact01) 48 16 = 13406509654384 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 8 8 7179234348313 6227275306071 contact01ColumnsJoin48_8 contact01ColumnsJoin56_8
private theorem contact01ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact01) 64 16 = 9872575935994 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 8 8 5343799512529 4528776423465 contact01ColumnsJoin64_8 contact01ColumnsJoin72_8
private theorem contact01ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact01) 80 16 = 6886557993474 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 8 8 3782303498604 3104254494870 contact01ColumnsJoin80_8 contact01ColumnsJoin88_8
private theorem contact01ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact01) 96 16 = 4448451039492 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 8 8 2494745510962 1953705528530 contact01ColumnsJoin96_8 contact01ColumnsJoin104_8
private theorem contact01ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact01) 112 16 = 2558231309065 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 8 8 1481131473514 1077099835551 contact01ColumnsJoin112_8 contact01ColumnsJoin120_8
private theorem contact01ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact01) 128 16 = 1215920879003 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 8 8 741491250977 474429628026 contact01ColumnsJoin128_8 contact01ColumnsJoin136_8
private theorem contact01ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact01) 144 16 = 415665042839 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 8 8 275345900372 140319142467 contact01ColumnsJoin144_8 contact01ColumnsJoin152_8
private theorem contact01ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact01) 0 32 = 49413057201997 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 16 16 27295113493584 22117943708413 contact01ColumnsJoin0_16 contact01ColumnsJoin16_16
private theorem contact01ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact01) 32 32 = 30894855555663 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 16 16 17488345901279 13406509654384 contact01ColumnsJoin32_16 contact01ColumnsJoin48_16
private theorem contact01ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact01) 64 32 = 16759133929468 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 16 16 9872575935994 6886557993474 contact01ColumnsJoin64_16 contact01ColumnsJoin80_16
private theorem contact01ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact01) 96 32 = 7006682348557 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 16 16 4448451039492 2558231309065 contact01ColumnsJoin96_16 contact01ColumnsJoin112_16
private theorem contact01ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact01) 128 32 = 1631585921842 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 16 16 1215920879003 415665042839 contact01ColumnsJoin128_16 contact01ColumnsJoin144_16
private theorem contact01ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact01) 0 64 = 80307912757660 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 32 32 49413057201997 30894855555663 contact01ColumnsJoin0_32 contact01ColumnsJoin32_32
private theorem contact01ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact01) 64 64 = 23765816278025 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 32 32 16759133929468 7006682348557 contact01ColumnsJoin64_32 contact01ColumnsJoin96_32
private theorem contact01ColumnsJoin128_37 : sliceWindow (auxiliaryColumnSlice contact01) 128 37 = 1675607773828 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 32 5 1631585921842 44021851986 contact01ColumnsJoin128_32 contact01ColumnsJoin160_5
private theorem contact01ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact01) 0 128 = 104073729035685 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 64 64 80307912757660 23765816278025 contact01ColumnsJoin0_64 contact01ColumnsJoin64_64
private theorem contact01ColumnsJoin0_165 : sliceWindow (auxiliaryColumnSlice contact01) 0 165 = 105749336809513 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 128 37 104073729035685 1675607773828 contact01ColumnsJoin0_128 contact01ColumnsJoin128_37
private theorem contact01OrdinaryRanks : ordinaryRankBound contact01 = 9310481132 := by decide +kernel
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
  margin_of_checked_counts contact01 165 2418554595580809 105749336809513 9310481132 318970250 rfl contact01OrdinaryColumns contact01ColumnsJoin0_165 contact01OrdinaryRanks contact01RanksJoin0_165 (by decide +kernel)

private theorem contact03OrdinaryColumns : ordinaryColumnCount contact03 = 2248980451501511 := by decide +kernel
private theorem contact03ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact03) 0 4 = 7519125653614 :=
  contactColumnsWindow_fast contact03 0 4 7519125653614 (by decide +kernel)
private theorem contact03ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact03) 4 4 = 7160371349278 :=
  contactColumnsWindow_fast contact03 4 4 7160371349278 (by decide +kernel)
private theorem contact03ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact03) 8 4 = 6810419465760 :=
  contactColumnsWindow_fast contact03 8 4 6810419465760 (by decide +kernel)
private theorem contact03ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact03) 12 4 = 6469270215400 :=
  contactColumnsWindow_fast contact03 12 4 6469270215400 (by decide +kernel)
private theorem contact03ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact03) 16 4 = 6136956715400 :=
  contactColumnsWindow_fast contact03 16 4 6136956715400 (by decide +kernel)
private theorem contact03ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact03) 20 4 = 5813465091456 :=
  contactColumnsWindow_fast contact03 20 4 5813465091456 (by decide +kernel)
private theorem contact03ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact03) 24 4 = 5498779559164 :=
  contactColumnsWindow_fast contact03 24 4 5498779559164 (by decide +kernel)
private theorem contact03ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact03) 28 4 = 5192898773803 :=
  contactColumnsWindow_fast contact03 28 4 5192898773803 (by decide +kernel)
private theorem contact03ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact03) 32 4 = 4895825712468 :=
  contactColumnsWindow_fast contact03 32 4 4895825712468 (by decide +kernel)
private theorem contact03ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact03) 36 4 = 4607592855491 :=
  contactColumnsWindow_fast contact03 36 4 4607592855491 (by decide +kernel)
private theorem contact03ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact03) 40 4 = 4328182934461 :=
  contactColumnsWindow_fast contact03 40 4 4328182934461 (by decide +kernel)
private theorem contact03ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact03) 44 4 = 4057580997379 :=
  contactColumnsWindow_fast contact03 44 4 4057580997379 (by decide +kernel)
private theorem contact03ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact03) 48 4 = 3795788317177 :=
  contactColumnsWindow_fast contact03 48 4 3795788317177 (by decide +kernel)
private theorem contact03ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact03) 52 4 = 3542806719619 :=
  contactColumnsWindow_fast contact03 52 4 3542806719619 (by decide +kernel)
private theorem contact03ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact03) 56 4 = 3298672170695 :=
  contactColumnsWindow_fast contact03 56 4 3298672170695 (by decide +kernel)
private theorem contact03ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact03) 60 4 = 3063360171883 :=
  contactColumnsWindow_fast contact03 60 4 3063360171883 (by decide +kernel)
private theorem contact03ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact03) 64 4 = 2836859622769 :=
  contactColumnsWindow_fast contact03 64 4 2836859622769 (by decide +kernel)
private theorem contact03ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact03) 68 4 = 2619168290391 :=
  contactColumnsWindow_fast contact03 68 4 2619168290391 (by decide +kernel)
private theorem contact03ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact03) 72 4 = 2410290305322 :=
  contactColumnsWindow_fast contact03 72 4 2410290305322 (by decide +kernel)
private theorem contact03ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact03) 76 4 = 2210259957917 :=
  contactColumnsWindow_fast contact03 76 4 2210259957917 (by decide +kernel)
private theorem contact03ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact03) 80 4 = 2019049889017 :=
  contactColumnsWindow_fast contact03 80 4 2019049889017 (by decide +kernel)
private theorem contact03ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact03) 84 4 = 1836650769415 :=
  contactColumnsWindow_fast contact03 84 4 1836650769415 (by decide +kernel)
private theorem contact03ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact03) 88 4 = 1663060860076 :=
  contactColumnsWindow_fast contact03 88 4 1663060860076 (by decide +kernel)
private theorem contact03ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact03) 92 4 = 1498286830846 :=
  contactColumnsWindow_fast contact03 92 4 1498286830846 (by decide +kernel)
private theorem contact03ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact03) 96 4 = 1342360256083 :=
  contactColumnsWindow_fast contact03 96 4 1342360256083 (by decide +kernel)
private theorem contact03ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact03) 100 4 = 1195252145431 :=
  contactColumnsWindow_fast contact03 100 4 1195252145431 (by decide +kernel)
private theorem contact03ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact03) 104 4 = 1056954615165 :=
  contactColumnsWindow_fast contact03 104 4 1056954615165 (by decide +kernel)
private theorem contact03ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact03) 108 4 = 927465925691 :=
  contactColumnsWindow_fast contact03 108 4 927465925691 (by decide +kernel)
private theorem contact03ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact03) 112 4 = 806795901214 :=
  contactColumnsWindow_fast contact03 112 4 806795901214 (by decide +kernel)
private theorem contact03ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact03) 116 4 = 694973342998 :=
  contactColumnsWindow_fast contact03 116 4 694973342998 (by decide +kernel)
private theorem contact03ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact03) 120 4 = 591966949948 :=
  contactColumnsWindow_fast contact03 120 4 591966949948 (by decide +kernel)
private theorem contact03ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact03) 124 4 = 497770940627 :=
  contactColumnsWindow_fast contact03 124 4 497770940627 (by decide +kernel)
private theorem contact03ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact03) 128 4 = 412383616918 :=
  contactColumnsWindow_fast contact03 128 4 412383616918 (by decide +kernel)
private theorem contact03ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact03) 132 4 = 335818700878 :=
  contactColumnsWindow_fast contact03 132 4 335818700878 (by decide +kernel)
private theorem contact03ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact03) 136 4 = 268098973305 :=
  contactColumnsWindow_fast contact03 136 4 268098973305 (by decide +kernel)
private theorem contact03ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact03) 140 4 = 209189232152 :=
  contactColumnsWindow_fast contact03 140 4 209189232152 (by decide +kernel)
private theorem contact03ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact03) 144 4 = 158993690558 :=
  contactColumnsWindow_fast contact03 144 4 158993690558 (by decide +kernel)
private theorem contact03ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact03) 148 4 = 117221676350 :=
  contactColumnsWindow_fast contact03 148 4 117221676350 (by decide +kernel)
private theorem contact03ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact03) 152 4 = 83430861650 :=
  contactColumnsWindow_fast contact03 152 4 83430861650 (by decide +kernel)
private theorem contact03ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact03) 156 4 = 57013756029 :=
  contactColumnsWindow_fast contact03 156 4 57013756029 (by decide +kernel)
private theorem contact03ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact03) 160 4 = 37156314001 :=
  contactColumnsWindow_fast contact03 160 4 37156314001 (by decide +kernel)
private theorem contact03ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact03) 0 8 = 14679497002892 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 4 4 7519125653614 7160371349278 contact03ColumnsSlice0 contact03ColumnsSlice4
private theorem contact03ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact03) 8 8 = 13279689681160 :=
  combineSlices (auxiliaryColumnSlice contact03) 8 4 4 6810419465760 6469270215400 contact03ColumnsSlice8 contact03ColumnsSlice12
private theorem contact03ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact03) 16 8 = 11950421806856 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 4 4 6136956715400 5813465091456 contact03ColumnsSlice16 contact03ColumnsSlice20
private theorem contact03ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact03) 24 8 = 10691678332967 :=
  combineSlices (auxiliaryColumnSlice contact03) 24 4 4 5498779559164 5192898773803 contact03ColumnsSlice24 contact03ColumnsSlice28
private theorem contact03ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact03) 32 8 = 9503418567959 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 4 4 4895825712468 4607592855491 contact03ColumnsSlice32 contact03ColumnsSlice36
private theorem contact03ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact03) 40 8 = 8385763931840 :=
  combineSlices (auxiliaryColumnSlice contact03) 40 4 4 4328182934461 4057580997379 contact03ColumnsSlice40 contact03ColumnsSlice44
private theorem contact03ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact03) 48 8 = 7338595036796 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 4 4 3795788317177 3542806719619 contact03ColumnsSlice48 contact03ColumnsSlice52
private theorem contact03ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact03) 56 8 = 6362032342578 :=
  combineSlices (auxiliaryColumnSlice contact03) 56 4 4 3298672170695 3063360171883 contact03ColumnsSlice56 contact03ColumnsSlice60
private theorem contact03ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact03) 64 8 = 5456027913160 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 4 4 2836859622769 2619168290391 contact03ColumnsSlice64 contact03ColumnsSlice68
private theorem contact03ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact03) 72 8 = 4620550263239 :=
  combineSlices (auxiliaryColumnSlice contact03) 72 4 4 2410290305322 2210259957917 contact03ColumnsSlice72 contact03ColumnsSlice76
private theorem contact03ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact03) 80 8 = 3855700658432 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 4 4 2019049889017 1836650769415 contact03ColumnsSlice80 contact03ColumnsSlice84
private theorem contact03ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact03) 88 8 = 3161347690922 :=
  combineSlices (auxiliaryColumnSlice contact03) 88 4 4 1663060860076 1498286830846 contact03ColumnsSlice88 contact03ColumnsSlice92
private theorem contact03ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact03) 96 8 = 2537612401514 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 4 4 1342360256083 1195252145431 contact03ColumnsSlice96 contact03ColumnsSlice100
private theorem contact03ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact03) 104 8 = 1984420540856 :=
  combineSlices (auxiliaryColumnSlice contact03) 104 4 4 1056954615165 927465925691 contact03ColumnsSlice104 contact03ColumnsSlice108
private theorem contact03ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact03) 112 8 = 1501769244212 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 4 4 806795901214 694973342998 contact03ColumnsSlice112 contact03ColumnsSlice116
private theorem contact03ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact03) 120 8 = 1089737890575 :=
  combineSlices (auxiliaryColumnSlice contact03) 120 4 4 591966949948 497770940627 contact03ColumnsSlice120 contact03ColumnsSlice124
private theorem contact03ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact03) 128 8 = 748202317796 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 4 4 412383616918 335818700878 contact03ColumnsSlice128 contact03ColumnsSlice132
private theorem contact03ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact03) 136 8 = 477288205457 :=
  combineSlices (auxiliaryColumnSlice contact03) 136 4 4 268098973305 209189232152 contact03ColumnsSlice136 contact03ColumnsSlice140
private theorem contact03ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact03) 144 8 = 276215366908 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 4 4 158993690558 117221676350 contact03ColumnsSlice144 contact03ColumnsSlice148
private theorem contact03ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact03) 152 8 = 140444617679 :=
  combineSlices (auxiliaryColumnSlice contact03) 152 4 4 83430861650 57013756029 contact03ColumnsSlice152 contact03ColumnsSlice156
private theorem contact03ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact03) 0 16 = 27959186684052 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 8 8 14679497002892 13279689681160 contact03ColumnsJoin0_8 contact03ColumnsJoin8_8
private theorem contact03ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact03) 16 16 = 22642100139823 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 8 8 11950421806856 10691678332967 contact03ColumnsJoin16_8 contact03ColumnsJoin24_8
private theorem contact03ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact03) 32 16 = 17889182499799 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 8 8 9503418567959 8385763931840 contact03ColumnsJoin32_8 contact03ColumnsJoin40_8
private theorem contact03ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact03) 48 16 = 13700627379374 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 8 8 7338595036796 6362032342578 contact03ColumnsJoin48_8 contact03ColumnsJoin56_8
private theorem contact03ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact03) 64 16 = 10076578176399 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 8 8 5456027913160 4620550263239 contact03ColumnsJoin64_8 contact03ColumnsJoin72_8
private theorem contact03ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact03) 80 16 = 7017048349354 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 8 8 3855700658432 3161347690922 contact03ColumnsJoin80_8 contact03ColumnsJoin88_8
private theorem contact03ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact03) 96 16 = 4522032942370 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 8 8 2537612401514 1984420540856 contact03ColumnsJoin96_8 contact03ColumnsJoin104_8
private theorem contact03ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact03) 112 16 = 2591507134787 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 8 8 1501769244212 1089737890575 contact03ColumnsJoin112_8 contact03ColumnsJoin120_8
private theorem contact03ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact03) 128 16 = 1225490523253 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 8 8 748202317796 477288205457 contact03ColumnsJoin128_8 contact03ColumnsJoin136_8
private theorem contact03ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact03) 144 16 = 416659984587 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 8 8 276215366908 140444617679 contact03ColumnsJoin144_8 contact03ColumnsJoin152_8
private theorem contact03ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact03) 0 32 = 50601286823875 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 16 16 27959186684052 22642100139823 contact03ColumnsJoin0_16 contact03ColumnsJoin16_16
private theorem contact03ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact03) 32 32 = 31589809879173 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 16 16 17889182499799 13700627379374 contact03ColumnsJoin32_16 contact03ColumnsJoin48_16
private theorem contact03ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact03) 64 32 = 17093626525753 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 16 16 10076578176399 7017048349354 contact03ColumnsJoin64_16 contact03ColumnsJoin80_16
private theorem contact03ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact03) 96 32 = 7113540077157 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 16 16 4522032942370 2591507134787 contact03ColumnsJoin96_16 contact03ColumnsJoin112_16
private theorem contact03ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact03) 128 32 = 1642150507840 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 16 16 1225490523253 416659984587 contact03ColumnsJoin128_16 contact03ColumnsJoin144_16
private theorem contact03ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact03) 0 64 = 82191096703048 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 32 32 50601286823875 31589809879173 contact03ColumnsJoin0_32 contact03ColumnsJoin32_32
private theorem contact03ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact03) 64 64 = 24207166602910 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 32 32 17093626525753 7113540077157 contact03ColumnsJoin64_32 contact03ColumnsJoin96_32
private theorem contact03ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact03) 128 36 = 1679306821841 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 32 4 1642150507840 37156314001 contact03ColumnsJoin128_32 contact03ColumnsSlice160
private theorem contact03ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact03) 0 128 = 106398263305958 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 64 64 82191096703048 24207166602910 contact03ColumnsJoin0_64 contact03ColumnsJoin64_64
private theorem contact03ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact03) 0 164 = 108077570127799 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 128 36 106398263305958 1679306821841 contact03ColumnsJoin0_128 contact03ColumnsJoin128_36
private theorem contact03OrdinaryRanks : ordinaryRankBound contact03 = 8664840493 := by decide +kernel
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
  margin_of_checked_counts contact03 164 2248980451501511 108077570127799 8664840493 326617835 rfl contact03OrdinaryColumns contact03ColumnsJoin0_164 contact03OrdinaryRanks contact03RanksJoin0_164 (by decide +kernel)

private theorem contact05OrdinaryColumns : ordinaryColumnCount contact05 = 2146142837690364 := by decide +kernel
private theorem contact05ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact05) 0 4 = 7743515803990 :=
  contactColumnsWindow_fast contact05 0 4 7743515803990 (by decide +kernel)
private theorem contact05ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact05) 4 4 = 7373051591238 :=
  contactColumnsWindow_fast contact05 4 4 7373051591238 (by decide +kernel)
private theorem contact05ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact05) 8 4 = 7011704133110 :=
  contactColumnsWindow_fast contact05 8 4 7011704133110 (by decide +kernel)
private theorem contact05ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact05) 12 4 = 6659473660167 :=
  contactColumnsWindow_fast contact05 12 4 6659473660167 (by decide +kernel)
private theorem contact05ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact05) 16 4 = 6316394999550 :=
  contactColumnsWindow_fast contact05 16 4 6316394999550 (by decide +kernel)
private theorem contact05ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact05) 20 4 = 5982453519164 :=
  contactColumnsWindow_fast contact05 20 4 5982453519164 (by decide +kernel)
private theorem contact05ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact05) 24 4 = 5657632538350 :=
  contactColumnsWindow_fast contact05 24 4 5657632538350 (by decide +kernel)
private theorem contact05ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact05) 28 4 = 5341930684326 :=
  contactColumnsWindow_fast contact05 28 4 5341930684326 (by decide +kernel)
private theorem contact05ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact05) 32 4 = 5035351041701 :=
  contactColumnsWindow_fast contact05 32 4 5035351041701 (by decide +kernel)
private theorem contact05ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact05) 36 4 = 4737927829670 :=
  contactColumnsWindow_fast contact05 36 4 4737927829670 (by decide +kernel)
private theorem contact05ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact05) 40 4 = 4449642755046 :=
  contactColumnsWindow_fast contact05 40 4 4449642755046 (by decide +kernel)
private theorem contact05ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact05) 44 4 = 4170480104617 :=
  contactColumnsWindow_fast contact05 44 4 4170480104617 (by decide +kernel)
private theorem contact05ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact05) 48 4 = 3900441170634 :=
  contactColumnsWindow_fast contact05 48 4 3900441170634 (by decide +kernel)
private theorem contact05ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact05) 52 4 = 3639527905077 :=
  contactColumnsWindow_fast contact05 52 4 3639527905077 (by decide +kernel)
private theorem contact05ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact05) 56 4 = 3387778116513 :=
  contactColumnsWindow_fast contact05 56 4 3387778116513 (by decide +kernel)
private theorem contact05ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact05) 60 4 = 3145165944790 :=
  contactColumnsWindow_fast contact05 60 4 3145165944790 (by decide +kernel)
private theorem contact05ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact05) 64 4 = 2911679718279 :=
  contactColumnsWindow_fast contact05 64 4 2911679718279 (by decide +kernel)
private theorem contact05ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact05) 68 4 = 2687317168070 :=
  contactColumnsWindow_fast contact05 68 4 2687317168070 (by decide +kernel)
private theorem contact05ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact05) 72 4 = 2472082660794 :=
  contactColumnsWindow_fast contact05 72 4 2472082660794 (by decide +kernel)
private theorem contact05ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact05) 76 4 = 2266012255775 :=
  contactColumnsWindow_fast contact05 76 4 2266012255775 (by decide +kernel)
private theorem contact05ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact05) 80 4 = 2069077059950 :=
  contactColumnsWindow_fast contact05 80 4 2069077059950 (by decide +kernel)
private theorem contact05ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact05) 84 4 = 1881267299710 :=
  contactColumnsWindow_fast contact05 84 4 1881267299710 (by decide +kernel)
private theorem contact05ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact05) 88 4 = 1702581209857 :=
  contactColumnsWindow_fast contact05 88 4 1702581209857 (by decide +kernel)
private theorem contact05ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact05) 92 4 = 1533025822662 :=
  contactColumnsWindow_fast contact05 92 4 1533025822662 (by decide +kernel)
private theorem contact05ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact05) 96 4 = 1372634352166 :=
  contactColumnsWindow_fast contact05 96 4 1372634352166 (by decide +kernel)
private theorem contact05ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact05) 100 4 = 1221376161236 :=
  contactColumnsWindow_fast contact05 100 4 1221376161236 (by decide +kernel)
private theorem contact05ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact05) 104 4 = 1079243030158 :=
  contactColumnsWindow_fast contact05 104 4 1079243030158 (by decide +kernel)
private theorem contact05ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact05) 108 4 = 946233193611 :=
  contactColumnsWindow_fast contact05 108 4 946233193611 (by decide +kernel)
private theorem contact05ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact05) 112 4 = 822356977901 :=
  contactColumnsWindow_fast contact05 112 4 822356977901 (by decide +kernel)
private theorem contact05ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact05) 116 4 = 707644688797 :=
  contactColumnsWindow_fast contact05 116 4 707644688797 (by decide +kernel)
private theorem contact05ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact05) 120 4 = 602063257696 :=
  contactColumnsWindow_fast contact05 120 4 602063257696 (by decide +kernel)
private theorem contact05ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact05) 124 4 = 505606686022 :=
  contactColumnsWindow_fast contact05 124 4 505606686022 (by decide +kernel)
private theorem contact05ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact05) 128 4 = 418273251152 :=
  contactColumnsWindow_fast contact05 128 4 418273251152 (by decide +kernel)
private theorem contact05ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact05) 132 4 = 340077370551 :=
  contactColumnsWindow_fast contact05 132 4 340077370551 (by decide +kernel)
private theorem contact05ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact05) 136 4 = 271043010284 :=
  contactColumnsWindow_fast contact05 136 4 271043010284 (by decide +kernel)
private theorem contact05ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact05) 140 4 = 211125476216 :=
  contactColumnsWindow_fast contact05 140 4 211125476216 (by decide +kernel)
private theorem contact05ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact05) 144 4 = 160186044394 :=
  contactColumnsWindow_fast contact05 144 4 160186044394 (by decide +kernel)
private theorem contact05ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact05) 148 4 = 117889582570 :=
  contactColumnsWindow_fast contact05 148 4 117889582570 (by decide +kernel)
private theorem contact05ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact05) 152 4 = 83756681046 :=
  contactColumnsWindow_fast contact05 152 4 83756681046 (by decide +kernel)
private theorem contact05ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact05) 156 4 = 57141197023 :=
  contactColumnsWindow_fast contact05 156 4 57141197023 (by decide +kernel)
private theorem contact05ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact05) 160 4 = 37189023651 :=
  contactColumnsWindow_fast contact05 160 4 37189023651 (by decide +kernel)
private theorem contact05ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact05) 164 1 = 6868787285 :=
  contactColumnsWindow_fast contact05 164 1 6868787285 (by decide +kernel)
private theorem contact05ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact05) 0 8 = 15116567395228 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 4 4 7743515803990 7373051591238 contact05ColumnsSlice0 contact05ColumnsSlice4
private theorem contact05ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact05) 8 8 = 13671177793277 :=
  combineSlices (auxiliaryColumnSlice contact05) 8 4 4 7011704133110 6659473660167 contact05ColumnsSlice8 contact05ColumnsSlice12
private theorem contact05ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact05) 16 8 = 12298848518714 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 4 4 6316394999550 5982453519164 contact05ColumnsSlice16 contact05ColumnsSlice20
private theorem contact05ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact05) 24 8 = 10999563222676 :=
  combineSlices (auxiliaryColumnSlice contact05) 24 4 4 5657632538350 5341930684326 contact05ColumnsSlice24 contact05ColumnsSlice28
private theorem contact05ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact05) 32 8 = 9773278871371 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 4 4 5035351041701 4737927829670 contact05ColumnsSlice32 contact05ColumnsSlice36
private theorem contact05ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact05) 40 8 = 8620122859663 :=
  combineSlices (auxiliaryColumnSlice contact05) 40 4 4 4449642755046 4170480104617 contact05ColumnsSlice40 contact05ColumnsSlice44
private theorem contact05ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact05) 48 8 = 7539969075711 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 4 4 3900441170634 3639527905077 contact05ColumnsSlice48 contact05ColumnsSlice52
private theorem contact05ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact05) 56 8 = 6532944061303 :=
  combineSlices (auxiliaryColumnSlice contact05) 56 4 4 3387778116513 3145165944790 contact05ColumnsSlice56 contact05ColumnsSlice60
private theorem contact05ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact05) 64 8 = 5598996886349 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 4 4 2911679718279 2687317168070 contact05ColumnsSlice64 contact05ColumnsSlice68
private theorem contact05ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact05) 72 8 = 4738094916569 :=
  combineSlices (auxiliaryColumnSlice contact05) 72 4 4 2472082660794 2266012255775 contact05ColumnsSlice72 contact05ColumnsSlice76
private theorem contact05ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact05) 80 8 = 3950344359660 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 4 4 2069077059950 1881267299710 contact05ColumnsSlice80 contact05ColumnsSlice84
private theorem contact05ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact05) 88 8 = 3235607032519 :=
  combineSlices (auxiliaryColumnSlice contact05) 88 4 4 1702581209857 1533025822662 contact05ColumnsSlice88 contact05ColumnsSlice92
private theorem contact05ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact05) 96 8 = 2594010513402 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 4 4 1372634352166 1221376161236 contact05ColumnsSlice96 contact05ColumnsSlice100
private theorem contact05ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact05) 104 8 = 2025476223769 :=
  combineSlices (auxiliaryColumnSlice contact05) 104 4 4 1079243030158 946233193611 contact05ColumnsSlice104 contact05ColumnsSlice108
private theorem contact05ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact05) 112 8 = 1530001666698 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 4 4 822356977901 707644688797 contact05ColumnsSlice112 contact05ColumnsSlice116
private theorem contact05ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact05) 120 8 = 1107669943718 :=
  combineSlices (auxiliaryColumnSlice contact05) 120 4 4 602063257696 505606686022 contact05ColumnsSlice120 contact05ColumnsSlice124
private theorem contact05ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact05) 128 8 = 758350621703 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 4 4 418273251152 340077370551 contact05ColumnsSlice128 contact05ColumnsSlice132
private theorem contact05ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact05) 136 8 = 482168486500 :=
  combineSlices (auxiliaryColumnSlice contact05) 136 4 4 271043010284 211125476216 contact05ColumnsSlice136 contact05ColumnsSlice140
private theorem contact05ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact05) 144 8 = 278075626964 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 4 4 160186044394 117889582570 contact05ColumnsSlice144 contact05ColumnsSlice148
private theorem contact05ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact05) 152 8 = 140897878069 :=
  combineSlices (auxiliaryColumnSlice contact05) 152 4 4 83756681046 57141197023 contact05ColumnsSlice152 contact05ColumnsSlice156
private theorem contact05ColumnsJoin160_5 : sliceWindow (auxiliaryColumnSlice contact05) 160 5 = 44057810936 :=
  combineSlices (auxiliaryColumnSlice contact05) 160 4 1 37189023651 6868787285 contact05ColumnsSlice160 contact05ColumnsSlice164
private theorem contact05ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact05) 0 16 = 28787745188505 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 8 8 15116567395228 13671177793277 contact05ColumnsJoin0_8 contact05ColumnsJoin8_8
private theorem contact05ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact05) 16 16 = 23298411741390 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 8 8 12298848518714 10999563222676 contact05ColumnsJoin16_8 contact05ColumnsJoin24_8
private theorem contact05ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact05) 32 16 = 18393401731034 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 8 8 9773278871371 8620122859663 contact05ColumnsJoin32_8 contact05ColumnsJoin40_8
private theorem contact05ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact05) 48 16 = 14072913137014 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 8 8 7539969075711 6532944061303 contact05ColumnsJoin48_8 contact05ColumnsJoin56_8
private theorem contact05ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact05) 64 16 = 10337091802918 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 8 8 5598996886349 4738094916569 contact05ColumnsJoin64_8 contact05ColumnsJoin72_8
private theorem contact05ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact05) 80 16 = 7185951392179 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 8 8 3950344359660 3235607032519 contact05ColumnsJoin80_8 contact05ColumnsJoin88_8
private theorem contact05ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact05) 96 16 = 4619486737171 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 8 8 2594010513402 2025476223769 contact05ColumnsJoin96_8 contact05ColumnsJoin104_8
private theorem contact05ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact05) 112 16 = 2637671610416 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 8 8 1530001666698 1107669943718 contact05ColumnsJoin112_8 contact05ColumnsJoin120_8
private theorem contact05ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact05) 128 16 = 1240519108203 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 8 8 758350621703 482168486500 contact05ColumnsJoin128_8 contact05ColumnsJoin136_8
private theorem contact05ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact05) 144 16 = 418973505033 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 8 8 278075626964 140897878069 contact05ColumnsJoin144_8 contact05ColumnsJoin152_8
private theorem contact05ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact05) 0 32 = 52086156929895 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 16 16 28787745188505 23298411741390 contact05ColumnsJoin0_16 contact05ColumnsJoin16_16
private theorem contact05ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact05) 32 32 = 32466314868048 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 16 16 18393401731034 14072913137014 contact05ColumnsJoin32_16 contact05ColumnsJoin48_16
private theorem contact05ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact05) 64 32 = 17523043195097 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 16 16 10337091802918 7185951392179 contact05ColumnsJoin64_16 contact05ColumnsJoin80_16
private theorem contact05ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact05) 96 32 = 7257158347587 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 16 16 4619486737171 2637671610416 contact05ColumnsJoin96_16 contact05ColumnsJoin112_16
private theorem contact05ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact05) 128 32 = 1659492613236 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 16 16 1240519108203 418973505033 contact05ColumnsJoin128_16 contact05ColumnsJoin144_16
private theorem contact05ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact05) 0 64 = 84552471797943 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 32 32 52086156929895 32466314868048 contact05ColumnsJoin0_32 contact05ColumnsJoin32_32
private theorem contact05ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact05) 64 64 = 24780201542684 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 32 32 17523043195097 7257158347587 contact05ColumnsJoin64_32 contact05ColumnsJoin96_32
private theorem contact05ColumnsJoin128_37 : sliceWindow (auxiliaryColumnSlice contact05) 128 37 = 1703550424172 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 32 5 1659492613236 44057810936 contact05ColumnsJoin128_32 contact05ColumnsJoin160_5
private theorem contact05ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact05) 0 128 = 109332673340627 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 64 64 84552471797943 24780201542684 contact05ColumnsJoin0_64 contact05ColumnsJoin64_64
private theorem contact05ColumnsJoin0_165 : sliceWindow (auxiliaryColumnSlice contact05) 0 165 = 111036223764799 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 128 37 109332673340627 1703550424172 contact05ColumnsJoin0_128 contact05ColumnsJoin128_37
private theorem contact05OrdinaryRanks : ordinaryRankBound contact05 = 8274231376 := by decide +kernel
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
private theorem contact05RanksSlice152 : sliceWindow (auxiliaryRankSlice contact05) 152 13 = 0 :=
  contactRankWindow_of_rec contact05 152 13 0 (by decide +kernel)
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
private theorem contact05RanksJoin144_21 : sliceWindow (auxiliaryRankSlice contact05) 144 21 = 18067 :=
  combineSlices (auxiliaryRankSlice contact05) 144 8 13 18067 0 contact05RanksJoin144_8 contact05RanksSlice152
private theorem contact05RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact05) 0 32 = 185982544 :=
  combineSlices (auxiliaryRankSlice contact05) 0 16 16 106053800 79928744 contact05RanksJoin0_16 contact05RanksJoin16_16
private theorem contact05RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact05) 32 32 = 97635070 :=
  combineSlices (auxiliaryRankSlice contact05) 32 16 16 57842344 39792726 contact05RanksJoin32_16 contact05RanksJoin48_16
private theorem contact05RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact05) 64 32 = 40874783 :=
  combineSlices (auxiliaryRankSlice contact05) 64 16 16 25689111 15185672 contact05RanksJoin64_16 contact05RanksJoin80_16
private theorem contact05RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact05) 96 32 = 10990212 :=
  combineSlices (auxiliaryRankSlice contact05) 96 16 16 7829277 3160935 contact05RanksJoin96_16 contact05RanksJoin112_16
private theorem contact05RanksJoin128_37 : sliceWindow (auxiliaryRankSlice contact05) 128 37 = 739723 :=
  combineSlices (auxiliaryRankSlice contact05) 128 16 21 721656 18067 contact05RanksJoin128_16 contact05RanksJoin144_21
private theorem contact05RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact05) 0 64 = 283617614 :=
  combineSlices (auxiliaryRankSlice contact05) 0 32 32 185982544 97635070 contact05RanksJoin0_32 contact05RanksJoin32_32
private theorem contact05RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact05) 64 64 = 51864995 :=
  combineSlices (auxiliaryRankSlice contact05) 64 32 32 40874783 10990212 contact05RanksJoin64_32 contact05RanksJoin96_32
private theorem contact05RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact05) 0 128 = 335482609 :=
  combineSlices (auxiliaryRankSlice contact05) 0 64 64 283617614 51864995 contact05RanksJoin0_64 contact05RanksJoin64_64
private theorem contact05RanksJoin0_165 : sliceWindow (auxiliaryRankSlice contact05) 0 165 = 336222332 :=
  combineSlices (auxiliaryRankSlice contact05) 0 128 37 335482609 739723 contact05RanksJoin0_128 contact05RanksJoin128_37
theorem contact05_margin : sourceMargin contact05 :=
  margin_of_checked_counts contact05 165 2146142837690364 111036223764799 8274231376 336222332 rfl contact05OrdinaryColumns contact05ColumnsJoin0_165 contact05OrdinaryRanks contact05RanksJoin0_165 (by decide +kernel)

private theorem contact07OrdinaryColumns : ordinaryColumnCount contact07 = 2057166296419432 := by decide +kernel
private theorem contact07ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact07) 0 4 = 8153142127966 :=
  contactColumnsWindow_fast contact07 0 4 8153142127966 (by decide +kernel)
private theorem contact07ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact07) 4 4 = 7760973471086 :=
  contactColumnsWindow_fast contact07 4 4 7760973471086 (by decide +kernel)
private theorem contact07ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact07) 8 4 = 7378513262606 :=
  contactColumnsWindow_fast contact07 8 4 7378513262606 (by decide +kernel)
private theorem contact07ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact07) 12 4 = 7005761765779 :=
  contactColumnsWindow_fast contact07 12 4 7005761765779 (by decide +kernel)
private theorem contact07ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact07) 16 4 = 6642756956678 :=
  contactColumnsWindow_fast contact07 16 4 6642756956678 (by decide +kernel)
private theorem contact07ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact07) 20 4 = 6289482813345 :=
  contactColumnsWindow_fast contact07 20 4 6289482813345 (by decide +kernel)
private theorem contact07ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact07) 24 4 = 5945921011606 :=
  contactColumnsWindow_fast contact07 24 4 5945921011606 (by decide +kernel)
private theorem contact07ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact07) 28 4 = 5612070122542 :=
  contactColumnsWindow_fast contact07 28 4 5612070122542 (by decide +kernel)
private theorem contact07ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact07) 32 4 = 5287933432001 :=
  contactColumnsWindow_fast contact07 32 4 5287933432001 (by decide +kernel)
private theorem contact07ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact07) 36 4 = 4973548355922 :=
  contactColumnsWindow_fast contact07 36 4 4973548355922 (by decide +kernel)
private theorem contact07ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact07) 40 4 = 4668894727462 :=
  contactColumnsWindow_fast contact07 40 4 4668894727462 (by decide +kernel)
private theorem contact07ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact07) 44 4 = 4373955429873 :=
  contactColumnsWindow_fast contact07 44 4 4373955429873 (by decide +kernel)
private theorem contact07ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact07) 48 4 = 4088731794038 :=
  contactColumnsWindow_fast contact07 48 4 4088731794038 (by decide +kernel)
private theorem contact07ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact07) 52 4 = 3813226000526 :=
  contactColumnsWindow_fast contact07 52 4 3813226000526 (by decide +kernel)
private theorem contact07ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact07) 56 4 = 3547479252049 :=
  contactColumnsWindow_fast contact07 56 4 3547479252049 (by decide +kernel)
private theorem contact07ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact07) 60 4 = 3291463191274 :=
  contactColumnsWindow_fast contact07 60 4 3291463191274 (by decide +kernel)
private theorem contact07ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact07) 64 4 = 3045165092927 :=
  contactColumnsWindow_fast contact07 64 4 3045165092927 (by decide +kernel)
private theorem contact07ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact07) 68 4 = 2808582616190 :=
  contactColumnsWindow_fast contact07 68 4 2808582616190 (by decide +kernel)
private theorem contact07ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact07) 72 4 = 2581720558762 :=
  contactColumnsWindow_fast contact07 72 4 2581720558762 (by decide +kernel)
private theorem contact07ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact07) 76 4 = 2364618238367 :=
  contactColumnsWindow_fast contact07 76 4 2364618238367 (by decide +kernel)
private theorem contact07ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact07) 80 4 = 2157243948886 :=
  contactColumnsWindow_fast contact07 80 4 2157243948886 (by decide +kernel)
private theorem contact07ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact07) 84 4 = 1959587093746 :=
  contactColumnsWindow_fast contact07 84 4 1959587093746 (by decide +kernel)
private theorem contact07ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact07) 88 4 = 1771645855426 :=
  contactColumnsWindow_fast contact07 88 4 1771645855426 (by decide +kernel)
private theorem contact07ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact07) 92 4 = 1593427929918 :=
  contactColumnsWindow_fast contact07 92 4 1593427929918 (by decide +kernel)
private theorem contact07ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact07) 96 4 = 1424969551157 :=
  contactColumnsWindow_fast contact07 96 4 1424969551157 (by decide +kernel)
private theorem contact07ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact07) 100 4 = 1266237063289 :=
  contactColumnsWindow_fast contact07 100 4 1266237063289 (by decide +kernel)
private theorem contact07ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact07) 104 4 = 1117221620390 :=
  contactColumnsWindow_fast contact07 104 4 1117221620390 (by decide +kernel)
private theorem contact07ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact07) 108 4 = 977921405682 :=
  contactColumnsWindow_fast contact07 108 4 977921405682 (by decide +kernel)
private theorem contact07ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact07) 112 4 = 848347667953 :=
  contactColumnsWindow_fast contact07 112 4 848347667953 (by decide +kernel)
private theorem contact07ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact07) 116 4 = 728533484142 :=
  contactColumnsWindow_fast contact07 116 4 728533484142 (by decide +kernel)
private theorem contact07ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact07) 120 4 = 618442543987 :=
  contactColumnsWindow_fast contact07 120 4 618442543987 (by decide +kernel)
private theorem contact07ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact07) 124 4 = 518068440834 :=
  contactColumnsWindow_fast contact07 124 4 518068440834 (by decide +kernel)
private theorem contact07ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact07) 128 4 = 427409403045 :=
  contactColumnsWindow_fast contact07 128 4 427409403045 (by decide +kernel)
private theorem contact07ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact07) 132 4 = 346481127091 :=
  contactColumnsWindow_fast contact07 132 4 346481127091 (by decide +kernel)
private theorem contact07ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact07) 136 4 = 275308615926 :=
  contactColumnsWindow_fast contact07 136 4 275308615926 (by decide +kernel)
private theorem contact07ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact07) 140 4 = 213806401002 :=
  contactColumnsWindow_fast contact07 140 4 213806401002 (by decide +kernel)
private theorem contact07ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact07) 144 4 = 161737545844 :=
  contactColumnsWindow_fast contact07 144 4 161737545844 (by decide +kernel)
private theorem contact07ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact07) 148 4 = 118687029796 :=
  contactColumnsWindow_fast contact07 148 4 118687029796 (by decide +kernel)
private theorem contact07ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact07) 152 4 = 84099843571 :=
  contactColumnsWindow_fast contact07 152 4 84099843571 (by decide +kernel)
private theorem contact07ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact07) 156 4 = 57252298565 :=
  contactColumnsWindow_fast contact07 156 4 57252298565 (by decide +kernel)
private theorem contact07ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact07) 160 2 = 20724953602 :=
  contactColumnsWindow_fast contact07 160 2 20724953602 (by decide +kernel)
private theorem contact07ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact07) 0 8 = 15914115599052 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 4 4 8153142127966 7760973471086 contact07ColumnsSlice0 contact07ColumnsSlice4
private theorem contact07ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact07) 8 8 = 14384275028385 :=
  combineSlices (auxiliaryColumnSlice contact07) 8 4 4 7378513262606 7005761765779 contact07ColumnsSlice8 contact07ColumnsSlice12
private theorem contact07ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact07) 16 8 = 12932239770023 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 4 4 6642756956678 6289482813345 contact07ColumnsSlice16 contact07ColumnsSlice20
private theorem contact07ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact07) 24 8 = 11557991134148 :=
  combineSlices (auxiliaryColumnSlice contact07) 24 4 4 5945921011606 5612070122542 contact07ColumnsSlice24 contact07ColumnsSlice28
private theorem contact07ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact07) 32 8 = 10261481787923 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 4 4 5287933432001 4973548355922 contact07ColumnsSlice32 contact07ColumnsSlice36
private theorem contact07ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact07) 40 8 = 9042850157335 :=
  combineSlices (auxiliaryColumnSlice contact07) 40 4 4 4668894727462 4373955429873 contact07ColumnsSlice40 contact07ColumnsSlice44
private theorem contact07ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact07) 48 8 = 7901957794564 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 4 4 4088731794038 3813226000526 contact07ColumnsSlice48 contact07ColumnsSlice52
private theorem contact07ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact07) 56 8 = 6838942443323 :=
  combineSlices (auxiliaryColumnSlice contact07) 56 4 4 3547479252049 3291463191274 contact07ColumnsSlice56 contact07ColumnsSlice60
private theorem contact07ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact07) 64 8 = 5853747709117 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 4 4 3045165092927 2808582616190 contact07ColumnsSlice64 contact07ColumnsSlice68
private theorem contact07ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact07) 72 8 = 4946338797129 :=
  combineSlices (auxiliaryColumnSlice contact07) 72 4 4 2581720558762 2364618238367 contact07ColumnsSlice72 contact07ColumnsSlice76
private theorem contact07ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact07) 80 8 = 4116831042632 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 4 4 2157243948886 1959587093746 contact07ColumnsSlice80 contact07ColumnsSlice84
private theorem contact07ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact07) 88 8 = 3365073785344 :=
  combineSlices (auxiliaryColumnSlice contact07) 88 4 4 1771645855426 1593427929918 contact07ColumnsSlice88 contact07ColumnsSlice92
private theorem contact07ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact07) 96 8 = 2691206614446 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 4 4 1424969551157 1266237063289 contact07ColumnsSlice96 contact07ColumnsSlice100
private theorem contact07ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact07) 104 8 = 2095143026072 :=
  combineSlices (auxiliaryColumnSlice contact07) 104 4 4 1117221620390 977921405682 contact07ColumnsSlice104 contact07ColumnsSlice108
private theorem contact07ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact07) 112 8 = 1576881152095 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 4 4 848347667953 728533484142 contact07ColumnsSlice112 contact07ColumnsSlice116
private theorem contact07ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact07) 120 8 = 1136510984821 :=
  combineSlices (auxiliaryColumnSlice contact07) 120 4 4 618442543987 518068440834 contact07ColumnsSlice120 contact07ColumnsSlice124
private theorem contact07ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact07) 128 8 = 773890530136 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 4 4 427409403045 346481127091 contact07ColumnsSlice128 contact07ColumnsSlice132
private theorem contact07ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact07) 136 8 = 489115016928 :=
  combineSlices (auxiliaryColumnSlice contact07) 136 4 4 275308615926 213806401002 contact07ColumnsSlice136 contact07ColumnsSlice140
private theorem contact07ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact07) 144 8 = 280424575640 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 4 4 161737545844 118687029796 contact07ColumnsSlice144 contact07ColumnsSlice148
private theorem contact07ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact07) 152 8 = 141352142136 :=
  combineSlices (auxiliaryColumnSlice contact07) 152 4 4 84099843571 57252298565 contact07ColumnsSlice152 contact07ColumnsSlice156
private theorem contact07ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact07) 0 16 = 30298390627437 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 8 8 15914115599052 14384275028385 contact07ColumnsJoin0_8 contact07ColumnsJoin8_8
private theorem contact07ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact07) 16 16 = 24490230904171 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 8 8 12932239770023 11557991134148 contact07ColumnsJoin16_8 contact07ColumnsJoin24_8
private theorem contact07ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact07) 32 16 = 19304331945258 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 8 8 10261481787923 9042850157335 contact07ColumnsJoin32_8 contact07ColumnsJoin40_8
private theorem contact07ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact07) 48 16 = 14740900237887 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 8 8 7901957794564 6838942443323 contact07ColumnsJoin48_8 contact07ColumnsJoin56_8
private theorem contact07ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact07) 64 16 = 10800086506246 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 8 8 5853747709117 4946338797129 contact07ColumnsJoin64_8 contact07ColumnsJoin72_8
private theorem contact07ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact07) 80 16 = 7481904827976 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 8 8 4116831042632 3365073785344 contact07ColumnsJoin80_8 contact07ColumnsJoin88_8
private theorem contact07ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact07) 96 16 = 4786349640518 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 8 8 2691206614446 2095143026072 contact07ColumnsJoin96_8 contact07ColumnsJoin104_8
private theorem contact07ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact07) 112 16 = 2713392136916 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 8 8 1576881152095 1136510984821 contact07ColumnsJoin112_8 contact07ColumnsJoin120_8
private theorem contact07ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact07) 128 16 = 1263005547064 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 8 8 773890530136 489115016928 contact07ColumnsJoin128_8 contact07ColumnsJoin136_8
private theorem contact07ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact07) 144 16 = 421776717776 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 8 8 280424575640 141352142136 contact07ColumnsJoin144_8 contact07ColumnsJoin152_8
private theorem contact07ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact07) 0 32 = 54788621531608 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 16 16 30298390627437 24490230904171 contact07ColumnsJoin0_16 contact07ColumnsJoin16_16
private theorem contact07ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact07) 32 32 = 34045232183145 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 16 16 19304331945258 14740900237887 contact07ColumnsJoin32_16 contact07ColumnsJoin48_16
private theorem contact07ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact07) 64 32 = 18281991334222 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 16 16 10800086506246 7481904827976 contact07ColumnsJoin64_16 contact07ColumnsJoin80_16
private theorem contact07ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact07) 96 32 = 7499741777434 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 16 16 4786349640518 2713392136916 contact07ColumnsJoin96_16 contact07ColumnsJoin112_16
private theorem contact07ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact07) 128 32 = 1684782264840 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 16 16 1263005547064 421776717776 contact07ColumnsJoin128_16 contact07ColumnsJoin144_16
private theorem contact07ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact07) 0 64 = 88833853714753 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 32 32 54788621531608 34045232183145 contact07ColumnsJoin0_32 contact07ColumnsJoin32_32
private theorem contact07ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact07) 64 64 = 25781733111656 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 32 32 18281991334222 7499741777434 contact07ColumnsJoin64_32 contact07ColumnsJoin96_32
private theorem contact07ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact07) 128 34 = 1705507218442 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 32 2 1684782264840 20724953602 contact07ColumnsJoin128_32 contact07ColumnsSlice160
private theorem contact07ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact07) 0 128 = 114615586826409 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 64 64 88833853714753 25781733111656 contact07ColumnsJoin0_64 contact07ColumnsJoin64_64
private theorem contact07ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact07) 0 162 = 116321094044851 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 128 34 114615586826409 1705507218442 contact07ColumnsJoin0_128 contact07ColumnsJoin128_34
private theorem contact07OrdinaryRanks : ordinaryRankBound contact07 = 7937402063 := by decide +kernel
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
private theorem contact07RanksSlice152 : sliceWindow (auxiliaryRankSlice contact07) 152 10 = 0 :=
  contactRankWindow_of_rec contact07 152 10 0 (by decide +kernel)
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
private theorem contact07RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact07) 144 18 = 19027 :=
  combineSlices (auxiliaryRankSlice contact07) 144 8 10 19027 0 contact07RanksJoin144_8 contact07RanksSlice152
private theorem contact07RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact07) 0 32 = 195665712 :=
  combineSlices (auxiliaryRankSlice contact07) 0 16 16 111608856 84056856 contact07RanksJoin0_16 contact07RanksJoin16_16
private theorem contact07RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact07) 32 32 = 102655168 :=
  combineSlices (auxiliaryRankSlice contact07) 32 16 16 60805656 41849512 contact07RanksJoin32_16 contact07RanksJoin48_16
private theorem contact07RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact07) 64 32 = 43066603 :=
  combineSlices (auxiliaryRankSlice contact07) 64 16 16 27051185 16015418 contact07RanksJoin64_16 contact07RanksJoin80_16
private theorem contact07RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact07) 96 32 = 11617130 :=
  combineSlices (auxiliaryRankSlice contact07) 96 16 16 8271449 3345681 contact07RanksJoin96_16 contact07RanksJoin112_16
private theorem contact07RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact07) 128 34 = 783596 :=
  combineSlices (auxiliaryRankSlice contact07) 128 16 18 764569 19027 contact07RanksJoin128_16 contact07RanksJoin144_18
private theorem contact07RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact07) 0 64 = 298320880 :=
  combineSlices (auxiliaryRankSlice contact07) 0 32 32 195665712 102655168 contact07RanksJoin0_32 contact07RanksJoin32_32
private theorem contact07RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact07) 64 64 = 54683733 :=
  combineSlices (auxiliaryRankSlice contact07) 64 32 32 43066603 11617130 contact07RanksJoin64_32 contact07RanksJoin96_32
private theorem contact07RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact07) 0 128 = 353004613 :=
  combineSlices (auxiliaryRankSlice contact07) 0 64 64 298320880 54683733 contact07RanksJoin0_64 contact07RanksJoin64_64
private theorem contact07RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact07) 0 162 = 353788209 :=
  combineSlices (auxiliaryRankSlice contact07) 0 128 34 353004613 783596 contact07RanksJoin0_128 contact07RanksJoin128_34
theorem contact07_margin : sourceMargin contact07 :=
  margin_of_checked_counts contact07 162 2057166296419432 116321094044851 7937402063 353788209 rfl contact07OrdinaryColumns contact07ColumnsJoin0_162 contact07OrdinaryRanks contact07RanksJoin0_162 (by decide +kernel)

private theorem contact09OrdinaryColumns : ordinaryColumnCount contact09 = 2690601805393878 := by decide +kernel
private theorem contact09ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact09) 0 4 = 6674927890074 :=
  contactColumnsWindow_fast contact09 0 4 6674927890074 (by decide +kernel)
private theorem contact09ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact09) 4 4 = 6348056796666 :=
  contactColumnsWindow_fast contact09 4 4 6348056796666 (by decide +kernel)
private theorem contact09ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact09) 8 4 = 6029422316875 :=
  contactColumnsWindow_fast contact09 8 4 6029422316875 (by decide +kernel)
private theorem contact09ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact09) 12 4 = 5719027202744 :=
  contactColumnsWindow_fast contact09 12 4 5719027202744 (by decide +kernel)
private theorem contact09ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact09) 16 4 = 5416869579906 :=
  contactColumnsWindow_fast contact09 16 4 5416869579906 (by decide +kernel)
private theorem contact09ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact09) 20 4 = 5122951339114 :=
  contactColumnsWindow_fast contact09 20 4 5122951339114 (by decide +kernel)
private theorem contact09ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact09) 24 4 = 4837286222435 :=
  contactColumnsWindow_fast contact09 24 4 4837286222435 (by decide +kernel)
private theorem contact09ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact09) 28 4 = 4559891431295 :=
  contactColumnsWindow_fast contact09 28 4 4559891431295 (by decide +kernel)
private theorem contact09ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact09) 32 4 = 4290739054248 :=
  contactColumnsWindow_fast contact09 32 4 4290739054248 (by decide +kernel)
private theorem contact09ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact09) 36 4 = 4029827194829 :=
  contactColumnsWindow_fast contact09 36 4 4029827194829 (by decide +kernel)
private theorem contact09ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact09) 40 4 = 3777157668028 :=
  contactColumnsWindow_fast contact09 40 4 3777157668028 (by decide +kernel)
private theorem contact09ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact09) 44 4 = 3532747621719 :=
  contactColumnsWindow_fast contact09 44 4 3532747621719 (by decide +kernel)
private theorem contact09ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact09) 48 4 = 3296608692924 :=
  contactColumnsWindow_fast contact09 48 4 3296608692924 (by decide +kernel)
private theorem contact09ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact09) 52 4 = 3068713781943 :=
  contactColumnsWindow_fast contact09 52 4 3068713781943 (by decide +kernel)
private theorem contact09ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact09) 56 4 = 2849063527296 :=
  contactColumnsWindow_fast contact09 56 4 2849063527296 (by decide +kernel)
private theorem contact09ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact09) 60 4 = 2637657673701 :=
  contactColumnsWindow_fast contact09 60 4 2637657673701 (by decide +kernel)
private theorem contact09ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact09) 64 4 = 2434520254996 :=
  contactColumnsWindow_fast contact09 64 4 2434520254996 (by decide +kernel)
private theorem contact09ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact09) 68 4 = 2239651718845 :=
  contactColumnsWindow_fast contact09 68 4 2239651718845 (by decide +kernel)
private theorem contact09ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact09) 72 4 = 2053032008793 :=
  contactColumnsWindow_fast contact09 72 4 2053032008793 (by decide +kernel)
private theorem contact09ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact09) 76 4 = 1874657458719 :=
  contactColumnsWindow_fast contact09 76 4 1874657458719 (by decide +kernel)
private theorem contact09ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact09) 80 4 = 1704527090121 :=
  contactColumnsWindow_fast contact09 80 4 1704527090121 (by decide +kernel)
private theorem contact09ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact09) 84 4 = 1542669750035 :=
  contactColumnsWindow_fast contact09 84 4 1542669750035 (by decide +kernel)
private theorem contact09ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact09) 88 4 = 1389077318231 :=
  contactColumnsWindow_fast contact09 88 4 1389077318231 (by decide +kernel)
private theorem contact09ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact09) 92 4 = 1243733278729 :=
  contactColumnsWindow_fast contact09 92 4 1243733278729 (by decide +kernel)
private theorem contact09ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact09) 96 4 = 1106634396528 :=
  contactColumnsWindow_fast contact09 96 4 1106634396528 (by decide +kernel)
private theorem contact09ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact09) 100 4 = 977780444802 :=
  contactColumnsWindow_fast contact09 100 4 977780444802 (by decide +kernel)
private theorem contact09ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact09) 104 4 = 857202341579 :=
  contactColumnsWindow_fast contact09 104 4 857202341579 (by decide +kernel)
private theorem contact09ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact09) 108 4 = 744885986615 :=
  contactColumnsWindow_fast contact09 108 4 744885986615 (by decide +kernel)
private theorem contact09ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact09) 112 4 = 640817594781 :=
  contactColumnsWindow_fast contact09 112 4 640817594781 (by decide +kernel)
private theorem contact09ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact09) 116 4 = 544994451663 :=
  contactColumnsWindow_fast contact09 116 4 544994451663 (by decide +kernel)
private theorem contact09ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact09) 120 4 = 457417213238 :=
  contactColumnsWindow_fast contact09 120 4 457417213238 (by decide +kernel)
private theorem contact09ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact09) 124 4 = 378117936719 :=
  contactColumnsWindow_fast contact09 124 4 378117936719 (by decide +kernel)
private theorem contact09ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact09) 128 4 = 307077748951 :=
  contactColumnsWindow_fast contact09 128 4 307077748951 (by decide +kernel)
private theorem contact09ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact09) 132 4 = 244285122809 :=
  contactColumnsWindow_fast contact09 132 4 244285122809 (by decide +kernel)
private theorem contact09ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact09) 136 4 = 189735143898 :=
  contactColumnsWindow_fast contact09 136 4 189735143898 (by decide +kernel)
private theorem contact09ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact09) 140 4 = 143363710602 :=
  contactColumnsWindow_fast contact09 140 4 143363710602 (by decide +kernel)
private theorem contact09ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact09) 144 4 = 104946743492 :=
  contactColumnsWindow_fast contact09 144 4 104946743492 (by decide +kernel)
private theorem contact09ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact09) 148 4 = 74025166847 :=
  contactColumnsWindow_fast contact09 148 4 74025166847 (by decide +kernel)
private theorem contact09ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact09) 152 4 = 49994850900 :=
  contactColumnsWindow_fast contact09 152 4 49994850900 (by decide +kernel)
private theorem contact09ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact09) 156 4 = 32098097759 :=
  contactColumnsWindow_fast contact09 156 4 32098097759 (by decide +kernel)
private theorem contact09ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact09) 160 4 = 19422139697 :=
  contactColumnsWindow_fast contact09 160 4 19422139697 (by decide +kernel)
private theorem contact09ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact09) 0 8 = 13022984686740 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 4 4 6674927890074 6348056796666 contact09ColumnsSlice0 contact09ColumnsSlice4
private theorem contact09ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact09) 8 8 = 11748449519619 :=
  combineSlices (auxiliaryColumnSlice contact09) 8 4 4 6029422316875 5719027202744 contact09ColumnsSlice8 contact09ColumnsSlice12
private theorem contact09ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact09) 16 8 = 10539820919020 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 4 4 5416869579906 5122951339114 contact09ColumnsSlice16 contact09ColumnsSlice20
private theorem contact09ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact09) 24 8 = 9397177653730 :=
  combineSlices (auxiliaryColumnSlice contact09) 24 4 4 4837286222435 4559891431295 contact09ColumnsSlice24 contact09ColumnsSlice28
private theorem contact09ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact09) 32 8 = 8320566249077 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 4 4 4290739054248 4029827194829 contact09ColumnsSlice32 contact09ColumnsSlice36
private theorem contact09ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact09) 40 8 = 7309905289747 :=
  combineSlices (auxiliaryColumnSlice contact09) 40 4 4 3777157668028 3532747621719 contact09ColumnsSlice40 contact09ColumnsSlice44
private theorem contact09ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact09) 48 8 = 6365322474867 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 4 4 3296608692924 3068713781943 contact09ColumnsSlice48 contact09ColumnsSlice52
private theorem contact09ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact09) 56 8 = 5486721200997 :=
  combineSlices (auxiliaryColumnSlice contact09) 56 4 4 2849063527296 2637657673701 contact09ColumnsSlice56 contact09ColumnsSlice60
private theorem contact09ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact09) 64 8 = 4674171973841 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 4 4 2434520254996 2239651718845 contact09ColumnsSlice64 contact09ColumnsSlice68
private theorem contact09ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact09) 72 8 = 3927689467512 :=
  combineSlices (auxiliaryColumnSlice contact09) 72 4 4 2053032008793 1874657458719 contact09ColumnsSlice72 contact09ColumnsSlice76
private theorem contact09ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact09) 80 8 = 3247196840156 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 4 4 1704527090121 1542669750035 contact09ColumnsSlice80 contact09ColumnsSlice84
private theorem contact09ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact09) 88 8 = 2632810596960 :=
  combineSlices (auxiliaryColumnSlice contact09) 88 4 4 1389077318231 1243733278729 contact09ColumnsSlice88 contact09ColumnsSlice92
private theorem contact09ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact09) 96 8 = 2084414841330 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 4 4 1106634396528 977780444802 contact09ColumnsSlice96 contact09ColumnsSlice100
private theorem contact09ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact09) 104 8 = 1602088328194 :=
  combineSlices (auxiliaryColumnSlice contact09) 104 4 4 857202341579 744885986615 contact09ColumnsSlice104 contact09ColumnsSlice108
private theorem contact09ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact09) 112 8 = 1185812046444 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 4 4 640817594781 544994451663 contact09ColumnsSlice112 contact09ColumnsSlice116
private theorem contact09ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact09) 120 8 = 835535149957 :=
  combineSlices (auxiliaryColumnSlice contact09) 120 4 4 457417213238 378117936719 contact09ColumnsSlice120 contact09ColumnsSlice124
private theorem contact09ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact09) 128 8 = 551362871760 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 4 4 307077748951 244285122809 contact09ColumnsSlice128 contact09ColumnsSlice132
private theorem contact09ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact09) 136 8 = 333098854500 :=
  combineSlices (auxiliaryColumnSlice contact09) 136 4 4 189735143898 143363710602 contact09ColumnsSlice136 contact09ColumnsSlice140
private theorem contact09ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact09) 144 8 = 178971910339 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 4 4 104946743492 74025166847 contact09ColumnsSlice144 contact09ColumnsSlice148
private theorem contact09ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact09) 152 8 = 82092948659 :=
  combineSlices (auxiliaryColumnSlice contact09) 152 4 4 49994850900 32098097759 contact09ColumnsSlice152 contact09ColumnsSlice156
private theorem contact09ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact09) 0 16 = 24771434206359 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 8 8 13022984686740 11748449519619 contact09ColumnsJoin0_8 contact09ColumnsJoin8_8
private theorem contact09ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact09) 16 16 = 19936998572750 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 8 8 10539820919020 9397177653730 contact09ColumnsJoin16_8 contact09ColumnsJoin24_8
private theorem contact09ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact09) 32 16 = 15630471538824 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 8 8 8320566249077 7309905289747 contact09ColumnsJoin32_8 contact09ColumnsJoin40_8
private theorem contact09ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact09) 48 16 = 11852043675864 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 8 8 6365322474867 5486721200997 contact09ColumnsJoin48_8 contact09ColumnsJoin56_8
private theorem contact09ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact09) 64 16 = 8601861441353 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 8 8 4674171973841 3927689467512 contact09ColumnsJoin64_8 contact09ColumnsJoin72_8
private theorem contact09ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact09) 80 16 = 5880007437116 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 8 8 3247196840156 2632810596960 contact09ColumnsJoin80_8 contact09ColumnsJoin88_8
private theorem contact09ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact09) 96 16 = 3686503169524 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 8 8 2084414841330 1602088328194 contact09ColumnsJoin96_8 contact09ColumnsJoin104_8
private theorem contact09ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact09) 112 16 = 2021347196401 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 8 8 1185812046444 835535149957 contact09ColumnsJoin112_8 contact09ColumnsJoin120_8
private theorem contact09ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact09) 128 16 = 884461726260 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 8 8 551362871760 333098854500 contact09ColumnsJoin128_8 contact09ColumnsJoin136_8
private theorem contact09ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact09) 144 16 = 261064858998 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 8 8 178971910339 82092948659 contact09ColumnsJoin144_8 contact09ColumnsJoin152_8
private theorem contact09ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact09) 0 32 = 44708432779109 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 16 16 24771434206359 19936998572750 contact09ColumnsJoin0_16 contact09ColumnsJoin16_16
private theorem contact09ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact09) 32 32 = 27482515214688 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 16 16 15630471538824 11852043675864 contact09ColumnsJoin32_16 contact09ColumnsJoin48_16
private theorem contact09ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact09) 64 32 = 14481868878469 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 16 16 8601861441353 5880007437116 contact09ColumnsJoin64_16 contact09ColumnsJoin80_16
private theorem contact09ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact09) 96 32 = 5707850365925 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 16 16 3686503169524 2021347196401 contact09ColumnsJoin96_16 contact09ColumnsJoin112_16
private theorem contact09ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact09) 128 32 = 1145526585258 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 16 16 884461726260 261064858998 contact09ColumnsJoin128_16 contact09ColumnsJoin144_16
private theorem contact09ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact09) 0 64 = 72190947993797 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 32 32 44708432779109 27482515214688 contact09ColumnsJoin0_32 contact09ColumnsJoin32_32
private theorem contact09ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact09) 64 64 = 20189719244394 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 32 32 14481868878469 5707850365925 contact09ColumnsJoin64_32 contact09ColumnsJoin96_32
private theorem contact09ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact09) 128 36 = 1164948724955 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 32 4 1145526585258 19422139697 contact09ColumnsJoin128_32 contact09ColumnsSlice160
private theorem contact09ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact09) 0 128 = 92380667238191 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 64 64 72190947993797 20189719244394 contact09ColumnsJoin0_64 contact09ColumnsJoin64_64
private theorem contact09ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact09) 0 164 = 93545615963146 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 128 36 92380667238191 1164948724955 contact09ColumnsJoin0_128 contact09ColumnsJoin128_36
private theorem contact09OrdinaryRanks : ordinaryRankBound contact09 = 10338009975 := by decide +kernel
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
private theorem contact09RanksSlice148 : sliceWindow (auxiliaryRankSlice contact09) 148 16 = 0 :=
  contactRankWindow_of_rec contact09 148 16 0 (by decide +kernel)
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
private theorem contact09RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact09) 144 20 = 876 :=
  combineSlices (auxiliaryRankSlice contact09) 144 4 16 876 0 contact09RanksSlice144 contact09RanksSlice148
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
private theorem contact09RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact09) 128 36 = 370215 :=
  combineSlices (auxiliaryRankSlice contact09) 128 16 20 369339 876 contact09RanksJoin128_16 contact09RanksJoin144_20
private theorem contact09RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact09) 0 64 = 241380078 :=
  combineSlices (auxiliaryRankSlice contact09) 0 32 32 159467232 81912846 contact09RanksJoin0_32 contact09RanksJoin32_32
private theorem contact09RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact09) 64 64 = 40917900 :=
  combineSlices (auxiliaryRankSlice contact09) 64 32 32 32893765 8024135 contact09RanksJoin64_32 contact09RanksJoin96_32
private theorem contact09RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact09) 0 128 = 282297978 :=
  combineSlices (auxiliaryRankSlice contact09) 0 64 64 241380078 40917900 contact09RanksJoin0_64 contact09RanksJoin64_64
private theorem contact09RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact09) 0 164 = 282668193 :=
  combineSlices (auxiliaryRankSlice contact09) 0 128 36 282297978 370215 contact09RanksJoin0_128 contact09RanksJoin128_36
theorem contact09_margin : sourceMargin contact09 :=
  margin_of_checked_counts contact09 164 2690601805393878 93545615963146 10338009975 282668193 rfl contact09OrdinaryColumns contact09ColumnsJoin0_164 contact09OrdinaryRanks contact09RanksJoin0_164 (by decide +kernel)

private theorem contact11OrdinaryColumns : ordinaryColumnCount contact11 = 210602855885789 := by decide +kernel
private theorem contact11ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact11) 0 4 = 913657416804 :=
  contactColumnsWindow_fast contact11 0 4 913657416804 (by decide +kernel)
private theorem contact11ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact11) 4 4 = 839575639504 :=
  contactColumnsWindow_fast contact11 4 4 839575639504 (by decide +kernel)
private theorem contact11ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact11) 8 4 = 768655712468 :=
  contactColumnsWindow_fast contact11 8 4 768655712468 (by decide +kernel)
private theorem contact11ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact11) 12 4 = 700883518420 :=
  contactColumnsWindow_fast contact11 12 4 700883518420 (by decide +kernel)
private theorem contact11ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact11) 16 4 = 636256664148 :=
  contactColumnsWindow_fast contact11 16 4 636256664148 (by decide +kernel)
private theorem contact11ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact11) 20 4 = 574773745649 :=
  contactColumnsWindow_fast contact11 20 4 574773745649 (by decide +kernel)
private theorem contact11ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact11) 24 4 = 516439332236 :=
  contactColumnsWindow_fast contact11 24 4 516439332236 (by decide +kernel)
private theorem contact11ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact11) 28 4 = 461268176070 :=
  contactColumnsWindow_fast contact11 28 4 461268176070 (by decide +kernel)
private theorem contact11ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact11) 32 4 = 409246275595 :=
  contactColumnsWindow_fast contact11 32 4 409246275595 (by decide +kernel)
private theorem contact11ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact11) 36 4 = 360369790844 :=
  contactColumnsWindow_fast contact11 36 4 360369790844 (by decide +kernel)
private theorem contact11ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact11) 40 4 = 314637337223 :=
  contactColumnsWindow_fast contact11 40 4 314637337223 (by decide +kernel)
private theorem contact11ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact11) 44 4 = 272054412360 :=
  contactColumnsWindow_fast contact11 44 4 272054412360 (by decide +kernel)
private theorem contact11ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact11) 48 4 = 232634944756 :=
  contactColumnsWindow_fast contact11 48 4 232634944756 (by decide +kernel)
private theorem contact11ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact11) 52 4 = 196363569732 :=
  contactColumnsWindow_fast contact11 52 4 196363569732 (by decide +kernel)
private theorem contact11ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact11) 56 4 = 163237374580 :=
  contactColumnsWindow_fast contact11 56 4 163237374580 (by decide +kernel)
private theorem contact11ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact11) 60 4 = 133255385837 :=
  contactColumnsWindow_fast contact11 60 4 133255385837 (by decide +kernel)
private theorem contact11ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact11) 64 4 = 106424296745 :=
  contactColumnsWindow_fast contact11 64 4 106424296745 (by decide +kernel)
private theorem contact11ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact11) 68 4 = 82756246460 :=
  contactColumnsWindow_fast contact11 68 4 82756246460 (by decide +kernel)
private theorem contact11ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact11) 72 4 = 62235321260 :=
  contactColumnsWindow_fast contact11 72 4 62235321260 (by decide +kernel)
private theorem contact11ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact11) 76 4 = 44859415356 :=
  contactColumnsWindow_fast contact11 76 4 44859415356 (by decide +kernel)
private theorem contact11ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact11) 80 4 = 30627830188 :=
  contactColumnsWindow_fast contact11 80 4 30627830188 (by decide +kernel)
private theorem contact11ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact11) 84 4 = 19527004660 :=
  contactColumnsWindow_fast contact11 84 4 19527004660 (by decide +kernel)
private theorem contact11ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact11) 88 4 = 11419953166 :=
  contactColumnsWindow_fast contact11 88 4 11419953166 (by decide +kernel)
private theorem contact11ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact11) 92 4 = 5973052840 :=
  contactColumnsWindow_fast contact11 92 4 5973052840 (by decide +kernel)
private theorem contact11ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact11) 96 2 = 1648110083 :=
  contactColumnsWindow_fast contact11 96 2 1648110083 (by decide +kernel)
private theorem contact11ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact11) 0 8 = 1753233056308 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 4 4 913657416804 839575639504 contact11ColumnsSlice0 contact11ColumnsSlice4
private theorem contact11ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact11) 8 8 = 1469539230888 :=
  combineSlices (auxiliaryColumnSlice contact11) 8 4 4 768655712468 700883518420 contact11ColumnsSlice8 contact11ColumnsSlice12
private theorem contact11ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact11) 16 8 = 1211030409797 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 4 4 636256664148 574773745649 contact11ColumnsSlice16 contact11ColumnsSlice20
private theorem contact11ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact11) 24 8 = 977707508306 :=
  combineSlices (auxiliaryColumnSlice contact11) 24 4 4 516439332236 461268176070 contact11ColumnsSlice24 contact11ColumnsSlice28
private theorem contact11ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact11) 32 8 = 769616066439 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 4 4 409246275595 360369790844 contact11ColumnsSlice32 contact11ColumnsSlice36
private theorem contact11ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact11) 40 8 = 586691749583 :=
  combineSlices (auxiliaryColumnSlice contact11) 40 4 4 314637337223 272054412360 contact11ColumnsSlice40 contact11ColumnsSlice44
private theorem contact11ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact11) 48 8 = 428998514488 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 4 4 232634944756 196363569732 contact11ColumnsSlice48 contact11ColumnsSlice52
private theorem contact11ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact11) 56 8 = 296492760417 :=
  combineSlices (auxiliaryColumnSlice contact11) 56 4 4 163237374580 133255385837 contact11ColumnsSlice56 contact11ColumnsSlice60
private theorem contact11ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact11) 64 8 = 189180543205 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 4 4 106424296745 82756246460 contact11ColumnsSlice64 contact11ColumnsSlice68
private theorem contact11ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact11) 72 8 = 107094736616 :=
  combineSlices (auxiliaryColumnSlice contact11) 72 4 4 62235321260 44859415356 contact11ColumnsSlice72 contact11ColumnsSlice76
private theorem contact11ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact11) 80 8 = 50154834848 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 4 4 30627830188 19527004660 contact11ColumnsSlice80 contact11ColumnsSlice84
private theorem contact11ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact11) 88 8 = 17393006006 :=
  combineSlices (auxiliaryColumnSlice contact11) 88 4 4 11419953166 5973052840 contact11ColumnsSlice88 contact11ColumnsSlice92
private theorem contact11ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact11) 0 16 = 3222772287196 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 8 8 1753233056308 1469539230888 contact11ColumnsJoin0_8 contact11ColumnsJoin8_8
private theorem contact11ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact11) 16 16 = 2188737918103 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 8 8 1211030409797 977707508306 contact11ColumnsJoin16_8 contact11ColumnsJoin24_8
private theorem contact11ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact11) 32 16 = 1356307816022 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 8 8 769616066439 586691749583 contact11ColumnsJoin32_8 contact11ColumnsJoin40_8
private theorem contact11ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact11) 48 16 = 725491274905 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 8 8 428998514488 296492760417 contact11ColumnsJoin48_8 contact11ColumnsJoin56_8
private theorem contact11ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact11) 64 16 = 296275279821 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 8 8 189180543205 107094736616 contact11ColumnsJoin64_8 contact11ColumnsJoin72_8
private theorem contact11ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact11) 80 16 = 67547840854 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 8 8 50154834848 17393006006 contact11ColumnsJoin80_8 contact11ColumnsJoin88_8
private theorem contact11ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact11) 0 32 = 5411510205299 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 16 16 3222772287196 2188737918103 contact11ColumnsJoin0_16 contact11ColumnsJoin16_16
private theorem contact11ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact11) 32 32 = 2081799090927 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 16 16 1356307816022 725491274905 contact11ColumnsJoin32_16 contact11ColumnsJoin48_16
private theorem contact11ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact11) 64 32 = 363823120675 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 16 16 296275279821 67547840854 contact11ColumnsJoin64_16 contact11ColumnsJoin80_16
private theorem contact11ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact11) 0 64 = 7493309296226 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 32 32 5411510205299 2081799090927 contact11ColumnsJoin0_32 contact11ColumnsJoin32_32
private theorem contact11ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact11) 64 34 = 365471230758 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 32 2 363823120675 1648110083 contact11ColumnsJoin64_32 contact11ColumnsSlice96
private theorem contact11ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact11) 0 98 = 7858780526984 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 64 34 7493309296226 365471230758 contact11ColumnsJoin0_64 contact11ColumnsJoin64_34
private theorem contact11OrdinaryRanks : ordinaryRankBound contact11 = 809603213 := by decide +kernel
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
private theorem contact11RanksSlice88 : sliceWindow (auxiliaryRankSlice contact11) 88 10 = 0 :=
  contactRankWindow_of_rec contact11 88 10 0 (by decide +kernel)
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
private theorem contact11RanksJoin80_18 : sliceWindow (auxiliaryRankSlice contact11) 80 18 = 14200 :=
  combineSlices (auxiliaryRankSlice contact11) 80 8 10 14200 0 contact11RanksJoin80_8 contact11RanksSlice88
private theorem contact11RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact11) 0 32 = 18477920 :=
  combineSlices (auxiliaryRankSlice contact11) 0 16 16 11610800 6867120 contact11RanksJoin0_16 contact11RanksJoin16_16
private theorem contact11RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact11) 32 32 = 4925200 :=
  combineSlices (auxiliaryRankSlice contact11) 32 16 16 3507980 1417220 contact11RanksJoin32_16 contact11RanksJoin48_16
private theorem contact11RanksJoin64_34 : sliceWindow (auxiliaryRankSlice contact11) 64 34 = 358555 :=
  combineSlices (auxiliaryRankSlice contact11) 64 16 18 344355 14200 contact11RanksJoin64_16 contact11RanksJoin80_18
private theorem contact11RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact11) 0 64 = 23403120 :=
  combineSlices (auxiliaryRankSlice contact11) 0 32 32 18477920 4925200 contact11RanksJoin0_32 contact11RanksJoin32_32
private theorem contact11RanksJoin0_98 : sliceWindow (auxiliaryRankSlice contact11) 0 98 = 23761675 :=
  combineSlices (auxiliaryRankSlice contact11) 0 64 34 23403120 358555 contact11RanksJoin0_64 contact11RanksJoin64_34
theorem contact11_margin : sourceMargin contact11 :=
  margin_of_checked_counts contact11 98 210602855885789 7858780526984 809603213 23761675 rfl contact11OrdinaryColumns contact11ColumnsJoin0_98 contact11OrdinaryRanks contact11RanksJoin0_98 (by decide +kernel)

private theorem contact13OrdinaryColumns : ordinaryColumnCount contact13 = 418104506482297 := by decide +kernel
private theorem contact13ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact13) 0 4 = 3650298707242 :=
  contactColumnsWindow_fast contact13 0 4 3650298707242 (by decide +kernel)
private theorem contact13ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact13) 4 4 = 3429338851242 :=
  contactColumnsWindow_fast contact13 4 4 3429338851242 (by decide +kernel)
private theorem contact13ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact13) 8 4 = 3215322950586 :=
  contactColumnsWindow_fast contact13 8 4 3215322950586 (by decide +kernel)
private theorem contact13ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact13) 12 4 = 3008243489034 :=
  contactColumnsWindow_fast contact13 12 4 3008243489034 (by decide +kernel)
private theorem contact13ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact13) 16 4 = 2808098317545 :=
  contactColumnsWindow_fast contact13 16 4 2808098317545 (by decide +kernel)
private theorem contact13ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact13) 20 4 = 2614896327806 :=
  contactColumnsWindow_fast contact13 20 4 2614896327806 (by decide +kernel)
private theorem contact13ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact13) 24 4 = 2428672689096 :=
  contactColumnsWindow_fast contact13 24 4 2428672689096 (by decide +kernel)
private theorem contact13ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact13) 28 4 = 2249394237714 :=
  contactColumnsWindow_fast contact13 28 4 2249394237714 (by decide +kernel)
private theorem contact13ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact13) 32 4 = 2077054748298 :=
  contactColumnsWindow_fast contact13 32 4 2077054748298 (by decide +kernel)
private theorem contact13ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact13) 36 4 = 1911653061159 :=
  contactColumnsWindow_fast contact13 36 4 1911653061159 (by decide +kernel)
private theorem contact13ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact13) 40 4 = 1753197044698 :=
  contactColumnsWindow_fast contact13 40 4 1753197044698 (by decide +kernel)
private theorem contact13ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact13) 44 4 = 1601719646754 :=
  contactColumnsWindow_fast contact13 44 4 1601719646754 (by decide +kernel)
private theorem contact13ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact13) 48 4 = 1457184775386 :=
  contactColumnsWindow_fast contact13 48 4 1457184775386 (by decide +kernel)
private theorem contact13ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact13) 52 4 = 1319589074562 :=
  contactColumnsWindow_fast contact13 52 4 1319589074562 (by decide +kernel)
private theorem contact13ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact13) 56 4 = 1188930871773 :=
  contactColumnsWindow_fast contact13 56 4 1188930871773 (by decide +kernel)
private theorem contact13ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact13) 60 4 = 1065221422267 :=
  contactColumnsWindow_fast contact13 60 4 1065221422267 (by decide +kernel)
private theorem contact13ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact13) 64 4 = 948489800346 :=
  contactColumnsWindow_fast contact13 64 4 948489800346 (by decide +kernel)
private theorem contact13ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact13) 68 4 = 838698398274 :=
  contactColumnsWindow_fast contact13 68 4 838698398274 (by decide +kernel)
private theorem contact13ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact13) 72 4 = 735846467826 :=
  contactColumnsWindow_fast contact13 72 4 735846467826 (by decide +kernel)
private theorem contact13ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact13) 76 4 = 639931824562 :=
  contactColumnsWindow_fast contact13 76 4 639931824562 (by decide +kernel)
private theorem contact13ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact13) 80 4 = 550969643073 :=
  contactColumnsWindow_fast contact13 80 4 550969643073 (by decide +kernel)
private theorem contact13ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact13) 84 4 = 468983020938 :=
  contactColumnsWindow_fast contact13 84 4 468983020938 (by decide +kernel)
private theorem contact13ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact13) 88 4 = 393935213925 :=
  contactColumnsWindow_fast contact13 88 4 393935213925 (by decide +kernel)
private theorem contact13ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact13) 92 4 = 325826928090 :=
  contactColumnsWindow_fast contact13 92 4 325826928090 (by decide +kernel)
private theorem contact13ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact13) 96 4 = 264655894626 :=
  contactColumnsWindow_fast contact13 96 4 264655894626 (by decide +kernel)
private theorem contact13ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact13) 100 4 = 210440976509 :=
  contactColumnsWindow_fast contact13 100 4 210440976509 (by decide +kernel)
private theorem contact13ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact13) 104 4 = 163199308530 :=
  contactColumnsWindow_fast contact13 104 4 163199308530 (by decide +kernel)
private theorem contact13ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact13) 108 4 = 122884673593 :=
  contactColumnsWindow_fast contact13 108 4 122884673593 (by decide +kernel)
private theorem contact13ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact13) 112 4 = 89384153623 :=
  contactColumnsWindow_fast contact13 112 4 89384153623 (by decide +kernel)
private theorem contact13ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact13) 116 4 = 62404015075 :=
  contactColumnsWindow_fast contact13 116 4 62404015075 (by decide +kernel)
private theorem contact13ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact13) 120 4 = 41507859100 :=
  contactColumnsWindow_fast contact13 120 4 41507859100 (by decide +kernel)
private theorem contact13ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact13) 124 2 = 14656058508 :=
  contactColumnsWindow_fast contact13 124 2 14656058508 (by decide +kernel)
private theorem contact13ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact13) 0 8 = 7079637558484 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 4 4 3650298707242 3429338851242 contact13ColumnsSlice0 contact13ColumnsSlice4
private theorem contact13ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact13) 8 8 = 6223566439620 :=
  combineSlices (auxiliaryColumnSlice contact13) 8 4 4 3215322950586 3008243489034 contact13ColumnsSlice8 contact13ColumnsSlice12
private theorem contact13ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact13) 16 8 = 5422994645351 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 4 4 2808098317545 2614896327806 contact13ColumnsSlice16 contact13ColumnsSlice20
private theorem contact13ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact13) 24 8 = 4678066926810 :=
  combineSlices (auxiliaryColumnSlice contact13) 24 4 4 2428672689096 2249394237714 contact13ColumnsSlice24 contact13ColumnsSlice28
private theorem contact13ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact13) 32 8 = 3988707809457 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 4 4 2077054748298 1911653061159 contact13ColumnsSlice32 contact13ColumnsSlice36
private theorem contact13ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact13) 40 8 = 3354916691452 :=
  combineSlices (auxiliaryColumnSlice contact13) 40 4 4 1753197044698 1601719646754 contact13ColumnsSlice40 contact13ColumnsSlice44
private theorem contact13ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact13) 48 8 = 2776773849948 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 4 4 1457184775386 1319589074562 contact13ColumnsSlice48 contact13ColumnsSlice52
private theorem contact13ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact13) 56 8 = 2254152294040 :=
  combineSlices (auxiliaryColumnSlice contact13) 56 4 4 1188930871773 1065221422267 contact13ColumnsSlice56 contact13ColumnsSlice60
private theorem contact13ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact13) 64 8 = 1787188198620 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 4 4 948489800346 838698398274 contact13ColumnsSlice64 contact13ColumnsSlice68
private theorem contact13ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact13) 72 8 = 1375778292388 :=
  combineSlices (auxiliaryColumnSlice contact13) 72 4 4 735846467826 639931824562 contact13ColumnsSlice72 contact13ColumnsSlice76
private theorem contact13ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact13) 80 8 = 1019952664011 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 4 4 550969643073 468983020938 contact13ColumnsSlice80 contact13ColumnsSlice84
private theorem contact13ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact13) 88 8 = 719762142015 :=
  combineSlices (auxiliaryColumnSlice contact13) 88 4 4 393935213925 325826928090 contact13ColumnsSlice88 contact13ColumnsSlice92
private theorem contact13ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact13) 96 8 = 475096871135 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 4 4 264655894626 210440976509 contact13ColumnsSlice96 contact13ColumnsSlice100
private theorem contact13ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact13) 104 8 = 286083982123 :=
  combineSlices (auxiliaryColumnSlice contact13) 104 4 4 163199308530 122884673593 contact13ColumnsSlice104 contact13ColumnsSlice108
private theorem contact13ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact13) 112 8 = 151788168698 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 4 4 89384153623 62404015075 contact13ColumnsSlice112 contact13ColumnsSlice116
private theorem contact13ColumnsJoin120_6 : sliceWindow (auxiliaryColumnSlice contact13) 120 6 = 56163917608 :=
  combineSlices (auxiliaryColumnSlice contact13) 120 4 2 41507859100 14656058508 contact13ColumnsSlice120 contact13ColumnsSlice124
private theorem contact13ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact13) 0 16 = 13303203998104 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 8 8 7079637558484 6223566439620 contact13ColumnsJoin0_8 contact13ColumnsJoin8_8
private theorem contact13ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact13) 16 16 = 10101061572161 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 8 8 5422994645351 4678066926810 contact13ColumnsJoin16_8 contact13ColumnsJoin24_8
private theorem contact13ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact13) 32 16 = 7343624500909 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 8 8 3988707809457 3354916691452 contact13ColumnsJoin32_8 contact13ColumnsJoin40_8
private theorem contact13ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact13) 48 16 = 5030926143988 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 8 8 2776773849948 2254152294040 contact13ColumnsJoin48_8 contact13ColumnsJoin56_8
private theorem contact13ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact13) 64 16 = 3162966491008 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 8 8 1787188198620 1375778292388 contact13ColumnsJoin64_8 contact13ColumnsJoin72_8
private theorem contact13ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact13) 80 16 = 1739714806026 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 8 8 1019952664011 719762142015 contact13ColumnsJoin80_8 contact13ColumnsJoin88_8
private theorem contact13ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact13) 96 16 = 761180853258 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 8 8 475096871135 286083982123 contact13ColumnsJoin96_8 contact13ColumnsJoin104_8
private theorem contact13ColumnsJoin112_14 : sliceWindow (auxiliaryColumnSlice contact13) 112 14 = 207952086306 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 8 6 151788168698 56163917608 contact13ColumnsJoin112_8 contact13ColumnsJoin120_6
private theorem contact13ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact13) 0 32 = 23404265570265 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 16 16 13303203998104 10101061572161 contact13ColumnsJoin0_16 contact13ColumnsJoin16_16
private theorem contact13ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact13) 32 32 = 12374550644897 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 16 16 7343624500909 5030926143988 contact13ColumnsJoin32_16 contact13ColumnsJoin48_16
private theorem contact13ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact13) 64 32 = 4902681297034 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 16 16 3162966491008 1739714806026 contact13ColumnsJoin64_16 contact13ColumnsJoin80_16
private theorem contact13ColumnsJoin96_30 : sliceWindow (auxiliaryColumnSlice contact13) 96 30 = 969132939564 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 16 14 761180853258 207952086306 contact13ColumnsJoin96_16 contact13ColumnsJoin112_14
private theorem contact13ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact13) 0 64 = 35778816215162 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 32 32 23404265570265 12374550644897 contact13ColumnsJoin0_32 contact13ColumnsJoin32_32
private theorem contact13ColumnsJoin64_62 : sliceWindow (auxiliaryColumnSlice contact13) 64 62 = 5871814236598 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 32 30 4902681297034 969132939564 contact13ColumnsJoin64_32 contact13ColumnsJoin96_30
private theorem contact13ColumnsJoin0_126 : sliceWindow (auxiliaryColumnSlice contact13) 0 126 = 41650630451760 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 64 62 35778816215162 5871814236598 contact13ColumnsJoin0_64 contact13ColumnsJoin64_62
private theorem contact13OrdinaryRanks : ordinaryRankBound contact13 = 1626507823 := by decide +kernel
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
private theorem contact13RanksSlice120 : sliceWindow (auxiliaryRankSlice contact13) 120 6 = 0 :=
  contactRankWindow_of_rec contact13 120 6 0 (by decide +kernel)
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
private theorem contact13RanksJoin112_14 : sliceWindow (auxiliaryRankSlice contact13) 112 14 = 29937 :=
  combineSlices (auxiliaryRankSlice contact13) 112 8 6 29937 0 contact13RanksJoin112_8 contact13RanksSlice120
private theorem contact13RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact13) 0 32 = 82160912 :=
  combineSlices (auxiliaryRankSlice contact13) 0 16 16 48520456 33640456 contact13RanksJoin0_16 contact13RanksJoin16_16
private theorem contact13RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact13) 32 32 = 34812808 :=
  combineSlices (auxiliaryRankSlice contact13) 32 16 16 21829007 12983801 contact13RanksJoin32_16 contact13RanksJoin48_16
private theorem contact13RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact13) 64 32 = 9604843 :=
  combineSlices (auxiliaryRankSlice contact13) 64 16 16 6781325 2823518 contact13RanksJoin64_16 contact13RanksJoin80_16
private theorem contact13RanksJoin96_30 : sliceWindow (auxiliaryRankSlice contact13) 96 30 = 740266 :=
  combineSlices (auxiliaryRankSlice contact13) 96 16 14 710329 29937 contact13RanksJoin96_16 contact13RanksJoin112_14
private theorem contact13RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact13) 0 64 = 116973720 :=
  combineSlices (auxiliaryRankSlice contact13) 0 32 32 82160912 34812808 contact13RanksJoin0_32 contact13RanksJoin32_32
private theorem contact13RanksJoin64_62 : sliceWindow (auxiliaryRankSlice contact13) 64 62 = 10345109 :=
  combineSlices (auxiliaryRankSlice contact13) 64 32 30 9604843 740266 contact13RanksJoin64_32 contact13RanksJoin96_30
private theorem contact13RanksJoin0_126 : sliceWindow (auxiliaryRankSlice contact13) 0 126 = 127318829 :=
  combineSlices (auxiliaryRankSlice contact13) 0 64 62 116973720 10345109 contact13RanksJoin0_64 contact13RanksJoin64_62
theorem contact13_margin : sourceMargin contact13 :=
  margin_of_checked_counts contact13 126 418104506482297 41650630451760 1626507823 127318829 rfl contact13OrdinaryColumns contact13ColumnsJoin0_126 contact13OrdinaryRanks contact13RanksJoin0_126 (by decide +kernel)

private theorem contact15OrdinaryColumns : ordinaryColumnCount contact15 = 189483570121092 := by decide +kernel
private theorem contact15ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact15) 0 4 = 996266788766 :=
  contactColumnsWindow_fast contact15 0 4 996266788766 (by decide +kernel)
private theorem contact15ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact15) 4 4 = 914747406946 :=
  contactColumnsWindow_fast contact15 4 4 914747406946 (by decide +kernel)
private theorem contact15ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact15) 8 4 = 836743691454 :=
  contactColumnsWindow_fast contact15 8 4 836743691454 (by decide +kernel)
private theorem contact15ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact15) 12 4 = 762239593014 :=
  contactColumnsWindow_fast contact15 12 4 762239593014 (by decide +kernel)
private theorem contact15ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact15) 16 4 = 691232245974 :=
  contactColumnsWindow_fast contact15 16 4 691232245974 (by decide +kernel)
private theorem contact15ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact15) 20 4 = 623720155652 :=
  contactColumnsWindow_fast contact15 20 4 623720155652 (by decide +kernel)
private theorem contact15ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact15) 24 4 = 559708390694 :=
  contactColumnsWindow_fast contact15 24 4 559708390694 (by decide +kernel)
private theorem contact15ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact15) 28 4 = 499213777763 :=
  contactColumnsWindow_fast contact15 28 4 499213777763 (by decide +kernel)
private theorem contact15ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact15) 32 4 = 442220296145 :=
  contactColumnsWindow_fast contact15 32 4 442220296145 (by decide +kernel)
private theorem contact15ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact15) 36 4 = 388723646134 :=
  contactColumnsWindow_fast contact15 36 4 388723646134 (by decide +kernel)
private theorem contact15ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact15) 40 4 = 338722353216 :=
  contactColumnsWindow_fast contact15 40 4 338722353216 (by decide +kernel)
private theorem contact15ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact15) 44 4 = 292222559874 :=
  contactColumnsWindow_fast contact15 44 4 292222559874 (by decide +kernel)
private theorem contact15ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact15) 48 4 = 249240129366 :=
  contactColumnsWindow_fast contact15 48 4 249240129366 (by decide +kernel)
private theorem contact15ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact15) 52 4 = 209757509929 :=
  contactColumnsWindow_fast contact15 52 4 209757509929 (by decide +kernel)
private theorem contact15ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact15) 56 4 = 173771472062 :=
  contactColumnsWindow_fast contact15 56 4 173771472062 (by decide +kernel)
private theorem contact15ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact15) 60 4 = 141280976548 :=
  contactColumnsWindow_fast contact15 60 4 141280976548 (by decide +kernel)
private theorem contact15ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact15) 64 4 = 112293548367 :=
  contactColumnsWindow_fast contact15 64 4 112293548367 (by decide +kernel)
private theorem contact15ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact15) 68 4 = 86822986974 :=
  contactColumnsWindow_fast contact15 68 4 86822986974 (by decide +kernel)
private theorem contact15ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact15) 72 4 = 64851149887 :=
  contactColumnsWindow_fast contact15 72 4 64851149887 (by decide +kernel)
private theorem contact15ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact15) 76 4 = 46375723758 :=
  contactColumnsWindow_fast contact15 76 4 46375723758 (by decide +kernel)
private theorem contact15ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact15) 80 4 = 31393066270 :=
  contactColumnsWindow_fast contact15 80 4 31393066270 (by decide +kernel)
private theorem contact15ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact15) 84 4 = 19845801977 :=
  contactColumnsWindow_fast contact15 84 4 19845801977 (by decide +kernel)
private theorem contact15ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact15) 88 4 = 11515118756 :=
  contactColumnsWindow_fast contact15 88 4 11515118756 (by decide +kernel)
private theorem contact15ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact15) 92 4 = 5987347054 :=
  contactColumnsWindow_fast contact15 92 4 5987347054 (by decide +kernel)
private theorem contact15ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact15) 0 8 = 1911014195712 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 4 4 996266788766 914747406946 contact15ColumnsSlice0 contact15ColumnsSlice4
private theorem contact15ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact15) 8 8 = 1598983284468 :=
  combineSlices (auxiliaryColumnSlice contact15) 8 4 4 836743691454 762239593014 contact15ColumnsSlice8 contact15ColumnsSlice12
private theorem contact15ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact15) 16 8 = 1314952401626 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 4 4 691232245974 623720155652 contact15ColumnsSlice16 contact15ColumnsSlice20
private theorem contact15ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact15) 24 8 = 1058922168457 :=
  combineSlices (auxiliaryColumnSlice contact15) 24 4 4 559708390694 499213777763 contact15ColumnsSlice24 contact15ColumnsSlice28
private theorem contact15ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact15) 32 8 = 830943942279 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 4 4 442220296145 388723646134 contact15ColumnsSlice32 contact15ColumnsSlice36
private theorem contact15ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact15) 40 8 = 630944913090 :=
  combineSlices (auxiliaryColumnSlice contact15) 40 4 4 338722353216 292222559874 contact15ColumnsSlice40 contact15ColumnsSlice44
private theorem contact15ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact15) 48 8 = 458997639295 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 4 4 249240129366 209757509929 contact15ColumnsSlice48 contact15ColumnsSlice52
private theorem contact15ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact15) 56 8 = 315052448610 :=
  combineSlices (auxiliaryColumnSlice contact15) 56 4 4 173771472062 141280976548 contact15ColumnsSlice56 contact15ColumnsSlice60
private theorem contact15ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact15) 64 8 = 199116535341 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 4 4 112293548367 86822986974 contact15ColumnsSlice64 contact15ColumnsSlice68
private theorem contact15ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact15) 72 8 = 111226873645 :=
  combineSlices (auxiliaryColumnSlice contact15) 72 4 4 64851149887 46375723758 contact15ColumnsSlice72 contact15ColumnsSlice76
private theorem contact15ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact15) 80 8 = 51238868247 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 4 4 31393066270 19845801977 contact15ColumnsSlice80 contact15ColumnsSlice84
private theorem contact15ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact15) 88 8 = 17502465810 :=
  combineSlices (auxiliaryColumnSlice contact15) 88 4 4 11515118756 5987347054 contact15ColumnsSlice88 contact15ColumnsSlice92
private theorem contact15ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact15) 0 16 = 3509997480180 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 8 8 1911014195712 1598983284468 contact15ColumnsJoin0_8 contact15ColumnsJoin8_8
private theorem contact15ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact15) 16 16 = 2373874570083 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 8 8 1314952401626 1058922168457 contact15ColumnsJoin16_8 contact15ColumnsJoin24_8
private theorem contact15ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact15) 32 16 = 1461888855369 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 8 8 830943942279 630944913090 contact15ColumnsJoin32_8 contact15ColumnsJoin40_8
private theorem contact15ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact15) 48 16 = 774050087905 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 8 8 458997639295 315052448610 contact15ColumnsJoin48_8 contact15ColumnsJoin56_8
private theorem contact15ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact15) 64 16 = 310343408986 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 8 8 199116535341 111226873645 contact15ColumnsJoin64_8 contact15ColumnsJoin72_8
private theorem contact15ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact15) 80 16 = 68741334057 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 8 8 51238868247 17502465810 contact15ColumnsJoin80_8 contact15ColumnsJoin88_8
private theorem contact15ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact15) 0 32 = 5883872050263 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 16 16 3509997480180 2373874570083 contact15ColumnsJoin0_16 contact15ColumnsJoin16_16
private theorem contact15ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact15) 32 32 = 2235938943274 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 16 16 1461888855369 774050087905 contact15ColumnsJoin32_16 contact15ColumnsJoin48_16
private theorem contact15ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact15) 64 32 = 379084743043 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 16 16 310343408986 68741334057 contact15ColumnsJoin64_16 contact15ColumnsJoin80_16
private theorem contact15ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact15) 0 64 = 8119810993537 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 32 32 5883872050263 2235938943274 contact15ColumnsJoin0_32 contact15ColumnsJoin32_32
private theorem contact15ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact15) 0 96 = 8498895736580 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 64 32 8119810993537 379084743043 contact15ColumnsJoin0_64 contact15ColumnsJoin64_32
private theorem contact15OrdinaryRanks : ordinaryRankBound contact15 = 729352674 := by decide +kernel
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
  margin_of_checked_counts contact15 96 189483570121092 8498895736580 729352674 25890102 rfl contact15OrdinaryColumns contact15ColumnsJoin0_96 contact15OrdinaryRanks contact15RanksJoin0_96 (by decide +kernel)

private theorem contact17OrdinaryColumns : ordinaryColumnCount contact17 = 2674129791454891 := by decide +kernel
private theorem contact17ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact17) 0 4 = 6595278447354 :=
  contactColumnsWindow_fast contact17 0 4 6595278447354 (by decide +kernel)
private theorem contact17ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact17) 4 4 = 6259694195269 :=
  contactColumnsWindow_fast contact17 4 4 6259694195269 (by decide +kernel)
private theorem contact17ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact17) 8 4 = 5932913161216 :=
  contactColumnsWindow_fast contact17 8 4 5932913161216 (by decide +kernel)
private theorem contact17ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact17) 12 4 = 5614936965444 :=
  contactColumnsWindow_fast contact17 12 4 5614936965444 (by decide +kernel)
private theorem contact17ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact17) 16 4 = 5305802638586 :=
  contactColumnsWindow_fast contact17 16 4 5305802638586 (by decide +kernel)
private theorem contact17ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact17) 20 4 = 5005482358615 :=
  contactColumnsWindow_fast contact17 20 4 5005482358615 (by decide +kernel)
private theorem contact17ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact17) 24 4 = 4713967708202 :=
  contactColumnsWindow_fast contact17 24 4 4713967708202 (by decide +kernel)
private theorem contact17ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact17) 28 4 = 4431258307608 :=
  contactColumnsWindow_fast contact17 28 4 4431258307608 (by decide +kernel)
private theorem contact17ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact17) 32 4 = 4157360209548 :=
  contactColumnsWindow_fast contact17 32 4 4157360209548 (by decide +kernel)
private theorem contact17ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact17) 36 4 = 3892306196697 :=
  contactColumnsWindow_fast contact17 36 4 3892306196697 (by decide +kernel)
private theorem contact17ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact17) 40 4 = 3636068039839 :=
  contactColumnsWindow_fast contact17 40 4 3636068039839 (by decide +kernel)
private theorem contact17ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact17) 44 4 = 3388638014677 :=
  contactColumnsWindow_fast contact17 44 4 3388638014677 (by decide +kernel)
private theorem contact17ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact17) 48 4 = 3150017051863 :=
  contactColumnsWindow_fast contact17 48 4 3150017051863 (by decide +kernel)
private theorem contact17ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact17) 52 4 = 2920212906818 :=
  contactColumnsWindow_fast contact17 52 4 2920212906818 (by decide +kernel)
private theorem contact17ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact17) 56 4 = 2699256227175 :=
  contactColumnsWindow_fast contact17 56 4 2699256227175 (by decide +kernel)
private theorem contact17ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact17) 60 4 = 2487117272688 :=
  contactColumnsWindow_fast contact17 60 4 2487117272688 (by decide +kernel)
private theorem contact17ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact17) 64 4 = 2283788792747 :=
  contactColumnsWindow_fast contact17 64 4 2283788792747 (by decide +kernel)
private theorem contact17ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact17) 68 4 = 2089269069976 :=
  contactColumnsWindow_fast contact17 68 4 2089269069976 (by decide +kernel)
private theorem contact17ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact17) 72 4 = 1903569362766 :=
  contactColumnsWindow_fast contact17 72 4 1903569362766 (by decide +kernel)
private theorem contact17ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact17) 76 4 = 1726716306405 :=
  contactColumnsWindow_fast contact17 76 4 1726716306405 (by decide +kernel)
private theorem contact17ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact17) 80 4 = 1558679009525 :=
  contactColumnsWindow_fast contact17 80 4 1558679009525 (by decide +kernel)
private theorem contact17ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact17) 84 4 = 1399452050529 :=
  contactColumnsWindow_fast contact17 84 4 1399452050529 (by decide +kernel)
private theorem contact17ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact17) 88 4 = 1249033770225 :=
  contactColumnsWindow_fast contact17 88 4 1249033770225 (by decide +kernel)
private theorem contact17ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact17) 92 4 = 1107439094750 :=
  contactColumnsWindow_fast contact17 92 4 1107439094750 (by decide +kernel)
private theorem contact17ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact17) 96 4 = 974688869032 :=
  contactColumnsWindow_fast contact17 96 4 974688869032 (by decide +kernel)
private theorem contact17ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact17) 100 4 = 850753348558 :=
  contactColumnsWindow_fast contact17 100 4 850753348558 (by decide +kernel)
private theorem contact17ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact17) 104 4 = 735627904207 :=
  contactColumnsWindow_fast contact17 104 4 735627904207 (by decide +kernel)
private theorem contact17ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact17) 108 4 = 629311008592 :=
  contactColumnsWindow_fast contact17 108 4 629311008592 (by decide +kernel)
private theorem contact17ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact17) 112 4 = 531821349401 :=
  contactColumnsWindow_fast contact17 112 4 531821349401 (by decide +kernel)
private theorem contact17ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact17) 116 4 = 443174111761 :=
  contactColumnsWindow_fast contact17 116 4 443174111761 (by decide +kernel)
private theorem contact17ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact17) 120 4 = 363340315791 :=
  contactColumnsWindow_fast contact17 120 4 363340315791 (by decide +kernel)
private theorem contact17ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact17) 124 4 = 292316239336 :=
  contactColumnsWindow_fast contact17 124 4 292316239336 (by decide +kernel)
private theorem contact17ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact17) 128 4 = 230100102918 :=
  contactColumnsWindow_fast contact17 128 4 230100102918 (by decide +kernel)
private theorem contact17ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact17) 132 4 = 176674170910 :=
  contactColumnsWindow_fast contact17 132 4 176674170910 (by decide +kernel)
private theorem contact17ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact17) 136 4 = 131831648774 :=
  contactColumnsWindow_fast contact17 136 4 131831648774 (by decide +kernel)
private theorem contact17ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact17) 140 4 = 95145957300 :=
  contactColumnsWindow_fast contact17 140 4 95145957300 (by decide +kernel)
private theorem contact17ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact17) 144 4 = 66053958127 :=
  contactColumnsWindow_fast contact17 144 4 66053958127 (by decide +kernel)
private theorem contact17ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact17) 148 4 = 43833713113 :=
  contactColumnsWindow_fast contact17 148 4 43833713113 (by decide +kernel)
private theorem contact17ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact17) 152 4 = 27618484524 :=
  contactColumnsWindow_fast contact17 152 4 27618484524 (by decide +kernel)
private theorem contact17ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact17) 156 1 = 4977360521 :=
  contactColumnsWindow_fast contact17 156 1 4977360521 (by decide +kernel)
private theorem contact17ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact17) 0 8 = 12854972642623 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 4 4 6595278447354 6259694195269 contact17ColumnsSlice0 contact17ColumnsSlice4
private theorem contact17ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact17) 8 8 = 11547850126660 :=
  combineSlices (auxiliaryColumnSlice contact17) 8 4 4 5932913161216 5614936965444 contact17ColumnsSlice8 contact17ColumnsSlice12
private theorem contact17ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact17) 16 8 = 10311284997201 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 4 4 5305802638586 5005482358615 contact17ColumnsSlice16 contact17ColumnsSlice20
private theorem contact17ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact17) 24 8 = 9145226015810 :=
  combineSlices (auxiliaryColumnSlice contact17) 24 4 4 4713967708202 4431258307608 contact17ColumnsSlice24 contact17ColumnsSlice28
private theorem contact17ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact17) 32 8 = 8049666406245 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 4 4 4157360209548 3892306196697 contact17ColumnsSlice32 contact17ColumnsSlice36
private theorem contact17ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact17) 40 8 = 7024706054516 :=
  combineSlices (auxiliaryColumnSlice contact17) 40 4 4 3636068039839 3388638014677 contact17ColumnsSlice40 contact17ColumnsSlice44
private theorem contact17ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact17) 48 8 = 6070229958681 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 4 4 3150017051863 2920212906818 contact17ColumnsSlice48 contact17ColumnsSlice52
private theorem contact17ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact17) 56 8 = 5186373499863 :=
  combineSlices (auxiliaryColumnSlice contact17) 56 4 4 2699256227175 2487117272688 contact17ColumnsSlice56 contact17ColumnsSlice60
private theorem contact17ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact17) 64 8 = 4373057862723 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 4 4 2283788792747 2089269069976 contact17ColumnsSlice64 contact17ColumnsSlice68
private theorem contact17ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact17) 72 8 = 3630285669171 :=
  combineSlices (auxiliaryColumnSlice contact17) 72 4 4 1903569362766 1726716306405 contact17ColumnsSlice72 contact17ColumnsSlice76
private theorem contact17ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact17) 80 8 = 2958131060054 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 4 4 1558679009525 1399452050529 contact17ColumnsSlice80 contact17ColumnsSlice84
private theorem contact17ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact17) 88 8 = 2356472864975 :=
  combineSlices (auxiliaryColumnSlice contact17) 88 4 4 1249033770225 1107439094750 contact17ColumnsSlice88 contact17ColumnsSlice92
private theorem contact17ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact17) 96 8 = 1825442217590 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 4 4 974688869032 850753348558 contact17ColumnsSlice96 contact17ColumnsSlice100
private theorem contact17ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact17) 104 8 = 1364938912799 :=
  combineSlices (auxiliaryColumnSlice contact17) 104 4 4 735627904207 629311008592 contact17ColumnsSlice104 contact17ColumnsSlice108
private theorem contact17ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact17) 112 8 = 974995461162 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 4 4 531821349401 443174111761 contact17ColumnsSlice112 contact17ColumnsSlice116
private theorem contact17ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact17) 120 8 = 655656555127 :=
  combineSlices (auxiliaryColumnSlice contact17) 120 4 4 363340315791 292316239336 contact17ColumnsSlice120 contact17ColumnsSlice124
private theorem contact17ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact17) 128 8 = 406774273828 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 4 4 230100102918 176674170910 contact17ColumnsSlice128 contact17ColumnsSlice132
private theorem contact17ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact17) 136 8 = 226977606074 :=
  combineSlices (auxiliaryColumnSlice contact17) 136 4 4 131831648774 95145957300 contact17ColumnsSlice136 contact17ColumnsSlice140
private theorem contact17ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact17) 144 8 = 109887671240 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 4 4 66053958127 43833713113 contact17ColumnsSlice144 contact17ColumnsSlice148
private theorem contact17ColumnsJoin152_5 : sliceWindow (auxiliaryColumnSlice contact17) 152 5 = 32595845045 :=
  combineSlices (auxiliaryColumnSlice contact17) 152 4 1 27618484524 4977360521 contact17ColumnsSlice152 contact17ColumnsSlice156
private theorem contact17ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact17) 0 16 = 24402822769283 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 8 8 12854972642623 11547850126660 contact17ColumnsJoin0_8 contact17ColumnsJoin8_8
private theorem contact17ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact17) 16 16 = 19456511013011 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 8 8 10311284997201 9145226015810 contact17ColumnsJoin16_8 contact17ColumnsJoin24_8
private theorem contact17ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact17) 32 16 = 15074372460761 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 8 8 8049666406245 7024706054516 contact17ColumnsJoin32_8 contact17ColumnsJoin40_8
private theorem contact17ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact17) 48 16 = 11256603458544 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 8 8 6070229958681 5186373499863 contact17ColumnsJoin48_8 contact17ColumnsJoin56_8
private theorem contact17ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact17) 64 16 = 8003343531894 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 8 8 4373057862723 3630285669171 contact17ColumnsJoin64_8 contact17ColumnsJoin72_8
private theorem contact17ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact17) 80 16 = 5314603925029 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 8 8 2958131060054 2356472864975 contact17ColumnsJoin80_8 contact17ColumnsJoin88_8
private theorem contact17ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact17) 96 16 = 3190381130389 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 8 8 1825442217590 1364938912799 contact17ColumnsJoin96_8 contact17ColumnsJoin104_8
private theorem contact17ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact17) 112 16 = 1630652016289 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 8 8 974995461162 655656555127 contact17ColumnsJoin112_8 contact17ColumnsJoin120_8
private theorem contact17ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact17) 128 16 = 633751879902 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 8 8 406774273828 226977606074 contact17ColumnsJoin128_8 contact17ColumnsJoin136_8
private theorem contact17ColumnsJoin144_13 : sliceWindow (auxiliaryColumnSlice contact17) 144 13 = 142483516285 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 8 5 109887671240 32595845045 contact17ColumnsJoin144_8 contact17ColumnsJoin152_5
private theorem contact17ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact17) 0 32 = 43859333782294 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 16 16 24402822769283 19456511013011 contact17ColumnsJoin0_16 contact17ColumnsJoin16_16
private theorem contact17ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact17) 32 32 = 26330975919305 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 16 16 15074372460761 11256603458544 contact17ColumnsJoin32_16 contact17ColumnsJoin48_16
private theorem contact17ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact17) 64 32 = 13317947456923 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 16 16 8003343531894 5314603925029 contact17ColumnsJoin64_16 contact17ColumnsJoin80_16
private theorem contact17ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact17) 96 32 = 4821033146678 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 16 16 3190381130389 1630652016289 contact17ColumnsJoin96_16 contact17ColumnsJoin112_16
private theorem contact17ColumnsJoin128_29 : sliceWindow (auxiliaryColumnSlice contact17) 128 29 = 776235396187 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 16 13 633751879902 142483516285 contact17ColumnsJoin128_16 contact17ColumnsJoin144_13
private theorem contact17ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact17) 0 64 = 70190309701599 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 32 32 43859333782294 26330975919305 contact17ColumnsJoin0_32 contact17ColumnsJoin32_32
private theorem contact17ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact17) 64 64 = 18138980603601 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 32 32 13317947456923 4821033146678 contact17ColumnsJoin64_32 contact17ColumnsJoin96_32
private theorem contact17ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact17) 0 128 = 88329290305200 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 64 64 70190309701599 18138980603601 contact17ColumnsJoin0_64 contact17ColumnsJoin64_64
private theorem contact17ColumnsJoin0_157 : sliceWindow (auxiliaryColumnSlice contact17) 0 157 = 89105525701387 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 128 29 88329290305200 776235396187 contact17ColumnsJoin0_128 contact17ColumnsJoin128_29
private theorem contact17OrdinaryRanks : ordinaryRankBound contact17 = 10269223428 := by decide +kernel
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
private theorem contact17RanksSlice144 : sliceWindow (auxiliaryRankSlice contact17) 144 13 = 0 :=
  contactRankWindow_of_rec contact17 144 13 0 (by decide +kernel)
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
private theorem contact17RanksJoin128_29 : sliceWindow (auxiliaryRankSlice contact17) 128 29 = 187852 :=
  combineSlices (auxiliaryRankSlice contact17) 128 16 13 187852 0 contact17RanksJoin128_16 contact17RanksSlice144
private theorem contact17RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact17) 0 64 = 234608320 :=
  combineSlices (auxiliaryRankSlice contact17) 0 32 32 156306144 78302176 contact17RanksJoin0_32 contact17RanksJoin32_32
private theorem contact17RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact17) 64 64 = 36886294 :=
  combineSlices (auxiliaryRankSlice contact17) 64 32 32 30229388 6656906 contact17RanksJoin64_32 contact17RanksJoin96_32
private theorem contact17RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact17) 0 128 = 271494614 :=
  combineSlices (auxiliaryRankSlice contact17) 0 64 64 234608320 36886294 contact17RanksJoin0_64 contact17RanksJoin64_64
private theorem contact17RanksJoin0_157 : sliceWindow (auxiliaryRankSlice contact17) 0 157 = 271682466 :=
  combineSlices (auxiliaryRankSlice contact17) 0 128 29 271494614 187852 contact17RanksJoin0_128 contact17RanksJoin128_29
theorem contact17_margin : sourceMargin contact17 :=
  margin_of_checked_counts contact17 157 2674129791454891 89105525701387 10269223428 271682466 rfl contact17OrdinaryColumns contact17ColumnsJoin0_157 contact17OrdinaryRanks contact17RanksJoin0_157 (by decide +kernel)

private theorem contact19OrdinaryColumns : ordinaryColumnCount contact19 = 159840236214329 := by decide +kernel
private theorem contact19ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact19) 0 4 = 1313219346166 :=
  contactColumnsWindow_fast contact19 0 4 1313219346166 (by decide +kernel)
private theorem contact19ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact19) 4 4 = 1212466177974 :=
  contactColumnsWindow_fast contact19 4 4 1212466177974 (by decide +kernel)
private theorem contact19ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact19) 8 4 = 1115752400054 :=
  contactColumnsWindow_fast contact19 8 4 1115752400054 (by decide +kernel)
private theorem contact19ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact19) 12 4 = 1023095318166 :=
  contactColumnsWindow_fast contact19 12 4 1023095318166 (by decide +kernel)
private theorem contact19ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact19) 16 4 = 934494531034 :=
  contactColumnsWindow_fast contact19 16 4 934494531034 (by decide +kernel)
private theorem contact19ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact19) 20 4 = 849935632932 :=
  contactColumnsWindow_fast contact19 20 4 849935632932 (by decide +kernel)
private theorem contact19ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact19) 24 4 = 769417719272 :=
  contactColumnsWindow_fast contact19 24 4 769417719272 (by decide +kernel)
private theorem contact19ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact19) 28 4 = 692942106142 :=
  contactColumnsWindow_fast contact19 28 4 692942106142 (by decide +kernel)
private theorem contact19ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact19) 32 4 = 620527843159 :=
  contactColumnsWindow_fast contact19 32 4 620527843159 (by decide +kernel)
private theorem contact19ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact19) 36 4 = 552170042313 :=
  contactColumnsWindow_fast contact19 36 4 552170042313 (by decide +kernel)
private theorem contact19ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact19) 40 4 = 487855073638 :=
  contactColumnsWindow_fast contact19 40 4 487855073638 (by decide +kernel)
private theorem contact19ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact19) 44 4 = 427580908757 :=
  contactColumnsWindow_fast contact19 44 4 427580908757 (by decide +kernel)
private theorem contact19ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact19) 48 4 = 371349829108 :=
  contactColumnsWindow_fast contact19 48 4 371349829108 (by decide +kernel)
private theorem contact19ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact19) 52 4 = 319182045311 :=
  contactColumnsWindow_fast contact19 52 4 319182045311 (by decide +kernel)
private theorem contact19ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact19) 56 4 = 271068193964 :=
  contactColumnsWindow_fast contact19 56 4 271068193964 (by decide +kernel)
private theorem contact19ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact19) 60 4 = 226997154716 :=
  contactColumnsWindow_fast contact19 60 4 226997154716 (by decide +kernel)
private theorem contact19ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact19) 64 4 = 186966826559 :=
  contactColumnsWindow_fast contact19 64 4 186966826559 (by decide +kernel)
private theorem contact19ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact19) 68 4 = 150980406326 :=
  contactColumnsWindow_fast contact19 68 4 150980406326 (by decide +kernel)
private theorem contact19ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact19) 72 4 = 119058887835 :=
  contactColumnsWindow_fast contact19 72 4 119058887835 (by decide +kernel)
private theorem contact19ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact19) 76 4 = 91189031127 :=
  contactColumnsWindow_fast contact19 76 4 91189031127 (by decide +kernel)
private theorem contact19ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact19) 80 4 = 67361876166 :=
  contactColumnsWindow_fast contact19 80 4 67361876166 (by decide +kernel)
private theorem contact19ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact19) 84 4 = 47574668420 :=
  contactColumnsWindow_fast contact19 84 4 47574668420 (by decide +kernel)
private theorem contact19ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact19) 88 4 = 31793196155 :=
  contactColumnsWindow_fast contact19 88 4 31793196155 (by decide +kernel)
private theorem contact19ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact19) 92 4 = 19854627040 :=
  contactColumnsWindow_fast contact19 92 4 19854627040 (by decide +kernel)
private theorem contact19ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact19) 96 4 = 11387249487 :=
  contactColumnsWindow_fast contact19 96 4 11387249487 (by decide +kernel)
private theorem contact19ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact19) 0 8 = 2525685524140 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 4 4 1313219346166 1212466177974 contact19ColumnsSlice0 contact19ColumnsSlice4
private theorem contact19ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact19) 8 8 = 2138847718220 :=
  combineSlices (auxiliaryColumnSlice contact19) 8 4 4 1115752400054 1023095318166 contact19ColumnsSlice8 contact19ColumnsSlice12
private theorem contact19ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact19) 16 8 = 1784430163966 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 4 4 934494531034 849935632932 contact19ColumnsSlice16 contact19ColumnsSlice20
private theorem contact19ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact19) 24 8 = 1462359825414 :=
  combineSlices (auxiliaryColumnSlice contact19) 24 4 4 769417719272 692942106142 contact19ColumnsSlice24 contact19ColumnsSlice28
private theorem contact19ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact19) 32 8 = 1172697885472 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 4 4 620527843159 552170042313 contact19ColumnsSlice32 contact19ColumnsSlice36
private theorem contact19ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact19) 40 8 = 915435982395 :=
  combineSlices (auxiliaryColumnSlice contact19) 40 4 4 487855073638 427580908757 contact19ColumnsSlice40 contact19ColumnsSlice44
private theorem contact19ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact19) 48 8 = 690531874419 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 4 4 371349829108 319182045311 contact19ColumnsSlice48 contact19ColumnsSlice52
private theorem contact19ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact19) 56 8 = 498065348680 :=
  combineSlices (auxiliaryColumnSlice contact19) 56 4 4 271068193964 226997154716 contact19ColumnsSlice56 contact19ColumnsSlice60
private theorem contact19ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact19) 64 8 = 337947232885 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 4 4 186966826559 150980406326 contact19ColumnsSlice64 contact19ColumnsSlice68
private theorem contact19ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact19) 72 8 = 210247918962 :=
  combineSlices (auxiliaryColumnSlice contact19) 72 4 4 119058887835 91189031127 contact19ColumnsSlice72 contact19ColumnsSlice76
private theorem contact19ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact19) 80 8 = 114936544586 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 4 4 67361876166 47574668420 contact19ColumnsSlice80 contact19ColumnsSlice84
private theorem contact19ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact19) 88 8 = 51647823195 :=
  combineSlices (auxiliaryColumnSlice contact19) 88 4 4 31793196155 19854627040 contact19ColumnsSlice88 contact19ColumnsSlice92
private theorem contact19ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact19) 0 16 = 4664533242360 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 8 8 2525685524140 2138847718220 contact19ColumnsJoin0_8 contact19ColumnsJoin8_8
private theorem contact19ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact19) 16 16 = 3246789989380 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 8 8 1784430163966 1462359825414 contact19ColumnsJoin16_8 contact19ColumnsJoin24_8
private theorem contact19ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact19) 32 16 = 2088133867867 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 8 8 1172697885472 915435982395 contact19ColumnsJoin32_8 contact19ColumnsJoin40_8
private theorem contact19ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact19) 48 16 = 1188597223099 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 8 8 690531874419 498065348680 contact19ColumnsJoin48_8 contact19ColumnsJoin56_8
private theorem contact19ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact19) 64 16 = 548195151847 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 8 8 337947232885 210247918962 contact19ColumnsJoin64_8 contact19ColumnsJoin72_8
private theorem contact19ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact19) 80 16 = 166584367781 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 8 8 114936544586 51647823195 contact19ColumnsJoin80_8 contact19ColumnsJoin88_8
private theorem contact19ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact19) 0 32 = 7911323231740 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 16 16 4664533242360 3246789989380 contact19ColumnsJoin0_16 contact19ColumnsJoin16_16
private theorem contact19ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact19) 32 32 = 3276731090966 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 16 16 2088133867867 1188597223099 contact19ColumnsJoin32_16 contact19ColumnsJoin48_16
private theorem contact19ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact19) 64 32 = 714779519628 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 16 16 548195151847 166584367781 contact19ColumnsJoin64_16 contact19ColumnsJoin80_16
private theorem contact19ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact19) 0 64 = 11188054322706 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 32 32 7911323231740 3276731090966 contact19ColumnsJoin0_32 contact19ColumnsJoin32_32
private theorem contact19ColumnsJoin64_36 : sliceWindow (auxiliaryColumnSlice contact19) 64 36 = 726166769115 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 32 4 714779519628 11387249487 contact19ColumnsJoin64_32 contact19ColumnsSlice96
private theorem contact19ColumnsJoin0_100 : sliceWindow (auxiliaryColumnSlice contact19) 0 100 = 11914221091821 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 64 36 11188054322706 726166769115 contact19ColumnsJoin0_64 contact19ColumnsJoin64_36
private theorem contact19OrdinaryRanks : ordinaryRankBound contact19 = 618910282 := by decide +kernel
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
  margin_of_checked_counts contact19 100 159840236214329 11914221091821 618910282 36280569 rfl contact19OrdinaryColumns contact19ColumnsJoin0_100 contact19OrdinaryRanks contact19RanksJoin0_100 (by decide +kernel)

private theorem contact21OrdinaryColumns : ordinaryColumnCount contact21 = 52050176787951 := by decide +kernel
private theorem contact21ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact21) 0 4 = 510919757169 :=
  contactColumnsWindow_fast contact21 0 4 510919757169 (by decide +kernel)
private theorem contact21ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact21) 4 4 = 463112001222 :=
  contactColumnsWindow_fast contact21 4 4 463112001222 (by decide +kernel)
private theorem contact21ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact21) 8 4 = 417666492333 :=
  contactColumnsWindow_fast contact21 8 4 417666492333 (by decide +kernel)
private theorem contact21ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact21) 12 4 = 374580389016 :=
  contactColumnsWindow_fast contact21 12 4 374580389016 (by decide +kernel)
private theorem contact21ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact21) 16 4 = 333852382501 :=
  contactColumnsWindow_fast contact21 16 4 333852382501 (by decide +kernel)
private theorem contact21ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact21) 20 4 = 295485587017 :=
  contactColumnsWindow_fast contact21 20 4 295485587017 (by decide +kernel)
private theorem contact21ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact21) 24 4 = 259491784176 :=
  contactColumnsWindow_fast contact21 24 4 259491784176 (by decide +kernel)
private theorem contact21ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact21) 28 4 = 225859077529 :=
  contactColumnsWindow_fast contact21 28 4 225859077529 (by decide +kernel)
private theorem contact21ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact21) 32 4 = 194585776454 :=
  contactColumnsWindow_fast contact21 32 4 194585776454 (by decide +kernel)
private theorem contact21ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact21) 36 4 = 165670622269 :=
  contactColumnsWindow_fast contact21 36 4 165670622269 (by decide +kernel)
private theorem contact21ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact21) 40 4 = 139117577521 :=
  contactColumnsWindow_fast contact21 40 4 139117577521 (by decide +kernel)
private theorem contact21ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact21) 44 4 = 114937409910 :=
  contactColumnsWindow_fast contact21 44 4 114937409910 (by decide +kernel)
private theorem contact21ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact21) 48 4 = 93117512958 :=
  contactColumnsWindow_fast contact21 48 4 93117512958 (by decide +kernel)
private theorem contact21ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact21) 52 4 = 73657006672 :=
  contactColumnsWindow_fast contact21 52 4 73657006672 (by decide +kernel)
private theorem contact21ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact21) 56 4 = 56554742544 :=
  contactColumnsWindow_fast contact21 56 4 56554742544 (by decide +kernel)
private theorem contact21ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact21) 60 4 = 41815410805 :=
  contactColumnsWindow_fast contact21 60 4 41815410805 (by decide +kernel)
private theorem contact21ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact21) 64 4 = 29448878424 :=
  contactColumnsWindow_fast contact21 64 4 29448878424 (by decide +kernel)
private theorem contact21ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact21) 68 4 = 19441856475 :=
  contactColumnsWindow_fast contact21 68 4 19441856475 (by decide +kernel)
private theorem contact21ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact21) 72 4 = 11784874117 :=
  contactColumnsWindow_fast contact21 72 4 11784874117 (by decide +kernel)
private theorem contact21ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact21) 76 4 = 6378481807 :=
  contactColumnsWindow_fast contact21 76 4 6378481807 (by decide +kernel)
private theorem contact21ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact21) 80 2 = 1799194154 :=
  contactColumnsWindow_fast contact21 80 2 1799194154 (by decide +kernel)
private theorem contact21ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact21) 0 8 = 974031758391 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 4 4 510919757169 463112001222 contact21ColumnsSlice0 contact21ColumnsSlice4
private theorem contact21ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact21) 8 8 = 792246881349 :=
  combineSlices (auxiliaryColumnSlice contact21) 8 4 4 417666492333 374580389016 contact21ColumnsSlice8 contact21ColumnsSlice12
private theorem contact21ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact21) 16 8 = 629337969518 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 4 4 333852382501 295485587017 contact21ColumnsSlice16 contact21ColumnsSlice20
private theorem contact21ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact21) 24 8 = 485350861705 :=
  combineSlices (auxiliaryColumnSlice contact21) 24 4 4 259491784176 225859077529 contact21ColumnsSlice24 contact21ColumnsSlice28
private theorem contact21ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact21) 32 8 = 360256398723 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 4 4 194585776454 165670622269 contact21ColumnsSlice32 contact21ColumnsSlice36
private theorem contact21ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact21) 40 8 = 254054987431 :=
  combineSlices (auxiliaryColumnSlice contact21) 40 4 4 139117577521 114937409910 contact21ColumnsSlice40 contact21ColumnsSlice44
private theorem contact21ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact21) 48 8 = 166774519630 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 4 4 93117512958 73657006672 contact21ColumnsSlice48 contact21ColumnsSlice52
private theorem contact21ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact21) 56 8 = 98370153349 :=
  combineSlices (auxiliaryColumnSlice contact21) 56 4 4 56554742544 41815410805 contact21ColumnsSlice56 contact21ColumnsSlice60
private theorem contact21ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact21) 64 8 = 48890734899 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 4 4 29448878424 19441856475 contact21ColumnsSlice64 contact21ColumnsSlice68
private theorem contact21ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact21) 72 8 = 18163355924 :=
  combineSlices (auxiliaryColumnSlice contact21) 72 4 4 11784874117 6378481807 contact21ColumnsSlice72 contact21ColumnsSlice76
private theorem contact21ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact21) 0 16 = 1766278639740 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 8 8 974031758391 792246881349 contact21ColumnsJoin0_8 contact21ColumnsJoin8_8
private theorem contact21ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact21) 16 16 = 1114688831223 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 8 8 629337969518 485350861705 contact21ColumnsJoin16_8 contact21ColumnsJoin24_8
private theorem contact21ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact21) 32 16 = 614311386154 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 8 8 360256398723 254054987431 contact21ColumnsJoin32_8 contact21ColumnsJoin40_8
private theorem contact21ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact21) 48 16 = 265144672979 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 8 8 166774519630 98370153349 contact21ColumnsJoin48_8 contact21ColumnsJoin56_8
private theorem contact21ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact21) 64 16 = 67054090823 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 8 8 48890734899 18163355924 contact21ColumnsJoin64_8 contact21ColumnsJoin72_8
private theorem contact21ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact21) 0 32 = 2880967470963 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 16 16 1766278639740 1114688831223 contact21ColumnsJoin0_16 contact21ColumnsJoin16_16
private theorem contact21ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact21) 32 32 = 879456059133 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 16 16 614311386154 265144672979 contact21ColumnsJoin32_16 contact21ColumnsJoin48_16
private theorem contact21ColumnsJoin64_18 : sliceWindow (auxiliaryColumnSlice contact21) 64 18 = 68853284977 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 16 2 67054090823 1799194154 contact21ColumnsJoin64_16 contact21ColumnsSlice80
private theorem contact21ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact21) 0 64 = 3760423530096 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 32 32 2880967470963 879456059133 contact21ColumnsJoin0_32 contact21ColumnsJoin32_32
private theorem contact21ColumnsJoin0_82 : sliceWindow (auxiliaryColumnSlice contact21) 0 82 = 3829276815073 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 64 18 3760423530096 68853284977 contact21ColumnsJoin0_64 contact21ColumnsJoin64_18
private theorem contact21OrdinaryRanks : ordinaryRankBound contact21 = 201622402 := by decide +kernel
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
  margin_of_checked_counts contact21 82 52050176787951 3829276815073 201622402 11540025 rfl contact21OrdinaryColumns contact21ColumnsJoin0_82 contact21OrdinaryRanks contact21RanksJoin0_82 (by decide +kernel)

private theorem contact23OrdinaryColumns : ordinaryColumnCount contact23 = 2299803782644577 := by decide +kernel
private theorem contact23ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact23) 0 4 = 7258445087254 :=
  contactColumnsWindow_fast contact23 0 4 7258445087254 (by decide +kernel)
private theorem contact23ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact23) 4 4 = 6900027339814 :=
  contactColumnsWindow_fast contact23 4 4 6900027339814 (by decide +kernel)
private theorem contact23ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact23) 8 4 = 6550724382614 :=
  contactColumnsWindow_fast contact23 8 4 6550724382614 (by decide +kernel)
private theorem contact23ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact23) 12 4 = 6210539159838 :=
  contactColumnsWindow_fast contact23 12 4 6210539159838 (by decide +kernel)
private theorem contact23ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact23) 16 4 = 5879469662806 :=
  contactColumnsWindow_fast contact23 16 4 5879469662806 (by decide +kernel)
private theorem contact23ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact23) 20 4 = 5557517907134 :=
  contactColumnsWindow_fast contact23 20 4 5557517907134 (by decide +kernel)
private theorem contact23ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact23) 24 4 = 5244699932055 :=
  contactColumnsWindow_fast contact23 24 4 5244699932055 (by decide +kernel)
private theorem contact23ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact23) 28 4 = 4941035439509 :=
  contactColumnsWindow_fast contact23 28 4 4941035439509 (by decide +kernel)
private theorem contact23ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact23) 32 4 = 4646491981382 :=
  contactColumnsWindow_fast contact23 32 4 4646491981382 (by decide +kernel)
private theorem contact23ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact23) 36 4 = 4361067461070 :=
  contactColumnsWindow_fast contact23 36 4 4361067461070 (by decide +kernel)
private theorem contact23ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact23) 40 4 = 4084763804158 :=
  contactColumnsWindow_fast contact23 40 4 4084763804158 (by decide +kernel)
private theorem contact23ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact23) 44 4 = 3817601019682 :=
  contactColumnsWindow_fast contact23 44 4 3817601019682 (by decide +kernel)
private theorem contact23ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact23) 48 4 = 3559592256047 :=
  contactColumnsWindow_fast contact23 48 4 3559592256047 (by decide +kernel)
private theorem contact23ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact23) 52 4 = 3310706151321 :=
  contactColumnsWindow_fast contact23 52 4 3310706151321 (by decide +kernel)
private theorem contact23ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact23) 56 4 = 3070943348089 :=
  contactColumnsWindow_fast contact23 56 4 3070943348089 (by decide +kernel)
private theorem contact23ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact23) 60 4 = 2840303587262 :=
  contactColumnsWindow_fast contact23 60 4 2840303587262 (by decide +kernel)
private theorem contact23ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact23) 64 4 = 2618814580226 :=
  contactColumnsWindow_fast contact23 64 4 2618814580226 (by decide +kernel)
private theorem contact23ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact23) 68 4 = 2406476786519 :=
  contactColumnsWindow_fast contact23 68 4 2406476786519 (by decide +kernel)
private theorem contact23ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact23) 72 4 = 2203266703810 :=
  contactColumnsWindow_fast contact23 72 4 2203266703810 (by decide +kernel)
private theorem contact23ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact23) 76 4 = 2009180453503 :=
  contactColumnsWindow_fast contact23 76 4 2009180453503 (by decide +kernel)
private theorem contact23ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact23) 80 4 = 1824217009246 :=
  contactColumnsWindow_fast contact23 80 4 1824217009246 (by decide +kernel)
private theorem contact23ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact23) 84 4 = 1648409611830 :=
  contactColumnsWindow_fast contact23 84 4 1648409611830 (by decide +kernel)
private theorem contact23ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact23) 88 4 = 1481748792383 :=
  contactColumnsWindow_fast contact23 88 4 1481748792383 (by decide +kernel)
private theorem contact23ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact23) 92 4 = 1324215223446 :=
  contactColumnsWindow_fast contact23 92 4 1324215223446 (by decide +kernel)
private theorem contact23ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact23) 96 4 = 1175805487381 :=
  contactColumnsWindow_fast contact23 96 4 1175805487381 (by decide +kernel)
private theorem contact23ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact23) 100 4 = 1036519422261 :=
  contactColumnsWindow_fast contact23 100 4 1036519422261 (by decide +kernel)
private theorem contact23ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact23) 104 4 = 906392667102 :=
  contactColumnsWindow_fast contact23 104 4 906392667102 (by decide +kernel)
private theorem contact23ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact23) 108 4 = 785408793445 :=
  contactColumnsWindow_fast contact23 108 4 785408793445 (by decide +kernel)
private theorem contact23ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact23) 112 4 = 673551713607 :=
  contactColumnsWindow_fast contact23 112 4 673551713607 (by decide +kernel)
private theorem contact23ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact23) 116 4 = 570818567014 :=
  contactColumnsWindow_fast contact23 116 4 570818567014 (by decide +kernel)
private theorem contact23ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact23) 120 4 = 477210225567 :=
  contactColumnsWindow_fast contact23 120 4 477210225567 (by decide +kernel)
private theorem contact23ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact23) 124 4 = 392763647790 :=
  contactColumnsWindow_fast contact23 124 4 392763647790 (by decide +kernel)
private theorem contact23ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact23) 128 4 = 317456815310 :=
  contactColumnsWindow_fast contact23 128 4 317456815310 (by decide +kernel)
private theorem contact23ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact23) 132 4 = 251275923480 :=
  contactColumnsWindow_fast contact23 132 4 251275923480 (by decide +kernel)
private theorem contact23ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact23) 136 4 = 194184675259 :=
  contactColumnsWindow_fast contact23 136 4 194184675259 (by decide +kernel)
private theorem contact23ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact23) 140 4 = 145988353892 :=
  contactColumnsWindow_fast contact23 140 4 145988353892 (by decide +kernel)
private theorem contact23ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact23) 144 4 = 106336655286 :=
  contactColumnsWindow_fast contact23 144 4 106336655286 (by decide +kernel)
private theorem contact23ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact23) 148 4 = 74651899793 :=
  contactColumnsWindow_fast contact23 148 4 74651899793 (by decide +kernel)
private theorem contact23ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact23) 152 4 = 50212595462 :=
  contactColumnsWindow_fast contact23 152 4 50212595462 (by decide +kernel)
private theorem contact23ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact23) 156 4 = 32144993457 :=
  contactColumnsWindow_fast contact23 156 4 32144993457 (by decide +kernel)
private theorem contact23ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact23) 160 1 = 5863776823 :=
  contactColumnsWindow_fast contact23 160 1 5863776823 (by decide +kernel)
private theorem contact23ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact23) 0 8 = 14158472427068 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 4 4 7258445087254 6900027339814 contact23ColumnsSlice0 contact23ColumnsSlice4
private theorem contact23ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact23) 8 8 = 12761263542452 :=
  combineSlices (auxiliaryColumnSlice contact23) 8 4 4 6550724382614 6210539159838 contact23ColumnsSlice8 contact23ColumnsSlice12
private theorem contact23ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact23) 16 8 = 11436987569940 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 4 4 5879469662806 5557517907134 contact23ColumnsSlice16 contact23ColumnsSlice20
private theorem contact23ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact23) 24 8 = 10185735371564 :=
  combineSlices (auxiliaryColumnSlice contact23) 24 4 4 5244699932055 4941035439509 contact23ColumnsSlice24 contact23ColumnsSlice28
private theorem contact23ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact23) 32 8 = 9007559442452 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 4 4 4646491981382 4361067461070 contact23ColumnsSlice32 contact23ColumnsSlice36
private theorem contact23ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact23) 40 8 = 7902364823840 :=
  combineSlices (auxiliaryColumnSlice contact23) 40 4 4 4084763804158 3817601019682 contact23ColumnsSlice40 contact23ColumnsSlice44
private theorem contact23ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact23) 48 8 = 6870298407368 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 4 4 3559592256047 3310706151321 contact23ColumnsSlice48 contact23ColumnsSlice52
private theorem contact23ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact23) 56 8 = 5911246935351 :=
  combineSlices (auxiliaryColumnSlice contact23) 56 4 4 3070943348089 2840303587262 contact23ColumnsSlice56 contact23ColumnsSlice60
private theorem contact23ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact23) 64 8 = 5025291366745 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 4 4 2618814580226 2406476786519 contact23ColumnsSlice64 contact23ColumnsSlice68
private theorem contact23ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact23) 72 8 = 4212447157313 :=
  combineSlices (auxiliaryColumnSlice contact23) 72 4 4 2203266703810 2009180453503 contact23ColumnsSlice72 contact23ColumnsSlice76
private theorem contact23ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact23) 80 8 = 3472626621076 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 4 4 1824217009246 1648409611830 contact23ColumnsSlice80 contact23ColumnsSlice84
private theorem contact23ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact23) 88 8 = 2805964015829 :=
  combineSlices (auxiliaryColumnSlice contact23) 88 4 4 1481748792383 1324215223446 contact23ColumnsSlice88 contact23ColumnsSlice92
private theorem contact23ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact23) 96 8 = 2212324909642 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 4 4 1175805487381 1036519422261 contact23ColumnsSlice96 contact23ColumnsSlice100
private theorem contact23ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact23) 104 8 = 1691801460547 :=
  combineSlices (auxiliaryColumnSlice contact23) 104 4 4 906392667102 785408793445 contact23ColumnsSlice104 contact23ColumnsSlice108
private theorem contact23ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact23) 112 8 = 1244370280621 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 4 4 673551713607 570818567014 contact23ColumnsSlice112 contact23ColumnsSlice116
private theorem contact23ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact23) 120 8 = 869973873357 :=
  combineSlices (auxiliaryColumnSlice contact23) 120 4 4 477210225567 392763647790 contact23ColumnsSlice120 contact23ColumnsSlice124
private theorem contact23ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact23) 128 8 = 568732738790 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 4 4 317456815310 251275923480 contact23ColumnsSlice128 contact23ColumnsSlice132
private theorem contact23ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact23) 136 8 = 340173029151 :=
  combineSlices (auxiliaryColumnSlice contact23) 136 4 4 194184675259 145988353892 contact23ColumnsSlice136 contact23ColumnsSlice140
private theorem contact23ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact23) 144 8 = 180988555079 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 4 4 106336655286 74651899793 contact23ColumnsSlice144 contact23ColumnsSlice148
private theorem contact23ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact23) 152 8 = 82357588919 :=
  combineSlices (auxiliaryColumnSlice contact23) 152 4 4 50212595462 32144993457 contact23ColumnsSlice152 contact23ColumnsSlice156
private theorem contact23ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact23) 0 16 = 26919735969520 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 8 8 14158472427068 12761263542452 contact23ColumnsJoin0_8 contact23ColumnsJoin8_8
private theorem contact23ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact23) 16 16 = 21622722941504 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 8 8 11436987569940 10185735371564 contact23ColumnsJoin16_8 contact23ColumnsJoin24_8
private theorem contact23ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact23) 32 16 = 16909924266292 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 8 8 9007559442452 7902364823840 contact23ColumnsJoin32_8 contact23ColumnsJoin40_8
private theorem contact23ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact23) 48 16 = 12781545342719 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 8 8 6870298407368 5911246935351 contact23ColumnsJoin48_8 contact23ColumnsJoin56_8
private theorem contact23ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact23) 64 16 = 9237738524058 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 8 8 5025291366745 4212447157313 contact23ColumnsJoin64_8 contact23ColumnsJoin72_8
private theorem contact23ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact23) 80 16 = 6278590636905 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 8 8 3472626621076 2805964015829 contact23ColumnsJoin80_8 contact23ColumnsJoin88_8
private theorem contact23ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact23) 96 16 = 3904126370189 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 8 8 2212324909642 1691801460547 contact23ColumnsJoin96_8 contact23ColumnsJoin104_8
private theorem contact23ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact23) 112 16 = 2114344153978 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 8 8 1244370280621 869973873357 contact23ColumnsJoin112_8 contact23ColumnsJoin120_8
private theorem contact23ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact23) 128 16 = 908905767941 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 8 8 568732738790 340173029151 contact23ColumnsJoin128_8 contact23ColumnsJoin136_8
private theorem contact23ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact23) 144 16 = 263346143998 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 8 8 180988555079 82357588919 contact23ColumnsJoin144_8 contact23ColumnsJoin152_8
private theorem contact23ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact23) 0 32 = 48542458911024 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 16 16 26919735969520 21622722941504 contact23ColumnsJoin0_16 contact23ColumnsJoin16_16
private theorem contact23ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact23) 32 32 = 29691469609011 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 16 16 16909924266292 12781545342719 contact23ColumnsJoin32_16 contact23ColumnsJoin48_16
private theorem contact23ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact23) 64 32 = 15516329160963 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 16 16 9237738524058 6278590636905 contact23ColumnsJoin64_16 contact23ColumnsJoin80_16
private theorem contact23ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact23) 96 32 = 6018470524167 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 16 16 3904126370189 2114344153978 contact23ColumnsJoin96_16 contact23ColumnsJoin112_16
private theorem contact23ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact23) 128 32 = 1172251911939 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 16 16 908905767941 263346143998 contact23ColumnsJoin128_16 contact23ColumnsJoin144_16
private theorem contact23ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact23) 0 64 = 78233928520035 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 32 32 48542458911024 29691469609011 contact23ColumnsJoin0_32 contact23ColumnsJoin32_32
private theorem contact23ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact23) 64 64 = 21534799685130 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 32 32 15516329160963 6018470524167 contact23ColumnsJoin64_32 contact23ColumnsJoin96_32
private theorem contact23ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact23) 128 33 = 1178115688762 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 32 1 1172251911939 5863776823 contact23ColumnsJoin128_32 contact23ColumnsSlice160
private theorem contact23ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact23) 0 128 = 99768728205165 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 64 64 78233928520035 21534799685130 contact23ColumnsJoin0_64 contact23ColumnsJoin64_64
private theorem contact23ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact23) 0 161 = 100946843893927 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 128 33 99768728205165 1178115688762 contact23ColumnsJoin0_128 contact23ColumnsJoin128_33
private theorem contact23OrdinaryRanks : ordinaryRankBound contact23 = 8851110973 := by decide +kernel
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
  margin_of_checked_counts contact23 161 2299803782644577 100946843893927 8851110973 307025579 rfl contact23OrdinaryColumns contact23ColumnsJoin0_161 contact23OrdinaryRanks contact23RanksJoin0_161 (by decide +kernel)

private theorem contact25OrdinaryColumns : ordinaryColumnCount contact25 = 2286710986441291 := by decide +kernel
private theorem contact25ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact25) 0 4 = 7596498545460 :=
  contactColumnsWindow_fast contact25 0 4 7596498545460 (by decide +kernel)
private theorem contact25ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact25) 4 4 = 7219320894676 :=
  contactColumnsWindow_fast contact25 4 4 7219320894676 (by decide +kernel)
private theorem contact25ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact25) 8 4 = 6851794186772 :=
  contactColumnsWindow_fast contact25 8 4 6851794186772 (by decide +kernel)
private theorem contact25ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact25) 12 4 = 6493921494036 :=
  contactColumnsWindow_fast contact25 12 4 6493921494036 (by decide +kernel)
private theorem contact25ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact25) 16 4 = 6145700718241 :=
  contactColumnsWindow_fast contact25 16 4 6145700718241 (by decide +kernel)
private theorem contact25ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact25) 20 4 = 5807133958260 :=
  contactColumnsWindow_fast contact25 20 4 5807133958260 (by decide +kernel)
private theorem contact25ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact25) 24 4 = 5478238595640 :=
  contactColumnsWindow_fast contact25 24 4 5478238595640 (by decide +kernel)
private theorem contact25ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact25) 28 4 = 5159035815820 :=
  contactColumnsWindow_fast contact25 28 4 5159035815820 (by decide +kernel)
private theorem contact25ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact25) 32 4 = 4849490510660 :=
  contactColumnsWindow_fast contact25 32 4 4849490510660 (by decide +kernel)
private theorem contact25ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact25) 36 4 = 4549600458351 :=
  contactColumnsWindow_fast contact25 36 4 4549600458351 (by decide +kernel)
private theorem contact25ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact25) 40 4 = 4259367658188 :=
  contactColumnsWindow_fast contact25 40 4 4259367658188 (by decide +kernel)
private theorem contact25ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact25) 44 4 = 3978813792229 :=
  contactColumnsWindow_fast contact25 44 4 3978813792229 (by decide +kernel)
private theorem contact25ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact25) 48 4 = 3707952915380 :=
  contactColumnsWindow_fast contact25 48 4 3707952915380 (by decide +kernel)
private theorem contact25ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact25) 52 4 = 3446751159738 :=
  contactColumnsWindow_fast contact25 52 4 3446751159738 (by decide +kernel)
private theorem contact25ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact25) 56 4 = 3195209170593 :=
  contactColumnsWindow_fast contact25 56 4 3195209170593 (by decide +kernel)
private theorem contact25ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact25) 60 4 = 2953326686328 :=
  contactColumnsWindow_fast contact25 60 4 2953326686328 (by decide +kernel)
private theorem contact25ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact25) 64 4 = 2721133582063 :=
  contactColumnsWindow_fast contact25 64 4 2721133582063 (by decide +kernel)
private theorem contact25ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact25) 68 4 = 2498630331215 :=
  contactColumnsWindow_fast contact25 68 4 2498630331215 (by decide +kernel)
private theorem contact25ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact25) 72 4 = 2285791416204 :=
  contactColumnsWindow_fast contact25 72 4 2285791416204 (by decide +kernel)
private theorem contact25ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact25) 76 4 = 2082612816784 :=
  contactColumnsWindow_fast contact25 76 4 2082612816784 (by decide +kernel)
private theorem contact25ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact25) 80 4 = 1889093474708 :=
  contactColumnsWindow_fast contact25 80 4 1889093474708 (by decide +kernel)
private theorem contact25ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact25) 84 4 = 1705269218432 :=
  contactColumnsWindow_fast contact25 84 4 1705269218432 (by decide +kernel)
private theorem contact25ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact25) 88 4 = 1531129793013 :=
  contactColumnsWindow_fast contact25 88 4 1531129793013 (by decide +kernel)
private theorem contact25ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact25) 92 4 = 1366654225164 :=
  contactColumnsWindow_fast contact25 92 4 1366654225164 (by decide +kernel)
private theorem contact25ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact25) 96 4 = 1211838975464 :=
  contactColumnsWindow_fast contact25 96 4 1211838975464 (by decide +kernel)
private theorem contact25ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact25) 100 4 = 1066683915559 :=
  contactColumnsWindow_fast contact25 100 4 1066683915559 (by decide +kernel)
private theorem contact25ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact25) 104 4 = 931227465884 :=
  contactColumnsWindow_fast contact25 104 4 931227465884 (by decide +kernel)
private theorem contact25ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact25) 108 4 = 805451836787 :=
  contactColumnsWindow_fast contact25 108 4 805451836787 (by decide +kernel)
private theorem contact25ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact25) 112 4 = 689339590213 :=
  contactColumnsWindow_fast contact25 112 4 689339590213 (by decide +kernel)
private theorem contact25ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact25) 116 4 = 582887768148 :=
  contactColumnsWindow_fast contact25 116 4 582887768148 (by decide +kernel)
private theorem contact25ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact25) 120 4 = 486097363353 :=
  contactColumnsWindow_fast contact25 120 4 486097363353 (by decide +kernel)
private theorem contact25ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact25) 124 4 = 399008222600 :=
  contactColumnsWindow_fast contact25 124 4 399008222600 (by decide +kernel)
private theorem contact25ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact25) 128 4 = 321596488556 :=
  contactColumnsWindow_fast contact25 128 4 321596488556 (by decide +kernel)
private theorem contact25ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact25) 132 4 = 253841969473 :=
  contactColumnsWindow_fast contact25 132 4 253841969473 (by decide +kernel)
private theorem contact25ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact25) 136 4 = 195646565687 :=
  contactColumnsWindow_fast contact25 136 4 195646565687 (by decide +kernel)
private theorem contact25ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact25) 140 4 = 146718775050 :=
  contactColumnsWindow_fast contact25 140 4 146718775050 (by decide +kernel)
private theorem contact25ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact25) 144 4 = 106634197102 :=
  contactColumnsWindow_fast contact25 144 4 106634197102 (by decide +kernel)
private theorem contact25ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact25) 148 4 = 74735220073 :=
  contactColumnsWindow_fast contact25 148 4 74735220073 (by decide +kernel)
private theorem contact25ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact25) 152 4 = 50222305790 :=
  contactColumnsWindow_fast contact25 152 4 50222305790 (by decide +kernel)
private theorem contact25ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact25) 156 4 = 32145030889 :=
  contactColumnsWindow_fast contact25 156 4 32145030889 (by decide +kernel)
private theorem contact25ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact25) 0 8 = 14815819440136 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 4 4 7596498545460 7219320894676 contact25ColumnsSlice0 contact25ColumnsSlice4
private theorem contact25ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact25) 8 8 = 13345715680808 :=
  combineSlices (auxiliaryColumnSlice contact25) 8 4 4 6851794186772 6493921494036 contact25ColumnsSlice8 contact25ColumnsSlice12
private theorem contact25ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact25) 16 8 = 11952834676501 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 4 4 6145700718241 5807133958260 contact25ColumnsSlice16 contact25ColumnsSlice20
private theorem contact25ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact25) 24 8 = 10637274411460 :=
  combineSlices (auxiliaryColumnSlice contact25) 24 4 4 5478238595640 5159035815820 contact25ColumnsSlice24 contact25ColumnsSlice28
private theorem contact25ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact25) 32 8 = 9399090969011 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 4 4 4849490510660 4549600458351 contact25ColumnsSlice32 contact25ColumnsSlice36
private theorem contact25ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact25) 40 8 = 8238181450417 :=
  combineSlices (auxiliaryColumnSlice contact25) 40 4 4 4259367658188 3978813792229 contact25ColumnsSlice40 contact25ColumnsSlice44
private theorem contact25ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact25) 48 8 = 7154704075118 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 4 4 3707952915380 3446751159738 contact25ColumnsSlice48 contact25ColumnsSlice52
private theorem contact25ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact25) 56 8 = 6148535856921 :=
  combineSlices (auxiliaryColumnSlice contact25) 56 4 4 3195209170593 2953326686328 contact25ColumnsSlice56 contact25ColumnsSlice60
private theorem contact25ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact25) 64 8 = 5219763913278 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 4 4 2721133582063 2498630331215 contact25ColumnsSlice64 contact25ColumnsSlice68
private theorem contact25ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact25) 72 8 = 4368404232988 :=
  combineSlices (auxiliaryColumnSlice contact25) 72 4 4 2285791416204 2082612816784 contact25ColumnsSlice72 contact25ColumnsSlice76
private theorem contact25ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact25) 80 8 = 3594362693140 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 4 4 1889093474708 1705269218432 contact25ColumnsSlice80 contact25ColumnsSlice84
private theorem contact25ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact25) 88 8 = 2897784018177 :=
  combineSlices (auxiliaryColumnSlice contact25) 88 4 4 1531129793013 1366654225164 contact25ColumnsSlice88 contact25ColumnsSlice92
private theorem contact25ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact25) 96 8 = 2278522891023 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 4 4 1211838975464 1066683915559 contact25ColumnsSlice96 contact25ColumnsSlice100
private theorem contact25ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact25) 104 8 = 1736679302671 :=
  combineSlices (auxiliaryColumnSlice contact25) 104 4 4 931227465884 805451836787 contact25ColumnsSlice104 contact25ColumnsSlice108
private theorem contact25ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact25) 112 8 = 1272227358361 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 4 4 689339590213 582887768148 contact25ColumnsSlice112 contact25ColumnsSlice116
private theorem contact25ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact25) 120 8 = 885105585953 :=
  combineSlices (auxiliaryColumnSlice contact25) 120 4 4 486097363353 399008222600 contact25ColumnsSlice120 contact25ColumnsSlice124
private theorem contact25ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact25) 128 8 = 575438458029 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 4 4 321596488556 253841969473 contact25ColumnsSlice128 contact25ColumnsSlice132
private theorem contact25ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact25) 136 8 = 342365340737 :=
  combineSlices (auxiliaryColumnSlice contact25) 136 4 4 195646565687 146718775050 contact25ColumnsSlice136 contact25ColumnsSlice140
private theorem contact25ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact25) 144 8 = 181369417175 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 4 4 106634197102 74735220073 contact25ColumnsSlice144 contact25ColumnsSlice148
private theorem contact25ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact25) 152 8 = 82367336679 :=
  combineSlices (auxiliaryColumnSlice contact25) 152 4 4 50222305790 32145030889 contact25ColumnsSlice152 contact25ColumnsSlice156
private theorem contact25ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact25) 0 16 = 28161535120944 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 8 8 14815819440136 13345715680808 contact25ColumnsJoin0_8 contact25ColumnsJoin8_8
private theorem contact25ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact25) 16 16 = 22590109087961 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 8 8 11952834676501 10637274411460 contact25ColumnsJoin16_8 contact25ColumnsJoin24_8
private theorem contact25ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact25) 32 16 = 17637272419428 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 8 8 9399090969011 8238181450417 contact25ColumnsJoin32_8 contact25ColumnsJoin40_8
private theorem contact25ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact25) 48 16 = 13303239932039 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 8 8 7154704075118 6148535856921 contact25ColumnsJoin48_8 contact25ColumnsJoin56_8
private theorem contact25ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact25) 64 16 = 9588168146266 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 8 8 5219763913278 4368404232988 contact25ColumnsJoin64_8 contact25ColumnsJoin72_8
private theorem contact25ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact25) 80 16 = 6492146711317 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 8 8 3594362693140 2897784018177 contact25ColumnsJoin80_8 contact25ColumnsJoin88_8
private theorem contact25ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact25) 96 16 = 4015202193694 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 8 8 2278522891023 1736679302671 contact25ColumnsJoin96_8 contact25ColumnsJoin104_8
private theorem contact25ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact25) 112 16 = 2157332944314 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 8 8 1272227358361 885105585953 contact25ColumnsJoin112_8 contact25ColumnsJoin120_8
private theorem contact25ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact25) 128 16 = 917803798766 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 8 8 575438458029 342365340737 contact25ColumnsJoin128_8 contact25ColumnsJoin136_8
private theorem contact25ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact25) 144 16 = 263736753854 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 8 8 181369417175 82367336679 contact25ColumnsJoin144_8 contact25ColumnsJoin152_8
private theorem contact25ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact25) 0 32 = 50751644208905 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 16 16 28161535120944 22590109087961 contact25ColumnsJoin0_16 contact25ColumnsJoin16_16
private theorem contact25ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact25) 32 32 = 30940512351467 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 16 16 17637272419428 13303239932039 contact25ColumnsJoin32_16 contact25ColumnsJoin48_16
private theorem contact25ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact25) 64 32 = 16080314857583 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 16 16 9588168146266 6492146711317 contact25ColumnsJoin64_16 contact25ColumnsJoin80_16
private theorem contact25ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact25) 96 32 = 6172535138008 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 16 16 4015202193694 2157332944314 contact25ColumnsJoin96_16 contact25ColumnsJoin112_16
private theorem contact25ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact25) 128 32 = 1181540552620 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 16 16 917803798766 263736753854 contact25ColumnsJoin128_16 contact25ColumnsJoin144_16
private theorem contact25ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact25) 0 64 = 81692156560372 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 32 32 50751644208905 30940512351467 contact25ColumnsJoin0_32 contact25ColumnsJoin32_32
private theorem contact25ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact25) 64 64 = 22252849995591 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 32 32 16080314857583 6172535138008 contact25ColumnsJoin64_32 contact25ColumnsJoin96_32
private theorem contact25ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact25) 0 128 = 103945006555963 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 64 64 81692156560372 22252849995591 contact25ColumnsJoin0_64 contact25ColumnsJoin64_64
private theorem contact25ColumnsJoin0_160 : sliceWindow (auxiliaryColumnSlice contact25) 0 160 = 105126547108583 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 128 32 103945006555963 1181540552620 contact25ColumnsJoin0_128 contact25ColumnsJoin128_32
private theorem contact25OrdinaryRanks : ordinaryRankBound contact25 = 8802927260 := by decide +kernel
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
private theorem contact25RanksSlice148 : sliceWindow (auxiliaryRankSlice contact25) 148 12 = 0 :=
  contactRankWindow_of_rec contact25 148 12 0 (by decide +kernel)
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
private theorem contact25RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact25) 144 16 = 989 :=
  combineSlices (auxiliaryRankSlice contact25) 144 4 12 989 0 contact25RanksSlice144 contact25RanksSlice148
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
private theorem contact25RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact25) 128 32 = 426801 :=
  combineSlices (auxiliaryRankSlice contact25) 128 16 16 425812 989 contact25RanksJoin128_16 contact25RanksJoin144_16
private theorem contact25RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact25) 0 64 = 274039262 :=
  combineSlices (auxiliaryRankSlice contact25) 0 32 32 181128704 92910558 contact25RanksJoin0_32 contact25RanksJoin32_32
private theorem contact25RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact25) 64 64 = 46739998 :=
  combineSlices (auxiliaryRankSlice contact25) 64 32 32 37514037 9225961 contact25RanksJoin64_32 contact25RanksJoin96_32
private theorem contact25RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact25) 0 128 = 320779260 :=
  combineSlices (auxiliaryRankSlice contact25) 0 64 64 274039262 46739998 contact25RanksJoin0_64 contact25RanksJoin64_64
private theorem contact25RanksJoin0_160 : sliceWindow (auxiliaryRankSlice contact25) 0 160 = 321206061 :=
  combineSlices (auxiliaryRankSlice contact25) 0 128 32 320779260 426801 contact25RanksJoin0_128 contact25RanksJoin128_32
theorem contact25_margin : sourceMargin contact25 :=
  margin_of_checked_counts contact25 160 2286710986441291 105126547108583 8802927260 321206061 rfl contact25OrdinaryColumns contact25ColumnsJoin0_160 contact25OrdinaryRanks contact25RanksJoin0_160 (by decide +kernel)

private theorem contact27OrdinaryColumns : ordinaryColumnCount contact27 = 2269085515968481 := by decide +kernel
private theorem contact27ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact27) 0 4 = 7428603722960 :=
  contactColumnsWindow_fast contact27 0 4 7428603722960 (by decide +kernel)
private theorem contact27ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact27) 4 4 = 7060774066080 :=
  contactColumnsWindow_fast contact27 4 4 7060774066080 (by decide +kernel)
private theorem contact27ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact27) 8 4 = 6702327275761 :=
  contactColumnsWindow_fast contact27 8 4 6702327275761 (by decide +kernel)
private theorem contact27ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact27) 12 4 = 6353266360238 :=
  contactColumnsWindow_fast contact27 12 4 6353266360238 (by decide +kernel)
private theorem contact27ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact27) 16 4 = 6013589266058 :=
  contactColumnsWindow_fast contact27 16 4 6013589266058 (by decide +kernel)
private theorem contact27ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact27) 20 4 = 5683298050464 :=
  contactColumnsWindow_fast contact27 20 4 5683298050464 (by decide +kernel)
private theorem contact27ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact27) 24 4 = 5362409423878 :=
  contactColumnsWindow_fast contact27 24 4 5362409423878 (by decide +kernel)
private theorem contact27ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact27) 28 4 = 5050943829939 :=
  contactColumnsWindow_fast contact27 28 4 5050943829939 (by decide +kernel)
private theorem contact27ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact27) 32 4 = 4748867490530 :=
  contactColumnsWindow_fast contact27 32 4 4748867490530 (by decide +kernel)
private theorem contact27ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact27) 36 4 = 4456178246453 :=
  contactColumnsWindow_fast contact27 36 4 4456178246453 (by decide +kernel)
private theorem contact27ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact27) 40 4 = 4172878060150 :=
  contactColumnsWindow_fast contact27 40 4 4172878060150 (by decide +kernel)
private theorem contact27ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact27) 44 4 = 3898987777207 :=
  contactColumnsWindow_fast contact27 44 4 3898987777207 (by decide +kernel)
private theorem contact27ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact27) 48 4 = 3634520999200 :=
  contactColumnsWindow_fast contact27 48 4 3634520999200 (by decide +kernel)
private theorem contact27ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact27) 52 4 = 3379445111251 :=
  contactColumnsWindow_fast contact27 52 4 3379445111251 (by decide +kernel)
private theorem contact27ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact27) 56 4 = 3133760757298 :=
  contactColumnsWindow_fast contact27 56 4 3133760757298 (by decide +kernel)
private theorem contact27ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact27) 60 4 = 2897467676987 :=
  contactColumnsWindow_fast contact27 60 4 2897467676987 (by decide +kernel)
private theorem contact27ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact27) 64 4 = 2670594663612 :=
  contactColumnsWindow_fast contact27 64 4 2670594663612 (by decide +kernel)
private theorem contact27ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact27) 68 4 = 2453142183571 :=
  contactColumnsWindow_fast contact27 68 4 2453142183571 (by decide +kernel)
private theorem contact27ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact27) 72 4 = 2245085726947 :=
  contactColumnsWindow_fast contact27 72 4 2245085726947 (by decide +kernel)
private theorem contact27ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact27) 76 4 = 2046421344319 :=
  contactColumnsWindow_fast contact27 76 4 2046421344319 (by decide +kernel)
private theorem contact27ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact27) 80 4 = 1857147993387 :=
  contactColumnsWindow_fast contact27 80 4 1857147993387 (by decide +kernel)
private theorem contact27ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact27) 84 4 = 1677300208817 :=
  contactColumnsWindow_fast contact27 84 4 1677300208817 (by decide +kernel)
private theorem contact27ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact27) 88 4 = 1506868128621 :=
  contactColumnsWindow_fast contact27 88 4 1506868128621 (by decide +kernel)
private theorem contact27ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact27) 92 4 = 1345831602463 :=
  contactColumnsWindow_fast contact27 92 4 1345831602463 (by decide +kernel)
private theorem contact27ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact27) 96 4 = 1194187151816 :=
  contactColumnsWindow_fast contact27 96 4 1194187151816 (by decide +kernel)
private theorem contact27ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact27) 100 4 = 1051934631549 :=
  contactColumnsWindow_fast contact27 100 4 1051934631549 (by decide +kernel)
private theorem contact27ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact27) 104 4 = 919111071397 :=
  contactColumnsWindow_fast contact27 104 4 919111071397 (by decide +kernel)
private theorem contact27ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact27) 108 4 = 795699362257 :=
  contactColumnsWindow_fast contact27 108 4 795699362257 (by decide +kernel)
private theorem contact27ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact27) 112 4 = 681682741287 :=
  contactColumnsWindow_fast contact27 112 4 681682741287 (by decide +kernel)
private theorem contact27ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact27) 116 4 = 577058299193 :=
  contactColumnsWindow_fast contact27 116 4 577058299193 (by decide +kernel)
private theorem contact27ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact27) 120 4 = 481826968317 :=
  contactColumnsWindow_fast contact27 120 4 481826968317 (by decide +kernel)
private theorem contact27ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact27) 124 4 = 396027151317 :=
  contactColumnsWindow_fast contact27 124 4 396027151317 (by decide +kernel)
private theorem contact27ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact27) 128 4 = 319635910293 :=
  contactColumnsWindow_fast contact27 128 4 319635910293 (by decide +kernel)
private theorem contact27ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact27) 132 4 = 252637460803 :=
  contactColumnsWindow_fast contact27 132 4 252637460803 (by decide +kernel)
private theorem contact27ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact27) 136 4 = 194969336573 :=
  contactColumnsWindow_fast contact27 136 4 194969336573 (by decide +kernel)
private theorem contact27ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact27) 140 4 = 146387375460 :=
  contactColumnsWindow_fast contact27 140 4 146387375460 (by decide +kernel)
private theorem contact27ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact27) 144 4 = 106503907346 :=
  contactColumnsWindow_fast contact27 144 4 106503907346 (by decide +kernel)
private theorem contact27ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact27) 148 4 = 74701342813 :=
  contactColumnsWindow_fast contact27 148 4 74701342813 (by decide +kernel)
private theorem contact27ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact27) 152 4 = 50219156930 :=
  contactColumnsWindow_fast contact27 152 4 50219156930 (by decide +kernel)
private theorem contact27ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact27) 156 4 = 32145030889 :=
  contactColumnsWindow_fast contact27 156 4 32145030889 (by decide +kernel)
private theorem contact27ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact27) 160 1 = 5863776823 :=
  contactColumnsWindow_fast contact27 160 1 5863776823 (by decide +kernel)
private theorem contact27ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact27) 0 8 = 14489377789040 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 4 4 7428603722960 7060774066080 contact27ColumnsSlice0 contact27ColumnsSlice4
private theorem contact27ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact27) 8 8 = 13055593635999 :=
  combineSlices (auxiliaryColumnSlice contact27) 8 4 4 6702327275761 6353266360238 contact27ColumnsSlice8 contact27ColumnsSlice12
private theorem contact27ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact27) 16 8 = 11696887316522 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 4 4 6013589266058 5683298050464 contact27ColumnsSlice16 contact27ColumnsSlice20
private theorem contact27ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact27) 24 8 = 10413353253817 :=
  combineSlices (auxiliaryColumnSlice contact27) 24 4 4 5362409423878 5050943829939 contact27ColumnsSlice24 contact27ColumnsSlice28
private theorem contact27ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact27) 32 8 = 9205045736983 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 4 4 4748867490530 4456178246453 contact27ColumnsSlice32 contact27ColumnsSlice36
private theorem contact27ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact27) 40 8 = 8071865837357 :=
  combineSlices (auxiliaryColumnSlice contact27) 40 4 4 4172878060150 3898987777207 contact27ColumnsSlice40 contact27ColumnsSlice44
private theorem contact27ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact27) 48 8 = 7013966110451 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 4 4 3634520999200 3379445111251 contact27ColumnsSlice48 contact27ColumnsSlice52
private theorem contact27ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact27) 56 8 = 6031228434285 :=
  combineSlices (auxiliaryColumnSlice contact27) 56 4 4 3133760757298 2897467676987 contact27ColumnsSlice56 contact27ColumnsSlice60
private theorem contact27ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact27) 64 8 = 5123736847183 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 4 4 2670594663612 2453142183571 contact27ColumnsSlice64 contact27ColumnsSlice68
private theorem contact27ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact27) 72 8 = 4291507071266 :=
  combineSlices (auxiliaryColumnSlice contact27) 72 4 4 2245085726947 2046421344319 contact27ColumnsSlice72 contact27ColumnsSlice76
private theorem contact27ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact27) 80 8 = 3534448202204 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 4 4 1857147993387 1677300208817 contact27ColumnsSlice80 contact27ColumnsSlice84
private theorem contact27ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact27) 88 8 = 2852699731084 :=
  combineSlices (auxiliaryColumnSlice contact27) 88 4 4 1506868128621 1345831602463 contact27ColumnsSlice88 contact27ColumnsSlice92
private theorem contact27ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact27) 96 8 = 2246121783365 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 4 4 1194187151816 1051934631549 contact27ColumnsSlice96 contact27ColumnsSlice100
private theorem contact27ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact27) 104 8 = 1714810433654 :=
  combineSlices (auxiliaryColumnSlice contact27) 104 4 4 919111071397 795699362257 contact27ColumnsSlice104 contact27ColumnsSlice108
private theorem contact27ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact27) 112 8 = 1258741040480 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 4 4 681682741287 577058299193 contact27ColumnsSlice112 contact27ColumnsSlice116
private theorem contact27ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact27) 120 8 = 877854119634 :=
  combineSlices (auxiliaryColumnSlice contact27) 120 4 4 481826968317 396027151317 contact27ColumnsSlice120 contact27ColumnsSlice124
private theorem contact27ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact27) 128 8 = 572273371096 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 4 4 319635910293 252637460803 contact27ColumnsSlice128 contact27ColumnsSlice132
private theorem contact27ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact27) 136 8 = 341356712033 :=
  combineSlices (auxiliaryColumnSlice contact27) 136 4 4 194969336573 146387375460 contact27ColumnsSlice136 contact27ColumnsSlice140
private theorem contact27ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact27) 144 8 = 181205250159 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 4 4 106503907346 74701342813 contact27ColumnsSlice144 contact27ColumnsSlice148
private theorem contact27ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact27) 152 8 = 82364187819 :=
  combineSlices (auxiliaryColumnSlice contact27) 152 4 4 50219156930 32145030889 contact27ColumnsSlice152 contact27ColumnsSlice156
private theorem contact27ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact27) 0 16 = 27544971425039 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 8 8 14489377789040 13055593635999 contact27ColumnsJoin0_8 contact27ColumnsJoin8_8
private theorem contact27ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact27) 16 16 = 22110240570339 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 8 8 11696887316522 10413353253817 contact27ColumnsJoin16_8 contact27ColumnsJoin24_8
private theorem contact27ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact27) 32 16 = 17276911574340 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 8 8 9205045736983 8071865837357 contact27ColumnsJoin32_8 contact27ColumnsJoin40_8
private theorem contact27ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact27) 48 16 = 13045194544736 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 8 8 7013966110451 6031228434285 contact27ColumnsJoin48_8 contact27ColumnsJoin56_8
private theorem contact27ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact27) 64 16 = 9415243918449 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 8 8 5123736847183 4291507071266 contact27ColumnsJoin64_8 contact27ColumnsJoin72_8
private theorem contact27ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact27) 80 16 = 6387147933288 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 8 8 3534448202204 2852699731084 contact27ColumnsJoin80_8 contact27ColumnsJoin88_8
private theorem contact27ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact27) 96 16 = 3960932217019 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 8 8 2246121783365 1714810433654 contact27ColumnsJoin96_8 contact27ColumnsJoin104_8
private theorem contact27ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact27) 112 16 = 2136595160114 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 8 8 1258741040480 877854119634 contact27ColumnsJoin112_8 contact27ColumnsJoin120_8
private theorem contact27ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact27) 128 16 = 913630083129 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 8 8 572273371096 341356712033 contact27ColumnsJoin128_8 contact27ColumnsJoin136_8
private theorem contact27ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact27) 144 16 = 263569437978 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 8 8 181205250159 82364187819 contact27ColumnsJoin144_8 contact27ColumnsJoin152_8
private theorem contact27ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact27) 0 32 = 49655211995378 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 16 16 27544971425039 22110240570339 contact27ColumnsJoin0_16 contact27ColumnsJoin16_16
private theorem contact27ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact27) 32 32 = 30322106119076 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 16 16 17276911574340 13045194544736 contact27ColumnsJoin32_16 contact27ColumnsJoin48_16
private theorem contact27ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact27) 64 32 = 15802391851737 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 16 16 9415243918449 6387147933288 contact27ColumnsJoin64_16 contact27ColumnsJoin80_16
private theorem contact27ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact27) 96 32 = 6097527377133 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 16 16 3960932217019 2136595160114 contact27ColumnsJoin96_16 contact27ColumnsJoin112_16
private theorem contact27ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact27) 128 32 = 1177199521107 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 16 16 913630083129 263569437978 contact27ColumnsJoin128_16 contact27ColumnsJoin144_16
private theorem contact27ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact27) 0 64 = 79977318114454 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 32 32 49655211995378 30322106119076 contact27ColumnsJoin0_32 contact27ColumnsJoin32_32
private theorem contact27ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact27) 64 64 = 21899919228870 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 32 32 15802391851737 6097527377133 contact27ColumnsJoin64_32 contact27ColumnsJoin96_32
private theorem contact27ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact27) 128 33 = 1183063297930 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 32 1 1177199521107 5863776823 contact27ColumnsJoin128_32 contact27ColumnsSlice160
private theorem contact27ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact27) 0 128 = 101877237343324 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 64 64 79977318114454 21899919228870 contact27ColumnsJoin0_64 contact27ColumnsJoin64_64
private theorem contact27ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact27) 0 161 = 103060300641254 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 128 33 101877237343324 1183063297930 contact27ColumnsJoin0_128 contact27ColumnsJoin128_33
private theorem contact27OrdinaryRanks : ordinaryRankBound contact27 = 8734867364 := by decide +kernel
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
private theorem contact27RanksSlice148 : sliceWindow (auxiliaryRankSlice contact27) 148 13 = 0 :=
  contactRankWindow_of_rec contact27 148 13 0 (by decide +kernel)
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
private theorem contact27RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact27) 144 17 = 970 :=
  combineSlices (auxiliaryRankSlice contact27) 144 4 13 970 0 contact27RanksSlice144 contact27RanksSlice148
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
private theorem contact27RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact27) 128 33 = 416760 :=
  combineSlices (auxiliaryRankSlice contact27) 128 16 17 415790 970 contact27RanksJoin128_16 contact27RanksJoin144_17
private theorem contact27RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact27) 0 64 = 268062126 :=
  combineSlices (auxiliaryRankSlice contact27) 0 32 32 177171008 90891118 contact27RanksJoin0_32 contact27RanksJoin32_32
private theorem contact27RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact27) 64 64 = 45671352 :=
  combineSlices (auxiliaryRankSlice contact27) 64 32 32 36664973 9006379 contact27RanksJoin64_32 contact27RanksJoin96_32
private theorem contact27RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact27) 0 128 = 313733478 :=
  combineSlices (auxiliaryRankSlice contact27) 0 64 64 268062126 45671352 contact27RanksJoin0_64 contact27RanksJoin64_64
private theorem contact27RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact27) 0 161 = 314150238 :=
  combineSlices (auxiliaryRankSlice contact27) 0 128 33 313733478 416760 contact27RanksJoin0_128 contact27RanksJoin128_33
theorem contact27_margin : sourceMargin contact27 :=
  margin_of_checked_counts contact27 161 2269085515968481 103060300641254 8734867364 314150238 rfl contact27OrdinaryColumns contact27ColumnsJoin0_161 contact27OrdinaryRanks contact27RanksJoin0_161 (by decide +kernel)

private theorem contact29OrdinaryColumns : ordinaryColumnCount contact29 = 193296390523611 := by decide +kernel
private theorem contact29ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact29) 0 4 = 1033641973894 :=
  contactColumnsWindow_fast contact29 0 4 1033641973894 (by decide +kernel)
private theorem contact29ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact29) 4 4 = 948680694423 :=
  contactColumnsWindow_fast contact29 4 4 948680694423 (by decide +kernel)
private theorem contact29ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact29) 8 4 = 867402665708 :=
  contactColumnsWindow_fast contact29 8 4 867402665708 (by decide +kernel)
private theorem contact29ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact29) 12 4 = 789790933829 :=
  contactColumnsWindow_fast contact29 12 4 789790933829 (by decide +kernel)
private theorem contact29ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact29) 16 4 = 715842415706 :=
  contactColumnsWindow_fast contact29 16 4 715842415706 (by decide +kernel)
private theorem contact29ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact29) 20 4 = 645555571316 :=
  contactColumnsWindow_fast contact29 20 4 645555571316 (by decide +kernel)
private theorem contact29ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact29) 24 4 = 578935706031 :=
  contactColumnsWindow_fast contact29 24 4 578935706031 (by decide +kernel)
private theorem contact29ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact29) 28 4 = 516000616556 :=
  contactColumnsWindow_fast contact29 28 4 516000616556 (by decide +kernel)
private theorem contact29ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact29) 32 4 = 456733338978 :=
  contactColumnsWindow_fast contact29 32 4 456733338978 (by decide +kernel)
private theorem contact29ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact29) 36 4 = 401129357494 :=
  contactColumnsWindow_fast contact29 36 4 401129357494 (by decide +kernel)
private theorem contact29ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact29) 40 4 = 349187152627 :=
  contactColumnsWindow_fast contact29 40 4 349187152627 (by decide +kernel)
private theorem contact29ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact29) 44 4 = 300913171329 :=
  contactColumnsWindow_fast contact29 44 4 300913171329 (by decide +kernel)
private theorem contact29ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact29) 48 4 = 256324182044 :=
  contactColumnsWindow_fast contact29 48 4 256324182044 (by decide +kernel)
private theorem contact29ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact29) 52 4 = 215401610868 :=
  contactColumnsWindow_fast contact29 52 4 215401610868 (by decide +kernel)
private theorem contact29ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact29) 56 4 = 178142078658 :=
  contactColumnsWindow_fast contact29 56 4 178142078658 (by decide +kernel)
private theorem contact29ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact29) 60 4 = 144544513314 :=
  contactColumnsWindow_fast contact29 60 4 144544513314 (by decide +kernel)
private theorem contact29ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact29) 64 4 = 114616831238 :=
  contactColumnsWindow_fast contact29 64 4 114616831238 (by decide +kernel)
private theorem contact29ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact29) 68 4 = 88373609276 :=
  contactColumnsWindow_fast contact29 68 4 88373609276 (by decide +kernel)
private theorem contact29ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact29) 72 4 = 65795662569 :=
  contactColumnsWindow_fast contact29 72 4 65795662569 (by decide +kernel)
private theorem contact29ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact29) 76 4 = 46880579198 :=
  contactColumnsWindow_fast contact29 76 4 46880579198 (by decide +kernel)
private theorem contact29ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact29) 80 4 = 31619419086 :=
  contactColumnsWindow_fast contact29 80 4 31619419086 (by decide +kernel)
private theorem contact29ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact29) 84 4 = 19922137017 :=
  contactColumnsWindow_fast contact29 84 4 19922137017 (by decide +kernel)
private theorem contact29ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact29) 88 4 = 11529376776 :=
  contactColumnsWindow_fast contact29 88 4 11529376776 (by decide +kernel)
private theorem contact29ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact29) 92 4 = 5987792898 :=
  contactColumnsWindow_fast contact29 92 4 5987792898 (by decide +kernel)
private theorem contact29ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact29) 96 1 = 910724503 :=
  contactColumnsWindow_fast contact29 96 1 910724503 (by decide +kernel)
private theorem contact29ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact29) 0 8 = 1982322668317 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 4 4 1033641973894 948680694423 contact29ColumnsSlice0 contact29ColumnsSlice4
private theorem contact29ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact29) 8 8 = 1657193599537 :=
  combineSlices (auxiliaryColumnSlice contact29) 8 4 4 867402665708 789790933829 contact29ColumnsSlice8 contact29ColumnsSlice12
private theorem contact29ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact29) 16 8 = 1361397987022 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 4 4 715842415706 645555571316 contact29ColumnsSlice16 contact29ColumnsSlice20
private theorem contact29ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact29) 24 8 = 1094936322587 :=
  combineSlices (auxiliaryColumnSlice contact29) 24 4 4 578935706031 516000616556 contact29ColumnsSlice24 contact29ColumnsSlice28
private theorem contact29ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact29) 32 8 = 857862696472 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 4 4 456733338978 401129357494 contact29ColumnsSlice32 contact29ColumnsSlice36
private theorem contact29ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact29) 40 8 = 650100323956 :=
  combineSlices (auxiliaryColumnSlice contact29) 40 4 4 349187152627 300913171329 contact29ColumnsSlice40 contact29ColumnsSlice44
private theorem contact29ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact29) 48 8 = 471725792912 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 4 4 256324182044 215401610868 contact29ColumnsSlice48 contact29ColumnsSlice52
private theorem contact29ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact29) 56 8 = 322686591972 :=
  combineSlices (auxiliaryColumnSlice contact29) 56 4 4 178142078658 144544513314 contact29ColumnsSlice56 contact29ColumnsSlice60
private theorem contact29ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact29) 64 8 = 202990440514 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 4 4 114616831238 88373609276 contact29ColumnsSlice64 contact29ColumnsSlice68
private theorem contact29ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact29) 72 8 = 112676241767 :=
  combineSlices (auxiliaryColumnSlice contact29) 72 4 4 65795662569 46880579198 contact29ColumnsSlice72 contact29ColumnsSlice76
private theorem contact29ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact29) 80 8 = 51541556103 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 4 4 31619419086 19922137017 contact29ColumnsSlice80 contact29ColumnsSlice84
private theorem contact29ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact29) 88 8 = 17517169674 :=
  combineSlices (auxiliaryColumnSlice contact29) 88 4 4 11529376776 5987792898 contact29ColumnsSlice88 contact29ColumnsSlice92
private theorem contact29ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact29) 0 16 = 3639516267854 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 8 8 1982322668317 1657193599537 contact29ColumnsJoin0_8 contact29ColumnsJoin8_8
private theorem contact29ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact29) 16 16 = 2456334309609 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 8 8 1361397987022 1094936322587 contact29ColumnsJoin16_8 contact29ColumnsJoin24_8
private theorem contact29ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact29) 32 16 = 1507963020428 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 8 8 857862696472 650100323956 contact29ColumnsJoin32_8 contact29ColumnsJoin40_8
private theorem contact29ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact29) 48 16 = 794412384884 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 8 8 471725792912 322686591972 contact29ColumnsJoin48_8 contact29ColumnsJoin56_8
private theorem contact29ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact29) 64 16 = 315666682281 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 8 8 202990440514 112676241767 contact29ColumnsJoin64_8 contact29ColumnsJoin72_8
private theorem contact29ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact29) 80 16 = 69058725777 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 8 8 51541556103 17517169674 contact29ColumnsJoin80_8 contact29ColumnsJoin88_8
private theorem contact29ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact29) 0 32 = 6095850577463 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 16 16 3639516267854 2456334309609 contact29ColumnsJoin0_16 contact29ColumnsJoin16_16
private theorem contact29ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact29) 32 32 = 2302375405312 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 16 16 1507963020428 794412384884 contact29ColumnsJoin32_16 contact29ColumnsJoin48_16
private theorem contact29ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact29) 64 32 = 384725408058 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 16 16 315666682281 69058725777 contact29ColumnsJoin64_16 contact29ColumnsJoin80_16
private theorem contact29ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact29) 0 64 = 8398225982775 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 32 32 6095850577463 2302375405312 contact29ColumnsJoin0_32 contact29ColumnsJoin32_32
private theorem contact29ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact29) 64 33 = 385636132561 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 32 1 384725408058 910724503 contact29ColumnsJoin64_32 contact29ColumnsSlice96
private theorem contact29ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact29) 0 97 = 8783862115336 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 64 33 8398225982775 385636132561 contact29ColumnsJoin0_64 contact29ColumnsJoin64_33
private theorem contact29OrdinaryRanks : ordinaryRankBound contact29 = 744015186 := by decide +kernel
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
  margin_of_checked_counts contact29 97 193296390523611 8783862115336 744015186 26859783 rfl contact29OrdinaryColumns contact29ColumnsJoin0_97 contact29OrdinaryRanks contact29RanksJoin0_97 (by decide +kernel)

private theorem contact31OrdinaryColumns : ordinaryColumnCount contact31 = 55095569343858 := by decide +kernel
private theorem contact31ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact31) 0 4 = 469397220354 :=
  contactColumnsWindow_fast contact31 0 4 469397220354 (by decide +kernel)
private theorem contact31ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact31) 4 4 = 422359815378 :=
  contactColumnsWindow_fast contact31 4 4 422359815378 (by decide +kernel)
private theorem contact31ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact31) 8 4 = 377818143522 :=
  contactColumnsWindow_fast contact31 8 4 377818143522 (by decide +kernel)
private theorem contact31ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact31) 12 4 = 335782674466 :=
  contactColumnsWindow_fast contact31 12 4 335782674466 (by decide +kernel)
private theorem contact31ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact31) 16 4 = 296254696562 :=
  contactColumnsWindow_fast contact31 16 4 296254696562 (by decide +kernel)
private theorem contact31ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact31) 20 4 = 259224387618 :=
  contactColumnsWindow_fast contact31 20 4 259224387618 (by decide +kernel)
private theorem contact31ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact31) 24 4 = 224691177186 :=
  contactColumnsWindow_fast contact31 24 4 224691177186 (by decide +kernel)
private theorem contact31ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact31) 28 4 = 192656027778 :=
  contactColumnsWindow_fast contact31 28 4 192656027778 (by decide +kernel)
private theorem contact31ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact31) 32 4 = 163130165090 :=
  contactColumnsWindow_fast contact31 32 4 163130165090 (by decide +kernel)
private theorem contact31ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact31) 36 4 = 136109764371 :=
  contactColumnsWindow_fast contact31 36 4 136109764371 (by decide +kernel)
private theorem contact31ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact31) 40 4 = 111587217082 :=
  contactColumnsWindow_fast contact31 40 4 111587217082 (by decide +kernel)
private theorem contact31ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact31) 44 4 = 89561605818 :=
  contactColumnsWindow_fast contact31 44 4 89561605818 (by decide +kernel)
private theorem contact31ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact31) 48 4 = 70034404238 :=
  contactColumnsWindow_fast contact31 48 4 70034404238 (by decide +kernel)
private theorem contact31ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact31) 52 4 = 53017959834 :=
  contactColumnsWindow_fast contact31 52 4 53017959834 (by decide +kernel)
private theorem contact31ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact31) 56 4 = 38505153265 :=
  contactColumnsWindow_fast contact31 56 4 38505153265 (by decide +kernel)
private theorem contact31ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact31) 60 4 = 26490350666 :=
  contactColumnsWindow_fast contact31 60 4 26490350666 (by decide +kernel)
private theorem contact31ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact31) 64 4 = 16971209946 :=
  contactColumnsWindow_fast contact31 64 4 16971209946 (by decide +kernel)
private theorem contact31ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact31) 68 4 = 9906100844 :=
  contactColumnsWindow_fast contact31 68 4 9906100844 (by decide +kernel)
private theorem contact31ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact31) 72 4 = 5119997833 :=
  contactColumnsWindow_fast contact31 72 4 5119997833 (by decide +kernel)
private theorem contact31ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact31) 76 1 = 767016679 :=
  contactColumnsWindow_fast contact31 76 1 767016679 (by decide +kernel)
private theorem contact31ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact31) 0 8 = 891757035732 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 4 4 469397220354 422359815378 contact31ColumnsSlice0 contact31ColumnsSlice4
private theorem contact31ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact31) 8 8 = 713600817988 :=
  combineSlices (auxiliaryColumnSlice contact31) 8 4 4 377818143522 335782674466 contact31ColumnsSlice8 contact31ColumnsSlice12
private theorem contact31ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact31) 16 8 = 555479084180 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 4 4 296254696562 259224387618 contact31ColumnsSlice16 contact31ColumnsSlice20
private theorem contact31ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact31) 24 8 = 417347204964 :=
  combineSlices (auxiliaryColumnSlice contact31) 24 4 4 224691177186 192656027778 contact31ColumnsSlice24 contact31ColumnsSlice28
private theorem contact31ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact31) 32 8 = 299239929461 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 4 4 163130165090 136109764371 contact31ColumnsSlice32 contact31ColumnsSlice36
private theorem contact31ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact31) 40 8 = 201148822900 :=
  combineSlices (auxiliaryColumnSlice contact31) 40 4 4 111587217082 89561605818 contact31ColumnsSlice40 contact31ColumnsSlice44
private theorem contact31ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact31) 48 8 = 123052364072 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 4 4 70034404238 53017959834 contact31ColumnsSlice48 contact31ColumnsSlice52
private theorem contact31ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact31) 56 8 = 64995503931 :=
  combineSlices (auxiliaryColumnSlice contact31) 56 4 4 38505153265 26490350666 contact31ColumnsSlice56 contact31ColumnsSlice60
private theorem contact31ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact31) 64 8 = 26877310790 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 4 4 16971209946 9906100844 contact31ColumnsSlice64 contact31ColumnsSlice68
private theorem contact31ColumnsJoin72_5 : sliceWindow (auxiliaryColumnSlice contact31) 72 5 = 5887014512 :=
  combineSlices (auxiliaryColumnSlice contact31) 72 4 1 5119997833 767016679 contact31ColumnsSlice72 contact31ColumnsSlice76
private theorem contact31ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact31) 0 16 = 1605357853720 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 8 8 891757035732 713600817988 contact31ColumnsJoin0_8 contact31ColumnsJoin8_8
private theorem contact31ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact31) 16 16 = 972826289144 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 8 8 555479084180 417347204964 contact31ColumnsJoin16_8 contact31ColumnsJoin24_8
private theorem contact31ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact31) 32 16 = 500388752361 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 8 8 299239929461 201148822900 contact31ColumnsJoin32_8 contact31ColumnsJoin40_8
private theorem contact31ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact31) 48 16 = 188047868003 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 8 8 123052364072 64995503931 contact31ColumnsJoin48_8 contact31ColumnsJoin56_8
private theorem contact31ColumnsJoin64_13 : sliceWindow (auxiliaryColumnSlice contact31) 64 13 = 32764325302 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 8 5 26877310790 5887014512 contact31ColumnsJoin64_8 contact31ColumnsJoin72_5
private theorem contact31ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact31) 0 32 = 2578184142864 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 16 16 1605357853720 972826289144 contact31ColumnsJoin0_16 contact31ColumnsJoin16_16
private theorem contact31ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact31) 32 32 = 688436620364 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 16 16 500388752361 188047868003 contact31ColumnsJoin32_16 contact31ColumnsJoin48_16
private theorem contact31ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact31) 0 64 = 3266620763228 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 32 32 2578184142864 688436620364 contact31ColumnsJoin0_32 contact31ColumnsJoin32_32
private theorem contact31ColumnsJoin0_77 : sliceWindow (auxiliaryColumnSlice contact31) 0 77 = 3299385088530 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 64 13 3266620763228 32764325302 contact31ColumnsJoin0_64 contact31ColumnsJoin64_13
private theorem contact31OrdinaryRanks : ordinaryRankBound contact31 = 212679096 := by decide +kernel
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
  margin_of_checked_counts contact31 77 55095569343858 3299385088530 212679096 10079727 rfl contact31OrdinaryColumns contact31ColumnsJoin0_77 contact31OrdinaryRanks contact31RanksJoin0_77 (by decide +kernel)

private theorem contact33OrdinaryColumns : ordinaryColumnCount contact33 = 223176832482775 := by decide +kernel
private theorem contact33ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact33) 0 4 = 942326937830 :=
  contactColumnsWindow_fast contact33 0 4 942326937830 (by decide +kernel)
private theorem contact33ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact33) 4 4 = 863115475254 :=
  contactColumnsWindow_fast contact33 4 4 863115475254 (by decide +kernel)
private theorem contact33ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact33) 8 4 = 787398770091 :=
  contactColumnsWindow_fast contact33 8 4 787398770091 (by decide +kernel)
private theorem contact33ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact33) 12 4 = 715195586686 :=
  contactColumnsWindow_fast contact33 12 4 715195586686 (by decide +kernel)
private theorem contact33ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact33) 16 4 = 646495269215 :=
  contactColumnsWindow_fast contact33 16 4 646495269215 (by decide +kernel)
private theorem contact33ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact33) 20 4 = 581291674414 :=
  contactColumnsWindow_fast contact33 20 4 581291674414 (by decide +kernel)
private theorem contact33ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact33) 24 4 = 519583295526 :=
  contactColumnsWindow_fast contact33 24 4 519583295526 (by decide +kernel)
private theorem contact33ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact33) 28 4 = 461373236809 :=
  contactColumnsWindow_fast contact33 28 4 461373236809 (by decide +kernel)
private theorem contact33ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact33) 32 4 = 406679311689 :=
  contactColumnsWindow_fast contact33 32 4 406679311689 (by decide +kernel)
private theorem contact33ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact33) 36 4 = 355489422054 :=
  contactColumnsWindow_fast contact33 36 4 355489422054 (by decide +kernel)
private theorem contact33ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact33) 40 4 = 307796538662 :=
  contactColumnsWindow_fast contact33 40 4 307796538662 (by decide +kernel)
private theorem contact33ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact33) 44 4 = 263598866854 :=
  contactColumnsWindow_fast contact33 44 4 263598866854 (by decide +kernel)
private theorem contact33ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact33) 48 4 = 222900475222 :=
  contactColumnsWindow_fast contact33 48 4 222900475222 (by decide +kernel)
private theorem contact33ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact33) 52 4 = 185719111747 :=
  contactColumnsWindow_fast contact33 52 4 185719111747 (by decide +kernel)
private theorem contact33ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact33) 56 4 = 152040015026 :=
  contactColumnsWindow_fast contact33 56 4 152040015026 (by decide +kernel)
private theorem contact33ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact33) 60 4 = 121857828678 :=
  contactColumnsWindow_fast contact33 60 4 121857828678 (by decide +kernel)
private theorem contact33ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact33) 64 4 = 95170916528 :=
  contactColumnsWindow_fast contact33 64 4 95170916528 (by decide +kernel)
private theorem contact33ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact33) 68 4 = 71984534258 :=
  contactColumnsWindow_fast contact33 68 4 71984534258 (by decide +kernel)
private theorem contact33ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact33) 72 4 = 52315338101 :=
  contactColumnsWindow_fast contact33 72 4 52315338101 (by decide +kernel)
private theorem contact33ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact33) 76 4 = 36146634884 :=
  contactColumnsWindow_fast contact33 76 4 36146634884 (by decide +kernel)
private theorem contact33ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact33) 80 4 = 23443072882 :=
  contactColumnsWindow_fast contact33 80 4 23443072882 (by decide +kernel)
private theorem contact33ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact33) 84 4 = 14034992680 :=
  contactColumnsWindow_fast contact33 84 4 14034992680 (by decide +kernel)
private theorem contact33ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact33) 88 4 = 7590325169 :=
  contactColumnsWindow_fast contact33 88 4 7590325169 (by decide +kernel)
private theorem contact33ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact33) 92 3 = 2973778197 :=
  contactColumnsWindow_fast contact33 92 3 2973778197 (by decide +kernel)
private theorem contact33ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact33) 0 8 = 1805442413084 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 4 4 942326937830 863115475254 contact33ColumnsSlice0 contact33ColumnsSlice4
private theorem contact33ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact33) 8 8 = 1502594356777 :=
  combineSlices (auxiliaryColumnSlice contact33) 8 4 4 787398770091 715195586686 contact33ColumnsSlice8 contact33ColumnsSlice12
private theorem contact33ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact33) 16 8 = 1227786943629 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 4 4 646495269215 581291674414 contact33ColumnsSlice16 contact33ColumnsSlice20
private theorem contact33ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact33) 24 8 = 980956532335 :=
  combineSlices (auxiliaryColumnSlice contact33) 24 4 4 519583295526 461373236809 contact33ColumnsSlice24 contact33ColumnsSlice28
private theorem contact33ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact33) 32 8 = 762168733743 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 4 4 406679311689 355489422054 contact33ColumnsSlice32 contact33ColumnsSlice36
private theorem contact33ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact33) 40 8 = 571395405516 :=
  combineSlices (auxiliaryColumnSlice contact33) 40 4 4 307796538662 263598866854 contact33ColumnsSlice40 contact33ColumnsSlice44
private theorem contact33ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact33) 48 8 = 408619586969 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 4 4 222900475222 185719111747 contact33ColumnsSlice48 contact33ColumnsSlice52
private theorem contact33ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact33) 56 8 = 273897843704 :=
  combineSlices (auxiliaryColumnSlice contact33) 56 4 4 152040015026 121857828678 contact33ColumnsSlice56 contact33ColumnsSlice60
private theorem contact33ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact33) 64 8 = 167155450786 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 4 4 95170916528 71984534258 contact33ColumnsSlice64 contact33ColumnsSlice68
private theorem contact33ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact33) 72 8 = 88461972985 :=
  combineSlices (auxiliaryColumnSlice contact33) 72 4 4 52315338101 36146634884 contact33ColumnsSlice72 contact33ColumnsSlice76
private theorem contact33ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact33) 80 8 = 37478065562 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 4 4 23443072882 14034992680 contact33ColumnsSlice80 contact33ColumnsSlice84
private theorem contact33ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact33) 88 7 = 10564103366 :=
  combineSlices (auxiliaryColumnSlice contact33) 88 4 3 7590325169 2973778197 contact33ColumnsSlice88 contact33ColumnsSlice92
private theorem contact33ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact33) 0 16 = 3308036769861 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 8 8 1805442413084 1502594356777 contact33ColumnsJoin0_8 contact33ColumnsJoin8_8
private theorem contact33ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact33) 16 16 = 2208743475964 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 8 8 1227786943629 980956532335 contact33ColumnsJoin16_8 contact33ColumnsJoin24_8
private theorem contact33ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact33) 32 16 = 1333564139259 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 8 8 762168733743 571395405516 contact33ColumnsJoin32_8 contact33ColumnsJoin40_8
private theorem contact33ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact33) 48 16 = 682517430673 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 8 8 408619586969 273897843704 contact33ColumnsJoin48_8 contact33ColumnsJoin56_8
private theorem contact33ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact33) 64 16 = 255617423771 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 8 8 167155450786 88461972985 contact33ColumnsJoin64_8 contact33ColumnsJoin72_8
private theorem contact33ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact33) 80 15 = 48042168928 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 8 7 37478065562 10564103366 contact33ColumnsJoin80_8 contact33ColumnsJoin88_7
private theorem contact33ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact33) 0 32 = 5516780245825 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 16 16 3308036769861 2208743475964 contact33ColumnsJoin0_16 contact33ColumnsJoin16_16
private theorem contact33ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact33) 32 32 = 2016081569932 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 16 16 1333564139259 682517430673 contact33ColumnsJoin32_16 contact33ColumnsJoin48_16
private theorem contact33ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact33) 64 31 = 303659592699 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 16 15 255617423771 48042168928 contact33ColumnsJoin64_16 contact33ColumnsJoin80_15
private theorem contact33ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact33) 0 64 = 7532861815757 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 32 32 5516780245825 2016081569932 contact33ColumnsJoin0_32 contact33ColumnsJoin32_32
private theorem contact33ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact33) 0 95 = 7836521408456 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 64 31 7532861815757 303659592699 contact33ColumnsJoin0_64 contact33ColumnsJoin64_31
private theorem contact33OrdinaryRanks : ordinaryRankBound contact33 = 857273652 := by decide +kernel
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
  margin_of_checked_counts contact33 95 223176832482775 7836521408456 857273652 23971545 rfl contact33OrdinaryColumns contact33ColumnsJoin0_95 contact33OrdinaryRanks contact33RanksJoin0_95 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

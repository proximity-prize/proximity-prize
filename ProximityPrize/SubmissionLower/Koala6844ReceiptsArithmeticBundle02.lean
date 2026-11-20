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

private theorem contact01OrdinaryColumns : ordinaryColumnCount contact01 = 2405351469914195 := by decide +kernel
private theorem contact01ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact01) 0 4 = 7339178380052 :=
  contactColumnsWindow_fast contact01 0 4 7339178380052 (by decide +kernel)
private theorem contact01ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact01) 4 4 = 6989949398004 :=
  contactColumnsWindow_fast contact01 4 4 6989949398004 (by decide +kernel)
private theorem contact01ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact01) 8 4 = 6649263696980 :=
  contactColumnsWindow_fast contact01 8 4 6649263696980 (by decide +kernel)
private theorem contact01ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact01) 12 4 = 6317121446804 :=
  contactColumnsWindow_fast contact01 12 4 6317121446804 (by decide +kernel)
private theorem contact01ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact01) 16 4 = 5993554333508 :=
  contactColumnsWindow_fast contact01 16 4 5993554333508 (by decide +kernel)
private theorem contact01ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact01) 20 4 = 5678549457663 :=
  contactColumnsWindow_fast contact01 20 4 5678549457663 (by decide +kernel)
private theorem contact01ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact01) 24 4 = 5372091500948 :=
  contactColumnsWindow_fast contact01 24 4 5372091500948 (by decide +kernel)
private theorem contact01ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact01) 28 4 = 5074179104572 :=
  contactColumnsWindow_fast contact01 28 4 5074179104572 (by decide +kernel)
private theorem contact01ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact01) 32 4 = 4784815115572 :=
  contactColumnsWindow_fast contact01 32 4 4784815115572 (by decide +kernel)
private theorem contact01ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact01) 36 4 = 4504030539880 :=
  contactColumnsWindow_fast contact01 36 4 4504030539880 (by decide +kernel)
private theorem contact01ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact01) 40 4 = 4231809357676 :=
  contactColumnsWindow_fast contact01 40 4 4231809357676 (by decide +kernel)
private theorem contact01ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact01) 44 4 = 3968136953037 :=
  contactColumnsWindow_fast contact01 44 4 3968136953037 (by decide +kernel)
private theorem contact01ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact01) 48 4 = 3713014569436 :=
  contactColumnsWindow_fast contact01 48 4 3713014569436 (by decide +kernel)
private theorem contact01ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact01) 52 4 = 3466443812939 :=
  contactColumnsWindow_fast contact01 52 4 3466443812939 (by decide +kernel)
private theorem contact01ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact01) 56 4 = 3228459104221 :=
  contactColumnsWindow_fast contact01 56 4 3228459104221 (by decide +kernel)
private theorem contact01ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact01) 60 4 = 2999037542416 :=
  contactColumnsWindow_fast contact01 60 4 2999037542416 (by decide +kernel)
private theorem contact01ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact01) 64 4 = 2778168209811 :=
  contactColumnsWindow_fast contact01 64 4 2778168209811 (by decide +kernel)
private theorem contact01ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact01) 68 4 = 2565848858740 :=
  contactColumnsWindow_fast contact01 68 4 2565848858740 (by decide +kernel)
private theorem contact01ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact01) 72 4 = 2362083130612 :=
  contactColumnsWindow_fast contact01 72 4 2362083130612 (by decide +kernel)
private theorem contact01ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact01) 76 4 = 2166904302763 :=
  contactColumnsWindow_fast contact01 76 4 2166904302763 (by decide +kernel)
private theorem contact01ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact01) 80 4 = 1980286336420 :=
  contactColumnsWindow_fast contact01 80 4 1980286336420 (by decide +kernel)
private theorem contact01ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact01) 84 4 = 1802220096204 :=
  contactColumnsWindow_fast contact01 84 4 1802220096204 (by decide +kernel)
private theorem contact01ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact01) 88 4 = 1632703854938 :=
  contactColumnsWindow_fast contact01 88 4 1632703854938 (by decide +kernel)
private theorem contact01ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact01) 92 4 = 1471743644284 :=
  contactColumnsWindow_fast contact01 92 4 1471743644284 (by decide +kernel)
private theorem contact01ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact01) 96 4 = 1319370120319 :=
  contactColumnsWindow_fast contact01 96 4 1319370120319 (by decide +kernel)
private theorem contact01ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact01) 100 4 = 1175555780663 :=
  contactColumnsWindow_fast contact01 100 4 1175555780663 (by decide +kernel)
private theorem contact01ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact01) 104 4 = 1040292811332 :=
  contactColumnsWindow_fast contact01 104 4 1040292811332 (by decide +kernel)
private theorem contact01ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact01) 108 4 = 913579491158 :=
  contactColumnsWindow_fast contact01 108 4 913579491158 (by decide +kernel)
private theorem contact01ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact01) 112 4 = 795424767220 :=
  contactColumnsWindow_fast contact01 112 4 795424767220 (by decide +kernel)
private theorem contact01ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact01) 116 4 = 685856831694 :=
  contactColumnsWindow_fast contact01 116 4 685856831694 (by decide +kernel)
private theorem contact01ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact01) 120 4 = 584845916645 :=
  contactColumnsWindow_fast contact01 120 4 584845916645 (by decide +kernel)
private theorem contact01ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact01) 124 4 = 492386147736 :=
  contactColumnsWindow_fast contact01 124 4 492386147736 (by decide +kernel)
private theorem contact01ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact01) 128 4 = 408475835107 :=
  contactColumnsWindow_fast contact01 128 4 408475835107 (by decide +kernel)
private theorem contact01ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact01) 132 4 = 333127619260 :=
  contactColumnsWindow_fast contact01 132 4 333127619260 (by decide +kernel)
private theorem contact01ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact01) 136 4 = 266364248130 :=
  contactColumnsWindow_fast contact01 136 4 266364248130 (by decide +kernel)
private theorem contact01ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact01) 140 4 = 208155117009 :=
  contactColumnsWindow_fast contact01 140 4 208155117009 (by decide +kernel)
private theorem contact01ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact01) 144 4 = 158439153918 :=
  contactColumnsWindow_fast contact01 144 4 158439153918 (by decide +kernel)
private theorem contact01ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact01) 148 4 = 116973669511 :=
  contactColumnsWindow_fast contact01 148 4 116973669511 (by decide +kernel)
private theorem contact01ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact01) 152 4 = 83353058416 :=
  contactColumnsWindow_fast contact01 152 4 83353058416 (by decide +kernel)
private theorem contact01ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact01) 156 4 = 57009684913 :=
  contactColumnsWindow_fast contact01 156 4 57009684913 (by decide +kernel)
private theorem contact01ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact01) 160 4 = 37169263547 :=
  contactColumnsWindow_fast contact01 160 4 37169263547 (by decide +kernel)
private theorem contact01ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact01) 164 1 = 6869882768 :=
  contactColumnsWindow_fast contact01 164 1 6869882768 (by decide +kernel)
private theorem contact01ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact01) 0 8 = 14329127778056 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 4 4 7339178380052 6989949398004 contact01ColumnsSlice0 contact01ColumnsSlice4
private theorem contact01ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact01) 8 8 = 12966385143784 :=
  combineSlices (auxiliaryColumnSlice contact01) 8 4 4 6649263696980 6317121446804 contact01ColumnsSlice8 contact01ColumnsSlice12
private theorem contact01ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact01) 16 8 = 11672103791171 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 4 4 5993554333508 5678549457663 contact01ColumnsSlice16 contact01ColumnsSlice20
private theorem contact01ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact01) 24 8 = 10446270605520 :=
  combineSlices (auxiliaryColumnSlice contact01) 24 4 4 5372091500948 5074179104572 contact01ColumnsSlice24 contact01ColumnsSlice28
private theorem contact01ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact01) 32 8 = 9288845655452 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 4 4 4784815115572 4504030539880 contact01ColumnsSlice32 contact01ColumnsSlice36
private theorem contact01ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact01) 40 8 = 8199946310713 :=
  combineSlices (auxiliaryColumnSlice contact01) 40 4 4 4231809357676 3968136953037 contact01ColumnsSlice40 contact01ColumnsSlice44
private theorem contact01ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact01) 48 8 = 7179458382375 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 4 4 3713014569436 3466443812939 contact01ColumnsSlice48 contact01ColumnsSlice52
private theorem contact01ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact01) 56 8 = 6227496646637 :=
  combineSlices (auxiliaryColumnSlice contact01) 56 4 4 3228459104221 2999037542416 contact01ColumnsSlice56 contact01ColumnsSlice60
private theorem contact01ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact01) 64 8 = 5344017068551 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 4 4 2778168209811 2565848858740 contact01ColumnsSlice64 contact01ColumnsSlice68
private theorem contact01ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact01) 72 8 = 4528987433375 :=
  combineSlices (auxiliaryColumnSlice contact01) 72 4 4 2362083130612 2166904302763 contact01ColumnsSlice72 contact01ColumnsSlice76
private theorem contact01ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact01) 80 8 = 3782506432624 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 4 4 1980286336420 1802220096204 contact01ColumnsSlice80 contact01ColumnsSlice84
private theorem contact01ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact01) 88 8 = 3104447499222 :=
  combineSlices (auxiliaryColumnSlice contact01) 88 4 4 1632703854938 1471743644284 contact01ColumnsSlice88 contact01ColumnsSlice92
private theorem contact01ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact01) 96 8 = 2494925900982 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 4 4 1319370120319 1175555780663 contact01ColumnsSlice96 contact01ColumnsSlice100
private theorem contact01ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact01) 104 8 = 1953872302490 :=
  combineSlices (auxiliaryColumnSlice contact01) 104 4 4 1040292811332 913579491158 contact01ColumnsSlice104 contact01ColumnsSlice108
private theorem contact01ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact01) 112 8 = 1481281598914 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 4 4 795424767220 685856831694 contact01ColumnsSlice112 contact01ColumnsSlice116
private theorem contact01ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact01) 120 8 = 1077232064381 :=
  combineSlices (auxiliaryColumnSlice contact01) 120 4 4 584845916645 492386147736 contact01ColumnsSlice120 contact01ColumnsSlice124
private theorem contact01ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact01) 128 8 = 741603454367 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 4 4 408475835107 333127619260 contact01ColumnsSlice128 contact01ColumnsSlice132
private theorem contact01ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact01) 136 8 = 474519365139 :=
  combineSlices (auxiliaryColumnSlice contact01) 136 4 4 266364248130 208155117009 contact01ColumnsSlice136 contact01ColumnsSlice140
private theorem contact01ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact01) 144 8 = 275412823429 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 4 4 158439153918 116973669511 contact01ColumnsSlice144 contact01ColumnsSlice148
private theorem contact01ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact01) 152 8 = 140362743329 :=
  combineSlices (auxiliaryColumnSlice contact01) 152 4 4 83353058416 57009684913 contact01ColumnsSlice152 contact01ColumnsSlice156
private theorem contact01ColumnsJoin160_5 : sliceWindow (auxiliaryColumnSlice contact01) 160 5 = 44039146315 :=
  combineSlices (auxiliaryColumnSlice contact01) 160 4 1 37169263547 6869882768 contact01ColumnsSlice160 contact01ColumnsSlice164
private theorem contact01ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact01) 0 16 = 27295512921840 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 8 8 14329127778056 12966385143784 contact01ColumnsJoin0_8 contact01ColumnsJoin8_8
private theorem contact01ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact01) 16 16 = 22118374396691 :=
  combineSlices (auxiliaryColumnSlice contact01) 16 8 8 11672103791171 10446270605520 contact01ColumnsJoin16_8 contact01ColumnsJoin24_8
private theorem contact01ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact01) 32 16 = 17488791966165 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 8 8 9288845655452 8199946310713 contact01ColumnsJoin32_8 contact01ColumnsJoin40_8
private theorem contact01ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact01) 48 16 = 13406955029012 :=
  combineSlices (auxiliaryColumnSlice contact01) 48 8 8 7179458382375 6227496646637 contact01ColumnsJoin48_8 contact01ColumnsJoin56_8
private theorem contact01ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact01) 64 16 = 9873004501926 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 8 8 5344017068551 4528987433375 contact01ColumnsJoin64_8 contact01ColumnsJoin72_8
private theorem contact01ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact01) 80 16 = 6886953931846 :=
  combineSlices (auxiliaryColumnSlice contact01) 80 8 8 3782506432624 3104447499222 contact01ColumnsJoin80_8 contact01ColumnsJoin88_8
private theorem contact01ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact01) 96 16 = 4448798203472 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 8 8 2494925900982 1953872302490 contact01ColumnsJoin96_8 contact01ColumnsJoin104_8
private theorem contact01ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact01) 112 16 = 2558513663295 :=
  combineSlices (auxiliaryColumnSlice contact01) 112 8 8 1481281598914 1077232064381 contact01ColumnsJoin112_8 contact01ColumnsJoin120_8
private theorem contact01ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact01) 128 16 = 1216122819506 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 8 8 741603454367 474519365139 contact01ColumnsJoin128_8 contact01ColumnsJoin136_8
private theorem contact01ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact01) 144 16 = 415775566758 :=
  combineSlices (auxiliaryColumnSlice contact01) 144 8 8 275412823429 140362743329 contact01ColumnsJoin144_8 contact01ColumnsJoin152_8
private theorem contact01ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact01) 0 32 = 49413887318531 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 16 16 27295512921840 22118374396691 contact01ColumnsJoin0_16 contact01ColumnsJoin16_16
private theorem contact01ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact01) 32 32 = 30895746995177 :=
  combineSlices (auxiliaryColumnSlice contact01) 32 16 16 17488791966165 13406955029012 contact01ColumnsJoin32_16 contact01ColumnsJoin48_16
private theorem contact01ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact01) 64 32 = 16759958433772 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 16 16 9873004501926 6886953931846 contact01ColumnsJoin64_16 contact01ColumnsJoin80_16
private theorem contact01ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact01) 96 32 = 7007311866767 :=
  combineSlices (auxiliaryColumnSlice contact01) 96 16 16 4448798203472 2558513663295 contact01ColumnsJoin96_16 contact01ColumnsJoin112_16
private theorem contact01ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact01) 128 32 = 1631898386264 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 16 16 1216122819506 415775566758 contact01ColumnsJoin128_16 contact01ColumnsJoin144_16
private theorem contact01ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact01) 0 64 = 80309634313708 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 32 32 49413887318531 30895746995177 contact01ColumnsJoin0_32 contact01ColumnsJoin32_32
private theorem contact01ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact01) 64 64 = 23767270300539 :=
  combineSlices (auxiliaryColumnSlice contact01) 64 32 32 16759958433772 7007311866767 contact01ColumnsJoin64_32 contact01ColumnsJoin96_32
private theorem contact01ColumnsJoin128_37 : sliceWindow (auxiliaryColumnSlice contact01) 128 37 = 1675937532579 :=
  combineSlices (auxiliaryColumnSlice contact01) 128 32 5 1631898386264 44039146315 contact01ColumnsJoin128_32 contact01ColumnsJoin160_5
private theorem contact01ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact01) 0 128 = 104076904614247 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 64 64 80309634313708 23767270300539 contact01ColumnsJoin0_64 contact01ColumnsJoin64_64
private theorem contact01ColumnsJoin0_165 : sliceWindow (auxiliaryColumnSlice contact01) 0 165 = 105752842146826 :=
  combineSlices (auxiliaryColumnSlice contact01) 0 128 37 104076904614247 1675937532579 contact01ColumnsJoin0_128 contact01ColumnsJoin128_37
private theorem contact01OrdinaryRanks : ordinaryRankBound contact01 = 9260125939 := by decide +kernel
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
  margin_of_checked_counts contact01 165 2405351469914195 105752842146826 9260125939 318970250 rfl contact01OrdinaryColumns contact01ColumnsJoin0_165 contact01OrdinaryRanks contact01RanksJoin0_165 (by decide +kernel)

private theorem contact03OrdinaryColumns : ordinaryColumnCount contact03 = 2237386453734845 := by decide +kernel
private theorem contact03ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact03) 0 4 = 7519224233814 :=
  contactColumnsWindow_fast contact03 0 4 7519224233814 (by decide +kernel)
private theorem contact03ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact03) 4 4 = 7160472774470 :=
  contactColumnsWindow_fast contact03 4 4 7160472774470 (by decide +kernel)
private theorem contact03ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact03) 8 4 = 6810523461400 :=
  contactColumnsWindow_fast contact03 8 4 6810523461400 (by decide +kernel)
private theorem contact03ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact03) 12 4 = 6469376474880 :=
  contactColumnsWindow_fast contact03 12 4 6469376474880 (by decide +kernel)
private theorem contact03ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact03) 16 4 = 6137064800080 :=
  contactColumnsWindow_fast contact03 16 4 6137064800080 (by decide +kernel)
private theorem contact03ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact03) 20 4 = 5813574984505 :=
  contactColumnsWindow_fast contact03 20 4 5813574984505 (by decide +kernel)
private theorem contact03ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact03) 24 4 = 5498891028384 :=
  contactColumnsWindow_fast contact03 24 4 5498891028384 (by decide +kernel)
private theorem contact03ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact03) 28 4 = 5193011543893 :=
  contactColumnsWindow_fast contact03 28 4 5193011543893 (by decide +kernel)
private theorem contact03ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact03) 32 4 = 4895939462108 :=
  contactColumnsWindow_fast contact03 32 4 4895939462108 (by decide +kernel)
private theorem contact03ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact03) 36 4 = 4607707100991 :=
  contactColumnsWindow_fast contact03 36 4 4607707100991 (by decide +kernel)
private theorem contact03ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact03) 40 4 = 4328297699529 :=
  contactColumnsWindow_fast contact03 40 4 4328297699529 (by decide +kernel)
private theorem contact03ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact03) 44 4 = 4057696048304 :=
  contactColumnsWindow_fast contact03 44 4 4057696048304 (by decide +kernel)
private theorem contact03ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact03) 48 4 = 3795903409695 :=
  contactColumnsWindow_fast contact03 48 4 3795903409695 (by decide +kernel)
private theorem contact03ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact03) 52 4 = 3542921475460 :=
  contactColumnsWindow_fast contact03 52 4 3542921475460 (by decide +kernel)
private theorem contact03ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact03) 56 4 = 3298786066744 :=
  contactColumnsWindow_fast contact03 56 4 3298786066744 (by decide +kernel)
private theorem contact03ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact03) 60 4 = 3063473283903 :=
  contactColumnsWindow_fast contact03 60 4 3063473283903 (by decide +kernel)
private theorem contact03ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact03) 64 4 = 2836971758822 :=
  contactColumnsWindow_fast contact03 64 4 2836971758822 (by decide +kernel)
private theorem contact03ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact03) 68 4 = 2619279206853 :=
  contactColumnsWindow_fast contact03 68 4 2619279206853 (by decide +kernel)
private theorem contact03ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact03) 72 4 = 2410399432342 :=
  contactColumnsWindow_fast contact03 72 4 2410399432342 (by decide +kernel)
private theorem contact03ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact03) 76 4 = 2210367073942 :=
  contactColumnsWindow_fast contact03 76 4 2210367073942 (by decide +kernel)
private theorem contact03ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact03) 80 4 = 2019154950549 :=
  contactColumnsWindow_fast contact03 80 4 2019154950549 (by decide +kernel)
private theorem contact03ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact03) 84 4 = 1836753572386 :=
  contactColumnsWindow_fast contact03 84 4 1836753572386 (by decide +kernel)
private theorem contact03ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact03) 88 4 = 1663161185764 :=
  contactColumnsWindow_fast contact03 88 4 1663161185764 (by decide +kernel)
private theorem contact03ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact03) 92 4 = 1498384079746 :=
  contactColumnsWindow_fast contact03 92 4 1498384079746 (by decide +kernel)
private theorem contact03ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact03) 96 4 = 1342454173294 :=
  contactColumnsWindow_fast contact03 96 4 1342454173294 (by decide +kernel)
private theorem contact03ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact03) 100 4 = 1195342741236 :=
  contactColumnsWindow_fast contact03 100 4 1195342741236 (by decide +kernel)
private theorem contact03ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact03) 104 4 = 1057041691969 :=
  contactColumnsWindow_fast contact03 104 4 1057041691969 (by decide +kernel)
private theorem contact03ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact03) 108 4 = 927549278323 :=
  contactColumnsWindow_fast contact03 108 4 927549278323 (by decide +kernel)
private theorem contact03ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact03) 112 4 = 806874809422 :=
  contactColumnsWindow_fast contact03 112 4 806874809422 (by decide +kernel)
private theorem contact03ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact03) 116 4 = 695047644810 :=
  contactColumnsWindow_fast contact03 116 4 695047644810 (by decide +kernel)
private theorem contact03ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact03) 120 4 = 592036698345 :=
  contactColumnsWindow_fast contact03 120 4 592036698345 (by decide +kernel)
private theorem contact03ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact03) 124 4 = 497835906079 :=
  contactColumnsWindow_fast contact03 124 4 497835906079 (by decide +kernel)
private theorem contact03ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact03) 128 4 = 412443553275 :=
  contactColumnsWindow_fast contact03 128 4 412443553275 (by decide +kernel)
private theorem contact03ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact03) 132 4 = 335872785330 :=
  contactColumnsWindow_fast contact03 132 4 335872785330 (by decide +kernel)
private theorem contact03ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact03) 136 4 = 268147296333 :=
  contactColumnsWindow_fast contact03 136 4 268147296333 (by decide +kernel)
private theorem contact03ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact03) 140 4 = 209231729594 :=
  contactColumnsWindow_fast contact03 140 4 209231729594 (by decide +kernel)
private theorem contact03ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact03) 144 4 = 159030311330 :=
  contactColumnsWindow_fast contact03 144 4 159030311330 (by decide +kernel)
private theorem contact03ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact03) 148 4 = 117252495389 :=
  contactColumnsWindow_fast contact03 148 4 117252495389 (by decide +kernel)
private theorem contact03ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact03) 152 4 = 83455474724 :=
  contactColumnsWindow_fast contact03 152 4 83455474724 (by decide +kernel)
private theorem contact03ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact03) 156 4 = 57032874677 :=
  contactColumnsWindow_fast contact03 156 4 57032874677 (by decide +kernel)
private theorem contact03ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact03) 160 4 = 37170682087 :=
  contactColumnsWindow_fast contact03 160 4 37170682087 (by decide +kernel)
private theorem contact03ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact03) 0 8 = 14679697008284 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 4 4 7519224233814 7160472774470 contact03ColumnsSlice0 contact03ColumnsSlice4
private theorem contact03ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact03) 8 8 = 13279899936280 :=
  combineSlices (auxiliaryColumnSlice contact03) 8 4 4 6810523461400 6469376474880 contact03ColumnsSlice8 contact03ColumnsSlice12
private theorem contact03ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact03) 16 8 = 11950639784585 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 4 4 6137064800080 5813574984505 contact03ColumnsSlice16 contact03ColumnsSlice20
private theorem contact03ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact03) 24 8 = 10691902572277 :=
  combineSlices (auxiliaryColumnSlice contact03) 24 4 4 5498891028384 5193011543893 contact03ColumnsSlice24 contact03ColumnsSlice28
private theorem contact03ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact03) 32 8 = 9503646563099 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 4 4 4895939462108 4607707100991 contact03ColumnsSlice32 contact03ColumnsSlice36
private theorem contact03ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact03) 40 8 = 8385993747833 :=
  combineSlices (auxiliaryColumnSlice contact03) 40 4 4 4328297699529 4057696048304 contact03ColumnsSlice40 contact03ColumnsSlice44
private theorem contact03ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact03) 48 8 = 7338824885155 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 4 4 3795903409695 3542921475460 contact03ColumnsSlice48 contact03ColumnsSlice52
private theorem contact03ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact03) 56 8 = 6362259350647 :=
  combineSlices (auxiliaryColumnSlice contact03) 56 4 4 3298786066744 3063473283903 contact03ColumnsSlice56 contact03ColumnsSlice60
private theorem contact03ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact03) 64 8 = 5456250965675 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 4 4 2836971758822 2619279206853 contact03ColumnsSlice64 contact03ColumnsSlice68
private theorem contact03ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact03) 72 8 = 4620766506284 :=
  combineSlices (auxiliaryColumnSlice contact03) 72 4 4 2410399432342 2210367073942 contact03ColumnsSlice72 contact03ColumnsSlice76
private theorem contact03ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact03) 80 8 = 3855908522935 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 4 4 2019154950549 1836753572386 contact03ColumnsSlice80 contact03ColumnsSlice84
private theorem contact03ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact03) 88 8 = 3161545265510 :=
  combineSlices (auxiliaryColumnSlice contact03) 88 4 4 1663161185764 1498384079746 contact03ColumnsSlice88 contact03ColumnsSlice92
private theorem contact03ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact03) 96 8 = 2537796914530 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 4 4 1342454173294 1195342741236 contact03ColumnsSlice96 contact03ColumnsSlice100
private theorem contact03ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact03) 104 8 = 1984590970292 :=
  combineSlices (auxiliaryColumnSlice contact03) 104 4 4 1057041691969 927549278323 contact03ColumnsSlice104 contact03ColumnsSlice108
private theorem contact03ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact03) 112 8 = 1501922454232 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 4 4 806874809422 695047644810 contact03ColumnsSlice112 contact03ColumnsSlice116
private theorem contact03ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact03) 120 8 = 1089872604424 :=
  combineSlices (auxiliaryColumnSlice contact03) 120 4 4 592036698345 497835906079 contact03ColumnsSlice120 contact03ColumnsSlice124
private theorem contact03ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact03) 128 8 = 748316338605 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 4 4 412443553275 335872785330 contact03ColumnsSlice128 contact03ColumnsSlice132
private theorem contact03ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact03) 136 8 = 477379025927 :=
  combineSlices (auxiliaryColumnSlice contact03) 136 4 4 268147296333 209231729594 contact03ColumnsSlice136 contact03ColumnsSlice140
private theorem contact03ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact03) 144 8 = 276282806719 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 4 4 159030311330 117252495389 contact03ColumnsSlice144 contact03ColumnsSlice148
private theorem contact03ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact03) 152 8 = 140488349401 :=
  combineSlices (auxiliaryColumnSlice contact03) 152 4 4 83455474724 57032874677 contact03ColumnsSlice152 contact03ColumnsSlice156
private theorem contact03ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact03) 0 16 = 27959596944564 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 8 8 14679697008284 13279899936280 contact03ColumnsJoin0_8 contact03ColumnsJoin8_8
private theorem contact03ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact03) 16 16 = 22642542356862 :=
  combineSlices (auxiliaryColumnSlice contact03) 16 8 8 11950639784585 10691902572277 contact03ColumnsJoin16_8 contact03ColumnsJoin24_8
private theorem contact03ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact03) 32 16 = 17889640310932 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 8 8 9503646563099 8385993747833 contact03ColumnsJoin32_8 contact03ColumnsJoin40_8
private theorem contact03ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact03) 48 16 = 13701084235802 :=
  combineSlices (auxiliaryColumnSlice contact03) 48 8 8 7338824885155 6362259350647 contact03ColumnsJoin48_8 contact03ColumnsJoin56_8
private theorem contact03ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact03) 64 16 = 10077017471959 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 8 8 5456250965675 4620766506284 contact03ColumnsJoin64_8 contact03ColumnsJoin72_8
private theorem contact03ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact03) 80 16 = 7017453788445 :=
  combineSlices (auxiliaryColumnSlice contact03) 80 8 8 3855908522935 3161545265510 contact03ColumnsJoin80_8 contact03ColumnsJoin88_8
private theorem contact03ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact03) 96 16 = 4522387884822 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 8 8 2537796914530 1984590970292 contact03ColumnsJoin96_8 contact03ColumnsJoin104_8
private theorem contact03ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact03) 112 16 = 2591795058656 :=
  combineSlices (auxiliaryColumnSlice contact03) 112 8 8 1501922454232 1089872604424 contact03ColumnsJoin112_8 contact03ColumnsJoin120_8
private theorem contact03ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact03) 128 16 = 1225695364532 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 8 8 748316338605 477379025927 contact03ColumnsJoin128_8 contact03ColumnsJoin136_8
private theorem contact03ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact03) 144 16 = 416771156120 :=
  combineSlices (auxiliaryColumnSlice contact03) 144 8 8 276282806719 140488349401 contact03ColumnsJoin144_8 contact03ColumnsJoin152_8
private theorem contact03ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact03) 0 32 = 50602139301426 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 16 16 27959596944564 22642542356862 contact03ColumnsJoin0_16 contact03ColumnsJoin16_16
private theorem contact03ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact03) 32 32 = 31590724546734 :=
  combineSlices (auxiliaryColumnSlice contact03) 32 16 16 17889640310932 13701084235802 contact03ColumnsJoin32_16 contact03ColumnsJoin48_16
private theorem contact03ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact03) 64 32 = 17094471260404 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 16 16 10077017471959 7017453788445 contact03ColumnsJoin64_16 contact03ColumnsJoin80_16
private theorem contact03ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact03) 96 32 = 7114182943478 :=
  combineSlices (auxiliaryColumnSlice contact03) 96 16 16 4522387884822 2591795058656 contact03ColumnsJoin96_16 contact03ColumnsJoin112_16
private theorem contact03ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact03) 128 32 = 1642466520652 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 16 16 1225695364532 416771156120 contact03ColumnsJoin128_16 contact03ColumnsJoin144_16
private theorem contact03ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact03) 0 64 = 82192863848160 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 32 32 50602139301426 31590724546734 contact03ColumnsJoin0_32 contact03ColumnsJoin32_32
private theorem contact03ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact03) 64 64 = 24208654203882 :=
  combineSlices (auxiliaryColumnSlice contact03) 64 32 32 17094471260404 7114182943478 contact03ColumnsJoin64_32 contact03ColumnsJoin96_32
private theorem contact03ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact03) 128 36 = 1679637202739 :=
  combineSlices (auxiliaryColumnSlice contact03) 128 32 4 1642466520652 37170682087 contact03ColumnsJoin128_32 contact03ColumnsSlice160
private theorem contact03ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact03) 0 128 = 106401518052042 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 64 64 82192863848160 24208654203882 contact03ColumnsJoin0_64 contact03ColumnsJoin64_64
private theorem contact03ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact03) 0 164 = 108081155254781 :=
  combineSlices (auxiliaryColumnSlice contact03) 0 128 36 106401518052042 1679637202739 contact03ColumnsJoin0_128 contact03ColumnsJoin128_36
private theorem contact03OrdinaryRanks : ordinaryRankBound contact03 = 8620626907 := by decide +kernel
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
  margin_of_checked_counts contact03 164 2237386453734845 108081155254781 8620626907 326617835 rfl contact03OrdinaryColumns contact03ColumnsJoin0_164 contact03OrdinaryRanks contact03RanksJoin0_164 (by decide +kernel)

private theorem contact05OrdinaryColumns : ordinaryColumnCount contact05 = 2138189529505366 := by decide +kernel
private theorem contact05ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact05) 0 4 = 7743617595210 :=
  contactColumnsWindow_fast contact05 0 4 7743617595210 (by decide +kernel)
private theorem contact05ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact05) 4 4 = 7373156313626 :=
  contactColumnsWindow_fast contact05 4 4 7373156313626 (by decide +kernel)
private theorem contact05ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact05) 8 4 = 7011811502762 :=
  contactColumnsWindow_fast contact05 8 4 7011811502762 (by decide +kernel)
private theorem contact05ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact05) 12 4 = 6659583357819 :=
  contactColumnsWindow_fast contact05 12 4 6659583357819 (by decide +kernel)
private theorem contact05ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact05) 16 4 = 6316506568186 :=
  contactColumnsWindow_fast contact05 16 4 6316506568186 (by decide +kernel)
private theorem contact05ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact05) 20 4 = 5982566945724 :=
  contactColumnsWindow_fast contact05 20 4 5982566945724 (by decide +kernel)
private theorem contact05ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact05) 24 4 = 5657747582242 :=
  contactColumnsWindow_fast contact05 24 4 5657747582242 (by decide +kernel)
private theorem contact05ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact05) 28 4 = 5342047060878 :=
  contactColumnsWindow_fast contact05 28 4 5342047060878 (by decide +kernel)
private theorem contact05ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact05) 32 4 = 5035468416033 :=
  contactColumnsWindow_fast contact05 32 4 5035468416033 (by decide +kernel)
private theorem contact05ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact05) 36 4 = 4738045697594 :=
  contactColumnsWindow_fast contact05 36 4 4738045697594 (by decide +kernel)
private theorem contact05ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact05) 40 4 = 4449761146706 :=
  contactColumnsWindow_fast contact05 40 4 4449761146706 (by decide +kernel)
private theorem contact05ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact05) 44 4 = 4170598777929 :=
  contactColumnsWindow_fast contact05 44 4 4170598777929 (by decide +kernel)
private theorem contact05ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact05) 48 4 = 3900559872546 :=
  contactColumnsWindow_fast contact05 48 4 3900559872546 (by decide +kernel)
private theorem contact05ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact05) 52 4 = 3639646242101 :=
  contactColumnsWindow_fast contact05 52 4 3639646242101 (by decide +kernel)
private theorem contact05ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact05) 56 4 = 3387895542921 :=
  contactColumnsWindow_fast contact05 56 4 3387895542921 (by decide +kernel)
private theorem contact05ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact05) 60 4 = 3145282545866 :=
  contactColumnsWindow_fast contact05 60 4 3145282545866 (by decide +kernel)
private theorem contact05ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact05) 64 4 = 2911795294335 :=
  contactColumnsWindow_fast contact05 64 4 2911795294335 (by decide +kernel)
private theorem contact05ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact05) 68 4 = 2687431466694 :=
  contactColumnsWindow_fast contact05 68 4 2687431466694 (by decide +kernel)
private theorem contact05ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact05) 72 4 = 2472195087978 :=
  contactColumnsWindow_fast contact05 72 4 2472195087978 (by decide +kernel)
private theorem contact05ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact05) 76 4 = 2266122581151 :=
  contactColumnsWindow_fast contact05 76 4 2266122581151 (by decide +kernel)
private theorem contact05ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact05) 80 4 = 2069185244522 :=
  contactColumnsWindow_fast contact05 80 4 2069185244522 (by decide +kernel)
private theorem contact05ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact05) 84 4 = 1881373131429 :=
  contactColumnsWindow_fast contact05 84 4 1881373131429 (by decide +kernel)
private theorem contact05ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact05) 88 4 = 1702684461669 :=
  contactColumnsWindow_fast contact05 88 4 1702684461669 (by decide +kernel)
private theorem contact05ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact05) 92 4 = 1533125869086 :=
  contactColumnsWindow_fast contact05 92 4 1533125869086 (by decide +kernel)
private theorem contact05ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact05) 96 4 = 1372730928890 :=
  contactColumnsWindow_fast contact05 96 4 1372730928890 (by decide +kernel)
private theorem contact05ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact05) 100 4 = 1221469285236 :=
  contactColumnsWindow_fast contact05 100 4 1221469285236 (by decide +kernel)
private theorem contact05ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact05) 104 4 = 1079332496042 :=
  contactColumnsWindow_fast contact05 104 4 1079332496042 (by decide +kernel)
private theorem contact05ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact05) 108 4 = 946318788135 :=
  contactColumnsWindow_fast contact05 108 4 946318788135 (by decide +kernel)
private theorem contact05ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact05) 112 4 = 822437949690 :=
  contactColumnsWindow_fast contact05 112 4 822437949690 (by decide +kernel)
private theorem contact05ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact05) 116 4 = 707720871353 :=
  contactColumnsWindow_fast contact05 116 4 707720871353 (by decide +kernel)
private theorem contact05ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact05) 120 4 = 602134711272 :=
  contactColumnsWindow_fast contact05 120 4 602134711272 (by decide +kernel)
private theorem contact05ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact05) 124 4 = 505673172650 :=
  contactColumnsWindow_fast contact05 124 4 505673172650 (by decide +kernel)
private theorem contact05ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact05) 128 4 = 418334515872 :=
  contactColumnsWindow_fast contact05 128 4 418334515872 (by decide +kernel)
private theorem contact05ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact05) 132 4 = 340132551095 :=
  contactColumnsWindow_fast contact05 132 4 340132551095 (by decide +kernel)
private theorem contact05ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact05) 136 4 = 271092207918 :=
  contactColumnsWindow_fast contact05 136 4 271092207918 (by decide +kernel)
private theorem contact05ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact05) 140 4 = 211168646030 :=
  contactColumnsWindow_fast contact05 140 4 211168646030 (by decide +kernel)
private theorem contact05ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact05) 144 4 = 160223169224 :=
  contactColumnsWindow_fast contact05 144 4 160223169224 (by decide +kernel)
private theorem contact05ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact05) 148 4 = 117920758299 :=
  contactColumnsWindow_fast contact05 148 4 117920758299 (by decide +kernel)
private theorem contact05ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact05) 152 4 = 83781506376 :=
  contactColumnsWindow_fast contact05 152 4 83781506376 (by decide +kernel)
private theorem contact05ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact05) 156 4 = 57160428045 :=
  contactColumnsWindow_fast contact05 156 4 57160428045 (by decide +kernel)
private theorem contact05ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact05) 160 4 = 37203438567 :=
  contactColumnsWindow_fast contact05 160 4 37203438567 (by decide +kernel)
private theorem contact05ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact05) 0 8 = 15116773908836 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 4 4 7743617595210 7373156313626 contact05ColumnsSlice0 contact05ColumnsSlice4
private theorem contact05ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact05) 8 8 = 13671394860581 :=
  combineSlices (auxiliaryColumnSlice contact05) 8 4 4 7011811502762 6659583357819 contact05ColumnsSlice8 contact05ColumnsSlice12
private theorem contact05ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact05) 16 8 = 12299073513910 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 4 4 6316506568186 5982566945724 contact05ColumnsSlice16 contact05ColumnsSlice20
private theorem contact05ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact05) 24 8 = 10999794643120 :=
  combineSlices (auxiliaryColumnSlice contact05) 24 4 4 5657747582242 5342047060878 contact05ColumnsSlice24 contact05ColumnsSlice28
private theorem contact05ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact05) 32 8 = 9773514113627 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 4 4 5035468416033 4738045697594 contact05ColumnsSlice32 contact05ColumnsSlice36
private theorem contact05ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact05) 40 8 = 8620359924635 :=
  combineSlices (auxiliaryColumnSlice contact05) 40 4 4 4449761146706 4170598777929 contact05ColumnsSlice40 contact05ColumnsSlice44
private theorem contact05ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact05) 48 8 = 7540206114647 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 4 4 3900559872546 3639646242101 contact05ColumnsSlice48 contact05ColumnsSlice52
private theorem contact05ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact05) 56 8 = 6533178088787 :=
  combineSlices (auxiliaryColumnSlice contact05) 56 4 4 3387895542921 3145282545866 contact05ColumnsSlice56 contact05ColumnsSlice60
private theorem contact05ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact05) 64 8 = 5599226761029 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 4 4 2911795294335 2687431466694 contact05ColumnsSlice64 contact05ColumnsSlice68
private theorem contact05ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact05) 72 8 = 4738317669129 :=
  combineSlices (auxiliaryColumnSlice contact05) 72 4 4 2472195087978 2266122581151 contact05ColumnsSlice72 contact05ColumnsSlice76
private theorem contact05ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact05) 80 8 = 3950558375951 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 4 4 2069185244522 1881373131429 contact05ColumnsSlice80 contact05ColumnsSlice84
private theorem contact05ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact05) 88 8 = 3235810330755 :=
  combineSlices (auxiliaryColumnSlice contact05) 88 4 4 1702684461669 1533125869086 contact05ColumnsSlice88 contact05ColumnsSlice92
private theorem contact05ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact05) 96 8 = 2594200214126 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 4 4 1372730928890 1221469285236 contact05ColumnsSlice96 contact05ColumnsSlice100
private theorem contact05ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact05) 104 8 = 2025651284177 :=
  combineSlices (auxiliaryColumnSlice contact05) 104 4 4 1079332496042 946318788135 contact05ColumnsSlice104 contact05ColumnsSlice108
private theorem contact05ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact05) 112 8 = 1530158821043 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 4 4 822437949690 707720871353 contact05ColumnsSlice112 contact05ColumnsSlice116
private theorem contact05ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact05) 120 8 = 1107807883922 :=
  combineSlices (auxiliaryColumnSlice contact05) 120 4 4 602134711272 505673172650 contact05ColumnsSlice120 contact05ColumnsSlice124
private theorem contact05ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact05) 128 8 = 758467066967 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 4 4 418334515872 340132551095 contact05ColumnsSlice128 contact05ColumnsSlice132
private theorem contact05ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact05) 136 8 = 482260853948 :=
  combineSlices (auxiliaryColumnSlice contact05) 136 4 4 271092207918 211168646030 contact05ColumnsSlice136 contact05ColumnsSlice140
private theorem contact05ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact05) 144 8 = 278143927523 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 4 4 160223169224 117920758299 contact05ColumnsSlice144 contact05ColumnsSlice148
private theorem contact05ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact05) 152 8 = 140941934421 :=
  combineSlices (auxiliaryColumnSlice contact05) 152 4 4 83781506376 57160428045 contact05ColumnsSlice152 contact05ColumnsSlice156
private theorem contact05ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact05) 0 16 = 28788168769417 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 8 8 15116773908836 13671394860581 contact05ColumnsJoin0_8 contact05ColumnsJoin8_8
private theorem contact05ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact05) 16 16 = 23298868157030 :=
  combineSlices (auxiliaryColumnSlice contact05) 16 8 8 12299073513910 10999794643120 contact05ColumnsJoin16_8 contact05ColumnsJoin24_8
private theorem contact05ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact05) 32 16 = 18393874038262 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 8 8 9773514113627 8620359924635 contact05ColumnsJoin32_8 contact05ColumnsJoin40_8
private theorem contact05ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact05) 48 16 = 14073384203434 :=
  combineSlices (auxiliaryColumnSlice contact05) 48 8 8 7540206114647 6533178088787 contact05ColumnsJoin48_8 contact05ColumnsJoin56_8
private theorem contact05ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact05) 64 16 = 10337544430158 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 8 8 5599226761029 4738317669129 contact05ColumnsJoin64_8 contact05ColumnsJoin72_8
private theorem contact05ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact05) 80 16 = 7186368706706 :=
  combineSlices (auxiliaryColumnSlice contact05) 80 8 8 3950558375951 3235810330755 contact05ColumnsJoin80_8 contact05ColumnsJoin88_8
private theorem contact05ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact05) 96 16 = 4619851498303 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 8 8 2594200214126 2025651284177 contact05ColumnsJoin96_8 contact05ColumnsJoin104_8
private theorem contact05ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact05) 112 16 = 2637966704965 :=
  combineSlices (auxiliaryColumnSlice contact05) 112 8 8 1530158821043 1107807883922 contact05ColumnsJoin112_8 contact05ColumnsJoin120_8
private theorem contact05ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact05) 128 16 = 1240727920915 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 8 8 758467066967 482260853948 contact05ColumnsJoin128_8 contact05ColumnsJoin136_8
private theorem contact05ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact05) 144 16 = 419085861944 :=
  combineSlices (auxiliaryColumnSlice contact05) 144 8 8 278143927523 140941934421 contact05ColumnsJoin144_8 contact05ColumnsJoin152_8
private theorem contact05ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact05) 0 32 = 52087036926447 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 16 16 28788168769417 23298868157030 contact05ColumnsJoin0_16 contact05ColumnsJoin16_16
private theorem contact05ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact05) 32 32 = 32467258241696 :=
  combineSlices (auxiliaryColumnSlice contact05) 32 16 16 18393874038262 14073384203434 contact05ColumnsJoin32_16 contact05ColumnsJoin48_16
private theorem contact05ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact05) 64 32 = 17523913136864 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 16 16 10337544430158 7186368706706 contact05ColumnsJoin64_16 contact05ColumnsJoin80_16
private theorem contact05ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact05) 96 32 = 7257818203268 :=
  combineSlices (auxiliaryColumnSlice contact05) 96 16 16 4619851498303 2637966704965 contact05ColumnsJoin96_16 contact05ColumnsJoin112_16
private theorem contact05ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact05) 128 32 = 1659813782859 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 16 16 1240727920915 419085861944 contact05ColumnsJoin128_16 contact05ColumnsJoin144_16
private theorem contact05ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact05) 0 64 = 84554295168143 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 32 32 52087036926447 32467258241696 contact05ColumnsJoin0_32 contact05ColumnsJoin32_32
private theorem contact05ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact05) 64 64 = 24781731340132 :=
  combineSlices (auxiliaryColumnSlice contact05) 64 32 32 17523913136864 7257818203268 contact05ColumnsJoin64_32 contact05ColumnsJoin96_32
private theorem contact05ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact05) 128 36 = 1697017221426 :=
  combineSlices (auxiliaryColumnSlice contact05) 128 32 4 1659813782859 37203438567 contact05ColumnsJoin128_32 contact05ColumnsSlice160
private theorem contact05ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact05) 0 128 = 109336026508275 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 64 64 84554295168143 24781731340132 contact05ColumnsJoin0_64 contact05ColumnsJoin64_64
private theorem contact05ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact05) 0 164 = 111033043729701 :=
  combineSlices (auxiliaryColumnSlice contact05) 0 128 36 109336026508275 1697017221426 contact05ColumnsJoin0_128 contact05ColumnsJoin128_36
private theorem contact05OrdinaryRanks : ordinaryRankBound contact05 = 8243879428 := by decide +kernel
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
private theorem contact05RanksSlice152 : sliceWindow (auxiliaryRankSlice contact05) 152 12 = 0 :=
  contactRankWindow_of_rec contact05 152 12 0 (by decide +kernel)
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
private theorem contact05RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact05) 144 20 = 18067 :=
  combineSlices (auxiliaryRankSlice contact05) 144 8 12 18067 0 contact05RanksJoin144_8 contact05RanksSlice152
private theorem contact05RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact05) 0 32 = 185982544 :=
  combineSlices (auxiliaryRankSlice contact05) 0 16 16 106053800 79928744 contact05RanksJoin0_16 contact05RanksJoin16_16
private theorem contact05RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact05) 32 32 = 97635070 :=
  combineSlices (auxiliaryRankSlice contact05) 32 16 16 57842344 39792726 contact05RanksJoin32_16 contact05RanksJoin48_16
private theorem contact05RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact05) 64 32 = 40874783 :=
  combineSlices (auxiliaryRankSlice contact05) 64 16 16 25689111 15185672 contact05RanksJoin64_16 contact05RanksJoin80_16
private theorem contact05RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact05) 96 32 = 10990212 :=
  combineSlices (auxiliaryRankSlice contact05) 96 16 16 7829277 3160935 contact05RanksJoin96_16 contact05RanksJoin112_16
private theorem contact05RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact05) 128 36 = 739723 :=
  combineSlices (auxiliaryRankSlice contact05) 128 16 20 721656 18067 contact05RanksJoin128_16 contact05RanksJoin144_20
private theorem contact05RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact05) 0 64 = 283617614 :=
  combineSlices (auxiliaryRankSlice contact05) 0 32 32 185982544 97635070 contact05RanksJoin0_32 contact05RanksJoin32_32
private theorem contact05RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact05) 64 64 = 51864995 :=
  combineSlices (auxiliaryRankSlice contact05) 64 32 32 40874783 10990212 contact05RanksJoin64_32 contact05RanksJoin96_32
private theorem contact05RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact05) 0 128 = 335482609 :=
  combineSlices (auxiliaryRankSlice contact05) 0 64 64 283617614 51864995 contact05RanksJoin0_64 contact05RanksJoin64_64
private theorem contact05RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact05) 0 164 = 336222332 :=
  combineSlices (auxiliaryRankSlice contact05) 0 128 36 335482609 739723 contact05RanksJoin0_128 contact05RanksJoin128_36
theorem contact05_margin : sourceMargin contact05 :=
  margin_of_checked_counts contact05 164 2138189529505366 111033043729701 8243879428 336222332 rfl contact05OrdinaryColumns contact05ColumnsJoin0_164 contact05OrdinaryRanks contact05RanksJoin0_164 (by decide +kernel)

private theorem contact07OrdinaryColumns : ordinaryColumnCount contact07 = 2042486315709952 := by decide +kernel
private theorem contact07ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact07) 0 4 = 8153249872594 :=
  contactColumnsWindow_fast contact07 0 4 8153249872594 (by decide +kernel)
private theorem contact07ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact07) 4 4 = 7761084304130 :=
  contactColumnsWindow_fast contact07 4 4 7761084304130 (by decide +kernel)
private theorem contact07ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact07) 8 4 = 7378626882466 :=
  contactColumnsWindow_fast contact07 8 4 7378626882466 (by decide +kernel)
private theorem contact07ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact07) 12 4 = 7005877829607 :=
  contactColumnsWindow_fast contact07 12 4 7005877829607 (by decide +kernel)
private theorem contact07ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact07) 16 4 = 6642874973218 :=
  contactColumnsWindow_fast contact07 16 4 6642874973218 (by decide +kernel)
private theorem contact07ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact07) 20 4 = 6289602776039 :=
  contactColumnsWindow_fast contact07 20 4 6289602776039 (by decide +kernel)
private theorem contact07ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact07) 24 4 = 5946042664098 :=
  contactColumnsWindow_fast contact07 24 4 5946042664098 (by decide +kernel)
private theorem contact07ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact07) 28 4 = 5612193162442 :=
  contactColumnsWindow_fast contact07 28 4 5612193162442 (by decide +kernel)
private theorem contact07ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact07) 32 4 = 5288057499197 :=
  contactColumnsWindow_fast contact07 32 4 5288057499197 (by decide +kernel)
private theorem contact07ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact07) 36 4 = 4973672908062 :=
  contactColumnsWindow_fast contact07 36 4 4973672908062 (by decide +kernel)
private theorem contact07ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact07) 40 4 = 4669019806042 :=
  contactColumnsWindow_fast contact07 40 4 4669019806042 (by decide +kernel)
private theorem contact07ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact07) 44 4 = 4374080777087 :=
  contactColumnsWindow_fast contact07 44 4 4374080777087 (by decide +kernel)
private theorem contact07ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact07) 48 4 = 4088857140282 :=
  contactColumnsWindow_fast contact07 48 4 4088857140282 (by decide +kernel)
private theorem contact07ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact07) 52 4 = 3813350923924 :=
  contactColumnsWindow_fast contact07 52 4 3813350923924 (by decide +kernel)
private theorem contact07ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact07) 56 4 = 3547603164799 :=
  contactColumnsWindow_fast contact07 56 4 3547603164799 (by decide +kernel)
private theorem contact07ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact07) 60 4 = 3291586195702 :=
  contactColumnsWindow_fast contact07 60 4 3291586195702 (by decide +kernel)
private theorem contact07ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact07) 64 4 = 3045286974869 :=
  contactColumnsWindow_fast contact07 64 4 3045286974869 (by decide +kernel)
private theorem contact07ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact07) 68 4 = 2808703106682 :=
  contactColumnsWindow_fast contact07 68 4 2808703106682 (by decide +kernel)
private theorem contact07ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact07) 72 4 = 2581839018866 :=
  contactColumnsWindow_fast contact07 72 4 2581839018866 (by decide +kernel)
private theorem contact07ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact07) 76 4 = 2364734421205 :=
  contactColumnsWindow_fast contact07 76 4 2364734421205 (by decide +kernel)
private theorem contact07ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact07) 80 4 = 2157357823162 :=
  contactColumnsWindow_fast contact07 80 4 2157357823162 (by decide +kernel)
private theorem contact07ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact07) 84 4 = 1959698432476 :=
  contactColumnsWindow_fast contact07 84 4 1959698432476 (by decide +kernel)
private theorem contact07ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact07) 88 4 = 1771754415910 :=
  contactColumnsWindow_fast contact07 88 4 1771754415910 (by decide +kernel)
private theorem contact07ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact07) 92 4 = 1593533038430 :=
  contactColumnsWindow_fast contact07 92 4 1593533038430 (by decide +kernel)
private theorem contact07ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact07) 96 4 = 1425070925683 :=
  contactColumnsWindow_fast contact07 96 4 1425070925683 (by decide +kernel)
private theorem contact07ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact07) 100 4 = 1266334732567 :=
  contactColumnsWindow_fast contact07 100 4 1266334732567 (by decide +kernel)
private theorem contact07ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact07) 104 4 = 1117315364458 :=
  contactColumnsWindow_fast contact07 104 4 1117315364458 (by decide +kernel)
private theorem contact07ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact07) 108 4 = 978010996174 :=
  contactColumnsWindow_fast contact07 108 4 978010996174 (by decide +kernel)
private theorem contact07ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact07) 112 4 = 848432295794 :=
  contactColumnsWindow_fast contact07 112 4 848432295794 (by decide +kernel)
private theorem contact07ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact07) 116 4 = 728612973858 :=
  contactColumnsWindow_fast contact07 116 4 728612973858 (by decide +kernel)
private theorem contact07ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact07) 120 4 = 618516968953 :=
  contactColumnsWindow_fast contact07 120 4 618516968953 (by decide +kernel)
private theorem contact07ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact07) 124 4 = 518137547230 :=
  contactColumnsWindow_fast contact07 124 4 518137547230 (by decide +kernel)
private theorem contact07ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact07) 128 4 = 427472919315 :=
  contactColumnsWindow_fast contact07 128 4 427472919315 (by decide +kernel)
private theorem contact07ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact07) 132 4 = 346538118043 :=
  contactColumnsWindow_fast contact07 132 4 346538118043 (by decide +kernel)
private theorem contact07ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact07) 136 4 = 275359206507 :=
  contactColumnsWindow_fast contact07 136 4 275359206507 (by decide +kernel)
private theorem contact07ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact07) 140 4 = 213850611073 :=
  contactColumnsWindow_fast contact07 140 4 213850611073 (by decide +kernel)
private theorem contact07ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact07) 144 4 = 161775417534 :=
  contactColumnsWindow_fast contact07 144 4 161775417534 (by decide +kernel)
private theorem contact07ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact07) 148 4 = 118718702705 :=
  contactColumnsWindow_fast contact07 148 4 118718702705 (by decide +kernel)
private theorem contact07ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact07) 152 4 = 84124933595 :=
  contactColumnsWindow_fast contact07 152 4 84124933595 (by decide +kernel)
private theorem contact07ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact07) 156 4 = 57271646531 :=
  contactColumnsWindow_fast contact07 156 4 57271646531 (by decide +kernel)
private theorem contact07ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact07) 160 4 = 37225094941 :=
  contactColumnsWindow_fast contact07 160 4 37225094941 (by decide +kernel)
private theorem contact07ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact07) 0 8 = 15914334176724 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 4 4 8153249872594 7761084304130 contact07ColumnsSlice0 contact07ColumnsSlice4
private theorem contact07ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact07) 8 8 = 14384504712073 :=
  combineSlices (auxiliaryColumnSlice contact07) 8 4 4 7378626882466 7005877829607 contact07ColumnsSlice8 contact07ColumnsSlice12
private theorem contact07ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact07) 16 8 = 12932477749257 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 4 4 6642874973218 6289602776039 contact07ColumnsSlice16 contact07ColumnsSlice20
private theorem contact07ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact07) 24 8 = 11558235826540 :=
  combineSlices (auxiliaryColumnSlice contact07) 24 4 4 5946042664098 5612193162442 contact07ColumnsSlice24 contact07ColumnsSlice28
private theorem contact07ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact07) 32 8 = 10261730407259 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 4 4 5288057499197 4973672908062 contact07ColumnsSlice32 contact07ColumnsSlice36
private theorem contact07ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact07) 40 8 = 9043100583129 :=
  combineSlices (auxiliaryColumnSlice contact07) 40 4 4 4669019806042 4374080777087 contact07ColumnsSlice40 contact07ColumnsSlice44
private theorem contact07ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact07) 48 8 = 7902208064206 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 4 4 4088857140282 3813350923924 contact07ColumnsSlice48 contact07ColumnsSlice52
private theorem contact07ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact07) 56 8 = 6839189360501 :=
  combineSlices (auxiliaryColumnSlice contact07) 56 4 4 3547603164799 3291586195702 contact07ColumnsSlice56 contact07ColumnsSlice60
private theorem contact07ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact07) 64 8 = 5853990081551 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 4 4 3045286974869 2808703106682 contact07ColumnsSlice64 contact07ColumnsSlice68
private theorem contact07ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact07) 72 8 = 4946573440071 :=
  combineSlices (auxiliaryColumnSlice contact07) 72 4 4 2581839018866 2364734421205 contact07ColumnsSlice72 contact07ColumnsSlice76
private theorem contact07ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact07) 80 8 = 4117056255638 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 4 4 2157357823162 1959698432476 contact07ColumnsSlice80 contact07ColumnsSlice84
private theorem contact07ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact07) 88 8 = 3365287454340 :=
  combineSlices (auxiliaryColumnSlice contact07) 88 4 4 1771754415910 1593533038430 contact07ColumnsSlice88 contact07ColumnsSlice92
private theorem contact07ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact07) 96 8 = 2691405658250 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 4 4 1425070925683 1266334732567 contact07ColumnsSlice96 contact07ColumnsSlice100
private theorem contact07ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact07) 104 8 = 2095326360632 :=
  combineSlices (auxiliaryColumnSlice contact07) 104 4 4 1117315364458 978010996174 contact07ColumnsSlice104 contact07ColumnsSlice108
private theorem contact07ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact07) 112 8 = 1577045269652 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 4 4 848432295794 728612973858 contact07ColumnsSlice112 contact07ColumnsSlice116
private theorem contact07ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact07) 120 8 = 1136654516183 :=
  combineSlices (auxiliaryColumnSlice contact07) 120 4 4 618516968953 518137547230 contact07ColumnsSlice120 contact07ColumnsSlice124
private theorem contact07ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact07) 128 8 = 774011037358 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 4 4 427472919315 346538118043 contact07ColumnsSlice128 contact07ColumnsSlice132
private theorem contact07ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact07) 136 8 = 489209817580 :=
  combineSlices (auxiliaryColumnSlice contact07) 136 4 4 275359206507 213850611073 contact07ColumnsSlice136 contact07ColumnsSlice140
private theorem contact07ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact07) 144 8 = 280494120239 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 4 4 161775417534 118718702705 contact07ColumnsSlice144 contact07ColumnsSlice148
private theorem contact07ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact07) 152 8 = 141396580126 :=
  combineSlices (auxiliaryColumnSlice contact07) 152 4 4 84124933595 57271646531 contact07ColumnsSlice152 contact07ColumnsSlice156
private theorem contact07ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact07) 0 16 = 30298838888797 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 8 8 15914334176724 14384504712073 contact07ColumnsJoin0_8 contact07ColumnsJoin8_8
private theorem contact07ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact07) 16 16 = 24490713575797 :=
  combineSlices (auxiliaryColumnSlice contact07) 16 8 8 12932477749257 11558235826540 contact07ColumnsJoin16_8 contact07ColumnsJoin24_8
private theorem contact07ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact07) 32 16 = 19304830990388 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 8 8 10261730407259 9043100583129 contact07ColumnsJoin32_8 contact07ColumnsJoin40_8
private theorem contact07ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact07) 48 16 = 14741397424707 :=
  combineSlices (auxiliaryColumnSlice contact07) 48 8 8 7902208064206 6839189360501 contact07ColumnsJoin48_8 contact07ColumnsJoin56_8
private theorem contact07ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact07) 64 16 = 10800563521622 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 8 8 5853990081551 4946573440071 contact07ColumnsJoin64_8 contact07ColumnsJoin72_8
private theorem contact07ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact07) 80 16 = 7482343709978 :=
  combineSlices (auxiliaryColumnSlice contact07) 80 8 8 4117056255638 3365287454340 contact07ColumnsJoin80_8 contact07ColumnsJoin88_8
private theorem contact07ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact07) 96 16 = 4786732018882 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 8 8 2691405658250 2095326360632 contact07ColumnsJoin96_8 contact07ColumnsJoin104_8
private theorem contact07ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact07) 112 16 = 2713699785835 :=
  combineSlices (auxiliaryColumnSlice contact07) 112 8 8 1577045269652 1136654516183 contact07ColumnsJoin112_8 contact07ColumnsJoin120_8
private theorem contact07ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact07) 128 16 = 1263220854938 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 8 8 774011037358 489209817580 contact07ColumnsJoin128_8 contact07ColumnsJoin136_8
private theorem contact07ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact07) 144 16 = 421890700365 :=
  combineSlices (auxiliaryColumnSlice contact07) 144 8 8 280494120239 141396580126 contact07ColumnsJoin144_8 contact07ColumnsJoin152_8
private theorem contact07ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact07) 0 32 = 54789552464594 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 16 16 30298838888797 24490713575797 contact07ColumnsJoin0_16 contact07ColumnsJoin16_16
private theorem contact07ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact07) 32 32 = 34046228415095 :=
  combineSlices (auxiliaryColumnSlice contact07) 32 16 16 19304830990388 14741397424707 contact07ColumnsJoin32_16 contact07ColumnsJoin48_16
private theorem contact07ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact07) 64 32 = 18282907231600 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 16 16 10800563521622 7482343709978 contact07ColumnsJoin64_16 contact07ColumnsJoin80_16
private theorem contact07ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact07) 96 32 = 7500431804717 :=
  combineSlices (auxiliaryColumnSlice contact07) 96 16 16 4786732018882 2713699785835 contact07ColumnsJoin96_16 contact07ColumnsJoin112_16
private theorem contact07ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact07) 128 32 = 1685111555303 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 16 16 1263220854938 421890700365 contact07ColumnsJoin128_16 contact07ColumnsJoin144_16
private theorem contact07ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact07) 0 64 = 88835780879689 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 32 32 54789552464594 34046228415095 contact07ColumnsJoin0_32 contact07ColumnsJoin32_32
private theorem contact07ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact07) 64 64 = 25783339036317 :=
  combineSlices (auxiliaryColumnSlice contact07) 64 32 32 18282907231600 7500431804717 contact07ColumnsJoin64_32 contact07ColumnsJoin96_32
private theorem contact07ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact07) 128 36 = 1722336650244 :=
  combineSlices (auxiliaryColumnSlice contact07) 128 32 4 1685111555303 37225094941 contact07ColumnsJoin128_32 contact07ColumnsSlice160
private theorem contact07ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact07) 0 128 = 114619119916006 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 64 64 88835780879689 25783339036317 contact07ColumnsJoin0_64 contact07ColumnsJoin64_64
private theorem contact07ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact07) 0 164 = 116341456566250 :=
  combineSlices (auxiliaryColumnSlice contact07) 0 128 36 114619119916006 1722336650244 contact07ColumnsJoin0_128 contact07ColumnsJoin128_36
private theorem contact07OrdinaryRanks : ordinaryRankBound contact07 = 7881482276 := by decide +kernel
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
private theorem contact07RanksSlice152 : sliceWindow (auxiliaryRankSlice contact07) 152 12 = 0 :=
  contactRankWindow_of_rec contact07 152 12 0 (by decide +kernel)
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
private theorem contact07RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact07) 144 20 = 19027 :=
  combineSlices (auxiliaryRankSlice contact07) 144 8 12 19027 0 contact07RanksJoin144_8 contact07RanksSlice152
private theorem contact07RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact07) 0 32 = 195665712 :=
  combineSlices (auxiliaryRankSlice contact07) 0 16 16 111608856 84056856 contact07RanksJoin0_16 contact07RanksJoin16_16
private theorem contact07RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact07) 32 32 = 102655168 :=
  combineSlices (auxiliaryRankSlice contact07) 32 16 16 60805656 41849512 contact07RanksJoin32_16 contact07RanksJoin48_16
private theorem contact07RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact07) 64 32 = 43066603 :=
  combineSlices (auxiliaryRankSlice contact07) 64 16 16 27051185 16015418 contact07RanksJoin64_16 contact07RanksJoin80_16
private theorem contact07RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact07) 96 32 = 11617130 :=
  combineSlices (auxiliaryRankSlice contact07) 96 16 16 8271449 3345681 contact07RanksJoin96_16 contact07RanksJoin112_16
private theorem contact07RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact07) 128 36 = 783596 :=
  combineSlices (auxiliaryRankSlice contact07) 128 16 20 764569 19027 contact07RanksJoin128_16 contact07RanksJoin144_20
private theorem contact07RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact07) 0 64 = 298320880 :=
  combineSlices (auxiliaryRankSlice contact07) 0 32 32 195665712 102655168 contact07RanksJoin0_32 contact07RanksJoin32_32
private theorem contact07RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact07) 64 64 = 54683733 :=
  combineSlices (auxiliaryRankSlice contact07) 64 32 32 43066603 11617130 contact07RanksJoin64_32 contact07RanksJoin96_32
private theorem contact07RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact07) 0 128 = 353004613 :=
  combineSlices (auxiliaryRankSlice contact07) 0 64 64 298320880 54683733 contact07RanksJoin0_64 contact07RanksJoin64_64
private theorem contact07RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact07) 0 164 = 353788209 :=
  combineSlices (auxiliaryRankSlice contact07) 0 128 36 353004613 783596 contact07RanksJoin0_128 contact07RanksJoin128_36
theorem contact07_margin : sourceMargin contact07 :=
  margin_of_checked_counts contact07 164 2042486315709952 116341456566250 7881482276 353788209 rfl contact07OrdinaryColumns contact07ColumnsJoin0_164 contact07OrdinaryRanks contact07RanksJoin0_164 (by decide +kernel)

private theorem contact09OrdinaryColumns : ordinaryColumnCount contact09 = 2676868289172936 := by decide +kernel
private theorem contact09ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact09) 0 4 = 6675015137274 :=
  contactColumnsWindow_fast contact09 0 4 6675015137274 (by decide +kernel)
private theorem contact09ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact09) 4 4 = 6348146621850 :=
  contactColumnsWindow_fast contact09 4 4 6348146621850 (by decide +kernel)
private theorem contact09ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact09) 8 4 = 6029514478101 :=
  contactColumnsWindow_fast contact09 8 4 6029514478101 (by decide +kernel)
private theorem contact09ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact09) 12 4 = 5719121470884 :=
  contactColumnsWindow_fast contact09 12 4 5719121470884 (by decide +kernel)
private theorem contact09ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact09) 16 4 = 5416965716471 :=
  contactColumnsWindow_fast contact09 16 4 5416965716471 (by decide +kernel)
private theorem contact09ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact09) 20 4 = 5123049130678 :=
  contactColumnsWindow_fast contact09 20 4 5123049130678 (by decide +kernel)
private theorem contact09ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact09) 24 4 = 4837385169909 :=
  contactColumnsWindow_fast contact09 24 4 4837385169909 (by decide +kernel)
private theorem contact09ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact09) 28 4 = 4559991453223 :=
  contactColumnsWindow_fast contact09 28 4 4559991453223 (by decide +kernel)
private theorem contact09ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact09) 32 4 = 4290839988380 :=
  contactColumnsWindow_fast contact09 32 4 4290839988380 (by decide +kernel)
private theorem contact09ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact09) 36 4 = 4029928831794 :=
  contactColumnsWindow_fast contact09 36 4 4029928831794 (by decide +kernel)
private theorem contact09ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact09) 40 4 = 3777259751692 :=
  contactColumnsWindow_fast contact09 40 4 3777259751692 (by decide +kernel)
private theorem contact09ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact09) 44 4 = 3532849519152 :=
  contactColumnsWindow_fast contact09 44 4 3532849519152 (by decide +kernel)
private theorem contact09ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact09) 48 4 = 3296710549776 :=
  contactColumnsWindow_fast contact09 48 4 3296710549776 (by decide +kernel)
private theorem contact09ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact09) 52 4 = 3068815363839 :=
  contactColumnsWindow_fast contact09 52 4 3068815363839 (by decide +kernel)
private theorem contact09ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact09) 56 4 = 2849164586403 :=
  contactColumnsWindow_fast contact09 56 4 2849164586403 (by decide +kernel)
private theorem contact09ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact09) 60 4 = 2637757986621 :=
  contactColumnsWindow_fast contact09 60 4 2637757986621 (by decide +kernel)
private theorem contact09ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact09) 64 4 = 2434619105269 :=
  contactColumnsWindow_fast contact09 64 4 2434619105269 (by decide +kernel)
private theorem contact09ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact09) 68 4 = 2239749301846 :=
  contactColumnsWindow_fast contact09 68 4 2239749301846 (by decide +kernel)
private theorem contact09ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact09) 72 4 = 2053128100251 :=
  contactColumnsWindow_fast contact09 72 4 2053128100251 (by decide +kernel)
private theorem contact09ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact09) 76 4 = 1874751847341 :=
  contactColumnsWindow_fast contact09 76 4 1874751847341 (by decide +kernel)
private theorem contact09ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact09) 80 4 = 1704619564269 :=
  contactColumnsWindow_fast contact09 80 4 1704619564269 (by decide +kernel)
private theorem contact09ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact09) 84 4 = 1542759492423 :=
  contactColumnsWindow_fast contact09 84 4 1542759492423 (by decide +kernel)
private theorem contact09ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact09) 88 4 = 1389164590134 :=
  contactColumnsWindow_fast contact09 88 4 1389164590134 (by decide +kernel)
private theorem contact09ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact09) 92 4 = 1243817906199 :=
  contactColumnsWindow_fast contact09 92 4 1243817906199 (by decide +kernel)
private theorem contact09ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact09) 96 4 = 1106716138530 :=
  contactColumnsWindow_fast contact09 96 4 1106716138530 (by decide +kernel)
private theorem contact09ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact09) 100 4 = 977858906073 :=
  contactColumnsWindow_fast contact09 100 4 977858906073 (by decide +kernel)
private theorem contact09ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact09) 104 4 = 857277003243 :=
  contactColumnsWindow_fast contact09 104 4 857277003243 (by decide +kernel)
private theorem contact09ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact09) 108 4 = 744956988642 :=
  contactColumnsWindow_fast contact09 108 4 744956988642 (by decide +kernel)
private theorem contact09ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact09) 112 4 = 640884746898 :=
  contactColumnsWindow_fast contact09 112 4 640884746898 (by decide +kernel)
private theorem contact09ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact09) 116 4 = 545057540145 :=
  contactColumnsWindow_fast contact09 116 4 545057540145 (by decide +kernel)
private theorem contact09ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact09) 120 4 = 457475839257 :=
  contactColumnsWindow_fast contact09 120 4 457475839257 (by decide +kernel)
private theorem contact09ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact09) 124 4 = 378171530139 :=
  contactColumnsWindow_fast contact09 124 4 378171530139 (by decide +kernel)
private theorem contact09ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact09) 128 4 = 307126449999 :=
  contactColumnsWindow_fast contact09 128 4 307126449999 (by decide +kernel)
private theorem contact09ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact09) 132 4 = 244328818588 :=
  contactColumnsWindow_fast contact09 132 4 244328818588 (by decide +kernel)
private theorem contact09ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact09) 136 4 = 189773617167 :=
  contactColumnsWindow_fast contact09 136 4 189773617167 (by decide +kernel)
private theorem contact09ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact09) 140 4 = 143396576178 :=
  contactColumnsWindow_fast contact09 140 4 143396576178 (by decide +kernel)
private theorem contact09ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact09) 144 4 = 104973788084 :=
  contactColumnsWindow_fast contact09 144 4 104973788084 (by decide +kernel)
private theorem contact09ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact09) 148 4 = 74047020146 :=
  contactColumnsWindow_fast contact09 148 4 74047020146 (by decide +kernel)
private theorem contact09ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact09) 152 4 = 50011913147 :=
  contactColumnsWindow_fast contact09 152 4 50011913147 (by decide +kernel)
private theorem contact09ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact09) 156 4 = 32110827501 :=
  contactColumnsWindow_fast contact09 156 4 32110827501 (by decide +kernel)
private theorem contact09ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact09) 160 2 = 11012877928 :=
  contactColumnsWindow_fast contact09 160 2 11012877928 (by decide +kernel)
private theorem contact09ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact09) 0 8 = 13023161759124 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 4 4 6675015137274 6348146621850 contact09ColumnsSlice0 contact09ColumnsSlice4
private theorem contact09ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact09) 8 8 = 11748635948985 :=
  combineSlices (auxiliaryColumnSlice contact09) 8 4 4 6029514478101 5719121470884 contact09ColumnsSlice8 contact09ColumnsSlice12
private theorem contact09ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact09) 16 8 = 10540014847149 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 4 4 5416965716471 5123049130678 contact09ColumnsSlice16 contact09ColumnsSlice20
private theorem contact09ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact09) 24 8 = 9397376623132 :=
  combineSlices (auxiliaryColumnSlice contact09) 24 4 4 4837385169909 4559991453223 contact09ColumnsSlice24 contact09ColumnsSlice28
private theorem contact09ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact09) 32 8 = 8320768820174 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 4 4 4290839988380 4029928831794 contact09ColumnsSlice32 contact09ColumnsSlice36
private theorem contact09ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact09) 40 8 = 7310109270844 :=
  combineSlices (auxiliaryColumnSlice contact09) 40 4 4 3777259751692 3532849519152 contact09ColumnsSlice40 contact09ColumnsSlice44
private theorem contact09ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact09) 48 8 = 6365525913615 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 4 4 3296710549776 3068815363839 contact09ColumnsSlice48 contact09ColumnsSlice52
private theorem contact09ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact09) 56 8 = 5486922573024 :=
  combineSlices (auxiliaryColumnSlice contact09) 56 4 4 2849164586403 2637757986621 contact09ColumnsSlice56 contact09ColumnsSlice60
private theorem contact09ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact09) 64 8 = 4674368407115 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 4 4 2434619105269 2239749301846 contact09ColumnsSlice64 contact09ColumnsSlice68
private theorem contact09ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact09) 72 8 = 3927879947592 :=
  combineSlices (auxiliaryColumnSlice contact09) 72 4 4 2053128100251 1874751847341 contact09ColumnsSlice72 contact09ColumnsSlice76
private theorem contact09ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact09) 80 8 = 3247379056692 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 4 4 1704619564269 1542759492423 contact09ColumnsSlice80 contact09ColumnsSlice84
private theorem contact09ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact09) 88 8 = 2632982496333 :=
  combineSlices (auxiliaryColumnSlice contact09) 88 4 4 1389164590134 1243817906199 contact09ColumnsSlice88 contact09ColumnsSlice92
private theorem contact09ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact09) 96 8 = 2084575044603 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 4 4 1106716138530 977858906073 contact09ColumnsSlice96 contact09ColumnsSlice100
private theorem contact09ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact09) 104 8 = 1602233991885 :=
  combineSlices (auxiliaryColumnSlice contact09) 104 4 4 857277003243 744956988642 contact09ColumnsSlice104 contact09ColumnsSlice108
private theorem contact09ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact09) 112 8 = 1185942287043 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 4 4 640884746898 545057540145 contact09ColumnsSlice112 contact09ColumnsSlice116
private theorem contact09ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact09) 120 8 = 835647369396 :=
  combineSlices (auxiliaryColumnSlice contact09) 120 4 4 457475839257 378171530139 contact09ColumnsSlice120 contact09ColumnsSlice124
private theorem contact09ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact09) 128 8 = 551455268587 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 4 4 307126449999 244328818588 contact09ColumnsSlice128 contact09ColumnsSlice132
private theorem contact09ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact09) 136 8 = 333170193345 :=
  combineSlices (auxiliaryColumnSlice contact09) 136 4 4 189773617167 143396576178 contact09ColumnsSlice136 contact09ColumnsSlice140
private theorem contact09ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact09) 144 8 = 179020808230 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 4 4 104973788084 74047020146 contact09ColumnsSlice144 contact09ColumnsSlice148
private theorem contact09ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact09) 152 8 = 82122740648 :=
  combineSlices (auxiliaryColumnSlice contact09) 152 4 4 50011913147 32110827501 contact09ColumnsSlice152 contact09ColumnsSlice156
private theorem contact09ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact09) 0 16 = 24771797708109 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 8 8 13023161759124 11748635948985 contact09ColumnsJoin0_8 contact09ColumnsJoin8_8
private theorem contact09ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact09) 16 16 = 19937391470281 :=
  combineSlices (auxiliaryColumnSlice contact09) 16 8 8 10540014847149 9397376623132 contact09ColumnsJoin16_8 contact09ColumnsJoin24_8
private theorem contact09ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact09) 32 16 = 15630878091018 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 8 8 8320768820174 7310109270844 contact09ColumnsJoin32_8 contact09ColumnsJoin40_8
private theorem contact09ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact09) 48 16 = 11852448486639 :=
  combineSlices (auxiliaryColumnSlice contact09) 48 8 8 6365525913615 5486922573024 contact09ColumnsJoin48_8 contact09ColumnsJoin56_8
private theorem contact09ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact09) 64 16 = 8602248354707 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 8 8 4674368407115 3927879947592 contact09ColumnsJoin64_8 contact09ColumnsJoin72_8
private theorem contact09ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact09) 80 16 = 5880361553025 :=
  combineSlices (auxiliaryColumnSlice contact09) 80 8 8 3247379056692 2632982496333 contact09ColumnsJoin80_8 contact09ColumnsJoin88_8
private theorem contact09ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact09) 96 16 = 3686809036488 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 8 8 2084575044603 1602233991885 contact09ColumnsJoin96_8 contact09ColumnsJoin104_8
private theorem contact09ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact09) 112 16 = 2021589656439 :=
  combineSlices (auxiliaryColumnSlice contact09) 112 8 8 1185942287043 835647369396 contact09ColumnsJoin112_8 contact09ColumnsJoin120_8
private theorem contact09ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact09) 128 16 = 884625461932 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 8 8 551455268587 333170193345 contact09ColumnsJoin128_8 contact09ColumnsJoin136_8
private theorem contact09ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact09) 144 16 = 261143548878 :=
  combineSlices (auxiliaryColumnSlice contact09) 144 8 8 179020808230 82122740648 contact09ColumnsJoin144_8 contact09ColumnsJoin152_8
private theorem contact09ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact09) 0 32 = 44709189178390 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 16 16 24771797708109 19937391470281 contact09ColumnsJoin0_16 contact09ColumnsJoin16_16
private theorem contact09ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact09) 32 32 = 27483326577657 :=
  combineSlices (auxiliaryColumnSlice contact09) 32 16 16 15630878091018 11852448486639 contact09ColumnsJoin32_16 contact09ColumnsJoin48_16
private theorem contact09ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact09) 64 32 = 14482609907732 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 16 16 8602248354707 5880361553025 contact09ColumnsJoin64_16 contact09ColumnsJoin80_16
private theorem contact09ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact09) 96 32 = 5708398692927 :=
  combineSlices (auxiliaryColumnSlice contact09) 96 16 16 3686809036488 2021589656439 contact09ColumnsJoin96_16 contact09ColumnsJoin112_16
private theorem contact09ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact09) 128 32 = 1145769010810 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 16 16 884625461932 261143548878 contact09ColumnsJoin128_16 contact09ColumnsJoin144_16
private theorem contact09ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact09) 0 64 = 72192515756047 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 32 32 44709189178390 27483326577657 contact09ColumnsJoin0_32 contact09ColumnsJoin32_32
private theorem contact09ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact09) 64 64 = 20191008600659 :=
  combineSlices (auxiliaryColumnSlice contact09) 64 32 32 14482609907732 5708398692927 contact09ColumnsJoin64_32 contact09ColumnsJoin96_32
private theorem contact09ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact09) 128 34 = 1156781888738 :=
  combineSlices (auxiliaryColumnSlice contact09) 128 32 2 1145769010810 11012877928 contact09ColumnsJoin128_32 contact09ColumnsSlice160
private theorem contact09ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact09) 0 128 = 92383524356706 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 64 64 72192515756047 20191008600659 contact09ColumnsJoin0_64 contact09ColumnsJoin64_64
private theorem contact09ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact09) 0 162 = 93540306245444 :=
  combineSlices (auxiliaryColumnSlice contact09) 0 128 34 92383524356706 1156781888738 contact09ColumnsJoin0_128 contact09ColumnsJoin128_34
private theorem contact09OrdinaryRanks : ordinaryRankBound contact09 = 10285597887 := by decide +kernel
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
private theorem contact09RanksSlice148 : sliceWindow (auxiliaryRankSlice contact09) 148 14 = 0 :=
  contactRankWindow_of_rec contact09 148 14 0 (by decide +kernel)
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
private theorem contact09RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact09) 144 18 = 876 :=
  combineSlices (auxiliaryRankSlice contact09) 144 4 14 876 0 contact09RanksSlice144 contact09RanksSlice148
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
private theorem contact09RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact09) 128 34 = 370215 :=
  combineSlices (auxiliaryRankSlice contact09) 128 16 18 369339 876 contact09RanksJoin128_16 contact09RanksJoin144_18
private theorem contact09RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact09) 0 64 = 241380078 :=
  combineSlices (auxiliaryRankSlice contact09) 0 32 32 159467232 81912846 contact09RanksJoin0_32 contact09RanksJoin32_32
private theorem contact09RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact09) 64 64 = 40917900 :=
  combineSlices (auxiliaryRankSlice contact09) 64 32 32 32893765 8024135 contact09RanksJoin64_32 contact09RanksJoin96_32
private theorem contact09RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact09) 0 128 = 282297978 :=
  combineSlices (auxiliaryRankSlice contact09) 0 64 64 241380078 40917900 contact09RanksJoin0_64 contact09RanksJoin64_64
private theorem contact09RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact09) 0 162 = 282668193 :=
  combineSlices (auxiliaryRankSlice contact09) 0 128 34 282297978 370215 contact09RanksJoin0_128 contact09RanksJoin128_34
theorem contact09_margin : sourceMargin contact09 :=
  margin_of_checked_counts contact09 162 2676868289172936 93540306245444 10285597887 282668193 rfl contact09OrdinaryColumns contact09ColumnsJoin0_162 contact09OrdinaryRanks contact09RanksJoin0_162 (by decide +kernel)

private theorem contact11OrdinaryColumns : ordinaryColumnCount contact11 = 209643997425033 := by decide +kernel
private theorem contact11ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact11) 0 4 = 913669859836 :=
  contactColumnsWindow_fast contact11 0 4 913669859836 (by decide +kernel)
private theorem contact11ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact11) 4 4 = 839588597368 :=
  contactColumnsWindow_fast contact11 4 4 839588597368 (by decide +kernel)
private theorem contact11ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact11) 8 4 = 768669092412 :=
  contactColumnsWindow_fast contact11 8 4 768669092412 (by decide +kernel)
private theorem contact11ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact11) 12 4 = 700897271612 :=
  contactColumnsWindow_fast contact11 12 4 700897271612 (by decide +kernel)
private theorem contact11ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact11) 16 4 = 636270702780 :=
  contactColumnsWindow_fast contact11 16 4 636270702780 (by decide +kernel)
private theorem contact11ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact11) 20 4 = 574787976347 :=
  contactColumnsWindow_fast contact11 20 4 574787976347 (by decide +kernel)
private theorem contact11ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact11) 24 4 = 516453609412 :=
  contactColumnsWindow_fast contact11 24 4 516453609412 (by decide +kernel)
private theorem contact11ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact11) 28 4 = 461282395158 :=
  contactColumnsWindow_fast contact11 28 4 461282395158 (by decide +kernel)
private theorem contact11ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact11) 32 4 = 409260414020 :=
  contactColumnsWindow_fast contact11 32 4 409260414020 (by decide +kernel)
private theorem contact11ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact11) 36 4 = 360383766084 :=
  contactColumnsWindow_fast contact11 36 4 360383766084 (by decide +kernel)
private theorem contact11ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact11) 40 4 = 314651054369 :=
  contactColumnsWindow_fast contact11 40 4 314651054369 (by decide +kernel)
private theorem contact11ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact11) 44 4 = 272067709504 :=
  contactColumnsWindow_fast contact11 44 4 272067709504 (by decide +kernel)
private theorem contact11ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact11) 48 4 = 232647707676 :=
  contactColumnsWindow_fast contact11 48 4 232647707676 (by decide +kernel)
private theorem contact11ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact11) 52 4 = 196375802412 :=
  contactColumnsWindow_fast contact11 52 4 196375802412 (by decide +kernel)
private theorem contact11ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact11) 56 4 = 163249001628 :=
  contactColumnsWindow_fast contact11 56 4 163249001628 (by decide +kernel)
private theorem contact11ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact11) 60 4 = 133266304631 :=
  contactColumnsWindow_fast contact11 60 4 133266304631 (by decide +kernel)
private theorem contact11ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact11) 64 4 = 106434277411 :=
  contactColumnsWindow_fast contact11 64 4 106434277411 (by decide +kernel)
private theorem contact11ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact11) 68 4 = 82765273668 :=
  contactColumnsWindow_fast contact11 68 4 82765273668 (by decide +kernel)
private theorem contact11ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact11) 72 4 = 62243368308 :=
  contactColumnsWindow_fast contact11 72 4 62243368308 (by decide +kernel)
private theorem contact11ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact11) 76 4 = 44866409412 :=
  contactColumnsWindow_fast contact11 76 4 44866409412 (by decide +kernel)
private theorem contact11ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact11) 80 4 = 30633657875 :=
  contactColumnsWindow_fast contact11 80 4 30633657875 (by decide +kernel)
private theorem contact11ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact11) 84 4 = 19531458016 :=
  contactColumnsWindow_fast contact11 84 4 19531458016 (by decide +kernel)
private theorem contact11ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact11) 88 4 = 11423144511 :=
  contactColumnsWindow_fast contact11 88 4 11423144511 (by decide +kernel)
private theorem contact11ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact11) 92 4 = 5975159345 :=
  contactColumnsWindow_fast contact11 92 4 5975159345 (by decide +kernel)
private theorem contact11ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact11) 96 1 = 910814500 :=
  contactColumnsWindow_fast contact11 96 1 910814500 (by decide +kernel)
private theorem contact11ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact11) 0 8 = 1753258457204 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 4 4 913669859836 839588597368 contact11ColumnsSlice0 contact11ColumnsSlice4
private theorem contact11ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact11) 8 8 = 1469566364024 :=
  combineSlices (auxiliaryColumnSlice contact11) 8 4 4 768669092412 700897271612 contact11ColumnsSlice8 contact11ColumnsSlice12
private theorem contact11ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact11) 16 8 = 1211058679127 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 4 4 636270702780 574787976347 contact11ColumnsSlice16 contact11ColumnsSlice20
private theorem contact11ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact11) 24 8 = 977736004570 :=
  combineSlices (auxiliaryColumnSlice contact11) 24 4 4 516453609412 461282395158 contact11ColumnsSlice24 contact11ColumnsSlice28
private theorem contact11ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact11) 32 8 = 769644180104 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 4 4 409260414020 360383766084 contact11ColumnsSlice32 contact11ColumnsSlice36
private theorem contact11ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact11) 40 8 = 586718763873 :=
  combineSlices (auxiliaryColumnSlice contact11) 40 4 4 314651054369 272067709504 contact11ColumnsSlice40 contact11ColumnsSlice44
private theorem contact11ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact11) 48 8 = 429023510088 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 4 4 232647707676 196375802412 contact11ColumnsSlice48 contact11ColumnsSlice52
private theorem contact11ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact11) 56 8 = 296515306259 :=
  combineSlices (auxiliaryColumnSlice contact11) 56 4 4 163249001628 133266304631 contact11ColumnsSlice56 contact11ColumnsSlice60
private theorem contact11ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact11) 64 8 = 189199551079 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 4 4 106434277411 82765273668 contact11ColumnsSlice64 contact11ColumnsSlice68
private theorem contact11ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact11) 72 8 = 107109777720 :=
  combineSlices (auxiliaryColumnSlice contact11) 72 4 4 62243368308 44866409412 contact11ColumnsSlice72 contact11ColumnsSlice76
private theorem contact11ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact11) 80 8 = 50165115891 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 4 4 30633657875 19531458016 contact11ColumnsSlice80 contact11ColumnsSlice84
private theorem contact11ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact11) 88 8 = 17398303856 :=
  combineSlices (auxiliaryColumnSlice contact11) 88 4 4 11423144511 5975159345 contact11ColumnsSlice88 contact11ColumnsSlice92
private theorem contact11ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact11) 0 16 = 3222824821228 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 8 8 1753258457204 1469566364024 contact11ColumnsJoin0_8 contact11ColumnsJoin8_8
private theorem contact11ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact11) 16 16 = 2188794683697 :=
  combineSlices (auxiliaryColumnSlice contact11) 16 8 8 1211058679127 977736004570 contact11ColumnsJoin16_8 contact11ColumnsJoin24_8
private theorem contact11ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact11) 32 16 = 1356362943977 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 8 8 769644180104 586718763873 contact11ColumnsJoin32_8 contact11ColumnsJoin40_8
private theorem contact11ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact11) 48 16 = 725538816347 :=
  combineSlices (auxiliaryColumnSlice contact11) 48 8 8 429023510088 296515306259 contact11ColumnsJoin48_8 contact11ColumnsJoin56_8
private theorem contact11ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact11) 64 16 = 296309328799 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 8 8 189199551079 107109777720 contact11ColumnsJoin64_8 contact11ColumnsJoin72_8
private theorem contact11ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact11) 80 16 = 67563419747 :=
  combineSlices (auxiliaryColumnSlice contact11) 80 8 8 50165115891 17398303856 contact11ColumnsJoin80_8 contact11ColumnsJoin88_8
private theorem contact11ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact11) 0 32 = 5411619504925 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 16 16 3222824821228 2188794683697 contact11ColumnsJoin0_16 contact11ColumnsJoin16_16
private theorem contact11ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact11) 32 32 = 2081901760324 :=
  combineSlices (auxiliaryColumnSlice contact11) 32 16 16 1356362943977 725538816347 contact11ColumnsJoin32_16 contact11ColumnsJoin48_16
private theorem contact11ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact11) 64 32 = 363872748546 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 16 16 296309328799 67563419747 contact11ColumnsJoin64_16 contact11ColumnsJoin80_16
private theorem contact11ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact11) 0 64 = 7493521265249 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 32 32 5411619504925 2081901760324 contact11ColumnsJoin0_32 contact11ColumnsJoin32_32
private theorem contact11ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact11) 64 33 = 364783563046 :=
  combineSlices (auxiliaryColumnSlice contact11) 64 32 1 363872748546 910814500 contact11ColumnsJoin64_32 contact11ColumnsSlice96
private theorem contact11ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact11) 0 97 = 7858304828295 :=
  combineSlices (auxiliaryColumnSlice contact11) 0 64 33 7493521265249 364783563046 contact11ColumnsJoin0_64 contact11ColumnsJoin64_33
private theorem contact11OrdinaryRanks : ordinaryRankBound contact11 = 805943333 := by decide +kernel
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
  margin_of_checked_counts contact11 97 209643997425033 7858304828295 805943333 23761675 rfl contact11OrdinaryColumns contact11ColumnsJoin0_97 contact11OrdinaryRanks contact11RanksJoin0_97 (by decide +kernel)

private theorem contact13OrdinaryColumns : ordinaryColumnCount contact13 = 417161633045255 := by decide +kernel
private theorem contact13ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact13) 0 4 = 3650348216306 :=
  contactColumnsWindow_fast contact13 0 4 3650348216306 (by decide +kernel)
private theorem contact13ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact13) 4 4 = 3429389920566 :=
  contactColumnsWindow_fast contact13 4 4 3429389920566 (by decide +kernel)
private theorem contact13ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact13) 8 4 = 3215375504678 :=
  contactColumnsWindow_fast contact13 8 4 3215375504678 (by decide +kernel)
private theorem contact13ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact13) 12 4 = 3008297334742 :=
  contactColumnsWindow_fast contact13 12 4 3008297334742 (by decide +kernel)
private theorem contact13ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact13) 16 4 = 2808153252525 :=
  contactColumnsWindow_fast contact13 16 4 2808153252525 (by decide +kernel)
private theorem contact13ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact13) 20 4 = 2614951996262 :=
  contactColumnsWindow_fast contact13 20 4 2614951996262 (by decide +kernel)
private theorem contact13ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact13) 24 4 = 2428728866536 :=
  contactColumnsWindow_fast contact13 24 4 2428728866536 (by decide +kernel)
private theorem contact13ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact13) 28 4 = 2249450905022 :=
  contactColumnsWindow_fast contact13 28 4 2249450905022 (by decide +kernel)
private theorem contact13ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact13) 32 4 = 2077111680286 :=
  contactColumnsWindow_fast contact13 32 4 2077111680286 (by decide +kernel)
private theorem contact13ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact13) 36 4 = 1911710092419 :=
  contactColumnsWindow_fast contact13 36 4 1911710092419 (by decide +kernel)
private theorem contact13ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact13) 40 4 = 1753253779754 :=
  contactColumnsWindow_fast contact13 40 4 1753253779754 (by decide +kernel)
private theorem contact13ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact13) 44 4 = 1601775855340 :=
  contactColumnsWindow_fast contact13 44 4 1601775855340 (by decide +kernel)
private theorem contact13ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact13) 48 4 = 1457240475038 :=
  contactColumnsWindow_fast contact13 48 4 1457240475038 (by decide +kernel)
private theorem contact13ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact13) 52 4 = 1319644052830 :=
  contactColumnsWindow_fast contact13 52 4 1319644052830 (by decide +kernel)
private theorem contact13ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact13) 56 4 = 1188984959313 :=
  contactColumnsWindow_fast contact13 56 4 1188984959313 (by decide +kernel)
private theorem contact13ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact13) 60 4 = 1065274052883 :=
  contactColumnsWindow_fast contact13 60 4 1065274052883 (by decide +kernel)
private theorem contact13ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact13) 64 4 = 948540990198 :=
  contactColumnsWindow_fast contact13 64 4 948540990198 (by decide +kernel)
private theorem contact13ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact13) 68 4 = 838748098766 :=
  contactColumnsWindow_fast contact13 68 4 838748098766 (by decide +kernel)
private theorem contact13ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact13) 72 4 = 735894452374 :=
  contactColumnsWindow_fast contact13 72 4 735894452374 (by decide +kernel)
private theorem contact13ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact13) 76 4 = 639977914782 :=
  contactColumnsWindow_fast contact13 76 4 639977914782 (by decide +kernel)
private theorem contact13ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact13) 80 4 = 551013238449 :=
  contactColumnsWindow_fast contact13 80 4 551013238449 (by decide +kernel)
private theorem contact13ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact13) 84 4 = 469024161390 :=
  contactColumnsWindow_fast contact13 84 4 469024161390 (by decide +kernel)
private theorem contact13ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact13) 88 4 = 393973844681 :=
  contactColumnsWindow_fast contact13 88 4 393973844681 (by decide +kernel)
private theorem contact13ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact13) 92 4 = 325862878918 :=
  contactColumnsWindow_fast contact13 92 4 325862878918 (by decide +kernel)
private theorem contact13ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact13) 96 4 = 264688959126 :=
  contactColumnsWindow_fast contact13 96 4 264688959126 (by decide +kernel)
private theorem contact13ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact13) 100 4 = 210470479641 :=
  contactColumnsWindow_fast contact13 100 4 210470479641 (by decide +kernel)
private theorem contact13ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact13) 104 4 = 163225359582 :=
  contactColumnsWindow_fast contact13 104 4 163225359582 (by decide +kernel)
private theorem contact13ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact13) 108 4 = 122907245017 :=
  contactColumnsWindow_fast contact13 108 4 122907245017 (by decide +kernel)
private theorem contact13ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact13) 112 4 = 89403204351 :=
  contactColumnsWindow_fast contact13 112 4 89403204351 (by decide +kernel)
private theorem contact13ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact13) 116 4 = 62419571187 :=
  contactColumnsWindow_fast contact13 116 4 62419571187 (by decide +kernel)
private theorem contact13ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact13) 120 4 = 41519459477 :=
  contactColumnsWindow_fast contact13 120 4 41519459477 (by decide +kernel)
private theorem contact13ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact13) 124 2 = 14660706572 :=
  contactColumnsWindow_fast contact13 124 2 14660706572 (by decide +kernel)
private theorem contact13ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact13) 0 8 = 7079738136872 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 4 4 3650348216306 3429389920566 contact13ColumnsSlice0 contact13ColumnsSlice4
private theorem contact13ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact13) 8 8 = 6223672839420 :=
  combineSlices (auxiliaryColumnSlice contact13) 8 4 4 3215375504678 3008297334742 contact13ColumnsSlice8 contact13ColumnsSlice12
private theorem contact13ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact13) 16 8 = 5423105248787 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 4 4 2808153252525 2614951996262 contact13ColumnsSlice16 contact13ColumnsSlice20
private theorem contact13ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact13) 24 8 = 4678179771558 :=
  combineSlices (auxiliaryColumnSlice contact13) 24 4 4 2428728866536 2249450905022 contact13ColumnsSlice24 contact13ColumnsSlice28
private theorem contact13ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact13) 32 8 = 3988821772705 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 4 4 2077111680286 1911710092419 contact13ColumnsSlice32 contact13ColumnsSlice36
private theorem contact13ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact13) 40 8 = 3355029635094 :=
  combineSlices (auxiliaryColumnSlice contact13) 40 4 4 1753253779754 1601775855340 contact13ColumnsSlice40 contact13ColumnsSlice44
private theorem contact13ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact13) 48 8 = 2776884527868 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 4 4 1457240475038 1319644052830 contact13ColumnsSlice48 contact13ColumnsSlice52
private theorem contact13ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact13) 56 8 = 2254259012196 :=
  combineSlices (auxiliaryColumnSlice contact13) 56 4 4 1188984959313 1065274052883 contact13ColumnsSlice56 contact13ColumnsSlice60
private theorem contact13ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact13) 64 8 = 1787289088964 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 4 4 948540990198 838748098766 contact13ColumnsSlice64 contact13ColumnsSlice68
private theorem contact13ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact13) 72 8 = 1375872367156 :=
  combineSlices (auxiliaryColumnSlice contact13) 72 4 4 735894452374 639977914782 contact13ColumnsSlice72 contact13ColumnsSlice76
private theorem contact13ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact13) 80 8 = 1020037399839 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 4 4 551013238449 469024161390 contact13ColumnsSlice80 contact13ColumnsSlice84
private theorem contact13ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact13) 88 8 = 719836723599 :=
  combineSlices (auxiliaryColumnSlice contact13) 88 4 4 393973844681 325862878918 contact13ColumnsSlice88 contact13ColumnsSlice92
private theorem contact13ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact13) 96 8 = 475159438767 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 4 4 264688959126 210470479641 contact13ColumnsSlice96 contact13ColumnsSlice100
private theorem contact13ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact13) 104 8 = 286132604599 :=
  combineSlices (auxiliaryColumnSlice contact13) 104 4 4 163225359582 122907245017 contact13ColumnsSlice104 contact13ColumnsSlice108
private theorem contact13ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact13) 112 8 = 151822775538 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 4 4 89403204351 62419571187 contact13ColumnsSlice112 contact13ColumnsSlice116
private theorem contact13ColumnsJoin120_6 : sliceWindow (auxiliaryColumnSlice contact13) 120 6 = 56180166049 :=
  combineSlices (auxiliaryColumnSlice contact13) 120 4 2 41519459477 14660706572 contact13ColumnsSlice120 contact13ColumnsSlice124
private theorem contact13ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact13) 0 16 = 13303410976292 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 8 8 7079738136872 6223672839420 contact13ColumnsJoin0_8 contact13ColumnsJoin8_8
private theorem contact13ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact13) 16 16 = 10101285020345 :=
  combineSlices (auxiliaryColumnSlice contact13) 16 8 8 5423105248787 4678179771558 contact13ColumnsJoin16_8 contact13ColumnsJoin24_8
private theorem contact13ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact13) 32 16 = 7343851407799 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 8 8 3988821772705 3355029635094 contact13ColumnsJoin32_8 contact13ColumnsJoin40_8
private theorem contact13ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact13) 48 16 = 5031143540064 :=
  combineSlices (auxiliaryColumnSlice contact13) 48 8 8 2776884527868 2254259012196 contact13ColumnsJoin48_8 contact13ColumnsJoin56_8
private theorem contact13ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact13) 64 16 = 3163161456120 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 8 8 1787289088964 1375872367156 contact13ColumnsJoin64_8 contact13ColumnsJoin72_8
private theorem contact13ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact13) 80 16 = 1739874123438 :=
  combineSlices (auxiliaryColumnSlice contact13) 80 8 8 1020037399839 719836723599 contact13ColumnsJoin80_8 contact13ColumnsJoin88_8
private theorem contact13ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact13) 96 16 = 761292043366 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 8 8 475159438767 286132604599 contact13ColumnsJoin96_8 contact13ColumnsJoin104_8
private theorem contact13ColumnsJoin112_14 : sliceWindow (auxiliaryColumnSlice contact13) 112 14 = 208002941587 :=
  combineSlices (auxiliaryColumnSlice contact13) 112 8 6 151822775538 56180166049 contact13ColumnsJoin112_8 contact13ColumnsJoin120_6
private theorem contact13ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact13) 0 32 = 23404695996637 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 16 16 13303410976292 10101285020345 contact13ColumnsJoin0_16 contact13ColumnsJoin16_16
private theorem contact13ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact13) 32 32 = 12374994947863 :=
  combineSlices (auxiliaryColumnSlice contact13) 32 16 16 7343851407799 5031143540064 contact13ColumnsJoin32_16 contact13ColumnsJoin48_16
private theorem contact13ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact13) 64 32 = 4903035579558 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 16 16 3163161456120 1739874123438 contact13ColumnsJoin64_16 contact13ColumnsJoin80_16
private theorem contact13ColumnsJoin96_30 : sliceWindow (auxiliaryColumnSlice contact13) 96 30 = 969294984953 :=
  combineSlices (auxiliaryColumnSlice contact13) 96 16 14 761292043366 208002941587 contact13ColumnsJoin96_16 contact13ColumnsJoin112_14
private theorem contact13ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact13) 0 64 = 35779690944500 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 32 32 23404695996637 12374994947863 contact13ColumnsJoin0_32 contact13ColumnsJoin32_32
private theorem contact13ColumnsJoin64_62 : sliceWindow (auxiliaryColumnSlice contact13) 64 62 = 5872330564511 :=
  combineSlices (auxiliaryColumnSlice contact13) 64 32 30 4903035579558 969294984953 contact13ColumnsJoin64_32 contact13ColumnsJoin96_30
private theorem contact13ColumnsJoin0_126 : sliceWindow (auxiliaryColumnSlice contact13) 0 126 = 41652021509011 :=
  combineSlices (auxiliaryColumnSlice contact13) 0 64 62 35779690944500 5872330564511 contact13ColumnsJoin0_64 contact13ColumnsJoin64_62
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
  margin_of_checked_counts contact13 126 417161633045255 41652021509011 1622911107 127318829 rfl contact13OrdinaryColumns contact13ColumnsJoin0_126 contact13OrdinaryRanks contact13RanksJoin0_126 (by decide +kernel)

private theorem contact15OrdinaryColumns : ordinaryColumnCount contact15 = 188437039194264 := by decide +kernel
private theorem contact15ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact15) 0 4 = 996280480986 :=
  contactColumnsWindow_fast contact15 0 4 996280480986 (by decide +kernel)
private theorem contact15ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact15) 4 4 = 914761658542 :=
  contactColumnsWindow_fast contact15 4 4 914761658542 (by decide +kernel)
private theorem contact15ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact15) 8 4 = 836758399178 :=
  contactColumnsWindow_fast contact15 8 4 836758399178 (by decide +kernel)
private theorem contact15ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact15) 12 4 = 762254703982 :=
  contactColumnsWindow_fast contact15 12 4 762254703982 (by decide +kernel)
private theorem contact15ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact15) 16 4 = 691247662602 :=
  contactColumnsWindow_fast contact15 16 4 691247662602 (by decide +kernel)
private theorem contact15ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact15) 20 4 = 623735774492 :=
  contactColumnsWindow_fast contact15 20 4 623735774492 (by decide +kernel)
private theorem contact15ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact15) 24 4 = 559724047946 :=
  contactColumnsWindow_fast contact15 24 4 559724047946 (by decide +kernel)
private theorem contact15ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact15) 28 4 = 499229357723 :=
  contactColumnsWindow_fast contact15 28 4 499229357723 (by decide +kernel)
private theorem contact15ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact15) 32 4 = 442235775130 :=
  contactColumnsWindow_fast contact15 32 4 442235775130 (by decide +kernel)
private theorem contact15ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact15) 36 4 = 388738932138 :=
  contactColumnsWindow_fast contact15 36 4 388738932138 (by decide +kernel)
private theorem contact15ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact15) 40 4 = 338737341176 :=
  contactColumnsWindow_fast contact15 40 4 338737341176 (by decide +kernel)
private theorem contact15ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact15) 44 4 = 292237067270 :=
  contactColumnsWindow_fast contact15 44 4 292237067270 (by decide +kernel)
private theorem contact15ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact15) 48 4 = 249254030306 :=
  contactColumnsWindow_fast contact15 48 4 249254030306 (by decide +kernel)
private theorem contact15ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact15) 52 4 = 209770810205 :=
  contactColumnsWindow_fast contact15 52 4 209770810205 (by decide +kernel)
private theorem contact15ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact15) 56 4 = 173784087282 :=
  contactColumnsWindow_fast contact15 56 4 173784087282 (by decide +kernel)
private theorem contact15ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact15) 60 4 = 141292793468 :=
  contactColumnsWindow_fast contact15 60 4 141292793468 (by decide +kernel)
private theorem contact15ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact15) 64 4 = 112304307157 :=
  contactColumnsWindow_fast contact15 64 4 112304307157 (by decide +kernel)
private theorem contact15ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact15) 68 4 = 86832674282 :=
  contactColumnsWindow_fast contact15 68 4 86832674282 (by decide +kernel)
private theorem contact15ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact15) 72 4 = 64859736515 :=
  contactColumnsWindow_fast contact15 72 4 64859736515 (by decide +kernel)
private theorem contact15ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact15) 76 4 = 46383128034 :=
  contactColumnsWindow_fast contact15 76 4 46383128034 (by decide +kernel)
private theorem contact15ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact15) 80 4 = 31399169383 :=
  contactColumnsWindow_fast contact15 80 4 31399169383 (by decide +kernel)
private theorem contact15ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact15) 84 4 = 19850401824 :=
  contactColumnsWindow_fast contact15 84 4 19850401824 (by decide +kernel)
private theorem contact15ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact15) 88 4 = 11518373259 :=
  contactColumnsWindow_fast contact15 88 4 11518373259 (by decide +kernel)
private theorem contact15ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact15) 92 4 = 5989470477 :=
  contactColumnsWindow_fast contact15 92 4 5989470477 (by decide +kernel)
private theorem contact15ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact15) 0 8 = 1911042139528 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 4 4 996280480986 914761658542 contact15ColumnsSlice0 contact15ColumnsSlice4
private theorem contact15ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact15) 8 8 = 1599013103160 :=
  combineSlices (auxiliaryColumnSlice contact15) 8 4 4 836758399178 762254703982 contact15ColumnsSlice8 contact15ColumnsSlice12
private theorem contact15ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact15) 16 8 = 1314983437094 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 4 4 691247662602 623735774492 contact15ColumnsSlice16 contact15ColumnsSlice20
private theorem contact15ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact15) 24 8 = 1058953405669 :=
  combineSlices (auxiliaryColumnSlice contact15) 24 4 4 559724047946 499229357723 contact15ColumnsSlice24 contact15ColumnsSlice28
private theorem contact15ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact15) 32 8 = 830974707268 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 4 4 442235775130 388738932138 contact15ColumnsSlice32 contact15ColumnsSlice36
private theorem contact15ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact15) 40 8 = 630974408446 :=
  combineSlices (auxiliaryColumnSlice contact15) 40 4 4 338737341176 292237067270 contact15ColumnsSlice40 contact15ColumnsSlice44
private theorem contact15ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact15) 48 8 = 459024840511 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 4 4 249254030306 209770810205 contact15ColumnsSlice48 contact15ColumnsSlice52
private theorem contact15ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact15) 56 8 = 315076880750 :=
  combineSlices (auxiliaryColumnSlice contact15) 56 4 4 173784087282 141292793468 contact15ColumnsSlice56 contact15ColumnsSlice60
private theorem contact15ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact15) 64 8 = 199136981439 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 4 4 112304307157 86832674282 contact15ColumnsSlice64 contact15ColumnsSlice68
private theorem contact15ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact15) 72 8 = 111242864549 :=
  combineSlices (auxiliaryColumnSlice contact15) 72 4 4 64859736515 46383128034 contact15ColumnsSlice72 contact15ColumnsSlice76
private theorem contact15ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact15) 80 8 = 51249571207 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 4 4 31399169383 19850401824 contact15ColumnsSlice80 contact15ColumnsSlice84
private theorem contact15ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact15) 88 8 = 17507843736 :=
  combineSlices (auxiliaryColumnSlice contact15) 88 4 4 11518373259 5989470477 contact15ColumnsSlice88 contact15ColumnsSlice92
private theorem contact15ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact15) 0 16 = 3510055242688 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 8 8 1911042139528 1599013103160 contact15ColumnsJoin0_8 contact15ColumnsJoin8_8
private theorem contact15ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact15) 16 16 = 2373936842763 :=
  combineSlices (auxiliaryColumnSlice contact15) 16 8 8 1314983437094 1058953405669 contact15ColumnsJoin16_8 contact15ColumnsJoin24_8
private theorem contact15ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact15) 32 16 = 1461949115714 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 8 8 830974707268 630974408446 contact15ColumnsJoin32_8 contact15ColumnsJoin40_8
private theorem contact15ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact15) 48 16 = 774101721261 :=
  combineSlices (auxiliaryColumnSlice contact15) 48 8 8 459024840511 315076880750 contact15ColumnsJoin48_8 contact15ColumnsJoin56_8
private theorem contact15ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact15) 64 16 = 310379845988 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 8 8 199136981439 111242864549 contact15ColumnsJoin64_8 contact15ColumnsJoin72_8
private theorem contact15ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact15) 80 16 = 68757414943 :=
  combineSlices (auxiliaryColumnSlice contact15) 80 8 8 51249571207 17507843736 contact15ColumnsJoin80_8 contact15ColumnsJoin88_8
private theorem contact15ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact15) 0 32 = 5883992085451 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 16 16 3510055242688 2373936842763 contact15ColumnsJoin0_16 contact15ColumnsJoin16_16
private theorem contact15ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact15) 32 32 = 2236050836975 :=
  combineSlices (auxiliaryColumnSlice contact15) 32 16 16 1461949115714 774101721261 contact15ColumnsJoin32_16 contact15ColumnsJoin48_16
private theorem contact15ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact15) 64 32 = 379137260931 :=
  combineSlices (auxiliaryColumnSlice contact15) 64 16 16 310379845988 68757414943 contact15ColumnsJoin64_16 contact15ColumnsJoin80_16
private theorem contact15ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact15) 0 64 = 8120042922426 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 32 32 5883992085451 2236050836975 contact15ColumnsJoin0_32 contact15ColumnsJoin32_32
private theorem contact15ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact15) 0 96 = 8499180183357 :=
  combineSlices (auxiliaryColumnSlice contact15) 0 64 32 8120042922426 379137260931 contact15ColumnsJoin0_64 contact15ColumnsJoin64_32
private theorem contact15OrdinaryRanks : ordinaryRankBound contact15 = 725361690 := by decide +kernel
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
  margin_of_checked_counts contact15 96 188437039194264 8499180183357 725361690 25890102 rfl contact15OrdinaryColumns contact15ColumnsJoin0_96 contact15OrdinaryRanks contact15RanksJoin0_96 (by decide +kernel)

private theorem contact17OrdinaryColumns : ordinaryColumnCount contact17 = 2655437445772829 := by decide +kernel
private theorem contact17ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact17) 0 4 = 6595365820490 :=
  contactColumnsWindow_fast contact17 0 4 6595365820490 (by decide +kernel)
private theorem contact17ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact17) 4 4 = 6259784193052 :=
  contactColumnsWindow_fast contact17 4 4 6259784193052 (by decide +kernel)
private theorem contact17ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact17) 8 4 = 5933005524800 :=
  contactColumnsWindow_fast contact17 8 4 5933005524800 (by decide +kernel)
private theorem contact17ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact17) 12 4 = 5615031309811 :=
  contactColumnsWindow_fast contact17 12 4 5615031309811 (by decide +kernel)
private theorem contact17ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact17) 16 4 = 5305898673652 :=
  contactColumnsWindow_fast contact17 16 4 5305898673652 (by decide +kernel)
private theorem contact17ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact17) 20 4 = 5005579989147 :=
  contactColumnsWindow_fast contact17 20 4 5005579989147 (by decide +kernel)
private theorem contact17ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact17) 24 4 = 4714066703237 :=
  contactColumnsWindow_fast contact17 24 4 4714066703237 (by decide +kernel)
private theorem contact17ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact17) 28 4 = 4431358391100 :=
  contactColumnsWindow_fast contact17 28 4 4431358391100 (by decide +kernel)
private theorem contact17ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact17) 32 4 = 4157460966932 :=
  contactColumnsWindow_fast contact17 32 4 4157460966932 (by decide +kernel)
private theorem contact17ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact17) 36 4 = 3892407336638 :=
  contactColumnsWindow_fast contact17 36 4 3892407336638 (by decide +kernel)
private theorem contact17ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact17) 40 4 = 3636169510691 :=
  contactColumnsWindow_fast contact17 40 4 3636169510691 (by decide +kernel)
private theorem contact17ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact17) 44 4 = 3388739536825 :=
  contactColumnsWindow_fast contact17 44 4 3388739536825 (by decide +kernel)
private theorem contact17ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact17) 48 4 = 3150118416047 :=
  contactColumnsWindow_fast contact17 48 4 3150118416047 (by decide +kernel)
private theorem contact17ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact17) 52 4 = 2920313596670 :=
  contactColumnsWindow_fast contact17 52 4 2920313596670 (by decide +kernel)
private theorem contact17ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact17) 56 4 = 2699355974870 :=
  contactColumnsWindow_fast contact17 56 4 2699355974870 (by decide +kernel)
private theorem contact17ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact17) 60 4 = 2487216041405 :=
  contactColumnsWindow_fast contact17 60 4 2487216041405 (by decide +kernel)
private theorem contact17ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact17) 64 4 = 2283886360087 :=
  contactColumnsWindow_fast contact17 64 4 2283886360087 (by decide +kernel)
private theorem contact17ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact17) 68 4 = 2089365203393 :=
  contactColumnsWindow_fast contact17 68 4 2089365203393 (by decide +kernel)
private theorem contact17ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact17) 72 4 = 1903663387346 :=
  contactColumnsWindow_fast contact17 72 4 1903663387346 (by decide +kernel)
private theorem contact17ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact17) 76 4 = 1726808217945 :=
  contactColumnsWindow_fast contact17 76 4 1726808217945 (by decide +kernel)
private theorem contact17ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact17) 80 4 = 1558768689938 :=
  contactColumnsWindow_fast contact17 80 4 1558768689938 (by decide +kernel)
private theorem contact17ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact17) 84 4 = 1399539265621 :=
  contactColumnsWindow_fast contact17 84 4 1399539265621 (by decide +kernel)
private theorem contact17ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact17) 88 4 = 1249118273142 :=
  contactColumnsWindow_fast contact17 88 4 1249118273142 (by decide +kernel)
private theorem contact17ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact17) 92 4 = 1107520184474 :=
  contactColumnsWindow_fast contact17 92 4 1107520184474 (by decide +kernel)
private theorem contact17ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact17) 96 4 = 974766560892 :=
  contactColumnsWindow_fast contact17 96 4 974766560892 (by decide +kernel)
private theorem contact17ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact17) 100 4 = 850827506102 :=
  contactColumnsWindow_fast contact17 100 4 850827506102 (by decide +kernel)
private theorem contact17ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact17) 104 4 = 735698353302 :=
  contactColumnsWindow_fast contact17 104 4 735698353302 (by decide +kernel)
private theorem contact17ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact17) 108 4 = 629377498197 :=
  contactColumnsWindow_fast contact17 108 4 629377498197 (by decide +kernel)
private theorem contact17ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact17) 112 4 = 531883086424 :=
  contactColumnsWindow_fast contact17 112 4 531883086424 (by decide +kernel)
private theorem contact17ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact17) 116 4 = 443231146671 :=
  contactColumnsWindow_fast contact17 116 4 443231146671 (by decide +kernel)
private theorem contact17ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact17) 120 4 = 363392585831 :=
  contactColumnsWindow_fast contact17 120 4 363392585831 (by decide +kernel)
private theorem contact17ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact17) 124 4 = 292363539423 :=
  contactColumnsWindow_fast contact17 124 4 292363539423 (by decide +kernel)
private theorem contact17ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact17) 128 4 = 230142161638 :=
  contactColumnsWindow_fast contact17 128 4 230142161638 (by decide +kernel)
private theorem contact17ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact17) 132 4 = 176710050684 :=
  contactColumnsWindow_fast contact17 132 4 176710050684 (by decide +kernel)
private theorem contact17ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact17) 136 4 = 131862078702 :=
  contactColumnsWindow_fast contact17 136 4 131862078702 (by decide +kernel)
private theorem contact17ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact17) 140 4 = 95171054876 :=
  contactColumnsWindow_fast contact17 140 4 95171054876 (by decide +kernel)
private theorem contact17ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact17) 144 4 = 66074001903 :=
  contactColumnsWindow_fast contact17 144 4 66074001903 (by decide +kernel)
private theorem contact17ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact17) 148 4 = 43849129990 :=
  contactColumnsWindow_fast contact17 148 4 43849129990 (by decide +kernel)
private theorem contact17ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact17) 152 4 = 27629296587 :=
  contactColumnsWindow_fast contact17 152 4 27629296587 (by decide +kernel)
private theorem contact17ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact17) 156 1 = 4979520650 :=
  contactColumnsWindow_fast contact17 156 1 4979520650 (by decide +kernel)
private theorem contact17ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact17) 0 8 = 12855150013542 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 4 4 6595365820490 6259784193052 contact17ColumnsSlice0 contact17ColumnsSlice4
private theorem contact17ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact17) 8 8 = 11548036834611 :=
  combineSlices (auxiliaryColumnSlice contact17) 8 4 4 5933005524800 5615031309811 contact17ColumnsSlice8 contact17ColumnsSlice12
private theorem contact17ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact17) 16 8 = 10311478662799 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 4 4 5305898673652 5005579989147 contact17ColumnsSlice16 contact17ColumnsSlice20
private theorem contact17ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact17) 24 8 = 9145425094337 :=
  combineSlices (auxiliaryColumnSlice contact17) 24 4 4 4714066703237 4431358391100 contact17ColumnsSlice24 contact17ColumnsSlice28
private theorem contact17ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact17) 32 8 = 8049868303570 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 4 4 4157460966932 3892407336638 contact17ColumnsSlice32 contact17ColumnsSlice36
private theorem contact17ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact17) 40 8 = 7024909047516 :=
  combineSlices (auxiliaryColumnSlice contact17) 40 4 4 3636169510691 3388739536825 contact17ColumnsSlice40 contact17ColumnsSlice44
private theorem contact17ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact17) 48 8 = 6070432012717 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 4 4 3150118416047 2920313596670 contact17ColumnsSlice48 contact17ColumnsSlice52
private theorem contact17ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact17) 56 8 = 5186572016275 :=
  combineSlices (auxiliaryColumnSlice contact17) 56 4 4 2699355974870 2487216041405 contact17ColumnsSlice56 contact17ColumnsSlice60
private theorem contact17ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact17) 64 8 = 4373251563480 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 4 4 2283886360087 2089365203393 contact17ColumnsSlice64 contact17ColumnsSlice68
private theorem contact17ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact17) 72 8 = 3630471605291 :=
  combineSlices (auxiliaryColumnSlice contact17) 72 4 4 1903663387346 1726808217945 contact17ColumnsSlice72 contact17ColumnsSlice76
private theorem contact17ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact17) 80 8 = 2958307955559 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 4 4 1558768689938 1399539265621 contact17ColumnsSlice80 contact17ColumnsSlice84
private theorem contact17ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact17) 88 8 = 2356638457616 :=
  combineSlices (auxiliaryColumnSlice contact17) 88 4 4 1249118273142 1107520184474 contact17ColumnsSlice88 contact17ColumnsSlice92
private theorem contact17ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact17) 96 8 = 1825594066994 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 4 4 974766560892 850827506102 contact17ColumnsSlice96 contact17ColumnsSlice100
private theorem contact17ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact17) 104 8 = 1365075851499 :=
  combineSlices (auxiliaryColumnSlice contact17) 104 4 4 735698353302 629377498197 contact17ColumnsSlice104 contact17ColumnsSlice108
private theorem contact17ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact17) 112 8 = 975114233095 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 4 4 531883086424 443231146671 contact17ColumnsSlice112 contact17ColumnsSlice116
private theorem contact17ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact17) 120 8 = 655756125254 :=
  combineSlices (auxiliaryColumnSlice contact17) 120 4 4 363392585831 292363539423 contact17ColumnsSlice120 contact17ColumnsSlice124
private theorem contact17ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact17) 128 8 = 406852212322 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 4 4 230142161638 176710050684 contact17ColumnsSlice128 contact17ColumnsSlice132
private theorem contact17ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact17) 136 8 = 227033133578 :=
  combineSlices (auxiliaryColumnSlice contact17) 136 4 4 131862078702 95171054876 contact17ColumnsSlice136 contact17ColumnsSlice140
private theorem contact17ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact17) 144 8 = 109923131893 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 4 4 66074001903 43849129990 contact17ColumnsSlice144 contact17ColumnsSlice148
private theorem contact17ColumnsJoin152_5 : sliceWindow (auxiliaryColumnSlice contact17) 152 5 = 32608817237 :=
  combineSlices (auxiliaryColumnSlice contact17) 152 4 1 27629296587 4979520650 contact17ColumnsSlice152 contact17ColumnsSlice156
private theorem contact17ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact17) 0 16 = 24403186848153 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 8 8 12855150013542 11548036834611 contact17ColumnsJoin0_8 contact17ColumnsJoin8_8
private theorem contact17ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact17) 16 16 = 19456903757136 :=
  combineSlices (auxiliaryColumnSlice contact17) 16 8 8 10311478662799 9145425094337 contact17ColumnsJoin16_8 contact17ColumnsJoin24_8
private theorem contact17ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact17) 32 16 = 15074777351086 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 8 8 8049868303570 7024909047516 contact17ColumnsJoin32_8 contact17ColumnsJoin40_8
private theorem contact17ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact17) 48 16 = 11257004028992 :=
  combineSlices (auxiliaryColumnSlice contact17) 48 8 8 6070432012717 5186572016275 contact17ColumnsJoin48_8 contact17ColumnsJoin56_8
private theorem contact17ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact17) 64 16 = 8003723168771 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 8 8 4373251563480 3630471605291 contact17ColumnsJoin64_8 contact17ColumnsJoin72_8
private theorem contact17ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact17) 80 16 = 5314946413175 :=
  combineSlices (auxiliaryColumnSlice contact17) 80 8 8 2958307955559 2356638457616 contact17ColumnsJoin80_8 contact17ColumnsJoin88_8
private theorem contact17ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact17) 96 16 = 3190669918493 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 8 8 1825594066994 1365075851499 contact17ColumnsJoin96_8 contact17ColumnsJoin104_8
private theorem contact17ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact17) 112 16 = 1630870358349 :=
  combineSlices (auxiliaryColumnSlice contact17) 112 8 8 975114233095 655756125254 contact17ColumnsJoin112_8 contact17ColumnsJoin120_8
private theorem contact17ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact17) 128 16 = 633885345900 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 8 8 406852212322 227033133578 contact17ColumnsJoin128_8 contact17ColumnsJoin136_8
private theorem contact17ColumnsJoin144_13 : sliceWindow (auxiliaryColumnSlice contact17) 144 13 = 142531949130 :=
  combineSlices (auxiliaryColumnSlice contact17) 144 8 5 109923131893 32608817237 contact17ColumnsJoin144_8 contact17ColumnsJoin152_5
private theorem contact17ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact17) 0 32 = 43860090605289 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 16 16 24403186848153 19456903757136 contact17ColumnsJoin0_16 contact17ColumnsJoin16_16
private theorem contact17ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact17) 32 32 = 26331781380078 :=
  combineSlices (auxiliaryColumnSlice contact17) 32 16 16 15074777351086 11257004028992 contact17ColumnsJoin32_16 contact17ColumnsJoin48_16
private theorem contact17ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact17) 64 32 = 13318669581946 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 16 16 8003723168771 5314946413175 contact17ColumnsJoin64_16 contact17ColumnsJoin80_16
private theorem contact17ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact17) 96 32 = 4821540276842 :=
  combineSlices (auxiliaryColumnSlice contact17) 96 16 16 3190669918493 1630870358349 contact17ColumnsJoin96_16 contact17ColumnsJoin112_16
private theorem contact17ColumnsJoin128_29 : sliceWindow (auxiliaryColumnSlice contact17) 128 29 = 776417295030 :=
  combineSlices (auxiliaryColumnSlice contact17) 128 16 13 633885345900 142531949130 contact17ColumnsJoin128_16 contact17ColumnsJoin144_13
private theorem contact17ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact17) 0 64 = 70191871985367 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 32 32 43860090605289 26331781380078 contact17ColumnsJoin0_32 contact17ColumnsJoin32_32
private theorem contact17ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact17) 64 64 = 18140209858788 :=
  combineSlices (auxiliaryColumnSlice contact17) 64 32 32 13318669581946 4821540276842 contact17ColumnsJoin64_32 contact17ColumnsJoin96_32
private theorem contact17ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact17) 0 128 = 88332081844155 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 64 64 70191871985367 18140209858788 contact17ColumnsJoin0_64 contact17ColumnsJoin64_64
private theorem contact17ColumnsJoin0_157 : sliceWindow (auxiliaryColumnSlice contact17) 0 157 = 89108499139185 :=
  combineSlices (auxiliaryColumnSlice contact17) 0 128 29 88332081844155 776417295030 contact17ColumnsJoin0_128 contact17ColumnsJoin128_29
private theorem contact17OrdinaryRanks : ordinaryRankBound contact17 = 10197926411 := by decide +kernel
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
  margin_of_checked_counts contact17 157 2655437445772829 89108499139185 10197926411 271682466 rfl contact17OrdinaryColumns contact17ColumnsJoin0_157 contact17OrdinaryRanks contact17RanksJoin0_157 (by decide +kernel)

private theorem contact19OrdinaryColumns : ordinaryColumnCount contact19 = 158808602406900 := by decide +kernel
private theorem contact19ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact19) 0 4 = 1313237314736 :=
  contactColumnsWindow_fast contact19 0 4 1313237314736 (by decide +kernel)
private theorem contact19ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact19) 4 4 = 1212484904864 :=
  contactColumnsWindow_fast contact19 4 4 1212484904864 (by decide +kernel)
private theorem contact19ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact19) 8 4 = 1115771773392 :=
  contactColumnsWindow_fast contact19 8 4 1115771773392 (by decide +kernel)
private theorem contact19ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact19) 12 4 = 1023115072480 :=
  contactColumnsWindow_fast contact19 12 4 1023115072480 (by decide +kernel)
private theorem contact19ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact19) 16 4 = 934514692928 :=
  contactColumnsWindow_fast contact19 16 4 934514692928 (by decide +kernel)
private theorem contact19ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact19) 20 4 = 849956080026 :=
  contactColumnsWindow_fast contact19 20 4 849956080026 (by decide +kernel)
private theorem contact19ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact19) 24 4 = 769438348091 :=
  contactColumnsWindow_fast contact19 24 4 769438348091 (by decide +kernel)
private theorem contact19ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact19) 28 4 = 692962792412 :=
  contactColumnsWindow_fast contact19 28 4 692962792412 (by decide +kernel)
private theorem contact19ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact19) 32 4 = 620548273643 :=
  contactColumnsWindow_fast contact19 32 4 620548273643 (by decide +kernel)
private theorem contact19ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact19) 36 4 = 552190292351 :=
  contactColumnsWindow_fast contact19 36 4 552190292351 (by decide +kernel)
private theorem contact19ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact19) 40 4 = 487875031092 :=
  contactColumnsWindow_fast contact19 40 4 487875031092 (by decide +kernel)
private theorem contact19ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact19) 44 4 = 427600473032 :=
  contactColumnsWindow_fast contact19 44 4 427600473032 (by decide +kernel)
private theorem contact19ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact19) 48 4 = 371368810410 :=
  contactColumnsWindow_fast contact19 48 4 371368810410 (by decide +kernel)
private theorem contact19ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact19) 52 4 = 319200205403 :=
  contactColumnsWindow_fast contact19 52 4 319200205403 (by decide +kernel)
private theorem contact19ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact19) 56 4 = 271085595506 :=
  contactColumnsWindow_fast contact19 56 4 271085595506 (by decide +kernel)
private theorem contact19ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact19) 60 4 = 227013685890 :=
  contactColumnsWindow_fast contact19 60 4 227013685890 (by decide +kernel)
private theorem contact19ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact19) 64 4 = 186982380797 :=
  contactColumnsWindow_fast contact19 64 4 186982380797 (by decide +kernel)
private theorem contact19ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact19) 68 4 = 150994795620 :=
  contactColumnsWindow_fast contact19 68 4 150994795620 (by decide +kernel)
private theorem contact19ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact19) 72 4 = 119071840895 :=
  contactColumnsWindow_fast contact19 72 4 119071840895 (by decide +kernel)
private theorem contact19ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact19) 76 4 = 91200638283 :=
  contactColumnsWindow_fast contact19 76 4 91200638283 (by decide +kernel)
private theorem contact19ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact19) 80 4 = 67372044420 :=
  contactColumnsWindow_fast contact19 80 4 67372044420 (by decide +kernel)
private theorem contact19ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact19) 84 4 = 47583285694 :=
  contactColumnsWindow_fast contact19 84 4 47583285694 (by decide +kernel)
private theorem contact19ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact19) 88 4 = 31800052689 :=
  contactColumnsWindow_fast contact19 88 4 31800052689 (by decide +kernel)
private theorem contact19ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact19) 92 4 = 19859682203 :=
  contactColumnsWindow_fast contact19 92 4 19859682203 (by decide +kernel)
private theorem contact19ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact19) 96 4 = 11390821082 :=
  contactColumnsWindow_fast contact19 96 4 11390821082 (by decide +kernel)
private theorem contact19ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact19) 100 1 = 1883704020 :=
  contactColumnsWindow_fast contact19 100 1 1883704020 (by decide +kernel)
private theorem contact19ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact19) 0 8 = 2525722219600 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 4 4 1313237314736 1212484904864 contact19ColumnsSlice0 contact19ColumnsSlice4
private theorem contact19ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact19) 8 8 = 2138886845872 :=
  combineSlices (auxiliaryColumnSlice contact19) 8 4 4 1115771773392 1023115072480 contact19ColumnsSlice8 contact19ColumnsSlice12
private theorem contact19ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact19) 16 8 = 1784470772954 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 4 4 934514692928 849956080026 contact19ColumnsSlice16 contact19ColumnsSlice20
private theorem contact19ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact19) 24 8 = 1462401140503 :=
  combineSlices (auxiliaryColumnSlice contact19) 24 4 4 769438348091 692962792412 contact19ColumnsSlice24 contact19ColumnsSlice28
private theorem contact19ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact19) 32 8 = 1172738565994 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 4 4 620548273643 552190292351 contact19ColumnsSlice32 contact19ColumnsSlice36
private theorem contact19ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact19) 40 8 = 915475504124 :=
  combineSlices (auxiliaryColumnSlice contact19) 40 4 4 487875031092 427600473032 contact19ColumnsSlice40 contact19ColumnsSlice44
private theorem contact19ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact19) 48 8 = 690569015813 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 4 4 371368810410 319200205403 contact19ColumnsSlice48 contact19ColumnsSlice52
private theorem contact19ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact19) 56 8 = 498099281396 :=
  combineSlices (auxiliaryColumnSlice contact19) 56 4 4 271085595506 227013685890 contact19ColumnsSlice56 contact19ColumnsSlice60
private theorem contact19ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact19) 64 8 = 337977176417 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 4 4 186982380797 150994795620 contact19ColumnsSlice64 contact19ColumnsSlice68
private theorem contact19ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact19) 72 8 = 210272479178 :=
  combineSlices (auxiliaryColumnSlice contact19) 72 4 4 119071840895 91200638283 contact19ColumnsSlice72 contact19ColumnsSlice76
private theorem contact19ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact19) 80 8 = 114955330114 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 4 4 67372044420 47583285694 contact19ColumnsSlice80 contact19ColumnsSlice84
private theorem contact19ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact19) 88 8 = 51659734892 :=
  combineSlices (auxiliaryColumnSlice contact19) 88 4 4 31800052689 19859682203 contact19ColumnsSlice88 contact19ColumnsSlice92
private theorem contact19ColumnsJoin96_5 : sliceWindow (auxiliaryColumnSlice contact19) 96 5 = 13274525102 :=
  combineSlices (auxiliaryColumnSlice contact19) 96 4 1 11390821082 1883704020 contact19ColumnsSlice96 contact19ColumnsSlice100
private theorem contact19ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact19) 0 16 = 4664609065472 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 8 8 2525722219600 2138886845872 contact19ColumnsJoin0_8 contact19ColumnsJoin8_8
private theorem contact19ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact19) 16 16 = 3246871913457 :=
  combineSlices (auxiliaryColumnSlice contact19) 16 8 8 1784470772954 1462401140503 contact19ColumnsJoin16_8 contact19ColumnsJoin24_8
private theorem contact19ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact19) 32 16 = 2088214070118 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 8 8 1172738565994 915475504124 contact19ColumnsJoin32_8 contact19ColumnsJoin40_8
private theorem contact19ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact19) 48 16 = 1188668297209 :=
  combineSlices (auxiliaryColumnSlice contact19) 48 8 8 690569015813 498099281396 contact19ColumnsJoin48_8 contact19ColumnsJoin56_8
private theorem contact19ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact19) 64 16 = 548249655595 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 8 8 337977176417 210272479178 contact19ColumnsJoin64_8 contact19ColumnsJoin72_8
private theorem contact19ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact19) 80 16 = 166615065006 :=
  combineSlices (auxiliaryColumnSlice contact19) 80 8 8 114955330114 51659734892 contact19ColumnsJoin80_8 contact19ColumnsJoin88_8
private theorem contact19ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact19) 0 32 = 7911480978929 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 16 16 4664609065472 3246871913457 contact19ColumnsJoin0_16 contact19ColumnsJoin16_16
private theorem contact19ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact19) 32 32 = 3276882367327 :=
  combineSlices (auxiliaryColumnSlice contact19) 32 16 16 2088214070118 1188668297209 contact19ColumnsJoin32_16 contact19ColumnsJoin48_16
private theorem contact19ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact19) 64 32 = 714864720601 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 16 16 548249655595 166615065006 contact19ColumnsJoin64_16 contact19ColumnsJoin80_16
private theorem contact19ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact19) 0 64 = 11188363346256 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 32 32 7911480978929 3276882367327 contact19ColumnsJoin0_32 contact19ColumnsJoin32_32
private theorem contact19ColumnsJoin64_37 : sliceWindow (auxiliaryColumnSlice contact19) 64 37 = 728139245703 :=
  combineSlices (auxiliaryColumnSlice contact19) 64 32 5 714864720601 13274525102 contact19ColumnsJoin64_32 contact19ColumnsJoin96_5
private theorem contact19ColumnsJoin0_101 : sliceWindow (auxiliaryColumnSlice contact19) 0 101 = 11916502591959 :=
  combineSlices (auxiliaryColumnSlice contact19) 0 64 37 11188363346256 728139245703 contact19ColumnsJoin0_64 contact19ColumnsJoin64_37
private theorem contact19OrdinaryRanks : ordinaryRankBound contact19 = 614983669 := by decide +kernel
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
private theorem contact19RanksSlice96 : sliceWindow (auxiliaryRankSlice contact19) 96 5 = 0 :=
  contactRankWindow_of_rec contact19 96 5 0 (by decide +kernel)
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
private theorem contact19RanksJoin64_37 : sliceWindow (auxiliaryRankSlice contact19) 64 37 = 894379 :=
  combineSlices (auxiliaryRankSlice contact19) 64 32 5 894379 0 contact19RanksJoin64_32 contact19RanksSlice96
private theorem contact19RanksJoin0_101 : sliceWindow (auxiliaryRankSlice contact19) 0 101 = 36280569 :=
  combineSlices (auxiliaryRankSlice contact19) 0 64 37 35386190 894379 contact19RanksJoin0_64 contact19RanksJoin64_37
theorem contact19_margin : sourceMargin contact19 :=
  margin_of_checked_counts contact19 101 158808602406900 11916502591959 614983669 36280569 rfl contact19OrdinaryColumns contact19ColumnsJoin0_101 contact19OrdinaryRanks contact19RanksJoin0_101 (by decide +kernel)

private theorem contact21OrdinaryColumns : ordinaryColumnCount contact21 = 52050806035571 := by decide +kernel
private theorem contact21ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact21) 0 4 = 510926821229 :=
  contactColumnsWindow_fast contact21 0 4 510926821229 (by decide +kernel)
private theorem contact21ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact21) 4 4 = 463119370996 :=
  contactColumnsWindow_fast contact21 4 4 463119370996 (by decide +kernel)
private theorem contact21ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact21) 8 4 = 417674142487 :=
  contactColumnsWindow_fast contact21 8 4 417674142487 (by decide +kernel)
private theorem contact21ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact21) 12 4 = 374588253574 :=
  contactColumnsWindow_fast contact21 12 4 374588253574 (by decide +kernel)
private theorem contact21ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact21) 16 4 = 333860394505 :=
  contactColumnsWindow_fast contact21 16 4 333860394505 (by decide +kernel)
private theorem contact21ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact21) 20 4 = 295493633253 :=
  contactColumnsWindow_fast contact21 20 4 295493633253 (by decide +kernel)
private theorem contact21ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact21) 24 4 = 259499801566 :=
  contactColumnsWindow_fast contact21 24 4 259499801566 (by decide +kernel)
private theorem contact21ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact21) 28 4 = 225867038419 :=
  contactColumnsWindow_fast contact21 28 4 225867038419 (by decide +kernel)
private theorem contact21ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact21) 32 4 = 194593614868 :=
  contactColumnsWindow_fast contact21 32 4 194593614868 (by decide +kernel)
private theorem contact21ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact21) 36 4 = 165678266377 :=
  contactColumnsWindow_fast contact21 36 4 165678266377 (by decide +kernel)
private theorem contact21ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact21) 40 4 = 139124907933 :=
  contactColumnsWindow_fast contact21 40 4 139124907933 (by decide +kernel)
private theorem contact21ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact21) 44 4 = 114944361316 :=
  contactColumnsWindow_fast contact21 44 4 114944361316 (by decide +kernel)
private theorem contact21ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact21) 48 4 = 93124065909 :=
  contactColumnsWindow_fast contact21 48 4 93124065909 (by decide +kernel)
private theorem contact21ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact21) 52 4 = 73663105342 :=
  contactColumnsWindow_fast contact21 52 4 73663105342 (by decide +kernel)
private theorem contact21ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact21) 56 4 = 56560308628 :=
  contactColumnsWindow_fast contact21 56 4 56560308628 (by decide +kernel)
private theorem contact21ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact21) 60 4 = 41820311793 :=
  contactColumnsWindow_fast contact21 60 4 41820311793 (by decide +kernel)
private theorem contact21ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact21) 64 4 = 29453050246 :=
  contactColumnsWindow_fast contact21 64 4 29453050246 (by decide +kernel)
private theorem contact21ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact21) 68 4 = 19445291802 :=
  contactColumnsWindow_fast contact21 68 4 19445291802 (by decide +kernel)
private theorem contact21ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact21) 72 4 = 11787531861 :=
  contactColumnsWindow_fast contact21 72 4 11787531861 (by decide +kernel)
private theorem contact21ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact21) 76 4 = 6380353785 :=
  contactColumnsWindow_fast contact21 76 4 6380353785 (by decide +kernel)
private theorem contact21ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact21) 80 1 = 991719565 :=
  contactColumnsWindow_fast contact21 80 1 991719565 (by decide +kernel)
private theorem contact21ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact21) 0 8 = 974046192225 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 4 4 510926821229 463119370996 contact21ColumnsSlice0 contact21ColumnsSlice4
private theorem contact21ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact21) 8 8 = 792262396061 :=
  combineSlices (auxiliaryColumnSlice contact21) 8 4 4 417674142487 374588253574 contact21ColumnsSlice8 contact21ColumnsSlice12
private theorem contact21ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact21) 16 8 = 629354027758 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 4 4 333860394505 295493633253 contact21ColumnsSlice16 contact21ColumnsSlice20
private theorem contact21ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact21) 24 8 = 485366839985 :=
  combineSlices (auxiliaryColumnSlice contact21) 24 4 4 259499801566 225867038419 contact21ColumnsSlice24 contact21ColumnsSlice28
private theorem contact21ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact21) 32 8 = 360271881245 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 4 4 194593614868 165678266377 contact21ColumnsSlice32 contact21ColumnsSlice36
private theorem contact21ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact21) 40 8 = 254069269249 :=
  combineSlices (auxiliaryColumnSlice contact21) 40 4 4 139124907933 114944361316 contact21ColumnsSlice40 contact21ColumnsSlice44
private theorem contact21ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact21) 48 8 = 166787171251 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 4 4 93124065909 73663105342 contact21ColumnsSlice48 contact21ColumnsSlice52
private theorem contact21ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact21) 56 8 = 98380620421 :=
  combineSlices (auxiliaryColumnSlice contact21) 56 4 4 56560308628 41820311793 contact21ColumnsSlice56 contact21ColumnsSlice60
private theorem contact21ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact21) 64 8 = 48898342048 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 4 4 29453050246 19445291802 contact21ColumnsSlice64 contact21ColumnsSlice68
private theorem contact21ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact21) 72 8 = 18167885646 :=
  combineSlices (auxiliaryColumnSlice contact21) 72 4 4 11787531861 6380353785 contact21ColumnsSlice72 contact21ColumnsSlice76
private theorem contact21ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact21) 0 16 = 1766308588286 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 8 8 974046192225 792262396061 contact21ColumnsJoin0_8 contact21ColumnsJoin8_8
private theorem contact21ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact21) 16 16 = 1114720867743 :=
  combineSlices (auxiliaryColumnSlice contact21) 16 8 8 629354027758 485366839985 contact21ColumnsJoin16_8 contact21ColumnsJoin24_8
private theorem contact21ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact21) 32 16 = 614341150494 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 8 8 360271881245 254069269249 contact21ColumnsJoin32_8 contact21ColumnsJoin40_8
private theorem contact21ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact21) 48 16 = 265167791672 :=
  combineSlices (auxiliaryColumnSlice contact21) 48 8 8 166787171251 98380620421 contact21ColumnsJoin48_8 contact21ColumnsJoin56_8
private theorem contact21ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact21) 64 16 = 67066227694 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 8 8 48898342048 18167885646 contact21ColumnsJoin64_8 contact21ColumnsJoin72_8
private theorem contact21ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact21) 0 32 = 2881029456029 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 16 16 1766308588286 1114720867743 contact21ColumnsJoin0_16 contact21ColumnsJoin16_16
private theorem contact21ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact21) 32 32 = 879508942166 :=
  combineSlices (auxiliaryColumnSlice contact21) 32 16 16 614341150494 265167791672 contact21ColumnsJoin32_16 contact21ColumnsJoin48_16
private theorem contact21ColumnsJoin64_17 : sliceWindow (auxiliaryColumnSlice contact21) 64 17 = 68057947259 :=
  combineSlices (auxiliaryColumnSlice contact21) 64 16 1 67066227694 991719565 contact21ColumnsJoin64_16 contact21ColumnsSlice80
private theorem contact21ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact21) 0 64 = 3760538398195 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 32 32 2881029456029 879508942166 contact21ColumnsJoin0_32 contact21ColumnsJoin32_32
private theorem contact21ColumnsJoin0_81 : sliceWindow (auxiliaryColumnSlice contact21) 0 81 = 3828596345454 :=
  combineSlices (auxiliaryColumnSlice contact21) 0 64 17 3760538398195 68057947259 contact21ColumnsJoin0_64 contact21ColumnsJoin64_17
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
private theorem contact21RanksSlice76 : sliceWindow (auxiliaryRankSlice contact21) 76 5 = 0 :=
  contactRankWindow_of_rec contact21 76 5 0 (by decide +kernel)
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
private theorem contact21RanksJoin72_9 : sliceWindow (auxiliaryRankSlice contact21) 72 9 = 1589 :=
  combineSlices (auxiliaryRankSlice contact21) 72 4 5 1589 0 contact21RanksSlice72 contact21RanksSlice76
private theorem contact21RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact21) 0 16 = 6293504 :=
  combineSlices (auxiliaryRankSlice contact21) 0 8 8 3579232 2714272 contact21RanksJoin0_8 contact21RanksJoin8_8
private theorem contact21RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact21) 16 16 = 3355889 :=
  combineSlices (auxiliaryRankSlice contact21) 16 8 8 1979872 1376017 contact21RanksJoin16_8 contact21RanksJoin24_8
private theorem contact21RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact21) 32 16 = 1443539 :=
  combineSlices (auxiliaryRankSlice contact21) 32 8 8 900547 542992 contact21RanksJoin32_8 contact21RanksJoin40_8
private theorem contact21RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact21) 48 16 = 412568 :=
  combineSlices (auxiliaryRankSlice contact21) 48 8 8 288877 123691 contact21RanksJoin48_8 contact21RanksJoin56_8
private theorem contact21RanksJoin64_17 : sliceWindow (auxiliaryRankSlice contact21) 64 17 = 34525 :=
  combineSlices (auxiliaryRankSlice contact21) 64 8 9 32936 1589 contact21RanksJoin64_8 contact21RanksJoin72_9
private theorem contact21RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact21) 0 32 = 9649393 :=
  combineSlices (auxiliaryRankSlice contact21) 0 16 16 6293504 3355889 contact21RanksJoin0_16 contact21RanksJoin16_16
private theorem contact21RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact21) 32 32 = 1856107 :=
  combineSlices (auxiliaryRankSlice contact21) 32 16 16 1443539 412568 contact21RanksJoin32_16 contact21RanksJoin48_16
private theorem contact21RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact21) 0 64 = 11505500 :=
  combineSlices (auxiliaryRankSlice contact21) 0 32 32 9649393 1856107 contact21RanksJoin0_32 contact21RanksJoin32_32
private theorem contact21RanksJoin0_81 : sliceWindow (auxiliaryRankSlice contact21) 0 81 = 11540025 :=
  combineSlices (auxiliaryRankSlice contact21) 0 64 17 11505500 34525 contact21RanksJoin0_64 contact21RanksJoin64_17
theorem contact21_margin : sourceMargin contact21 :=
  margin_of_checked_counts contact21 81 52050806035571 3828596345454 201622402 11540025 rfl contact21OrdinaryColumns contact21ColumnsJoin0_81 contact21OrdinaryRanks contact21RanksJoin0_81 (by decide +kernel)

private theorem contact23OrdinaryColumns : ordinaryColumnCount contact23 = 2284858276585501 := by decide +kernel
private theorem contact23ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact23) 0 4 = 7258540734562 :=
  contactColumnsWindow_fast contact23 0 4 7258540734562 (by decide +kernel)
private theorem contact23ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact23) 4 4 = 6900125793554 :=
  contactColumnsWindow_fast contact23 4 4 6900125793554 (by decide +kernel)
private theorem contact23ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact23) 8 4 = 6550825375558 :=
  contactColumnsWindow_fast contact23 8 4 6550825375558 (by decide +kernel)
private theorem contact23ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact23) 12 4 = 6210642438466 :=
  contactColumnsWindow_fast contact23 12 4 6210642438466 (by decide +kernel)
private theorem contact23ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact23) 16 4 = 5879574963658 :=
  contactColumnsWindow_fast contact23 16 4 5879574963658 (by decide +kernel)
private theorem contact23ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact23) 20 4 = 5557624993442 :=
  contactColumnsWindow_fast contact23 20 4 5557624993442 (by decide +kernel)
private theorem contact23ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact23) 24 4 = 5244808239607 :=
  contactColumnsWindow_fast contact23 24 4 5244808239607 (by decide +kernel)
private theorem contact23ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact23) 28 4 = 4941144886289 :=
  contactColumnsWindow_fast contact23 28 4 4941144886289 (by decide +kernel)
private theorem contact23ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact23) 32 4 = 4646602392906 :=
  contactColumnsWindow_fast contact23 32 4 4646602392906 (by decide +kernel)
private theorem contact23ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact23) 36 4 = 4361178604706 :=
  contactColumnsWindow_fast contact23 36 4 4361178604706 (by decide +kernel)
private theorem contact23ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact23) 40 4 = 4084875397946 :=
  contactColumnsWindow_fast contact23 40 4 4084875397946 (by decide +kernel)
private theorem contact23ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact23) 44 4 = 3817712342750 :=
  contactColumnsWindow_fast contact23 44 4 3817712342750 (by decide +kernel)
private theorem contact23ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact23) 48 4 = 3559703489971 :=
  contactColumnsWindow_fast contact23 48 4 3559703489971 (by decide +kernel)
private theorem contact23ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact23) 52 4 = 3310817037109 :=
  contactColumnsWindow_fast contact23 52 4 3310817037109 (by decide +kernel)
private theorem contact23ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact23) 56 4 = 3071053612505 :=
  contactColumnsWindow_fast contact23 56 4 3071053612505 (by decide +kernel)
private theorem contact23ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact23) 60 4 = 2840412983050 :=
  contactColumnsWindow_fast contact23 60 4 2840412983050 (by decide +kernel)
private theorem contact23ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact23) 64 4 = 2618922291246 :=
  contactColumnsWindow_fast contact23 64 4 2618922291246 (by decide +kernel)
private theorem contact23ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact23) 68 4 = 2406583053851 :=
  contactColumnsWindow_fast contact23 68 4 2406583053851 (by decide +kernel)
private theorem contact23ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact23) 72 4 = 2203371279322 :=
  contactColumnsWindow_fast contact23 72 4 2203371279322 (by decide +kernel)
private theorem contact23ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact23) 76 4 = 2009283102119 :=
  contactColumnsWindow_fast contact23 76 4 2009283102119 (by decide +kernel)
private theorem contact23ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact23) 80 4 = 1824317496466 :=
  contactColumnsWindow_fast contact23 80 4 1824317496466 (by decide +kernel)
private theorem contact23ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact23) 84 4 = 1648507007858 :=
  contactColumnsWindow_fast contact23 84 4 1648507007858 (by decide +kernel)
private theorem contact23ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact23) 88 4 = 1481843414815 :=
  contactColumnsWindow_fast contact23 88 4 1481843414815 (by decide +kernel)
private theorem contact23ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact23) 92 4 = 1324306877494 :=
  contactColumnsWindow_fast contact23 92 4 1324306877494 (by decide +kernel)
private theorem contact23ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact23) 96 4 = 1175893906421 :=
  contactColumnsWindow_fast contact23 96 4 1175893906421 (by decide +kernel)
private theorem contact23ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact23) 100 4 = 1036604162653 :=
  contactColumnsWindow_fast contact23 100 4 1036604162653 (by decide +kernel)
private theorem contact23ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact23) 104 4 = 906473137730 :=
  contactColumnsWindow_fast contact23 104 4 906473137730 (by decide +kernel)
private theorem contact23ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact23) 108 4 = 785485175485 :=
  contactColumnsWindow_fast contact23 108 4 785485175485 (by decide +kernel)
private theorem contact23ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact23) 112 4 = 673623795010 :=
  contactColumnsWindow_fast contact23 112 4 673623795010 (by decide +kernel)
private theorem contact23ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact23) 116 4 = 570886110038 :=
  contactColumnsWindow_fast contact23 116 4 570886110038 (by decide +kernel)
private theorem contact23ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact23) 120 4 = 477272781151 :=
  contactColumnsWindow_fast contact23 120 4 477272781151 (by decide +kernel)
private theorem contact23ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact23) 124 4 = 392820567098 :=
  contactColumnsWindow_fast contact23 124 4 392820567098 (by decide +kernel)
private theorem contact23ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact23) 128 4 = 317508285034 :=
  contactColumnsWindow_fast contact23 128 4 317508285034 (by decide +kernel)
private theorem contact23ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact23) 132 4 = 251321815719 :=
  contactColumnsWindow_fast contact23 132 4 251321815719 (by decide +kernel)
private theorem contact23ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact23) 136 4 = 194224809053 :=
  contactColumnsWindow_fast contact23 136 4 194224809053 (by decide +kernel)
private theorem contact23ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact23) 140 4 = 146022401943 :=
  contactColumnsWindow_fast contact23 140 4 146022401943 (by decide +kernel)
private theorem contact23ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact23) 144 4 = 106364441540 :=
  contactColumnsWindow_fast contact23 144 4 106364441540 (by decide +kernel)
private theorem contact23ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact23) 148 4 = 74674198122 :=
  contactColumnsWindow_fast contact23 148 4 74674198122 (by decide +kernel)
private theorem contact23ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact23) 152 4 = 50229881051 :=
  contactColumnsWindow_fast contact23 152 4 50229881051 (by decide +kernel)
private theorem contact23ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact23) 156 4 = 32157804405 :=
  contactColumnsWindow_fast contact23 156 4 32157804405 (by decide +kernel)
private theorem contact23ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact23) 160 2 = 11015587471 :=
  contactColumnsWindow_fast contact23 160 2 11015587471 (by decide +kernel)
private theorem contact23ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact23) 0 8 = 14158666528116 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 4 4 7258540734562 6900125793554 contact23ColumnsSlice0 contact23ColumnsSlice4
private theorem contact23ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact23) 8 8 = 12761467814024 :=
  combineSlices (auxiliaryColumnSlice contact23) 8 4 4 6550825375558 6210642438466 contact23ColumnsSlice8 contact23ColumnsSlice12
private theorem contact23ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact23) 16 8 = 11437199957100 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 4 4 5879574963658 5557624993442 contact23ColumnsSlice16 contact23ColumnsSlice20
private theorem contact23ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact23) 24 8 = 10185953125896 :=
  combineSlices (auxiliaryColumnSlice contact23) 24 4 4 5244808239607 4941144886289 contact23ColumnsSlice24 contact23ColumnsSlice28
private theorem contact23ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact23) 32 8 = 9007780997612 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 4 4 4646602392906 4361178604706 contact23ColumnsSlice32 contact23ColumnsSlice36
private theorem contact23ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact23) 40 8 = 7902587740696 :=
  combineSlices (auxiliaryColumnSlice contact23) 40 4 4 4084875397946 3817712342750 contact23ColumnsSlice40 contact23ColumnsSlice44
private theorem contact23ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact23) 48 8 = 6870520527080 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 4 4 3559703489971 3310817037109 contact23ColumnsSlice48 contact23ColumnsSlice52
private theorem contact23ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact23) 56 8 = 5911466595555 :=
  combineSlices (auxiliaryColumnSlice contact23) 56 4 4 3071053612505 2840412983050 contact23ColumnsSlice56 contact23ColumnsSlice60
private theorem contact23ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact23) 64 8 = 5025505345097 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 4 4 2618922291246 2406583053851 contact23ColumnsSlice64 contact23ColumnsSlice68
private theorem contact23ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact23) 72 8 = 4212654381441 :=
  combineSlices (auxiliaryColumnSlice contact23) 72 4 4 2203371279322 2009283102119 contact23ColumnsSlice72 contact23ColumnsSlice76
private theorem contact23ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact23) 80 8 = 3472824504324 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 4 4 1824317496466 1648507007858 contact23ColumnsSlice80 contact23ColumnsSlice84
private theorem contact23ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact23) 88 8 = 2806150292309 :=
  combineSlices (auxiliaryColumnSlice contact23) 88 4 4 1481843414815 1324306877494 contact23ColumnsSlice88 contact23ColumnsSlice92
private theorem contact23ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact23) 96 8 = 2212498069074 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 4 4 1175893906421 1036604162653 contact23ColumnsSlice96 contact23ColumnsSlice100
private theorem contact23ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact23) 104 8 = 1691958313215 :=
  combineSlices (auxiliaryColumnSlice contact23) 104 4 4 906473137730 785485175485 contact23ColumnsSlice104 contact23ColumnsSlice108
private theorem contact23ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact23) 112 8 = 1244509905048 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 4 4 673623795010 570886110038 contact23ColumnsSlice112 contact23ColumnsSlice116
private theorem contact23ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact23) 120 8 = 870093348249 :=
  combineSlices (auxiliaryColumnSlice contact23) 120 4 4 477272781151 392820567098 contact23ColumnsSlice120 contact23ColumnsSlice124
private theorem contact23ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact23) 128 8 = 568830100753 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 4 4 317508285034 251321815719 contact23ColumnsSlice128 contact23ColumnsSlice132
private theorem contact23ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact23) 136 8 = 340247210996 :=
  combineSlices (auxiliaryColumnSlice contact23) 136 4 4 194224809053 146022401943 contact23ColumnsSlice136 contact23ColumnsSlice140
private theorem contact23ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact23) 144 8 = 181038639662 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 4 4 106364441540 74674198122 contact23ColumnsSlice144 contact23ColumnsSlice148
private theorem contact23ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact23) 152 8 = 82387685456 :=
  combineSlices (auxiliaryColumnSlice contact23) 152 4 4 50229881051 32157804405 contact23ColumnsSlice152 contact23ColumnsSlice156
private theorem contact23ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact23) 0 16 = 26920134342140 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 8 8 14158666528116 12761467814024 contact23ColumnsJoin0_8 contact23ColumnsJoin8_8
private theorem contact23ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact23) 16 16 = 21623153082996 :=
  combineSlices (auxiliaryColumnSlice contact23) 16 8 8 11437199957100 10185953125896 contact23ColumnsJoin16_8 contact23ColumnsJoin24_8
private theorem contact23ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact23) 32 16 = 16910368738308 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 8 8 9007780997612 7902587740696 contact23ColumnsJoin32_8 contact23ColumnsJoin40_8
private theorem contact23ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact23) 48 16 = 12781987122635 :=
  combineSlices (auxiliaryColumnSlice contact23) 48 8 8 6870520527080 5911466595555 contact23ColumnsJoin48_8 contact23ColumnsJoin56_8
private theorem contact23ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact23) 64 16 = 9238159726538 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 8 8 5025505345097 4212654381441 contact23ColumnsJoin64_8 contact23ColumnsJoin72_8
private theorem contact23ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact23) 80 16 = 6278974796633 :=
  combineSlices (auxiliaryColumnSlice contact23) 80 8 8 3472824504324 2806150292309 contact23ColumnsJoin80_8 contact23ColumnsJoin88_8
private theorem contact23ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact23) 96 16 = 3904456382289 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 8 8 2212498069074 1691958313215 contact23ColumnsJoin96_8 contact23ColumnsJoin104_8
private theorem contact23ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact23) 112 16 = 2114603253297 :=
  combineSlices (auxiliaryColumnSlice contact23) 112 8 8 1244509905048 870093348249 contact23ColumnsJoin112_8 contact23ColumnsJoin120_8
private theorem contact23ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact23) 128 16 = 909077311749 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 8 8 568830100753 340247210996 contact23ColumnsJoin128_8 contact23ColumnsJoin136_8
private theorem contact23ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact23) 144 16 = 263426325118 :=
  combineSlices (auxiliaryColumnSlice contact23) 144 8 8 181038639662 82387685456 contact23ColumnsJoin144_8 contact23ColumnsJoin152_8
private theorem contact23ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact23) 0 32 = 48543287425136 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 16 16 26920134342140 21623153082996 contact23ColumnsJoin0_16 contact23ColumnsJoin16_16
private theorem contact23ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact23) 32 32 = 29692355860943 :=
  combineSlices (auxiliaryColumnSlice contact23) 32 16 16 16910368738308 12781987122635 contact23ColumnsJoin32_16 contact23ColumnsJoin48_16
private theorem contact23ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact23) 64 32 = 15517134523171 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 16 16 9238159726538 6278974796633 contact23ColumnsJoin64_16 contact23ColumnsJoin80_16
private theorem contact23ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact23) 96 32 = 6019059635586 :=
  combineSlices (auxiliaryColumnSlice contact23) 96 16 16 3904456382289 2114603253297 contact23ColumnsJoin96_16 contact23ColumnsJoin112_16
private theorem contact23ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact23) 128 32 = 1172503636867 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 16 16 909077311749 263426325118 contact23ColumnsJoin128_16 contact23ColumnsJoin144_16
private theorem contact23ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact23) 0 64 = 78235643286079 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 32 32 48543287425136 29692355860943 contact23ColumnsJoin0_32 contact23ColumnsJoin32_32
private theorem contact23ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact23) 64 64 = 21536194158757 :=
  combineSlices (auxiliaryColumnSlice contact23) 64 32 32 15517134523171 6019059635586 contact23ColumnsJoin64_32 contact23ColumnsJoin96_32
private theorem contact23ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact23) 128 34 = 1183519224338 :=
  combineSlices (auxiliaryColumnSlice contact23) 128 32 2 1172503636867 11015587471 contact23ColumnsJoin128_32 contact23ColumnsSlice160
private theorem contact23ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact23) 0 128 = 99771837444836 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 64 64 78235643286079 21536194158757 contact23ColumnsJoin0_64 contact23ColumnsJoin64_64
private theorem contact23ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact23) 0 162 = 100955356669174 :=
  combineSlices (auxiliaryColumnSlice contact23) 0 128 34 99771837444836 1183519224338 contact23ColumnsJoin0_128 contact23ColumnsJoin128_34
private theorem contact23OrdinaryRanks : ordinaryRankBound contact23 = 8794130957 := by decide +kernel
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
private theorem contact23RanksSlice148 : sliceWindow (auxiliaryRankSlice contact23) 148 14 = 0 :=
  contactRankWindow_of_rec contact23 148 14 0 (by decide +kernel)
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
private theorem contact23RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact23) 144 18 = 950 :=
  combineSlices (auxiliaryRankSlice contact23) 144 4 14 950 0 contact23RanksSlice144 contact23RanksSlice148
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
private theorem contact23RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact23) 128 34 = 406465 :=
  combineSlices (auxiliaryRankSlice contact23) 128 16 18 405515 950 contact23RanksJoin128_16 contact23RanksJoin144_18
private theorem contact23RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact23) 0 64 = 262024434 :=
  combineSlices (auxiliaryRankSlice contact23) 0 32 32 173169456 88854978 contact23RanksJoin0_32 contact23RanksJoin32_32
private theorem contact23RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact23) 64 64 = 44594680 :=
  combineSlices (auxiliaryRankSlice contact23) 64 32 32 35809673 8785007 contact23RanksJoin64_32 contact23RanksJoin96_32
private theorem contact23RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact23) 0 128 = 306619114 :=
  combineSlices (auxiliaryRankSlice contact23) 0 64 64 262024434 44594680 contact23RanksJoin0_64 contact23RanksJoin64_64
private theorem contact23RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact23) 0 162 = 307025579 :=
  combineSlices (auxiliaryRankSlice contact23) 0 128 34 306619114 406465 contact23RanksJoin0_128 contact23RanksJoin128_34
theorem contact23_margin : sourceMargin contact23 :=
  margin_of_checked_counts contact23 162 2284858276585501 100955356669174 8794130957 307025579 rfl contact23OrdinaryColumns contact23ColumnsJoin0_162 contact23OrdinaryRanks contact23RanksJoin0_162 (by decide +kernel)

private theorem contact25OrdinaryColumns : ordinaryColumnCount contact25 = 2276943010124997 := by decide +kernel
private theorem contact25ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact25) 0 4 = 7596599190300 :=
  contactColumnsWindow_fast contact25 0 4 7596599190300 (by decide +kernel)
private theorem contact25ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact25) 4 4 = 7219424478076 :=
  contactColumnsWindow_fast contact25 4 4 7219424478076 (by decide +kernel)
private theorem contact25ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact25) 8 4 = 6851900426012 :=
  contactColumnsWindow_fast contact25 8 4 6851900426012 (by decide +kernel)
private theorem contact25ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact25) 12 4 = 6494030120700 :=
  contactColumnsWindow_fast contact25 12 4 6494030120700 (by decide +kernel)
private theorem contact25ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact25) 16 4 = 6145811453587 :=
  contactColumnsWindow_fast contact25 16 4 6145811453587 (by decide +kernel)
private theorem contact25ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact25) 20 4 = 5807246551324 :=
  contactColumnsWindow_fast contact25 20 4 5807246551324 (by decide +kernel)
private theorem contact25ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact25) 24 4 = 5478352443264 :=
  contactColumnsWindow_fast contact25 24 4 5478352443264 (by decide +kernel)
private theorem contact25ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact25) 28 4 = 5159150835060 :=
  contactColumnsWindow_fast contact25 28 4 5159150835060 (by decide +kernel)
private theorem contact25ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact25) 32 4 = 4849606519228 :=
  contactColumnsWindow_fast contact25 32 4 4849606519228 (by decide +kernel)
private theorem contact25ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact25) 36 4 = 4549717209473 :=
  contactColumnsWindow_fast contact25 36 4 4549717209473 (by decide +kernel)
private theorem contact25ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact25) 40 4 = 4259484854052 :=
  contactColumnsWindow_fast contact25 40 4 4259484854052 (by decide +kernel)
private theorem contact25ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact25) 44 4 = 3978930659671 :=
  contactColumnsWindow_fast contact25 44 4 3978930659671 (by decide +kernel)
private theorem contact25ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact25) 48 4 = 3708069656492 :=
  contactColumnsWindow_fast contact25 48 4 3708069656492 (by decide +kernel)
private theorem contact25ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact25) 52 4 = 3446867500482 :=
  contactColumnsWindow_fast contact25 52 4 3446867500482 (by decide +kernel)
private theorem contact25ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact25) 56 4 = 3195324822163 :=
  contactColumnsWindow_fast contact25 56 4 3195324822163 (by decide +kernel)
private theorem contact25ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact25) 60 4 = 2953441386928 :=
  contactColumnsWindow_fast contact25 60 4 2953441386928 (by decide +kernel)
private theorem contact25ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact25) 64 4 = 2721246456289 :=
  contactColumnsWindow_fast contact25 64 4 2721246456289 (by decide +kernel)
private theorem contact25ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact25) 68 4 = 2498741646329 :=
  contactColumnsWindow_fast contact25 68 4 2498741646329 (by decide +kernel)
private theorem contact25ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact25) 72 4 = 2285900909532 :=
  contactColumnsWindow_fast contact25 72 4 2285900909532 (by decide +kernel)
private theorem contact25ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact25) 76 4 = 2082720238760 :=
  contactColumnsWindow_fast contact25 76 4 2082720238760 (by decide +kernel)
private theorem contact25ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact25) 80 4 = 1889198576956 :=
  contactColumnsWindow_fast contact25 80 4 1889198576956 (by decide +kernel)
private theorem contact25ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact25) 84 4 = 1705371004192 :=
  contactColumnsWindow_fast contact25 84 4 1705371004192 (by decide +kernel)
private theorem contact25ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact25) 88 4 = 1531228612287 :=
  contactColumnsWindow_fast contact25 88 4 1531228612287 (by decide +kernel)
private theorem contact25ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact25) 92 4 = 1366749870636 :=
  contactColumnsWindow_fast contact25 92 4 1366749870636 (by decide +kernel)
private theorem contact25ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact25) 96 4 = 1211931164816 :=
  contactColumnsWindow_fast contact25 96 4 1211931164816 (by decide +kernel)
private theorem contact25ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact25) 100 4 = 1066772176121 :=
  contactColumnsWindow_fast contact25 100 4 1066772176121 (by decide +kernel)
private theorem contact25ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact25) 104 4 = 931311163564 :=
  contactColumnsWindow_fast contact25 104 4 931311163564 (by decide +kernel)
private theorem contact25ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact25) 108 4 = 805531176093 :=
  contactColumnsWindow_fast contact25 108 4 805531176093 (by decide +kernel)
private theorem contact25ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact25) 112 4 = 689414345949 :=
  contactColumnsWindow_fast contact25 112 4 689414345949 (by decide +kernel)
private theorem contact25ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact25) 116 4 = 582957687916 :=
  contactColumnsWindow_fast contact25 116 4 582957687916 (by decide +kernel)
private theorem contact25ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact25) 120 4 = 486161968043 :=
  contactColumnsWindow_fast contact25 120 4 486161968043 (by decide +kernel)
private theorem contact25ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact25) 124 4 = 399066816520 :=
  contactColumnsWindow_fast contact25 124 4 399066816520 (by decide +kernel)
private theorem contact25ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact25) 128 4 = 321649284596 :=
  contactColumnsWindow_fast contact25 128 4 321649284596 (by decide +kernel)
private theorem contact25ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact25) 132 4 = 253888846048 :=
  contactColumnsWindow_fast contact25 132 4 253888846048 (by decide +kernel)
private theorem contact25ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact25) 136 4 = 195687400473 :=
  contactColumnsWindow_fast contact25 136 4 195687400473 (by decide +kernel)
private theorem contact25ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact25) 140 4 = 146753271201 :=
  contactColumnsWindow_fast contact25 140 4 146753271201 (by decide +kernel)
private theorem contact25ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact25) 144 4 = 106662214348 :=
  contactColumnsWindow_fast contact25 144 4 106662214348 (by decide +kernel)
private theorem contact25ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact25) 148 4 = 74757619682 :=
  contactColumnsWindow_fast contact25 148 4 74757619682 (by decide +kernel)
private theorem contact25ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact25) 152 4 = 50239615555 :=
  contactColumnsWindow_fast contact25 152 4 50239615555 (by decide +kernel)
private theorem contact25ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact25) 156 3 = 25501539286 :=
  contactColumnsWindow_fast contact25 156 3 25501539286 (by decide +kernel)
private theorem contact25ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact25) 0 8 = 14816023668376 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 4 4 7596599190300 7219424478076 contact25ColumnsSlice0 contact25ColumnsSlice4
private theorem contact25ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact25) 8 8 = 13345930546712 :=
  combineSlices (auxiliaryColumnSlice contact25) 8 4 4 6851900426012 6494030120700 contact25ColumnsSlice8 contact25ColumnsSlice12
private theorem contact25ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact25) 16 8 = 11953058004911 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 4 4 6145811453587 5807246551324 contact25ColumnsSlice16 contact25ColumnsSlice20
private theorem contact25ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact25) 24 8 = 10637503278324 :=
  combineSlices (auxiliaryColumnSlice contact25) 24 4 4 5478352443264 5159150835060 contact25ColumnsSlice24 contact25ColumnsSlice28
private theorem contact25ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact25) 32 8 = 9399323728701 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 4 4 4849606519228 4549717209473 contact25ColumnsSlice32 contact25ColumnsSlice36
private theorem contact25ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact25) 40 8 = 8238415513723 :=
  combineSlices (auxiliaryColumnSlice contact25) 40 4 4 4259484854052 3978930659671 contact25ColumnsSlice40 contact25ColumnsSlice44
private theorem contact25ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact25) 48 8 = 7154937156974 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 4 4 3708069656492 3446867500482 contact25ColumnsSlice48 contact25ColumnsSlice52
private theorem contact25ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact25) 56 8 = 6148766209091 :=
  combineSlices (auxiliaryColumnSlice contact25) 56 4 4 3195324822163 2953441386928 contact25ColumnsSlice56 contact25ColumnsSlice60
private theorem contact25ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact25) 64 8 = 5219988102618 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 4 4 2721246456289 2498741646329 contact25ColumnsSlice64 contact25ColumnsSlice68
private theorem contact25ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact25) 72 8 = 4368621148292 :=
  combineSlices (auxiliaryColumnSlice contact25) 72 4 4 2285900909532 2082720238760 contact25ColumnsSlice72 contact25ColumnsSlice76
private theorem contact25ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact25) 80 8 = 3594569581148 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 4 4 1889198576956 1705371004192 contact25ColumnsSlice80 contact25ColumnsSlice84
private theorem contact25ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact25) 88 8 = 2897978482923 :=
  combineSlices (auxiliaryColumnSlice contact25) 88 4 4 1531228612287 1366749870636 contact25ColumnsSlice88 contact25ColumnsSlice92
private theorem contact25ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact25) 96 8 = 2278703340937 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 4 4 1211931164816 1066772176121 contact25ColumnsSlice96 contact25ColumnsSlice100
private theorem contact25ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact25) 104 8 = 1736842339657 :=
  combineSlices (auxiliaryColumnSlice contact25) 104 4 4 931311163564 805531176093 contact25ColumnsSlice104 contact25ColumnsSlice108
private theorem contact25ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact25) 112 8 = 1272372033865 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 4 4 689414345949 582957687916 contact25ColumnsSlice112 contact25ColumnsSlice116
private theorem contact25ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact25) 120 8 = 885228784563 :=
  combineSlices (auxiliaryColumnSlice contact25) 120 4 4 486161968043 399066816520 contact25ColumnsSlice120 contact25ColumnsSlice124
private theorem contact25ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact25) 128 8 = 575538130644 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 4 4 321649284596 253888846048 contact25ColumnsSlice128 contact25ColumnsSlice132
private theorem contact25ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact25) 136 8 = 342440671674 :=
  combineSlices (auxiliaryColumnSlice contact25) 136 4 4 195687400473 146753271201 contact25ColumnsSlice136 contact25ColumnsSlice140
private theorem contact25ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact25) 144 8 = 181419834030 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 4 4 106662214348 74757619682 contact25ColumnsSlice144 contact25ColumnsSlice148
private theorem contact25ColumnsJoin152_7 : sliceWindow (auxiliaryColumnSlice contact25) 152 7 = 75741154841 :=
  combineSlices (auxiliaryColumnSlice contact25) 152 4 3 50239615555 25501539286 contact25ColumnsSlice152 contact25ColumnsSlice156
private theorem contact25ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact25) 0 16 = 28161954215088 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 8 8 14816023668376 13345930546712 contact25ColumnsJoin0_8 contact25ColumnsJoin8_8
private theorem contact25ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact25) 16 16 = 22590561283235 :=
  combineSlices (auxiliaryColumnSlice contact25) 16 8 8 11953058004911 10637503278324 contact25ColumnsJoin16_8 contact25ColumnsJoin24_8
private theorem contact25ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact25) 32 16 = 17637739242424 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 8 8 9399323728701 8238415513723 contact25ColumnsJoin32_8 contact25ColumnsJoin40_8
private theorem contact25ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact25) 48 16 = 13303703366065 :=
  combineSlices (auxiliaryColumnSlice contact25) 48 8 8 7154937156974 6148766209091 contact25ColumnsJoin48_8 contact25ColumnsJoin56_8
private theorem contact25ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact25) 64 16 = 9588609250910 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 8 8 5219988102618 4368621148292 contact25ColumnsJoin64_8 contact25ColumnsJoin72_8
private theorem contact25ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact25) 80 16 = 6492548064071 :=
  combineSlices (auxiliaryColumnSlice contact25) 80 8 8 3594569581148 2897978482923 contact25ColumnsJoin80_8 contact25ColumnsJoin88_8
private theorem contact25ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact25) 96 16 = 4015545680594 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 8 8 2278703340937 1736842339657 contact25ColumnsJoin96_8 contact25ColumnsJoin104_8
private theorem contact25ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact25) 112 16 = 2157600818428 :=
  combineSlices (auxiliaryColumnSlice contact25) 112 8 8 1272372033865 885228784563 contact25ColumnsJoin112_8 contact25ColumnsJoin120_8
private theorem contact25ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact25) 128 16 = 917978802318 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 8 8 575538130644 342440671674 contact25ColumnsJoin128_8 contact25ColumnsJoin136_8
private theorem contact25ColumnsJoin144_15 : sliceWindow (auxiliaryColumnSlice contact25) 144 15 = 257160988871 :=
  combineSlices (auxiliaryColumnSlice contact25) 144 8 7 181419834030 75741154841 contact25ColumnsJoin144_8 contact25ColumnsJoin152_7
private theorem contact25ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact25) 0 32 = 50752515498323 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 16 16 28161954215088 22590561283235 contact25ColumnsJoin0_16 contact25ColumnsJoin16_16
private theorem contact25ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact25) 32 32 = 30941442608489 :=
  combineSlices (auxiliaryColumnSlice contact25) 32 16 16 17637739242424 13303703366065 contact25ColumnsJoin32_16 contact25ColumnsJoin48_16
private theorem contact25ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact25) 64 32 = 16081157314981 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 16 16 9588609250910 6492548064071 contact25ColumnsJoin64_16 contact25ColumnsJoin80_16
private theorem contact25ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact25) 96 32 = 6173146499022 :=
  combineSlices (auxiliaryColumnSlice contact25) 96 16 16 4015545680594 2157600818428 contact25ColumnsJoin96_16 contact25ColumnsJoin112_16
private theorem contact25ColumnsJoin128_31 : sliceWindow (auxiliaryColumnSlice contact25) 128 31 = 1175139791189 :=
  combineSlices (auxiliaryColumnSlice contact25) 128 16 15 917978802318 257160988871 contact25ColumnsJoin128_16 contact25ColumnsJoin144_15
private theorem contact25ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact25) 0 64 = 81693958106812 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 32 32 50752515498323 30941442608489 contact25ColumnsJoin0_32 contact25ColumnsJoin32_32
private theorem contact25ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact25) 64 64 = 22254303814003 :=
  combineSlices (auxiliaryColumnSlice contact25) 64 32 32 16081157314981 6173146499022 contact25ColumnsJoin64_32 contact25ColumnsJoin96_32
private theorem contact25ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact25) 0 128 = 103948261920815 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 64 64 81693958106812 22254303814003 contact25ColumnsJoin0_64 contact25ColumnsJoin64_64
private theorem contact25ColumnsJoin0_159 : sliceWindow (auxiliaryColumnSlice contact25) 0 159 = 105123401712004 :=
  combineSlices (auxiliaryColumnSlice contact25) 0 128 31 103948261920815 1175139791189 contact25ColumnsJoin0_128 contact25ColumnsJoin128_31
private theorem contact25OrdinaryRanks : ordinaryRankBound contact25 = 8765654025 := by decide +kernel
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
private theorem contact25RanksSlice148 : sliceWindow (auxiliaryRankSlice contact25) 148 11 = 0 :=
  contactRankWindow_of_rec contact25 148 11 0 (by decide +kernel)
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
private theorem contact25RanksJoin144_15 : sliceWindow (auxiliaryRankSlice contact25) 144 15 = 989 :=
  combineSlices (auxiliaryRankSlice contact25) 144 4 11 989 0 contact25RanksSlice144 contact25RanksSlice148
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
private theorem contact25RanksJoin128_31 : sliceWindow (auxiliaryRankSlice contact25) 128 31 = 426801 :=
  combineSlices (auxiliaryRankSlice contact25) 128 16 15 425812 989 contact25RanksJoin128_16 contact25RanksJoin144_15
private theorem contact25RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact25) 0 64 = 274039262 :=
  combineSlices (auxiliaryRankSlice contact25) 0 32 32 181128704 92910558 contact25RanksJoin0_32 contact25RanksJoin32_32
private theorem contact25RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact25) 64 64 = 46739998 :=
  combineSlices (auxiliaryRankSlice contact25) 64 32 32 37514037 9225961 contact25RanksJoin64_32 contact25RanksJoin96_32
private theorem contact25RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact25) 0 128 = 320779260 :=
  combineSlices (auxiliaryRankSlice contact25) 0 64 64 274039262 46739998 contact25RanksJoin0_64 contact25RanksJoin64_64
private theorem contact25RanksJoin0_159 : sliceWindow (auxiliaryRankSlice contact25) 0 159 = 321206061 :=
  combineSlices (auxiliaryRankSlice contact25) 0 128 31 320779260 426801 contact25RanksJoin0_128 contact25RanksJoin128_31
theorem contact25_margin : sourceMargin contact25 :=
  margin_of_checked_counts contact25 159 2276943010124997 105123401712004 8765654025 321206061 rfl contact25OrdinaryColumns contact25ColumnsJoin0_159 contact25OrdinaryRanks contact25RanksJoin0_159 (by decide +kernel)

private theorem contact27OrdinaryColumns : ordinaryColumnCount contact27 = 2259534589662417 := by decide +kernel
private theorem contact27ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact27) 0 4 = 7428701877480 :=
  contactColumnsWindow_fast contact27 0 4 7428701877480 (by decide +kernel)
private theorem contact27ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact27) 4 4 = 7060875093560 :=
  contactColumnsWindow_fast contact27 4 4 7060875093560 (by decide +kernel)
private theorem contact27ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact27) 8 4 = 6702430901227 :=
  contactColumnsWindow_fast contact27 8 4 6702430901227 (by decide +kernel)
private theorem contact27ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact27) 12 4 = 6353372322722 :=
  contactColumnsWindow_fast contact27 12 4 6353372322722 (by decide +kernel)
private theorem contact27ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact27) 16 4 = 6013697294459 :=
  contactColumnsWindow_fast contact27 16 4 6013697294459 (by decide +kernel)
private theorem contact27ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact27) 20 4 = 5683407900916 :=
  contactColumnsWindow_fast contact27 20 4 5683407900916 (by decide +kernel)
private theorem contact27ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact27) 24 4 = 5362520512696 :=
  contactColumnsWindow_fast contact27 24 4 5362520512696 (by decide +kernel)
private theorem contact27ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact27) 28 4 = 5051056074643 :=
  contactColumnsWindow_fast contact27 28 4 5051056074643 (by decide +kernel)
private theorem contact27ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact27) 32 4 = 4748980712734 :=
  contactColumnsWindow_fast contact27 32 4 4748980712734 (by decide +kernel)
private theorem contact27ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact27) 36 4 = 4456292206454 :=
  contactColumnsWindow_fast contact27 36 4 4456292206454 (by decide +kernel)
private theorem contact27ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact27) 40 4 = 4172992468062 :=
  contactColumnsWindow_fast contact27 40 4 4172992468062 (by decide +kernel)
private theorem contact27ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact27) 44 4 = 3899101886012 :=
  contactColumnsWindow_fast contact27 44 4 3899101886012 (by decide +kernel)
private theorem contact27ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact27) 48 4 = 3634635000732 :=
  contactColumnsWindow_fast contact27 48 4 3634635000732 (by decide +kernel)
private theorem contact27ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact27) 52 4 = 3379558738995 :=
  contactColumnsWindow_fast contact27 52 4 3379558738995 (by decide +kernel)
private theorem contact27ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact27) 56 4 = 3133873730233 :=
  contactColumnsWindow_fast contact27 56 4 3133873730233 (by decide +kernel)
private theorem contact27ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact27) 60 4 = 2897579740587 :=
  contactColumnsWindow_fast contact27 60 4 2897579740587 (by decide +kernel)
private theorem contact27ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact27) 64 4 = 2670704972105 :=
  contactColumnsWindow_fast contact27 64 4 2670704972105 (by decide +kernel)
private theorem contact27ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact27) 68 4 = 2453250991128 :=
  contactColumnsWindow_fast contact27 68 4 2453250991128 (by decide +kernel)
private theorem contact27ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact27) 72 4 = 2245192778165 :=
  contactColumnsWindow_fast contact27 72 4 2245192778165 (by decide +kernel)
private theorem contact27ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact27) 76 4 = 2046526396877 :=
  contactColumnsWindow_fast contact27 76 4 2046526396877 (by decide +kernel)
private theorem contact27ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact27) 80 4 = 1857250805847 :=
  contactColumnsWindow_fast contact27 80 4 1857250805847 (by decide +kernel)
private theorem contact27ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact27) 84 4 = 1677399817901 :=
  contactColumnsWindow_fast contact27 84 4 1677399817901 (by decide +kernel)
private theorem contact27ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact27) 88 4 = 1506964868128 :=
  contactColumnsWindow_fast contact27 88 4 1506964868128 (by decide +kernel)
private theorem contact27ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact27) 92 4 = 1345925271341 :=
  contactColumnsWindow_fast contact27 92 4 1345925271341 (by decide +kernel)
private theorem contact27ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact27) 96 4 = 1194277475594 :=
  contactColumnsWindow_fast contact27 96 4 1194277475594 (by decide +kernel)
private theorem contact27ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact27) 100 4 = 1052021152072 :=
  contactColumnsWindow_fast contact27 100 4 1052021152072 (by decide +kernel)
private theorem contact27ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact27) 104 4 = 919193176061 :=
  contactColumnsWindow_fast contact27 104 4 919193176061 (by decide +kernel)
private theorem contact27ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact27) 108 4 = 795777243904 :=
  contactColumnsWindow_fast contact27 108 4 795777243904 (by decide +kernel)
private theorem contact27ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact27) 112 4 = 681756181294 :=
  contactColumnsWindow_fast contact27 112 4 681756181294 (by decide +kernel)
private theorem contact27ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact27) 116 4 = 577127052491 :=
  contactColumnsWindow_fast contact27 116 4 577127052491 (by decide +kernel)
private theorem contact27ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact27) 120 4 = 481890570820 :=
  contactColumnsWindow_fast contact27 120 4 481890570820 (by decide +kernel)
private theorem contact27ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact27) 124 4 = 396084930761 :=
  contactColumnsWindow_fast contact27 124 4 396084930761 (by decide +kernel)
private theorem contact27ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact27) 128 4 = 319688066469 :=
  contactColumnsWindow_fast contact27 128 4 319688066469 (by decide +kernel)
private theorem contact27ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact27) 132 4 = 252683866067 :=
  contactColumnsWindow_fast contact27 132 4 252683866067 (by decide +kernel)
private theorem contact27ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact27) 136 4 = 195009837539 :=
  contactColumnsWindow_fast contact27 136 4 195009837539 (by decide +kernel)
private theorem contact27ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact27) 140 4 = 146421661293 :=
  contactColumnsWindow_fast contact27 140 4 146421661293 (by decide +kernel)
private theorem contact27ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact27) 144 4 = 106531819050 :=
  contactColumnsWindow_fast contact27 144 4 106531819050 (by decide +kernel)
private theorem contact27ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact27) 148 4 = 74723698392 :=
  contactColumnsWindow_fast contact27 148 4 74723698392 (by decide +kernel)
private theorem contact27ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact27) 152 4 = 50236457745 :=
  contactColumnsWindow_fast contact27 152 4 50236457745 (by decide +kernel)
private theorem contact27ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact27) 156 4 = 32157842291 :=
  contactColumnsWindow_fast contact27 156 4 32157842291 (by decide +kernel)
private theorem contact27ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact27) 0 8 = 14489576971040 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 4 4 7428701877480 7060875093560 contact27ColumnsSlice0 contact27ColumnsSlice4
private theorem contact27ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact27) 8 8 = 13055803223949 :=
  combineSlices (auxiliaryColumnSlice contact27) 8 4 4 6702430901227 6353372322722 contact27ColumnsSlice8 contact27ColumnsSlice12
private theorem contact27ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact27) 16 8 = 11697105195375 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 4 4 6013697294459 5683407900916 contact27ColumnsSlice16 contact27ColumnsSlice20
private theorem contact27ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact27) 24 8 = 10413576587339 :=
  combineSlices (auxiliaryColumnSlice contact27) 24 4 4 5362520512696 5051056074643 contact27ColumnsSlice24 contact27ColumnsSlice28
private theorem contact27ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact27) 32 8 = 9205272919188 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 4 4 4748980712734 4456292206454 contact27ColumnsSlice32 contact27ColumnsSlice36
private theorem contact27ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact27) 40 8 = 8072094354074 :=
  combineSlices (auxiliaryColumnSlice contact27) 40 4 4 4172992468062 3899101886012 contact27ColumnsSlice40 contact27ColumnsSlice44
private theorem contact27ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact27) 48 8 = 7014193739727 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 4 4 3634635000732 3379558738995 contact27ColumnsSlice48 contact27ColumnsSlice52
private theorem contact27ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact27) 56 8 = 6031453470820 :=
  combineSlices (auxiliaryColumnSlice contact27) 56 4 4 3133873730233 2897579740587 contact27ColumnsSlice56 contact27ColumnsSlice60
private theorem contact27ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact27) 64 8 = 5123955963233 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 4 4 2670704972105 2453250991128 contact27ColumnsSlice64 contact27ColumnsSlice68
private theorem contact27ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact27) 72 8 = 4291719175042 :=
  combineSlices (auxiliaryColumnSlice contact27) 72 4 4 2245192778165 2046526396877 contact27ColumnsSlice72 contact27ColumnsSlice76
private theorem contact27ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact27) 80 8 = 3534650623748 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 4 4 1857250805847 1677399817901 contact27ColumnsSlice80 contact27ColumnsSlice84
private theorem contact27ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact27) 88 8 = 2852890139469 :=
  combineSlices (auxiliaryColumnSlice contact27) 88 4 4 1506964868128 1345925271341 contact27ColumnsSlice88 contact27ColumnsSlice92
private theorem contact27ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact27) 96 8 = 2246298627666 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 4 4 1194277475594 1052021152072 contact27ColumnsSlice96 contact27ColumnsSlice100
private theorem contact27ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact27) 104 8 = 1714970419965 :=
  combineSlices (auxiliaryColumnSlice contact27) 104 4 4 919193176061 795777243904 contact27ColumnsSlice104 contact27ColumnsSlice108
private theorem contact27ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact27) 112 8 = 1258883233785 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 4 4 681756181294 577127052491 contact27ColumnsSlice112 contact27ColumnsSlice116
private theorem contact27ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact27) 120 8 = 877975501581 :=
  combineSlices (auxiliaryColumnSlice contact27) 120 4 4 481890570820 396084930761 contact27ColumnsSlice120 contact27ColumnsSlice124
private theorem contact27ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact27) 128 8 = 572371932536 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 4 4 319688066469 252683866067 contact27ColumnsSlice128 contact27ColumnsSlice132
private theorem contact27ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact27) 136 8 = 341431498832 :=
  combineSlices (auxiliaryColumnSlice contact27) 136 4 4 195009837539 146421661293 contact27ColumnsSlice136 contact27ColumnsSlice140
private theorem contact27ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact27) 144 8 = 181255517442 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 4 4 106531819050 74723698392 contact27ColumnsSlice144 contact27ColumnsSlice148
private theorem contact27ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact27) 152 8 = 82394300036 :=
  combineSlices (auxiliaryColumnSlice contact27) 152 4 4 50236457745 32157842291 contact27ColumnsSlice152 contact27ColumnsSlice156
private theorem contact27ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact27) 0 16 = 27545380194989 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 8 8 14489576971040 13055803223949 contact27ColumnsJoin0_8 contact27ColumnsJoin8_8
private theorem contact27ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact27) 16 16 = 22110681782714 :=
  combineSlices (auxiliaryColumnSlice contact27) 16 8 8 11697105195375 10413576587339 contact27ColumnsJoin16_8 contact27ColumnsJoin24_8
private theorem contact27ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact27) 32 16 = 17277367273262 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 8 8 9205272919188 8072094354074 contact27ColumnsJoin32_8 contact27ColumnsJoin40_8
private theorem contact27ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact27) 48 16 = 13045647210547 :=
  combineSlices (auxiliaryColumnSlice contact27) 48 8 8 7014193739727 6031453470820 contact27ColumnsJoin48_8 contact27ColumnsJoin56_8
private theorem contact27ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact27) 64 16 = 9415675138275 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 8 8 5123955963233 4291719175042 contact27ColumnsJoin64_8 contact27ColumnsJoin72_8
private theorem contact27ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact27) 80 16 = 6387540763217 :=
  combineSlices (auxiliaryColumnSlice contact27) 80 8 8 3534650623748 2852890139469 contact27ColumnsJoin80_8 contact27ColumnsJoin88_8
private theorem contact27ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact27) 96 16 = 3961269047631 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 8 8 2246298627666 1714970419965 contact27ColumnsJoin96_8 contact27ColumnsJoin104_8
private theorem contact27ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact27) 112 16 = 2136858735366 :=
  combineSlices (auxiliaryColumnSlice contact27) 112 8 8 1258883233785 877975501581 contact27ColumnsJoin112_8 contact27ColumnsJoin120_8
private theorem contact27ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact27) 128 16 = 913803431368 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 8 8 572371932536 341431498832 contact27ColumnsJoin128_8 contact27ColumnsJoin136_8
private theorem contact27ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact27) 144 16 = 263649817478 :=
  combineSlices (auxiliaryColumnSlice contact27) 144 8 8 181255517442 82394300036 contact27ColumnsJoin144_8 contact27ColumnsJoin152_8
private theorem contact27ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact27) 0 32 = 49656061977703 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 16 16 27545380194989 22110681782714 contact27ColumnsJoin0_16 contact27ColumnsJoin16_16
private theorem contact27ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact27) 32 32 = 30323014483809 :=
  combineSlices (auxiliaryColumnSlice contact27) 32 16 16 17277367273262 13045647210547 contact27ColumnsJoin32_16 contact27ColumnsJoin48_16
private theorem contact27ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact27) 64 32 = 15803215901492 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 16 16 9415675138275 6387540763217 contact27ColumnsJoin64_16 contact27ColumnsJoin80_16
private theorem contact27ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact27) 96 32 = 6098127782997 :=
  combineSlices (auxiliaryColumnSlice contact27) 96 16 16 3961269047631 2136858735366 contact27ColumnsJoin96_16 contact27ColumnsJoin112_16
private theorem contact27ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact27) 128 32 = 1177453248846 :=
  combineSlices (auxiliaryColumnSlice contact27) 128 16 16 913803431368 263649817478 contact27ColumnsJoin128_16 contact27ColumnsJoin144_16
private theorem contact27ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact27) 0 64 = 79979076461512 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 32 32 49656061977703 30323014483809 contact27ColumnsJoin0_32 contact27ColumnsJoin32_32
private theorem contact27ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact27) 64 64 = 21901343684489 :=
  combineSlices (auxiliaryColumnSlice contact27) 64 32 32 15803215901492 6098127782997 contact27ColumnsJoin64_32 contact27ColumnsJoin96_32
private theorem contact27ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact27) 0 128 = 101880420146001 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 64 64 79979076461512 21901343684489 contact27ColumnsJoin0_64 contact27ColumnsJoin64_64
private theorem contact27ColumnsJoin0_160 : sliceWindow (auxiliaryColumnSlice contact27) 0 160 = 103057873394847 :=
  combineSlices (auxiliaryColumnSlice contact27) 0 128 32 101880420146001 1177453248846 contact27ColumnsJoin0_128 contact27ColumnsJoin128_32
private theorem contact27OrdinaryRanks : ordinaryRankBound contact27 = 8698419869 := by decide +kernel
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
private theorem contact27RanksSlice148 : sliceWindow (auxiliaryRankSlice contact27) 148 12 = 0 :=
  contactRankWindow_of_rec contact27 148 12 0 (by decide +kernel)
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
private theorem contact27RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact27) 144 16 = 970 :=
  combineSlices (auxiliaryRankSlice contact27) 144 4 12 970 0 contact27RanksSlice144 contact27RanksSlice148
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
private theorem contact27RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact27) 128 32 = 416760 :=
  combineSlices (auxiliaryRankSlice contact27) 128 16 16 415790 970 contact27RanksJoin128_16 contact27RanksJoin144_16
private theorem contact27RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact27) 0 64 = 268062126 :=
  combineSlices (auxiliaryRankSlice contact27) 0 32 32 177171008 90891118 contact27RanksJoin0_32 contact27RanksJoin32_32
private theorem contact27RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact27) 64 64 = 45671352 :=
  combineSlices (auxiliaryRankSlice contact27) 64 32 32 36664973 9006379 contact27RanksJoin64_32 contact27RanksJoin96_32
private theorem contact27RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact27) 0 128 = 313733478 :=
  combineSlices (auxiliaryRankSlice contact27) 0 64 64 268062126 45671352 contact27RanksJoin0_64 contact27RanksJoin64_64
private theorem contact27RanksJoin0_160 : sliceWindow (auxiliaryRankSlice contact27) 0 160 = 314150238 :=
  combineSlices (auxiliaryRankSlice contact27) 0 128 32 313733478 416760 contact27RanksJoin0_128 contact27RanksJoin128_32
theorem contact27_margin : sourceMargin contact27 :=
  margin_of_checked_counts contact27 160 2259534589662417 103057873394847 8698419869 314150238 rfl contact27OrdinaryColumns contact27ColumnsJoin0_160 contact27OrdinaryRanks contact27RanksJoin0_160 (by decide +kernel)

private theorem contact29OrdinaryColumns : ordinaryColumnCount contact29 = 192754548293943 := by decide +kernel
private theorem contact29ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact29) 0 4 = 1033656244602 :=
  contactColumnsWindow_fast contact29 0 4 1033656244602 (by decide +kernel)
private theorem contact29ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact29) 4 4 = 948695544451 :=
  contactColumnsWindow_fast contact29 4 4 948695544451 (by decide +kernel)
private theorem contact29ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact29) 8 4 = 867417986840 :=
  contactColumnsWindow_fast contact29 8 4 867417986840 (by decide +kernel)
private theorem contact29ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact29) 12 4 = 789806671219 :=
  contactColumnsWindow_fast contact29 12 4 789806671219 (by decide +kernel)
private theorem contact29ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact29) 16 4 = 715858467138 :=
  contactColumnsWindow_fast contact29 16 4 715858467138 (by decide +kernel)
private theorem contact29ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact29) 20 4 = 645571828561 :=
  contactColumnsWindow_fast contact29 20 4 645571828561 (by decide +kernel)
private theorem contact29ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact29) 24 4 = 578951996719 :=
  contactColumnsWindow_fast contact29 24 4 578951996719 (by decide +kernel)
private theorem contact29ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact29) 28 4 = 516016819694 :=
  contactColumnsWindow_fast contact29 28 4 516016819694 (by decide +kernel)
private theorem contact29ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact29) 32 4 = 456749430313 :=
  contactColumnsWindow_fast contact29 32 4 456749430313 (by decide +kernel)
private theorem contact29ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact29) 36 4 = 401145240534 :=
  contactColumnsWindow_fast contact29 36 4 401145240534 (by decide +kernel)
private theorem contact29ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact29) 40 4 = 349202717488 :=
  contactColumnsWindow_fast contact29 40 4 349202717488 (by decide +kernel)
private theorem contact29ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact29) 44 4 = 300928225801 :=
  contactColumnsWindow_fast contact29 44 4 300928225801 (by decide +kernel)
private theorem contact29ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact29) 48 4 = 256338594680 :=
  contactColumnsWindow_fast contact29 48 4 256338594680 (by decide +kernel)
private theorem contact29ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact29) 52 4 = 215415388268 :=
  contactColumnsWindow_fast contact29 52 4 215415388268 (by decide +kernel)
private theorem contact29ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact29) 56 4 = 178155132186 :=
  contactColumnsWindow_fast contact29 56 4 178155132186 (by decide +kernel)
private theorem contact29ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact29) 60 4 = 144556724671 :=
  contactColumnsWindow_fast contact29 60 4 144556724671 (by decide +kernel)
private theorem contact29ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact29) 64 4 = 114627926529 :=
  contactColumnsWindow_fast contact29 64 4 114627926529 (by decide +kernel)
private theorem contact29ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact29) 68 4 = 88383575984 :=
  contactColumnsWindow_fast contact29 68 4 88383575984 (by decide +kernel)
private theorem contact29ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact29) 72 4 = 65804470289 :=
  contactColumnsWindow_fast contact29 72 4 65804470289 (by decide +kernel)
private theorem contact29ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact29) 76 4 = 46888142094 :=
  contactColumnsWindow_fast contact29 76 4 46888142094 (by decide +kernel)
private theorem contact29ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact29) 80 4 = 31625620559 :=
  contactColumnsWindow_fast contact29 80 4 31625620559 (by decide +kernel)
private theorem contact29ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact29) 84 4 = 19926781891 :=
  contactColumnsWindow_fast contact29 84 4 19926781891 (by decide +kernel)
private theorem contact29ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact29) 88 4 = 11532645061 :=
  contactColumnsWindow_fast contact29 88 4 11532645061 (by decide +kernel)
private theorem contact29ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact29) 92 4 = 5989917407 :=
  contactColumnsWindow_fast contact29 92 4 5989917407 (by decide +kernel)
private theorem contact29ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact29) 0 8 = 1982351789053 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 4 4 1033656244602 948695544451 contact29ColumnsSlice0 contact29ColumnsSlice4
private theorem contact29ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact29) 8 8 = 1657224658059 :=
  combineSlices (auxiliaryColumnSlice contact29) 8 4 4 867417986840 789806671219 contact29ColumnsSlice8 contact29ColumnsSlice12
private theorem contact29ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact29) 16 8 = 1361430295699 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 4 4 715858467138 645571828561 contact29ColumnsSlice16 contact29ColumnsSlice20
private theorem contact29ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact29) 24 8 = 1094968816413 :=
  combineSlices (auxiliaryColumnSlice contact29) 24 4 4 578951996719 516016819694 contact29ColumnsSlice24 contact29ColumnsSlice28
private theorem contact29ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact29) 32 8 = 857894670847 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 4 4 456749430313 401145240534 contact29ColumnsSlice32 contact29ColumnsSlice36
private theorem contact29ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact29) 40 8 = 650130943289 :=
  combineSlices (auxiliaryColumnSlice contact29) 40 4 4 349202717488 300928225801 contact29ColumnsSlice40 contact29ColumnsSlice44
private theorem contact29ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact29) 48 8 = 471753982948 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 4 4 256338594680 215415388268 contact29ColumnsSlice48 contact29ColumnsSlice52
private theorem contact29ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact29) 56 8 = 322711856857 :=
  combineSlices (auxiliaryColumnSlice contact29) 56 4 4 178155132186 144556724671 contact29ColumnsSlice56 contact29ColumnsSlice60
private theorem contact29ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact29) 64 8 = 203011502513 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 4 4 114627926529 88383575984 contact29ColumnsSlice64 contact29ColumnsSlice68
private theorem contact29ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact29) 72 8 = 112692612383 :=
  combineSlices (auxiliaryColumnSlice contact29) 72 4 4 65804470289 46888142094 contact29ColumnsSlice72 contact29ColumnsSlice76
private theorem contact29ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact29) 80 8 = 51552402450 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 4 4 31625620559 19926781891 contact29ColumnsSlice80 contact29ColumnsSlice84
private theorem contact29ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact29) 88 8 = 17522562468 :=
  combineSlices (auxiliaryColumnSlice contact29) 88 4 4 11532645061 5989917407 contact29ColumnsSlice88 contact29ColumnsSlice92
private theorem contact29ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact29) 0 16 = 3639576447112 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 8 8 1982351789053 1657224658059 contact29ColumnsJoin0_8 contact29ColumnsJoin8_8
private theorem contact29ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact29) 16 16 = 2456399112112 :=
  combineSlices (auxiliaryColumnSlice contact29) 16 8 8 1361430295699 1094968816413 contact29ColumnsJoin16_8 contact29ColumnsJoin24_8
private theorem contact29ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact29) 32 16 = 1508025614136 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 8 8 857894670847 650130943289 contact29ColumnsJoin32_8 contact29ColumnsJoin40_8
private theorem contact29ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact29) 48 16 = 794465839805 :=
  combineSlices (auxiliaryColumnSlice contact29) 48 8 8 471753982948 322711856857 contact29ColumnsJoin48_8 contact29ColumnsJoin56_8
private theorem contact29ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact29) 64 16 = 315704114896 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 8 8 203011502513 112692612383 contact29ColumnsJoin64_8 contact29ColumnsJoin72_8
private theorem contact29ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact29) 80 16 = 69074964918 :=
  combineSlices (auxiliaryColumnSlice contact29) 80 8 8 51552402450 17522562468 contact29ColumnsJoin80_8 contact29ColumnsJoin88_8
private theorem contact29ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact29) 0 32 = 6095975559224 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 16 16 3639576447112 2456399112112 contact29ColumnsJoin0_16 contact29ColumnsJoin16_16
private theorem contact29ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact29) 32 32 = 2302491453941 :=
  combineSlices (auxiliaryColumnSlice contact29) 32 16 16 1508025614136 794465839805 contact29ColumnsJoin32_16 contact29ColumnsJoin48_16
private theorem contact29ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact29) 64 32 = 384779079814 :=
  combineSlices (auxiliaryColumnSlice contact29) 64 16 16 315704114896 69074964918 contact29ColumnsJoin64_16 contact29ColumnsJoin80_16
private theorem contact29ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact29) 0 64 = 8398467013165 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 32 32 6095975559224 2302491453941 contact29ColumnsJoin0_32 contact29ColumnsJoin32_32
private theorem contact29ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact29) 0 96 = 8783246092979 :=
  combineSlices (auxiliaryColumnSlice contact29) 0 64 32 8398467013165 384779079814 contact29ColumnsJoin0_64 contact29ColumnsJoin64_32
private theorem contact29OrdinaryRanks : ordinaryRankBound contact29 = 741944400 := by decide +kernel
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
private theorem contact29RanksSlice88 : sliceWindow (auxiliaryRankSlice contact29) 88 8 = 0 :=
  contactRankWindow_of_rec contact29 88 8 0 (by decide +kernel)
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
private theorem contact29RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact29) 80 16 = 16253 :=
  combineSlices (auxiliaryRankSlice contact29) 80 8 8 16253 0 contact29RanksJoin80_8 contact29RanksSlice88
private theorem contact29RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact29) 0 32 = 20866026 :=
  combineSlices (auxiliaryRankSlice contact29) 0 16 16 13119504 7746522 contact29RanksJoin0_16 contact29RanksJoin16_16
private theorem contact29RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact29) 32 32 = 5582892 :=
  combineSlices (auxiliaryRankSlice contact29) 32 16 16 3969686 1613206 contact29RanksJoin32_16 contact29RanksJoin48_16
private theorem contact29RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact29) 64 32 = 410865 :=
  combineSlices (auxiliaryRankSlice contact29) 64 16 16 394612 16253 contact29RanksJoin64_16 contact29RanksJoin80_16
private theorem contact29RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact29) 0 64 = 26448918 :=
  combineSlices (auxiliaryRankSlice contact29) 0 32 32 20866026 5582892 contact29RanksJoin0_32 contact29RanksJoin32_32
private theorem contact29RanksJoin0_96 : sliceWindow (auxiliaryRankSlice contact29) 0 96 = 26859783 :=
  combineSlices (auxiliaryRankSlice contact29) 0 64 32 26448918 410865 contact29RanksJoin0_64 contact29RanksJoin64_32
theorem contact29_margin : sourceMargin contact29 :=
  margin_of_checked_counts contact29 96 192754548293943 8783246092979 741944400 26859783 rfl contact29OrdinaryColumns contact29ColumnsJoin0_96 contact29OrdinaryRanks contact29RanksJoin0_96 (by decide +kernel)

private theorem contact31OrdinaryColumns : ordinaryColumnCount contact31 = 54846259901866 := by decide +kernel
private theorem contact31ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact31) 0 4 = 469403809110 :=
  contactColumnsWindow_fast contact31 0 4 469403809110 (by decide +kernel)
private theorem contact31ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact31) 4 4 = 422366743910 :=
  contactColumnsWindow_fast contact31 4 4 422366743910 (by decide +kernel)
private theorem contact31ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact31) 8 4 = 377825342710 :=
  contactColumnsWindow_fast contact31 8 4 377825342710 (by decide +kernel)
private theorem contact31ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact31) 12 4 = 335789992822 :=
  contactColumnsWindow_fast contact31 12 4 335789992822 (by decide +kernel)
private theorem contact31ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact31) 16 4 = 296262140678 :=
  contactColumnsWindow_fast contact31 16 4 296262140678 (by decide +kernel)
private theorem contact31ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact31) 20 4 = 259231874454 :=
  contactColumnsWindow_fast contact31 20 4 259231874454 (by decide +kernel)
private theorem contact31ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact31) 24 4 = 224698646486 :=
  contactColumnsWindow_fast contact31 24 4 224698646486 (by decide +kernel)
private theorem contact31ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact31) 28 4 = 192663401590 :=
  contactColumnsWindow_fast contact31 28 4 192663401590 (by decide +kernel)
private theorem contact31ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact31) 32 4 = 163137270550 :=
  contactColumnsWindow_fast contact31 32 4 163137270550 (by decide +kernel)
private theorem contact31ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact31) 36 4 = 136116636821 :=
  contactColumnsWindow_fast contact31 36 4 136116636821 (by decide +kernel)
private theorem contact31ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact31) 40 4 = 111593777742 :=
  contactColumnsWindow_fast contact31 40 4 111593777742 (by decide +kernel)
private theorem contact31ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact31) 44 4 = 89567793422 :=
  contactColumnsWindow_fast contact31 44 4 89567793422 (by decide +kernel)
private theorem contact31ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact31) 48 4 = 70040102082 :=
  contactColumnsWindow_fast contact31 48 4 70040102082 (by decide +kernel)
private theorem contact31ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact31) 52 4 = 53023037998 :=
  contactColumnsWindow_fast contact31 52 4 53023037998 (by decide +kernel)
private theorem contact31ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact31) 56 4 = 38509642979 :=
  contactColumnsWindow_fast contact31 56 4 38509642979 (by decide +kernel)
private theorem contact31ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact31) 60 4 = 26494170750 :=
  contactColumnsWindow_fast contact31 60 4 26494170750 (by decide +kernel)
private theorem contact31ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact31) 64 4 = 16974297760 :=
  contactColumnsWindow_fast contact31 64 4 16974297760 (by decide +kernel)
private theorem contact31ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact31) 68 4 = 9908382244 :=
  contactColumnsWindow_fast contact31 68 4 9908382244 (by decide +kernel)
private theorem contact31ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact31) 72 4 = 5121444657 :=
  contactColumnsWindow_fast contact31 72 4 5121444657 (by decide +kernel)
private theorem contact31ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact31) 76 1 = 767278638 :=
  contactColumnsWindow_fast contact31 76 1 767278638 (by decide +kernel)
private theorem contact31ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact31) 0 8 = 891770553020 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 4 4 469403809110 422366743910 contact31ColumnsSlice0 contact31ColumnsSlice4
private theorem contact31ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact31) 8 8 = 713615335532 :=
  combineSlices (auxiliaryColumnSlice contact31) 8 4 4 377825342710 335789992822 contact31ColumnsSlice8 contact31ColumnsSlice12
private theorem contact31ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact31) 16 8 = 555494015132 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 4 4 296262140678 259231874454 contact31ColumnsSlice16 contact31ColumnsSlice20
private theorem contact31ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact31) 24 8 = 417362048076 :=
  combineSlices (auxiliaryColumnSlice contact31) 24 4 4 224698646486 192663401590 contact31ColumnsSlice24 contact31ColumnsSlice28
private theorem contact31ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact31) 32 8 = 299253907371 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 4 4 163137270550 136116636821 contact31ColumnsSlice32 contact31ColumnsSlice36
private theorem contact31ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact31) 40 8 = 201161571164 :=
  combineSlices (auxiliaryColumnSlice contact31) 40 4 4 111593777742 89567793422 contact31ColumnsSlice40 contact31ColumnsSlice44
private theorem contact31ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact31) 48 8 = 123063140080 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 4 4 70040102082 53023037998 contact31ColumnsSlice48 contact31ColumnsSlice52
private theorem contact31ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact31) 56 8 = 65003813729 :=
  combineSlices (auxiliaryColumnSlice contact31) 56 4 4 38509642979 26494170750 contact31ColumnsSlice56 contact31ColumnsSlice60
private theorem contact31ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact31) 64 8 = 26882680004 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 4 4 16974297760 9908382244 contact31ColumnsSlice64 contact31ColumnsSlice68
private theorem contact31ColumnsJoin72_5 : sliceWindow (auxiliaryColumnSlice contact31) 72 5 = 5888723295 :=
  combineSlices (auxiliaryColumnSlice contact31) 72 4 1 5121444657 767278638 contact31ColumnsSlice72 contact31ColumnsSlice76
private theorem contact31ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact31) 0 16 = 1605385888552 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 8 8 891770553020 713615335532 contact31ColumnsJoin0_8 contact31ColumnsJoin8_8
private theorem contact31ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact31) 16 16 = 972856063208 :=
  combineSlices (auxiliaryColumnSlice contact31) 16 8 8 555494015132 417362048076 contact31ColumnsJoin16_8 contact31ColumnsJoin24_8
private theorem contact31ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact31) 32 16 = 500415478535 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 8 8 299253907371 201161571164 contact31ColumnsJoin32_8 contact31ColumnsJoin40_8
private theorem contact31ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact31) 48 16 = 188066953809 :=
  combineSlices (auxiliaryColumnSlice contact31) 48 8 8 123063140080 65003813729 contact31ColumnsJoin48_8 contact31ColumnsJoin56_8
private theorem contact31ColumnsJoin64_13 : sliceWindow (auxiliaryColumnSlice contact31) 64 13 = 32771403299 :=
  combineSlices (auxiliaryColumnSlice contact31) 64 8 5 26882680004 5888723295 contact31ColumnsJoin64_8 contact31ColumnsJoin72_5
private theorem contact31ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact31) 0 32 = 2578241951760 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 16 16 1605385888552 972856063208 contact31ColumnsJoin0_16 contact31ColumnsJoin16_16
private theorem contact31ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact31) 32 32 = 688482432344 :=
  combineSlices (auxiliaryColumnSlice contact31) 32 16 16 500415478535 188066953809 contact31ColumnsJoin32_16 contact31ColumnsJoin48_16
private theorem contact31ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact31) 0 64 = 3266724384104 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 32 32 2578241951760 688482432344 contact31ColumnsJoin0_32 contact31ColumnsJoin32_32
private theorem contact31ColumnsJoin0_77 : sliceWindow (auxiliaryColumnSlice contact31) 0 77 = 3299495787403 :=
  combineSlices (auxiliaryColumnSlice contact31) 0 64 13 3266724384104 32771403299 contact31ColumnsJoin0_64 contact31ColumnsJoin64_13
private theorem contact31OrdinaryRanks : ordinaryRankBound contact31 = 211728678 := by decide +kernel
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
  margin_of_checked_counts contact31 77 54846259901866 3299495787403 211728678 10079727 rfl contact31OrdinaryColumns contact31ColumnsJoin0_77 contact31OrdinaryRanks contact31RanksJoin0_77 (by decide +kernel)

private theorem contact33OrdinaryColumns : ordinaryColumnCount contact33 = 221689377040908 := by decide +kernel
private theorem contact33ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact33) 0 4 = 942339925842 :=
  contactColumnsWindow_fast contact33 0 4 942339925842 (by decide +kernel)
private theorem contact33ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact33) 4 4 = 863129052450 :=
  contactColumnsWindow_fast contact33 4 4 863129052450 (by decide +kernel)
private theorem contact33ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact33) 8 4 = 787412810813 :=
  contactColumnsWindow_fast contact33 8 4 787412810813 (by decide +kernel)
private theorem contact33ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact33) 12 4 = 715209930986 :=
  contactColumnsWindow_fast contact33 12 4 715209930986 (by decide +kernel)
private theorem contact33ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact33) 16 4 = 646509899539 :=
  contactColumnsWindow_fast contact33 16 4 646509899539 (by decide +kernel)
private theorem contact33ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact33) 20 4 = 581306484882 :=
  contactColumnsWindow_fast contact33 20 4 581306484882 (by decide +kernel)
private theorem contact33ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact33) 24 4 = 519598191530 :=
  contactColumnsWindow_fast contact33 24 4 519598191530 (by decide +kernel)
private theorem contact33ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact33) 28 4 = 461388081027 :=
  contactColumnsWindow_fast contact33 28 4 461388081027 (by decide +kernel)
private theorem contact33ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact33) 32 4 = 406693920418 :=
  contactColumnsWindow_fast contact33 32 4 406693920418 (by decide +kernel)
private theorem contact33ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact33) 36 4 = 355503802390 :=
  contactColumnsWindow_fast contact33 36 4 355503802390 (by decide +kernel)
private theorem contact33ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact33) 40 4 = 307810604634 :=
  contactColumnsWindow_fast contact33 40 4 307810604634 (by decide +kernel)
private theorem contact33ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact33) 44 4 = 263612519546 :=
  contactColumnsWindow_fast contact33 44 4 263612519546 (by decide +kernel)
private theorem contact33ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact33) 48 4 = 222913516562 :=
  contactColumnsWindow_fast contact33 48 4 222913516562 (by decide +kernel)
private theorem contact33ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact33) 52 4 = 185731428815 :=
  contactColumnsWindow_fast contact33 52 4 185731428815 (by decide +kernel)
private theorem contact33ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact33) 56 4 = 152051609362 :=
  contactColumnsWindow_fast contact33 56 4 152051609362 (by decide +kernel)
private theorem contact33ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact33) 60 4 = 121868609994 :=
  contactColumnsWindow_fast contact33 60 4 121868609994 (by decide +kernel)
private theorem contact33ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact33) 64 4 = 95180777936 :=
  contactColumnsWindow_fast contact33 64 4 95180777936 (by decide +kernel)
private theorem contact33ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact33) 68 4 = 71993271710 :=
  contactColumnsWindow_fast contact33 68 4 71993271710 (by decide +kernel)
private theorem contact33ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact33) 72 4 = 52322829185 :=
  contactColumnsWindow_fast contact33 72 4 52322829185 (by decide +kernel)
private theorem contact33ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact33) 76 4 = 36152896371 :=
  contactColumnsWindow_fast contact33 76 4 36152896371 (by decide +kernel)
private theorem contact33ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact33) 80 4 = 23448068273 :=
  contactColumnsWindow_fast contact33 80 4 23448068273 (by decide +kernel)
private theorem contact33ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact33) 84 4 = 14038721492 :=
  contactColumnsWindow_fast contact33 84 4 14038721492 (by decide +kernel)
private theorem contact33ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact33) 88 4 = 7592795893 :=
  contactColumnsWindow_fast contact33 88 4 7592795893 (by decide +kernel)
private theorem contact33ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact33) 92 3 = 2974912638 :=
  contactColumnsWindow_fast contact33 92 3 2974912638 (by decide +kernel)
private theorem contact33ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact33) 0 8 = 1805468978292 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 4 4 942339925842 863129052450 contact33ColumnsSlice0 contact33ColumnsSlice4
private theorem contact33ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact33) 8 8 = 1502622741799 :=
  combineSlices (auxiliaryColumnSlice contact33) 8 4 4 787412810813 715209930986 contact33ColumnsSlice8 contact33ColumnsSlice12
private theorem contact33ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact33) 16 8 = 1227816384421 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 4 4 646509899539 581306484882 contact33ColumnsSlice16 contact33ColumnsSlice20
private theorem contact33ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact33) 24 8 = 980986272557 :=
  combineSlices (auxiliaryColumnSlice contact33) 24 4 4 519598191530 461388081027 contact33ColumnsSlice24 contact33ColumnsSlice28
private theorem contact33ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact33) 32 8 = 762197722808 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 4 4 406693920418 355503802390 contact33ColumnsSlice32 contact33ColumnsSlice36
private theorem contact33ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact33) 40 8 = 571423124180 :=
  combineSlices (auxiliaryColumnSlice contact33) 40 4 4 307810604634 263612519546 contact33ColumnsSlice40 contact33ColumnsSlice44
private theorem contact33ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact33) 48 8 = 408644945377 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 4 4 222913516562 185731428815 contact33ColumnsSlice48 contact33ColumnsSlice52
private theorem contact33ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact33) 56 8 = 273920219356 :=
  combineSlices (auxiliaryColumnSlice contact33) 56 4 4 152051609362 121868609994 contact33ColumnsSlice56 contact33ColumnsSlice60
private theorem contact33ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact33) 64 8 = 167174049646 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 4 4 95180777936 71993271710 contact33ColumnsSlice64 contact33ColumnsSlice68
private theorem contact33ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact33) 72 8 = 88475725556 :=
  combineSlices (auxiliaryColumnSlice contact33) 72 4 4 52322829185 36152896371 contact33ColumnsSlice72 contact33ColumnsSlice76
private theorem contact33ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact33) 80 8 = 37486789765 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 4 4 23448068273 14038721492 contact33ColumnsSlice80 contact33ColumnsSlice84
private theorem contact33ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact33) 88 7 = 10567708531 :=
  combineSlices (auxiliaryColumnSlice contact33) 88 4 3 7592795893 2974912638 contact33ColumnsSlice88 contact33ColumnsSlice92
private theorem contact33ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact33) 0 16 = 3308091720091 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 8 8 1805468978292 1502622741799 contact33ColumnsJoin0_8 contact33ColumnsJoin8_8
private theorem contact33ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact33) 16 16 = 2208802656978 :=
  combineSlices (auxiliaryColumnSlice contact33) 16 8 8 1227816384421 980986272557 contact33ColumnsJoin16_8 contact33ColumnsJoin24_8
private theorem contact33ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact33) 32 16 = 1333620846988 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 8 8 762197722808 571423124180 contact33ColumnsJoin32_8 contact33ColumnsJoin40_8
private theorem contact33ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact33) 48 16 = 682565164733 :=
  combineSlices (auxiliaryColumnSlice contact33) 48 8 8 408644945377 273920219356 contact33ColumnsJoin48_8 contact33ColumnsJoin56_8
private theorem contact33ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact33) 64 16 = 255649775202 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 8 8 167174049646 88475725556 contact33ColumnsJoin64_8 contact33ColumnsJoin72_8
private theorem contact33ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact33) 80 15 = 48054498296 :=
  combineSlices (auxiliaryColumnSlice contact33) 80 8 7 37486789765 10567708531 contact33ColumnsJoin80_8 contact33ColumnsJoin88_7
private theorem contact33ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact33) 0 32 = 5516894377069 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 16 16 3308091720091 2208802656978 contact33ColumnsJoin0_16 contact33ColumnsJoin16_16
private theorem contact33ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact33) 32 32 = 2016186011721 :=
  combineSlices (auxiliaryColumnSlice contact33) 32 16 16 1333620846988 682565164733 contact33ColumnsJoin32_16 contact33ColumnsJoin48_16
private theorem contact33ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact33) 64 31 = 303704273498 :=
  combineSlices (auxiliaryColumnSlice contact33) 64 16 15 255649775202 48054498296 contact33ColumnsJoin64_16 contact33ColumnsJoin80_15
private theorem contact33ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact33) 0 64 = 7533080388790 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 32 32 5516894377069 2016186011721 contact33ColumnsJoin0_32 contact33ColumnsJoin32_32
private theorem contact33ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact33) 0 95 = 7836784662288 :=
  combineSlices (auxiliaryColumnSlice contact33) 0 64 31 7533080388790 303704273498 contact33ColumnsJoin0_64 contact33ColumnsJoin64_31
private theorem contact33OrdinaryRanks : ordinaryRankBound contact33 = 851600268 := by decide +kernel
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
  margin_of_checked_counts contact33 95 221689377040908 7836784662288 851600268 23971545 rfl contact33OrdinaryColumns contact33ColumnsJoin0_95 contact33OrdinaryRanks contact33RanksJoin0_95 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

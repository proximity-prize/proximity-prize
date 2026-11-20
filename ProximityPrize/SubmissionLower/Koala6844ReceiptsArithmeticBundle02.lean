import ProximityPrize.SubmissionLower.Koala6844ReceiptsColumnsClosed
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticFast
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle00_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle00_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle00_sliceWindow f a b = x) (hy : arithBundle00_sliceWindow f (a+b) c = y) :
    arithBundle00_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle00_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle00_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle00_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle00_sliceWindow,Nat.zero_add]

private theorem arithBundle00_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle00_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle00_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle00_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle00_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle00_ordinary_columns : ordinaryColumnCount contact00 = 2443789302189367 := by decide +kernel
private theorem arithBundle00_columns_000 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 4 = 6882067743304 :=
  contactColumnsWindow_fast contact00 0 4 6882067743304 (by decide +kernel)
private theorem arithBundle00_columns_004 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 4 4 = 6544130473864 :=
  contactColumnsWindow_fast contact00 4 4 6544130473864 (by decide +kernel)
private theorem arithBundle00_columns_008 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 8 4 = 6214734235340 :=
  contactColumnsWindow_fast contact00 8 4 6214734235340 (by decide +kernel)
private theorem arithBundle00_columns_012 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 12 4 = 5893881882672 :=
  contactColumnsWindow_fast contact00 12 4 5893881882672 (by decide +kernel)
private theorem arithBundle00_columns_016 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 16 4 = 5581571469319 :=
  contactColumnsWindow_fast contact00 16 4 5581571469319 (by decide +kernel)
private theorem arithBundle00_columns_020 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 20 4 = 5277805001580 :=
  contactColumnsWindow_fast contact00 20 4 5277805001580 (by decide +kernel)
private theorem arithBundle00_columns_024 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 24 4 = 4982596174572 :=
  contactColumnsWindow_fast contact00 24 4 4982596174572 (by decide +kernel)
private theorem arithBundle00_columns_028 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 28 4 = 4695964334479 :=
  contactColumnsWindow_fast contact00 28 4 4695964334479 (by decide +kernel)
private theorem arithBundle00_columns_032 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 32 4 = 4417879719288 :=
  contactColumnsWindow_fast contact00 32 4 4417879719288 (by decide +kernel)
private theorem arithBundle00_columns_036 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 36 4 = 4148340217193 :=
  contactColumnsWindow_fast contact00 36 4 4148340217193 (by decide +kernel)
private theorem arithBundle00_columns_040 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 40 4 = 3887347544836 :=
  contactColumnsWindow_fast contact00 40 4 3887347544836 (by decide +kernel)
private theorem arithBundle00_columns_044 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 44 4 = 3634918746913 :=
  contactColumnsWindow_fast contact00 44 4 3634918746913 (by decide +kernel)
private theorem arithBundle00_columns_048 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 48 4 = 3391068296602 :=
  contactColumnsWindow_fast contact00 48 4 3391068296602 (by decide +kernel)
private theorem arithBundle00_columns_052 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 52 4 = 3155766461296 :=
  contactColumnsWindow_fast contact00 52 4 3155766461296 (by decide +kernel)
private theorem arithBundle00_columns_056 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 56 4 = 2929013842837 :=
  contactColumnsWindow_fast contact00 56 4 2929013842837 (by decide +kernel)
private theorem arithBundle00_columns_060 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 60 4 = 2710810253954 :=
  contactColumnsWindow_fast contact00 60 4 2710810253954 (by decide +kernel)
private theorem arithBundle00_columns_064 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 64 4 = 2501179593439 :=
  contactColumnsWindow_fast contact00 64 4 2501179593439 (by decide +kernel)
private theorem arithBundle00_columns_068 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 68 4 = 2300124992290 :=
  contactColumnsWindow_fast contact00 68 4 2300124992290 (by decide +kernel)
private theorem arithBundle00_columns_072 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 72 4 = 2107623880956 :=
  contactColumnsWindow_fast contact00 72 4 2107623880956 (by decide +kernel)
private theorem arithBundle00_columns_076 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 76 4 = 1923672623826 :=
  contactColumnsWindow_fast contact00 76 4 1923672623826 (by decide +kernel)
private theorem arithBundle00_columns_080 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 80 4 = 1748270203694 :=
  contactColumnsWindow_fast contact00 80 4 1748270203694 (by decide +kernel)
private theorem arithBundle00_columns_084 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 84 4 = 1581445287589 :=
  contactColumnsWindow_fast contact00 84 4 1581445287589 (by decide +kernel)
private theorem arithBundle00_columns_088 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 88 4 = 1423192363727 :=
  contactColumnsWindow_fast contact00 88 4 1423192363727 (by decide +kernel)
private theorem arithBundle00_columns_092 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 92 4 = 1273492675788 :=
  contactColumnsWindow_fast contact00 92 4 1273492675788 (by decide +kernel)
private theorem arithBundle00_columns_096 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 96 4 = 1132342735326 :=
  contactColumnsWindow_fast contact00 96 4 1132342735326 (by decide +kernel)
private theorem arithBundle00_columns_100 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 100 4 = 999741900949 :=
  contactColumnsWindow_fast contact00 100 4 999741900949 (by decide +kernel)
private theorem arithBundle00_columns_104 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 104 4 = 875722401310 :=
  contactColumnsWindow_fast contact00 104 4 875722401310 (by decide +kernel)
private theorem arithBundle00_columns_108 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 108 4 = 760271199869 :=
  contactColumnsWindow_fast contact00 108 4 760271199869 (by decide +kernel)
private theorem arithBundle00_columns_112 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 112 4 = 653372765964 :=
  contactColumnsWindow_fast contact00 112 4 653372765964 (by decide +kernel)
private theorem arithBundle00_columns_116 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 116 4 = 555024205012 :=
  contactColumnsWindow_fast contact00 116 4 555024205012 (by decide +kernel)
private theorem arithBundle00_columns_120 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 120 4 = 465225795235 :=
  contactColumnsWindow_fast contact00 120 4 465225795235 (by decide +kernel)
private theorem arithBundle00_columns_124 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 124 4 = 384010816234 :=
  contactColumnsWindow_fast contact00 124 4 384010816234 (by decide +kernel)
private theorem arithBundle00_columns_128 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 128 4 = 311361337180 :=
  contactColumnsWindow_fast contact00 128 4 311361337180 (by decide +kernel)
private theorem arithBundle00_columns_132 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 132 4 = 247264338613 :=
  contactColumnsWindow_fast contact00 132 4 247264338613 (by decide +kernel)
private theorem arithBundle00_columns_136 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 136 4 = 191710107070 :=
  contactColumnsWindow_fast contact00 136 4 191710107070 (by decide +kernel)
private theorem arithBundle00_columns_140 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 140 4 = 144597018199 :=
  contactColumnsWindow_fast contact00 140 4 144597018199 (by decide +kernel)
private theorem arithBundle00_columns_144 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 144 4 = 105655802970 :=
  contactColumnsWindow_fast contact00 144 4 105655802970 (by decide +kernel)
private theorem arithBundle00_columns_148 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 148 4 = 74390738865 :=
  contactColumnsWindow_fast contact00 148 4 74390738865 (by decide +kernel)
private theorem arithBundle00_columns_152 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 152 4 = 50157728120 :=
  contactColumnsWindow_fast contact00 152 4 50157728120 (by decide +kernel)
private theorem arithBundle00_columns_156 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 156 4 = 32160562350 :=
  contactColumnsWindow_fast contact00 156 4 32160562350 (by decide +kernel)
private theorem arithBundle00_columns_160 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 160 4 = 19447648814 :=
  contactColumnsWindow_fast contact00 160 4 19447648814 (by decide +kernel)
private theorem arithBundle00_columns_164 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 164 2 = 6321987952 :=
  contactColumnsWindow_fast contact00 164 2 6321987952 (by decide +kernel)
private theorem arithBundle00_prefix_columns_00 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 8 = 13426198217168 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 4 4 6882067743304 6544130473864 arithBundle00_columns_000 arithBundle00_columns_004
private theorem arithBundle00_prefix_columns_01 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 12 = 19640932452508 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 8 4 13426198217168 6214734235340 arithBundle00_prefix_columns_00 arithBundle00_columns_008
private theorem arithBundle00_prefix_columns_02 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 16 = 25534814335180 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 12 4 19640932452508 5893881882672 arithBundle00_prefix_columns_01 arithBundle00_columns_012
private theorem arithBundle00_prefix_columns_03 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 20 = 31116385804499 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 16 4 25534814335180 5581571469319 arithBundle00_prefix_columns_02 arithBundle00_columns_016
private theorem arithBundle00_prefix_columns_04 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 24 = 36394190806079 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 20 4 31116385804499 5277805001580 arithBundle00_prefix_columns_03 arithBundle00_columns_020
private theorem arithBundle00_prefix_columns_05 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 28 = 41376786980651 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 24 4 36394190806079 4982596174572 arithBundle00_prefix_columns_04 arithBundle00_columns_024
private theorem arithBundle00_prefix_columns_06 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 32 = 46072751315130 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 28 4 41376786980651 4695964334479 arithBundle00_prefix_columns_05 arithBundle00_columns_028
private theorem arithBundle00_prefix_columns_07 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 36 = 50490631034418 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 32 4 46072751315130 4417879719288 arithBundle00_prefix_columns_06 arithBundle00_columns_032
private theorem arithBundle00_prefix_columns_08 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 40 = 54638971251611 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 36 4 50490631034418 4148340217193 arithBundle00_prefix_columns_07 arithBundle00_columns_036
private theorem arithBundle00_prefix_columns_09 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 44 = 58526318796447 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 40 4 54638971251611 3887347544836 arithBundle00_prefix_columns_08 arithBundle00_columns_040
private theorem arithBundle00_prefix_columns_10 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 48 = 62161237543360 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 44 4 58526318796447 3634918746913 arithBundle00_prefix_columns_09 arithBundle00_columns_044
private theorem arithBundle00_prefix_columns_11 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 52 = 65552305839962 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 48 4 62161237543360 3391068296602 arithBundle00_prefix_columns_10 arithBundle00_columns_048
private theorem arithBundle00_prefix_columns_12 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 56 = 68708072301258 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 52 4 65552305839962 3155766461296 arithBundle00_prefix_columns_11 arithBundle00_columns_052
private theorem arithBundle00_prefix_columns_13 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 60 = 71637086144095 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 56 4 68708072301258 2929013842837 arithBundle00_prefix_columns_12 arithBundle00_columns_056
private theorem arithBundle00_prefix_columns_14 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 64 = 74347896398049 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 60 4 71637086144095 2710810253954 arithBundle00_prefix_columns_13 arithBundle00_columns_060
private theorem arithBundle00_prefix_columns_15 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 68 = 76849075991488 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 64 4 74347896398049 2501179593439 arithBundle00_prefix_columns_14 arithBundle00_columns_064
private theorem arithBundle00_prefix_columns_16 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 72 = 79149200983778 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 68 4 76849075991488 2300124992290 arithBundle00_prefix_columns_15 arithBundle00_columns_068
private theorem arithBundle00_prefix_columns_17 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 76 = 81256824864734 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 72 4 79149200983778 2107623880956 arithBundle00_prefix_columns_16 arithBundle00_columns_072
private theorem arithBundle00_prefix_columns_18 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 80 = 83180497488560 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 76 4 81256824864734 1923672623826 arithBundle00_prefix_columns_17 arithBundle00_columns_076
private theorem arithBundle00_prefix_columns_19 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 84 = 84928767692254 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 80 4 83180497488560 1748270203694 arithBundle00_prefix_columns_18 arithBundle00_columns_080
private theorem arithBundle00_prefix_columns_20 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 88 = 86510212979843 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 84 4 84928767692254 1581445287589 arithBundle00_prefix_columns_19 arithBundle00_columns_084
private theorem arithBundle00_prefix_columns_21 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 92 = 87933405343570 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 88 4 86510212979843 1423192363727 arithBundle00_prefix_columns_20 arithBundle00_columns_088
private theorem arithBundle00_prefix_columns_22 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 96 = 89206898019358 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 92 4 87933405343570 1273492675788 arithBundle00_prefix_columns_21 arithBundle00_columns_092
private theorem arithBundle00_prefix_columns_23 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 100 = 90339240754684 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 96 4 89206898019358 1132342735326 arithBundle00_prefix_columns_22 arithBundle00_columns_096
private theorem arithBundle00_prefix_columns_24 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 104 = 91338982655633 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 100 4 90339240754684 999741900949 arithBundle00_prefix_columns_23 arithBundle00_columns_100
private theorem arithBundle00_prefix_columns_25 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 108 = 92214705056943 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 104 4 91338982655633 875722401310 arithBundle00_prefix_columns_24 arithBundle00_columns_104
private theorem arithBundle00_prefix_columns_26 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 112 = 92974976256812 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 108 4 92214705056943 760271199869 arithBundle00_prefix_columns_25 arithBundle00_columns_108
private theorem arithBundle00_prefix_columns_27 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 116 = 93628349022776 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 112 4 92974976256812 653372765964 arithBundle00_prefix_columns_26 arithBundle00_columns_112
private theorem arithBundle00_prefix_columns_28 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 120 = 94183373227788 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 116 4 93628349022776 555024205012 arithBundle00_prefix_columns_27 arithBundle00_columns_116
private theorem arithBundle00_prefix_columns_29 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 124 = 94648599023023 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 120 4 94183373227788 465225795235 arithBundle00_prefix_columns_28 arithBundle00_columns_120
private theorem arithBundle00_prefix_columns_30 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 128 = 95032609839257 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 124 4 94648599023023 384010816234 arithBundle00_prefix_columns_29 arithBundle00_columns_124
private theorem arithBundle00_prefix_columns_31 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 132 = 95343971176437 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 128 4 95032609839257 311361337180 arithBundle00_prefix_columns_30 arithBundle00_columns_128
private theorem arithBundle00_prefix_columns_32 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 136 = 95591235515050 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 132 4 95343971176437 247264338613 arithBundle00_prefix_columns_31 arithBundle00_columns_132
private theorem arithBundle00_prefix_columns_33 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 140 = 95782945622120 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 136 4 95591235515050 191710107070 arithBundle00_prefix_columns_32 arithBundle00_columns_136
private theorem arithBundle00_prefix_columns_34 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 144 = 95927542640319 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 140 4 95782945622120 144597018199 arithBundle00_prefix_columns_33 arithBundle00_columns_140
private theorem arithBundle00_prefix_columns_35 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 148 = 96033198443289 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 144 4 95927542640319 105655802970 arithBundle00_prefix_columns_34 arithBundle00_columns_144
private theorem arithBundle00_prefix_columns_36 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 152 = 96107589182154 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 148 4 96033198443289 74390738865 arithBundle00_prefix_columns_35 arithBundle00_columns_148
private theorem arithBundle00_prefix_columns_37 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 156 = 96157746910274 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 152 4 96107589182154 50157728120 arithBundle00_prefix_columns_36 arithBundle00_columns_152
private theorem arithBundle00_prefix_columns_38 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 160 = 96189907472624 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 156 4 96157746910274 32160562350 arithBundle00_prefix_columns_37 arithBundle00_columns_156
private theorem arithBundle00_prefix_columns_39 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 164 = 96209355121438 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 160 4 96189907472624 19447648814 arithBundle00_prefix_columns_38 arithBundle00_columns_160
private theorem arithBundle00_prefix_columns_40 : arithBundle00_sliceWindow (auxiliaryColumnSlice contact00) 0 166 = 96215677109390 :=
  arithBundle00_combineSlices (auxiliaryColumnSlice contact00) 0 164 2 96209355121438 6321987952 arithBundle00_prefix_columns_39 arithBundle00_columns_164

private theorem arithBundle00_ordinary_ranks : ordinaryRankBound contact00 = 9398055887 := by decide +kernel
private theorem arithBundle00_ranks_000 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 4 = 25947700 :=
  contactRankWindow_of_rec contact00 0 4 25947700 (by decide +kernel)
private theorem arithBundle00_ranks_004 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 4 4 = 24284500 :=
  contactRankWindow_of_rec contact00 4 4 24284500 (by decide +kernel)
private theorem arithBundle00_ranks_008 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 8 4 = 22680436 :=
  contactRankWindow_of_rec contact00 8 4 22680436 (by decide +kernel)
private theorem arithBundle00_ranks_012 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 12 4 = 21135508 :=
  contactRankWindow_of_rec contact00 12 4 21135508 (by decide +kernel)
private theorem arithBundle00_ranks_016 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 16 4 = 19649716 :=
  contactRankWindow_of_rec contact00 16 4 19649716 (by decide +kernel)
private theorem arithBundle00_ranks_020 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 20 4 = 18223060 :=
  contactRankWindow_of_rec contact00 20 4 18223060 (by decide +kernel)
private theorem arithBundle00_ranks_024 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 24 4 = 16855540 :=
  contactRankWindow_of_rec contact00 24 4 16855540 (by decide +kernel)
private theorem arithBundle00_ranks_028 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 28 4 = 15547156 :=
  contactRankWindow_of_rec contact00 28 4 15547156 (by decide +kernel)
private theorem arithBundle00_ranks_032 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 32 4 = 14297908 :=
  contactRankWindow_of_rec contact00 32 4 14297908 (by decide +kernel)
private theorem arithBundle00_ranks_036 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 36 4 = 13107796 :=
  contactRankWindow_of_rec contact00 36 4 13107796 (by decide +kernel)
private theorem arithBundle00_ranks_040 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 40 4 = 11976820 :=
  contactRankWindow_of_rec contact00 40 4 11976820 (by decide +kernel)
private theorem arithBundle00_ranks_044 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 44 4 = 10904980 :=
  contactRankWindow_of_rec contact00 44 4 10904980 (by decide +kernel)
private theorem arithBundle00_ranks_048 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 48 4 = 9892276 :=
  contactRankWindow_of_rec contact00 48 4 9892276 (by decide +kernel)
private theorem arithBundle00_ranks_052 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 52 4 = 8938708 :=
  contactRankWindow_of_rec contact00 52 4 8938708 (by decide +kernel)
private theorem arithBundle00_ranks_056 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 56 4 = 8043882 :=
  contactRankWindow_of_rec contact00 56 4 8043882 (by decide +kernel)
private theorem arithBundle00_ranks_060 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 60 4 = 7206684 :=
  contactRankWindow_of_rec contact00 60 4 7206684 (by decide +kernel)
private theorem arithBundle00_ranks_064 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 64 4 = 6425827 :=
  contactRankWindow_of_rec contact00 64 4 6425827 (by decide +kernel)
private theorem arithBundle00_ranks_068 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 68 4 = 5699744 :=
  contactRankWindow_of_rec contact00 68 4 5699744 (by decide +kernel)
private theorem arithBundle00_ranks_072 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 72 4 = 5026688 :=
  contactRankWindow_of_rec contact00 72 4 5026688 (by decide +kernel)
private theorem arithBundle00_ranks_076 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 76 4 = 4404859 :=
  contactRankWindow_of_rec contact00 76 4 4404859 (by decide +kernel)
private theorem arithBundle00_ranks_080 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 80 4 = 3832688 :=
  contactRankWindow_of_rec contact00 80 4 3832688 (by decide +kernel)
private theorem arithBundle00_ranks_084 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 84 4 = 3308292 :=
  contactRankWindow_of_rec contact00 84 4 3308292 (by decide +kernel)
private theorem arithBundle00_ranks_088 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 88 4 = 2829875 :=
  contactRankWindow_of_rec contact00 88 4 2829875 (by decide +kernel)
private theorem arithBundle00_ranks_092 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 92 4 = 2396000 :=
  contactRankWindow_of_rec contact00 92 4 2396000 (by decide +kernel)
private theorem arithBundle00_ranks_096 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 96 4 = 2004648 :=
  contactRankWindow_of_rec contact00 96 4 2004648 (by decide +kernel)
private theorem arithBundle00_ranks_100 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 100 4 = 1654027 :=
  contactRankWindow_of_rec contact00 100 4 1654027 (by decide +kernel)
private theorem arithBundle00_ranks_104 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 104 4 = 1342832 :=
  contactRankWindow_of_rec contact00 104 4 1342832 (by decide +kernel)
private theorem arithBundle00_ranks_108 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 108 4 = 1068908 :=
  contactRankWindow_of_rec contact00 108 4 1068908 (by decide +kernel)
private theorem arithBundle00_ranks_112 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 112 4 = 830467 :=
  contactRankWindow_of_rec contact00 112 4 830467 (by decide +kernel)
private theorem arithBundle00_ranks_116 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 116 4 = 626336 :=
  contactRankWindow_of_rec contact00 116 4 626336 (by decide +kernel)
private theorem arithBundle00_ranks_120 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 120 4 = 454224 :=
  contactRankWindow_of_rec contact00 120 4 454224 (by decide +kernel)
private theorem arithBundle00_ranks_124 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 124 4 = 312347 :=
  contactRankWindow_of_rec contact00 124 4 312347 (by decide +kernel)
private theorem arithBundle00_ranks_128 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 128 4 = 199664 :=
  contactRankWindow_of_rec contact00 128 4 199664 (by decide +kernel)
private theorem arithBundle00_ranks_132 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 132 4 = 113748 :=
  contactRankWindow_of_rec contact00 132 4 113748 (by decide +kernel)
private theorem arithBundle00_ranks_136 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 136 4 = 52819 :=
  contactRankWindow_of_rec contact00 136 4 52819 (by decide +kernel)
private theorem arithBundle00_ranks_140 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 140 4 = 16030 :=
  contactRankWindow_of_rec contact00 140 4 16030 (by decide +kernel)
private theorem arithBundle00_ranks_144 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 144 4 = 903 :=
  contactRankWindow_of_rec contact00 144 4 903 (by decide +kernel)
private theorem arithBundle00_ranks_148 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 148 18 = 0 :=
  contactRankWindow_of_rec contact00 148 18 0 (by decide +kernel)
private theorem arithBundle00_prefix_ranks_00 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 8 = 50232200 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 4 4 25947700 24284500 arithBundle00_ranks_000 arithBundle00_ranks_004
private theorem arithBundle00_prefix_ranks_01 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 12 = 72912636 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 8 4 50232200 22680436 arithBundle00_prefix_ranks_00 arithBundle00_ranks_008
private theorem arithBundle00_prefix_ranks_02 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 16 = 94048144 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 12 4 72912636 21135508 arithBundle00_prefix_ranks_01 arithBundle00_ranks_012
private theorem arithBundle00_prefix_ranks_03 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 20 = 113697860 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 16 4 94048144 19649716 arithBundle00_prefix_ranks_02 arithBundle00_ranks_016
private theorem arithBundle00_prefix_ranks_04 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 24 = 131920920 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 20 4 113697860 18223060 arithBundle00_prefix_ranks_03 arithBundle00_ranks_020
private theorem arithBundle00_prefix_ranks_05 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 28 = 148776460 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 24 4 131920920 16855540 arithBundle00_prefix_ranks_04 arithBundle00_ranks_024
private theorem arithBundle00_prefix_ranks_06 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 32 = 164323616 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 28 4 148776460 15547156 arithBundle00_prefix_ranks_05 arithBundle00_ranks_028
private theorem arithBundle00_prefix_ranks_07 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 36 = 178621524 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 32 4 164323616 14297908 arithBundle00_prefix_ranks_06 arithBundle00_ranks_032
private theorem arithBundle00_prefix_ranks_08 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 40 = 191729320 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 36 4 178621524 13107796 arithBundle00_prefix_ranks_07 arithBundle00_ranks_036
private theorem arithBundle00_prefix_ranks_09 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 44 = 203706140 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 40 4 191729320 11976820 arithBundle00_prefix_ranks_08 arithBundle00_ranks_040
private theorem arithBundle00_prefix_ranks_10 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 48 = 214611120 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 44 4 203706140 10904980 arithBundle00_prefix_ranks_09 arithBundle00_ranks_044
private theorem arithBundle00_prefix_ranks_11 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 52 = 224503396 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 48 4 214611120 9892276 arithBundle00_prefix_ranks_10 arithBundle00_ranks_048
private theorem arithBundle00_prefix_ranks_12 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 56 = 233442104 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 52 4 224503396 8938708 arithBundle00_prefix_ranks_11 arithBundle00_ranks_052
private theorem arithBundle00_prefix_ranks_13 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 60 = 241485986 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 56 4 233442104 8043882 arithBundle00_prefix_ranks_12 arithBundle00_ranks_056
private theorem arithBundle00_prefix_ranks_14 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 64 = 248692670 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 60 4 241485986 7206684 arithBundle00_prefix_ranks_13 arithBundle00_ranks_060
private theorem arithBundle00_prefix_ranks_15 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 68 = 255118497 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 64 4 248692670 6425827 arithBundle00_prefix_ranks_14 arithBundle00_ranks_064
private theorem arithBundle00_prefix_ranks_16 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 72 = 260818241 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 68 4 255118497 5699744 arithBundle00_prefix_ranks_15 arithBundle00_ranks_068
private theorem arithBundle00_prefix_ranks_17 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 76 = 265844929 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 72 4 260818241 5026688 arithBundle00_prefix_ranks_16 arithBundle00_ranks_072
private theorem arithBundle00_prefix_ranks_18 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 80 = 270249788 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 76 4 265844929 4404859 arithBundle00_prefix_ranks_17 arithBundle00_ranks_076
private theorem arithBundle00_prefix_ranks_19 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 84 = 274082476 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 80 4 270249788 3832688 arithBundle00_prefix_ranks_18 arithBundle00_ranks_080
private theorem arithBundle00_prefix_ranks_20 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 88 = 277390768 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 84 4 274082476 3308292 arithBundle00_prefix_ranks_19 arithBundle00_ranks_084
private theorem arithBundle00_prefix_ranks_21 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 92 = 280220643 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 88 4 277390768 2829875 arithBundle00_prefix_ranks_20 arithBundle00_ranks_088
private theorem arithBundle00_prefix_ranks_22 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 96 = 282616643 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 92 4 280220643 2396000 arithBundle00_prefix_ranks_21 arithBundle00_ranks_092
private theorem arithBundle00_prefix_ranks_23 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 100 = 284621291 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 96 4 282616643 2004648 arithBundle00_prefix_ranks_22 arithBundle00_ranks_096
private theorem arithBundle00_prefix_ranks_24 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 104 = 286275318 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 100 4 284621291 1654027 arithBundle00_prefix_ranks_23 arithBundle00_ranks_100
private theorem arithBundle00_prefix_ranks_25 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 108 = 287618150 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 104 4 286275318 1342832 arithBundle00_prefix_ranks_24 arithBundle00_ranks_104
private theorem arithBundle00_prefix_ranks_26 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 112 = 288687058 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 108 4 287618150 1068908 arithBundle00_prefix_ranks_25 arithBundle00_ranks_108
private theorem arithBundle00_prefix_ranks_27 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 116 = 289517525 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 112 4 288687058 830467 arithBundle00_prefix_ranks_26 arithBundle00_ranks_112
private theorem arithBundle00_prefix_ranks_28 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 120 = 290143861 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 116 4 289517525 626336 arithBundle00_prefix_ranks_27 arithBundle00_ranks_116
private theorem arithBundle00_prefix_ranks_29 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 124 = 290598085 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 120 4 290143861 454224 arithBundle00_prefix_ranks_28 arithBundle00_ranks_120
private theorem arithBundle00_prefix_ranks_30 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 128 = 290910432 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 124 4 290598085 312347 arithBundle00_prefix_ranks_29 arithBundle00_ranks_124
private theorem arithBundle00_prefix_ranks_31 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 132 = 291110096 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 128 4 290910432 199664 arithBundle00_prefix_ranks_30 arithBundle00_ranks_128
private theorem arithBundle00_prefix_ranks_32 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 136 = 291223844 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 132 4 291110096 113748 arithBundle00_prefix_ranks_31 arithBundle00_ranks_132
private theorem arithBundle00_prefix_ranks_33 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 140 = 291276663 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 136 4 291223844 52819 arithBundle00_prefix_ranks_32 arithBundle00_ranks_136
private theorem arithBundle00_prefix_ranks_34 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 144 = 291292693 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 140 4 291276663 16030 arithBundle00_prefix_ranks_33 arithBundle00_ranks_140
private theorem arithBundle00_prefix_ranks_35 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 148 = 291293596 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 144 4 291292693 903 arithBundle00_prefix_ranks_34 arithBundle00_ranks_144
private theorem arithBundle00_prefix_ranks_36 : arithBundle00_sliceWindow (auxiliaryRankSlice contact00) 0 166 = 291293596 :=
  arithBundle00_combineSlices (auxiliaryRankSlice contact00) 0 148 18 291293596 0 arithBundle00_prefix_ranks_35 arithBundle00_ranks_148

theorem contact00_margin : sourceMargin contact00 :=
  arithBundle00_margin_of_checked_counts contact00 166 2443789302189367 96215677109390 9398055887 291293596
    rfl arithBundle00_ordinary_columns arithBundle00_prefix_columns_40 arithBundle00_ordinary_ranks arithBundle00_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle01_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle01_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle01_sliceWindow f a b = x) (hy : arithBundle01_sliceWindow f (a+b) c = y) :
    arithBundle01_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle01_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle01_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle01_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle01_sliceWindow,Nat.zero_add]

private theorem arithBundle01_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle01_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle01_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle01_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle01_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle01_ordinary_columns : ordinaryColumnCount contact02 = 3567503565385676 := by decide +kernel
private theorem arithBundle01_columns_000 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 4 = 11546074333662 :=
  contactColumnsWindow_fast contact02 0 4 11546074333662 (by decide +kernel)
private theorem arithBundle01_columns_004 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 4 4 = 11029310050494 :=
  contactColumnsWindow_fast contact02 4 4 11029310050494 (by decide +kernel)
private theorem arithBundle01_columns_008 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 8 4 = 10524441271518 :=
  contactColumnsWindow_fast contact02 8 4 10524441271518 (by decide +kernel)
private theorem arithBundle01_columns_012 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 12 4 = 10031467996734 :=
  contactColumnsWindow_fast contact02 12 4 10031467996734 (by decide +kernel)
private theorem arithBundle01_columns_016 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 16 4 = 9550390226142 :=
  contactColumnsWindow_fast contact02 16 4 9550390226142 (by decide +kernel)
private theorem arithBundle01_columns_020 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 20 4 = 9081207959742 :=
  contactColumnsWindow_fast contact02 20 4 9081207959742 (by decide +kernel)
private theorem arithBundle01_columns_024 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 24 4 = 8623921197534 :=
  contactColumnsWindow_fast contact02 24 4 8623921197534 (by decide +kernel)
private theorem arithBundle01_columns_028 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 28 4 = 8178529939518 :=
  contactColumnsWindow_fast contact02 28 4 8178529939518 (by decide +kernel)
private theorem arithBundle01_columns_032 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 32 4 = 7745034185694 :=
  contactColumnsWindow_fast contact02 32 4 7745034185694 (by decide +kernel)
private theorem arithBundle01_columns_036 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 36 4 = 7323433936062 :=
  contactColumnsWindow_fast contact02 36 4 7323433936062 (by decide +kernel)
private theorem arithBundle01_columns_040 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 40 4 = 6913729190622 :=
  contactColumnsWindow_fast contact02 40 4 6913729190622 (by decide +kernel)
private theorem arithBundle01_columns_044 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 44 4 = 6515919949374 :=
  contactColumnsWindow_fast contact02 44 4 6515919949374 (by decide +kernel)
private theorem arithBundle01_columns_048 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 48 4 = 6130006212318 :=
  contactColumnsWindow_fast contact02 48 4 6130006212318 (by decide +kernel)
private theorem arithBundle01_columns_052 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 52 4 = 5755987979454 :=
  contactColumnsWindow_fast contact02 52 4 5755987979454 (by decide +kernel)
private theorem arithBundle01_columns_056 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 56 4 = 5393872059896 :=
  contactColumnsWindow_fast contact02 56 4 5393872059896 (by decide +kernel)
private theorem arithBundle01_columns_060 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 60 4 = 5043718277746 :=
  contactColumnsWindow_fast contact02 60 4 5043718277746 (by decide +kernel)
private theorem arithBundle01_columns_064 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 64 4 = 4705476298782 :=
  contactColumnsWindow_fast contact02 64 4 4705476298782 (by decide +kernel)
private theorem arithBundle01_columns_068 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 68 4 = 4379134549202 :=
  contactColumnsWindow_fast contact02 68 4 4379134549202 (by decide +kernel)
private theorem arithBundle01_columns_072 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 72 4 = 4064690403020 :=
  contactColumnsWindow_fast contact02 72 4 4064690403020 (by decide +kernel)
private theorem arithBundle01_columns_076 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 76 4 = 3762157330864 :=
  contactColumnsWindow_fast contact02 76 4 3762157330864 (by decide +kernel)
private theorem arithBundle01_columns_080 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 80 4 = 3471588866081 :=
  contactColumnsWindow_fast contact02 80 4 3471588866081 (by decide +kernel)
private theorem arithBundle01_columns_084 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 84 4 = 3192932947431 :=
  contactColumnsWindow_fast contact02 84 4 3192932947431 (by decide +kernel)
private theorem arithBundle01_columns_088 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 88 4 = 2926180360458 :=
  contactColumnsWindow_fast contact02 88 4 2926180360458 (by decide +kernel)
private theorem arithBundle01_columns_092 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 92 4 = 2671329502803 :=
  contactColumnsWindow_fast contact02 92 4 2671329502803 (by decide +kernel)
private theorem arithBundle01_columns_096 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 96 4 = 2428397435628 :=
  contactColumnsWindow_fast contact02 96 4 2428397435628 (by decide +kernel)
private theorem arithBundle01_columns_100 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 100 4 = 2197433578206 :=
  contactColumnsWindow_fast contact02 100 4 2197433578206 (by decide +kernel)
private theorem arithBundle01_columns_104 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 104 4 = 1978383185721 :=
  contactColumnsWindow_fast contact02 104 4 1978383185721 (by decide +kernel)
private theorem arithBundle01_columns_108 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 108 4 = 1771239110637 :=
  contactColumnsWindow_fast contact02 108 4 1771239110637 (by decide +kernel)
private theorem arithBundle01_columns_112 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 112 4 = 1576001964662 :=
  contactColumnsWindow_fast contact02 112 4 1576001964662 (by decide +kernel)
private theorem arithBundle01_columns_116 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 116 4 = 1392690694909 :=
  contactColumnsWindow_fast contact02 116 4 1392690694909 (by decide +kernel)
private theorem arithBundle01_columns_120 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 120 4 = 1221345483051 :=
  contactColumnsWindow_fast contact02 120 4 1221345483051 (by decide +kernel)
private theorem arithBundle01_columns_124 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 124 4 = 1061910967590 :=
  contactColumnsWindow_fast contact02 124 4 1061910967590 (by decide +kernel)
private theorem arithBundle01_columns_128 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 128 4 = 914382853848 :=
  contactColumnsWindow_fast contact02 128 4 914382853848 (by decide +kernel)
private theorem arithBundle01_columns_132 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 132 4 = 778761805689 :=
  contactColumnsWindow_fast contact02 132 4 778761805689 (by decide +kernel)
private theorem arithBundle01_columns_136 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 136 4 = 655072031581 :=
  contactColumnsWindow_fast contact02 136 4 655072031581 (by decide +kernel)
private theorem arithBundle01_columns_140 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 140 4 = 543344549268 :=
  contactColumnsWindow_fast contact02 140 4 543344549268 (by decide +kernel)
private theorem arithBundle01_columns_144 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 144 4 = 443525924068 :=
  contactColumnsWindow_fast contact02 144 4 443525924068 (by decide +kernel)
private theorem arithBundle01_columns_148 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 148 4 = 355589229567 :=
  contactColumnsWindow_fast contact02 148 4 355589229567 (by decide +kernel)
private theorem arithBundle01_columns_152 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 152 4 = 279362481673 :=
  contactColumnsWindow_fast contact02 152 4 279362481673 (by decide +kernel)
private theorem arithBundle01_columns_156 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 156 4 = 214500141519 :=
  contactColumnsWindow_fast contact02 156 4 214500141519 (by decide +kernel)
private theorem arithBundle01_columns_160 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 160 4 = 160477821339 :=
  contactColumnsWindow_fast contact02 160 4 160477821339 (by decide +kernel)
private theorem arithBundle01_columns_164 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 164 4 = 116537533293 :=
  contactColumnsWindow_fast contact02 164 4 116537533293 (by decide +kernel)
private theorem arithBundle01_columns_168 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 168 4 = 81810083260 :=
  contactColumnsWindow_fast contact02 168 4 81810083260 (by decide +kernel)
private theorem arithBundle01_columns_172 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 172 4 = 55266639048 :=
  contactColumnsWindow_fast contact02 172 4 55266639048 (by decide +kernel)
private theorem arithBundle01_columns_176 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 176 3 = 28298594604 :=
  contactColumnsWindow_fast contact02 176 3 28298594604 (by decide +kernel)
private theorem arithBundle01_prefix_columns_00 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 8 = 22575384384156 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 4 4 11546074333662 11029310050494 arithBundle01_columns_000 arithBundle01_columns_004
private theorem arithBundle01_prefix_columns_01 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 12 = 33099825655674 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 8 4 22575384384156 10524441271518 arithBundle01_prefix_columns_00 arithBundle01_columns_008
private theorem arithBundle01_prefix_columns_02 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 16 = 43131293652408 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 12 4 33099825655674 10031467996734 arithBundle01_prefix_columns_01 arithBundle01_columns_012
private theorem arithBundle01_prefix_columns_03 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 20 = 52681683878550 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 16 4 43131293652408 9550390226142 arithBundle01_prefix_columns_02 arithBundle01_columns_016
private theorem arithBundle01_prefix_columns_04 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 24 = 61762891838292 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 20 4 52681683878550 9081207959742 arithBundle01_prefix_columns_03 arithBundle01_columns_020
private theorem arithBundle01_prefix_columns_05 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 28 = 70386813035826 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 24 4 61762891838292 8623921197534 arithBundle01_prefix_columns_04 arithBundle01_columns_024
private theorem arithBundle01_prefix_columns_06 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 32 = 78565342975344 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 28 4 70386813035826 8178529939518 arithBundle01_prefix_columns_05 arithBundle01_columns_028
private theorem arithBundle01_prefix_columns_07 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 36 = 86310377161038 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 32 4 78565342975344 7745034185694 arithBundle01_prefix_columns_06 arithBundle01_columns_032
private theorem arithBundle01_prefix_columns_08 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 40 = 93633811097100 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 36 4 86310377161038 7323433936062 arithBundle01_prefix_columns_07 arithBundle01_columns_036
private theorem arithBundle01_prefix_columns_09 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 44 = 100547540287722 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 40 4 93633811097100 6913729190622 arithBundle01_prefix_columns_08 arithBundle01_columns_040
private theorem arithBundle01_prefix_columns_10 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 48 = 107063460237096 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 44 4 100547540287722 6515919949374 arithBundle01_prefix_columns_09 arithBundle01_columns_044
private theorem arithBundle01_prefix_columns_11 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 52 = 113193466449414 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 48 4 107063460237096 6130006212318 arithBundle01_prefix_columns_10 arithBundle01_columns_048
private theorem arithBundle01_prefix_columns_12 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 56 = 118949454428868 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 52 4 113193466449414 5755987979454 arithBundle01_prefix_columns_11 arithBundle01_columns_052
private theorem arithBundle01_prefix_columns_13 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 60 = 124343326488764 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 56 4 118949454428868 5393872059896 arithBundle01_prefix_columns_12 arithBundle01_columns_056
private theorem arithBundle01_prefix_columns_14 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 64 = 129387044766510 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 60 4 124343326488764 5043718277746 arithBundle01_prefix_columns_13 arithBundle01_columns_060
private theorem arithBundle01_prefix_columns_15 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 68 = 134092521065292 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 64 4 129387044766510 4705476298782 arithBundle01_prefix_columns_14 arithBundle01_columns_064
private theorem arithBundle01_prefix_columns_16 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 72 = 138471655614494 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 68 4 134092521065292 4379134549202 arithBundle01_prefix_columns_15 arithBundle01_columns_068
private theorem arithBundle01_prefix_columns_17 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 76 = 142536346017514 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 72 4 138471655614494 4064690403020 arithBundle01_prefix_columns_16 arithBundle01_columns_072
private theorem arithBundle01_prefix_columns_18 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 80 = 146298503348378 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 76 4 142536346017514 3762157330864 arithBundle01_prefix_columns_17 arithBundle01_columns_076
private theorem arithBundle01_prefix_columns_19 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 84 = 149770092214459 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 80 4 146298503348378 3471588866081 arithBundle01_prefix_columns_18 arithBundle01_columns_080
private theorem arithBundle01_prefix_columns_20 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 88 = 152963025161890 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 84 4 149770092214459 3192932947431 arithBundle01_prefix_columns_19 arithBundle01_columns_084
private theorem arithBundle01_prefix_columns_21 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 92 = 155889205522348 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 88 4 152963025161890 2926180360458 arithBundle01_prefix_columns_20 arithBundle01_columns_088
private theorem arithBundle01_prefix_columns_22 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 96 = 158560535025151 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 92 4 155889205522348 2671329502803 arithBundle01_prefix_columns_21 arithBundle01_columns_092
private theorem arithBundle01_prefix_columns_23 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 100 = 160988932460779 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 96 4 158560535025151 2428397435628 arithBundle01_prefix_columns_22 arithBundle01_columns_096
private theorem arithBundle01_prefix_columns_24 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 104 = 163186366038985 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 100 4 160988932460779 2197433578206 arithBundle01_prefix_columns_23 arithBundle01_columns_100
private theorem arithBundle01_prefix_columns_25 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 108 = 165164749224706 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 104 4 163186366038985 1978383185721 arithBundle01_prefix_columns_24 arithBundle01_columns_104
private theorem arithBundle01_prefix_columns_26 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 112 = 166935988335343 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 108 4 165164749224706 1771239110637 arithBundle01_prefix_columns_25 arithBundle01_columns_108
private theorem arithBundle01_prefix_columns_27 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 116 = 168511990300005 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 112 4 166935988335343 1576001964662 arithBundle01_prefix_columns_26 arithBundle01_columns_112
private theorem arithBundle01_prefix_columns_28 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 120 = 169904680994914 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 116 4 168511990300005 1392690694909 arithBundle01_prefix_columns_27 arithBundle01_columns_116
private theorem arithBundle01_prefix_columns_29 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 124 = 171126026477965 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 120 4 169904680994914 1221345483051 arithBundle01_prefix_columns_28 arithBundle01_columns_120
private theorem arithBundle01_prefix_columns_30 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 128 = 172187937445555 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 124 4 171126026477965 1061910967590 arithBundle01_prefix_columns_29 arithBundle01_columns_124
private theorem arithBundle01_prefix_columns_31 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 132 = 173102320299403 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 128 4 172187937445555 914382853848 arithBundle01_prefix_columns_30 arithBundle01_columns_128
private theorem arithBundle01_prefix_columns_32 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 136 = 173881082105092 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 132 4 173102320299403 778761805689 arithBundle01_prefix_columns_31 arithBundle01_columns_132
private theorem arithBundle01_prefix_columns_33 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 140 = 174536154136673 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 136 4 173881082105092 655072031581 arithBundle01_prefix_columns_32 arithBundle01_columns_136
private theorem arithBundle01_prefix_columns_34 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 144 = 175079498685941 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 140 4 174536154136673 543344549268 arithBundle01_prefix_columns_33 arithBundle01_columns_140
private theorem arithBundle01_prefix_columns_35 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 148 = 175523024610009 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 144 4 175079498685941 443525924068 arithBundle01_prefix_columns_34 arithBundle01_columns_144
private theorem arithBundle01_prefix_columns_36 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 152 = 175878613839576 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 148 4 175523024610009 355589229567 arithBundle01_prefix_columns_35 arithBundle01_columns_148
private theorem arithBundle01_prefix_columns_37 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 156 = 176157976321249 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 152 4 175878613839576 279362481673 arithBundle01_prefix_columns_36 arithBundle01_columns_152
private theorem arithBundle01_prefix_columns_38 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 160 = 176372476462768 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 156 4 176157976321249 214500141519 arithBundle01_prefix_columns_37 arithBundle01_columns_156
private theorem arithBundle01_prefix_columns_39 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 164 = 176532954284107 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 160 4 176372476462768 160477821339 arithBundle01_prefix_columns_38 arithBundle01_columns_160
private theorem arithBundle01_prefix_columns_40 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 168 = 176649491817400 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 164 4 176532954284107 116537533293 arithBundle01_prefix_columns_39 arithBundle01_columns_164
private theorem arithBundle01_prefix_columns_41 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 172 = 176731301900660 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 168 4 176649491817400 81810083260 arithBundle01_prefix_columns_40 arithBundle01_columns_168
private theorem arithBundle01_prefix_columns_42 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 176 = 176786568539708 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 172 4 176731301900660 55266639048 arithBundle01_prefix_columns_41 arithBundle01_columns_172
private theorem arithBundle01_prefix_columns_43 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact02) 0 179 = 176814867134312 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact02) 0 176 3 176786568539708 28298594604 arithBundle01_prefix_columns_42 arithBundle01_columns_176

private theorem arithBundle01_ordinary_ranks : ordinaryRankBound contact02 = 13743409701 := by decide +kernel
private theorem arithBundle01_ranks_000 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 4 = 43553844 :=
  contactRankWindow_of_rec contact02 0 4 43553844 (by decide +kernel)
private theorem arithBundle01_ranks_004 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 4 4 = 41021028 :=
  contactRankWindow_of_rec contact02 4 4 41021028 (by decide +kernel)
private theorem arithBundle01_ranks_008 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 8 4 = 38570580 :=
  contactRankWindow_of_rec contact02 8 4 38570580 (by decide +kernel)
private theorem arithBundle01_ranks_012 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 12 4 = 36202500 :=
  contactRankWindow_of_rec contact02 12 4 36202500 (by decide +kernel)
private theorem arithBundle01_ranks_016 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 16 4 = 33916788 :=
  contactRankWindow_of_rec contact02 16 4 33916788 (by decide +kernel)
private theorem arithBundle01_ranks_020 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 20 4 = 31713444 :=
  contactRankWindow_of_rec contact02 20 4 31713444 (by decide +kernel)
private theorem arithBundle01_ranks_024 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 24 4 = 29592468 :=
  contactRankWindow_of_rec contact02 24 4 29592468 (by decide +kernel)
private theorem arithBundle01_ranks_028 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 28 4 = 27553860 :=
  contactRankWindow_of_rec contact02 28 4 27553860 (by decide +kernel)
private theorem arithBundle01_ranks_032 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 32 4 = 25597620 :=
  contactRankWindow_of_rec contact02 32 4 25597620 (by decide +kernel)
private theorem arithBundle01_ranks_036 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 36 4 = 23723748 :=
  contactRankWindow_of_rec contact02 36 4 23723748 (by decide +kernel)
private theorem arithBundle01_ranks_040 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 40 4 = 21932244 :=
  contactRankWindow_of_rec contact02 40 4 21932244 (by decide +kernel)
private theorem arithBundle01_ranks_044 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 44 4 = 20223108 :=
  contactRankWindow_of_rec contact02 44 4 20223108 (by decide +kernel)
private theorem arithBundle01_ranks_048 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 48 4 = 18596340 :=
  contactRankWindow_of_rec contact02 48 4 18596340 (by decide +kernel)
private theorem arithBundle01_ranks_052 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 52 4 = 17051907 :=
  contactRankWindow_of_rec contact02 52 4 17051907 (by decide +kernel)
private theorem arithBundle01_ranks_056 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 56 4 = 15589111 :=
  contactRankWindow_of_rec contact02 56 4 15589111 (by decide +kernel)
private theorem arithBundle01_ranks_060 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 60 4 = 14206537 :=
  contactRankWindow_of_rec contact02 60 4 14206537 (by decide +kernel)
private theorem arithBundle01_ranks_064 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 64 4 = 12902711 :=
  contactRankWindow_of_rec contact02 64 4 12902711 (by decide +kernel)
private theorem arithBundle01_ranks_068 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 68 4 = 11675852 :=
  contactRankWindow_of_rec contact02 68 4 11675852 (by decide +kernel)
private theorem arithBundle01_ranks_072 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 72 4 = 10523989 :=
  contactRankWindow_of_rec contact02 72 4 10523989 (by decide +kernel)
private theorem arithBundle01_ranks_076 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 76 4 = 9444995 :=
  contactRankWindow_of_rec contact02 76 4 9444995 (by decide +kernel)
private theorem arithBundle01_ranks_080 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 80 4 = 8436772 :=
  contactRankWindow_of_rec contact02 80 4 8436772 (by decide +kernel)
private theorem arithBundle01_ranks_084 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 84 4 = 7497505 :=
  contactRankWindow_of_rec contact02 84 4 7497505 (by decide +kernel)
private theorem arithBundle01_ranks_088 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 88 4 = 6624911 :=
  contactRankWindow_of_rec contact02 88 4 6624911 (by decide +kernel)
private theorem arithBundle01_ranks_092 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 92 4 = 5816892 :=
  contactRankWindow_of_rec contact02 92 4 5816892 (by decide +kernel)
private theorem arithBundle01_ranks_096 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 96 4 = 5071789 :=
  contactRankWindow_of_rec contact02 96 4 5071789 (by decide +kernel)
private theorem arithBundle01_ranks_100 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 100 4 = 4387163 :=
  contactRankWindow_of_rec contact02 100 4 4387163 (by decide +kernel)
private theorem arithBundle01_ranks_104 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 104 4 = 3760916 :=
  contactRankWindow_of_rec contact02 104 4 3760916 (by decide +kernel)
private theorem arithBundle01_ranks_108 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 108 4 = 3191545 :=
  contactRankWindow_of_rec contact02 108 4 3191545 (by decide +kernel)
private theorem arithBundle01_ranks_112 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 112 4 = 2676455 :=
  contactRankWindow_of_rec contact02 112 4 2676455 (by decide +kernel)
private theorem arithBundle01_ranks_116 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 116 4 = 2213548 :=
  contactRankWindow_of_rec contact02 116 4 2213548 (by decide +kernel)
private theorem arithBundle01_ranks_120 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 120 4 = 1801477 :=
  contactRankWindow_of_rec contact02 120 4 1801477 (by decide +kernel)
private theorem arithBundle01_ranks_124 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 124 4 = 1437491 :=
  contactRankWindow_of_rec contact02 124 4 1437491 (by decide +kernel)
private theorem arithBundle01_ranks_128 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 128 4 = 1119492 :=
  contactRankWindow_of_rec contact02 128 4 1119492 (by decide +kernel)
private theorem arithBundle01_ranks_132 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 132 4 = 846289 :=
  contactRankWindow_of_rec contact02 132 4 846289 (by decide +kernel)
private theorem arithBundle01_ranks_136 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 136 4 = 614975 :=
  contactRankWindow_of_rec contact02 136 4 614975 (by decide +kernel)
private theorem arithBundle01_ranks_140 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 140 4 = 423452 :=
  contactRankWindow_of_rec contact02 140 4 423452 (by decide +kernel)
private theorem arithBundle01_ranks_144 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 144 4 = 270685 :=
  contactRankWindow_of_rec contact02 144 4 270685 (by decide +kernel)
private theorem arithBundle01_ranks_148 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 148 4 = 153674 :=
  contactRankWindow_of_rec contact02 148 4 153674 (by decide +kernel)
private theorem arithBundle01_ranks_152 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 152 4 = 70801 :=
  contactRankWindow_of_rec contact02 152 4 70801 (by decide +kernel)
private theorem arithBundle01_ranks_156 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 156 4 = 21315 :=
  contactRankWindow_of_rec contact02 156 4 21315 (by decide +kernel)
private theorem arithBundle01_ranks_160 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 160 4 = 1196 :=
  contactRankWindow_of_rec contact02 160 4 1196 (by decide +kernel)
private theorem ranks_164 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 164 15 = 0 :=
  contactRankWindow_of_rec contact02 164 15 0 (by decide +kernel)
private theorem arithBundle01_prefix_ranks_00 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 8 = 84574872 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 4 4 43553844 41021028 arithBundle01_ranks_000 arithBundle01_ranks_004
private theorem arithBundle01_prefix_ranks_01 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 12 = 123145452 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 8 4 84574872 38570580 arithBundle01_prefix_ranks_00 arithBundle01_ranks_008
private theorem arithBundle01_prefix_ranks_02 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 16 = 159347952 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 12 4 123145452 36202500 arithBundle01_prefix_ranks_01 arithBundle01_ranks_012
private theorem arithBundle01_prefix_ranks_03 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 20 = 193264740 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 16 4 159347952 33916788 arithBundle01_prefix_ranks_02 arithBundle01_ranks_016
private theorem arithBundle01_prefix_ranks_04 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 24 = 224978184 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 20 4 193264740 31713444 arithBundle01_prefix_ranks_03 arithBundle01_ranks_020
private theorem arithBundle01_prefix_ranks_05 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 28 = 254570652 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 24 4 224978184 29592468 arithBundle01_prefix_ranks_04 arithBundle01_ranks_024
private theorem arithBundle01_prefix_ranks_06 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 32 = 282124512 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 28 4 254570652 27553860 arithBundle01_prefix_ranks_05 arithBundle01_ranks_028
private theorem arithBundle01_prefix_ranks_07 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 36 = 307722132 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 32 4 282124512 25597620 arithBundle01_prefix_ranks_06 arithBundle01_ranks_032
private theorem arithBundle01_prefix_ranks_08 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 40 = 331445880 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 36 4 307722132 23723748 arithBundle01_prefix_ranks_07 arithBundle01_ranks_036
private theorem arithBundle01_prefix_ranks_09 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 44 = 353378124 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 40 4 331445880 21932244 arithBundle01_prefix_ranks_08 arithBundle01_ranks_040
private theorem arithBundle01_prefix_ranks_10 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 48 = 373601232 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 44 4 353378124 20223108 arithBundle01_prefix_ranks_09 arithBundle01_ranks_044
private theorem arithBundle01_prefix_ranks_11 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 52 = 392197572 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 48 4 373601232 18596340 arithBundle01_prefix_ranks_10 arithBundle01_ranks_048
private theorem arithBundle01_prefix_ranks_12 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 56 = 409249479 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 52 4 392197572 17051907 arithBundle01_prefix_ranks_11 arithBundle01_ranks_052
private theorem arithBundle01_prefix_ranks_13 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 60 = 424838590 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 56 4 409249479 15589111 arithBundle01_prefix_ranks_12 arithBundle01_ranks_056
private theorem arithBundle01_prefix_ranks_14 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 64 = 439045127 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 60 4 424838590 14206537 arithBundle01_prefix_ranks_13 arithBundle01_ranks_060
private theorem arithBundle01_prefix_ranks_15 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 68 = 451947838 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 64 4 439045127 12902711 arithBundle01_prefix_ranks_14 arithBundle01_ranks_064
private theorem arithBundle01_prefix_ranks_16 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 72 = 463623690 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 68 4 451947838 11675852 arithBundle01_prefix_ranks_15 arithBundle01_ranks_068
private theorem arithBundle01_prefix_ranks_17 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 76 = 474147679 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 72 4 463623690 10523989 arithBundle01_prefix_ranks_16 arithBundle01_ranks_072
private theorem arithBundle01_prefix_ranks_18 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 80 = 483592674 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 76 4 474147679 9444995 arithBundle01_prefix_ranks_17 arithBundle01_ranks_076
private theorem arithBundle01_prefix_ranks_19 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 84 = 492029446 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 80 4 483592674 8436772 arithBundle01_prefix_ranks_18 arithBundle01_ranks_080
private theorem arithBundle01_prefix_ranks_20 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 88 = 499526951 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 84 4 492029446 7497505 arithBundle01_prefix_ranks_19 arithBundle01_ranks_084
private theorem arithBundle01_prefix_ranks_21 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 92 = 506151862 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 88 4 499526951 6624911 arithBundle01_prefix_ranks_20 arithBundle01_ranks_088
private theorem arithBundle01_prefix_ranks_22 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 96 = 511968754 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 92 4 506151862 5816892 arithBundle01_prefix_ranks_21 arithBundle01_ranks_092
private theorem arithBundle01_prefix_ranks_23 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 100 = 517040543 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 96 4 511968754 5071789 arithBundle01_prefix_ranks_22 arithBundle01_ranks_096
private theorem arithBundle01_prefix_ranks_24 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 104 = 521427706 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 100 4 517040543 4387163 arithBundle01_prefix_ranks_23 arithBundle01_ranks_100
private theorem arithBundle01_prefix_ranks_25 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 108 = 525188622 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 104 4 521427706 3760916 arithBundle01_prefix_ranks_24 arithBundle01_ranks_104
private theorem arithBundle01_prefix_ranks_26 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 112 = 528380167 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 108 4 525188622 3191545 arithBundle01_prefix_ranks_25 arithBundle01_ranks_108
private theorem arithBundle01_prefix_ranks_27 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 116 = 531056622 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 112 4 528380167 2676455 arithBundle01_prefix_ranks_26 arithBundle01_ranks_112
private theorem arithBundle01_prefix_ranks_28 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 120 = 533270170 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 116 4 531056622 2213548 arithBundle01_prefix_ranks_27 arithBundle01_ranks_116
private theorem arithBundle01_prefix_ranks_29 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 124 = 535071647 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 120 4 533270170 1801477 arithBundle01_prefix_ranks_28 arithBundle01_ranks_120
private theorem arithBundle01_prefix_ranks_30 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 128 = 536509138 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 124 4 535071647 1437491 arithBundle01_prefix_ranks_29 arithBundle01_ranks_124
private theorem arithBundle01_prefix_ranks_31 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 132 = 537628630 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 128 4 536509138 1119492 arithBundle01_prefix_ranks_30 arithBundle01_ranks_128
private theorem arithBundle01_prefix_ranks_32 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 136 = 538474919 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 132 4 537628630 846289 arithBundle01_prefix_ranks_31 arithBundle01_ranks_132
private theorem arithBundle01_prefix_ranks_33 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 140 = 539089894 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 136 4 538474919 614975 arithBundle01_prefix_ranks_32 arithBundle01_ranks_136
private theorem arithBundle01_prefix_ranks_34 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 144 = 539513346 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 140 4 539089894 423452 arithBundle01_prefix_ranks_33 arithBundle01_ranks_140
private theorem arithBundle01_prefix_ranks_35 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 148 = 539784031 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 144 4 539513346 270685 arithBundle01_prefix_ranks_34 arithBundle01_ranks_144
private theorem arithBundle01_prefix_ranks_36 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 152 = 539937705 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 148 4 539784031 153674 arithBundle01_prefix_ranks_35 arithBundle01_ranks_148
private theorem arithBundle01_prefix_ranks_37 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 156 = 540008506 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 152 4 539937705 70801 arithBundle01_prefix_ranks_36 arithBundle01_ranks_152
private theorem arithBundle01_prefix_ranks_38 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 160 = 540029821 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 156 4 540008506 21315 arithBundle01_prefix_ranks_37 arithBundle01_ranks_156
private theorem arithBundle01_prefix_ranks_39 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 164 = 540031017 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 160 4 540029821 1196 arithBundle01_prefix_ranks_38 arithBundle01_ranks_160
private theorem prefix_ranks_40 : arithBundle01_sliceWindow (auxiliaryRankSlice contact02) 0 179 = 540031017 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact02) 0 164 15 540031017 0 arithBundle01_prefix_ranks_39 ranks_164

theorem contact02_margin : sourceMargin contact02 :=
  arithBundle01_margin_of_checked_counts contact02 179 3567503565385676 176814867134312 13743409701 540031017
    rfl arithBundle01_ordinary_columns arithBundle01_prefix_columns_43 arithBundle01_ordinary_ranks prefix_ranks_40 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle02_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle02_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle02_sliceWindow f a b = x) (hy : arithBundle02_sliceWindow f (a+b) c = y) :
    arithBundle02_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle02_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle02_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle02_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle02_sliceWindow,Nat.zero_add]

private theorem arithBundle02_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle02_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle02_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle02_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle02_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle02_ordinary_columns : ordinaryColumnCount contact05 = 2110312870615866 := by decide +kernel
private theorem arithBundle02_columns_000 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 4 = 7743819487120 :=
  contactColumnsWindow_fast contact05 0 4 7743819487120 (by decide +kernel)
private theorem arithBundle02_columns_004 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 4 4 = 7373361457680 :=
  contactColumnsWindow_fast contact05 4 4 7373361457680 (by decide +kernel)
private theorem arithBundle02_columns_008 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 8 4 = 7012019459376 :=
  contactColumnsWindow_fast contact05 8 4 7012019459376 (by decide +kernel)
private theorem arithBundle02_columns_012 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 12 4 = 6659793622225 :=
  contactColumnsWindow_fast contact05 12 4 6659793622225 (by decide +kernel)
private theorem arithBundle02_columns_016 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 16 4 = 6316718375660 :=
  contactColumnsWindow_fast contact05 16 4 6316718375660 (by decide +kernel)
private theorem arithBundle02_columns_020 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 20 4 = 5982780378642 :=
  contactColumnsWindow_fast contact05 20 4 5982780378642 (by decide +kernel)
private theorem arithBundle02_columns_024 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 24 4 = 5657962285240 :=
  contactColumnsWindow_fast contact05 24 4 5657962285240 (by decide +kernel)
private theorem arithBundle02_columns_028 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 28 4 = 5342262596646 :=
  contactColumnsWindow_fast contact05 28 4 5342262596646 (by decide +kernel)
private theorem arithBundle02_columns_032 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 32 4 = 5035684256379 :=
  contactColumnsWindow_fast contact05 32 4 5035684256379 (by decide +kernel)
private theorem arithBundle02_columns_036 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 36 4 = 4738261006688 :=
  contactColumnsWindow_fast contact05 36 4 4738261006688 (by decide +kernel)
private theorem arithBundle02_columns_040 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 40 4 = 4449976085146 :=
  contactColumnsWindow_fast contact05 40 4 4449976085146 (by decide +kernel)
private theorem arithBundle02_columns_044 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 44 4 = 4170812953205 :=
  contactColumnsWindow_fast contact05 44 4 4170812953205 (by decide +kernel)
private theorem arithBundle02_columns_048 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 48 4 = 3900772923642 :=
  contactColumnsWindow_fast contact05 48 4 3900772923642 (by decide +kernel)
private theorem arithBundle02_columns_052 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 52 4 = 3639857540363 :=
  contactColumnsWindow_fast contact05 52 4 3639857540363 (by decide +kernel)
private theorem arithBundle02_columns_056 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 56 4 = 3388104192232 :=
  contactColumnsWindow_fast contact05 56 4 3388104192232 (by decide +kernel)
private theorem arithBundle02_columns_060 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 60 4 = 3145488772052 :=
  contactColumnsWindow_fast contact05 60 4 3145488772052 (by decide +kernel)
private theorem arithBundle02_columns_064 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 64 4 = 2911998814535 :=
  contactColumnsWindow_fast contact05 64 4 2911998814535 (by decide +kernel)
private theorem arithBundle02_columns_068 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 68 4 = 2687631903666 :=
  contactColumnsWindow_fast contact05 68 4 2687631903666 (by decide +kernel)
private theorem arithBundle02_columns_072 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 72 4 = 2472391468218 :=
  contactColumnsWindow_fast contact05 72 4 2472391468218 (by decide +kernel)
private theorem arithBundle02_columns_076 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 76 4 = 2266314569257 :=
  contactColumnsWindow_fast contact05 76 4 2266314569257 (by decide +kernel)
private theorem arithBundle02_columns_080 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 80 4 = 2069372836760 :=
  contactColumnsWindow_fast contact05 80 4 2069372836760 (by decide +kernel)
private theorem arithBundle02_columns_084 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 84 4 = 1881556036481 :=
  contactColumnsWindow_fast contact05 84 4 1881556036481 (by decide +kernel)
private theorem arithBundle02_columns_088 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 88 4 = 1702862315289 :=
  contactColumnsWindow_fast contact05 88 4 1702862315289 (by decide +kernel)
private theorem arithBundle02_columns_092 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 92 4 = 1533297668994 :=
  contactColumnsWindow_fast contact05 92 4 1533297668994 (by decide +kernel)
private theorem arithBundle02_columns_096 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 96 4 = 1372896307363 :=
  contactColumnsWindow_fast contact05 96 4 1372896307363 (by decide +kernel)
private theorem arithBundle02_columns_100 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 100 4 = 1221628273654 :=
  contactColumnsWindow_fast contact05 100 4 1221628273654 (by decide +kernel)
private theorem arithBundle02_columns_104 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 104 4 = 1079484824876 :=
  contactColumnsWindow_fast contact05 104 4 1079484824876 (by decide +kernel)
private theorem arithBundle02_columns_108 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 108 4 = 946464146631 :=
  contactColumnsWindow_fast contact05 108 4 946464146631 (by decide +kernel)
private theorem arithBundle02_columns_112 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 112 4 = 822575230386 :=
  contactColumnsWindow_fast contact05 112 4 822575230386 (by decide +kernel)
private theorem arithBundle02_columns_116 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 116 4 = 707849614813 :=
  contactColumnsWindow_fast contact05 116 4 707849614813 (by decide +kernel)
private theorem arithBundle02_columns_120 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 120 4 = 602255184862 :=
  contactColumnsWindow_fast contact05 120 4 602255184862 (by decide +kernel)
private theorem arithBundle02_columns_124 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 124 4 = 505785023408 :=
  contactColumnsWindow_fast contact05 124 4 505785023408 (by decide +kernel)
private theorem arithBundle02_columns_128 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 128 4 = 418437391299 :=
  contactColumnsWindow_fast contact05 128 4 418437391299 (by decide +kernel)
private theorem arithBundle02_columns_132 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 132 4 = 340224994199 :=
  contactColumnsWindow_fast contact05 132 4 340224994199 (by decide +kernel)
private theorem arithBundle02_columns_136 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 136 4 = 271174464878 :=
  contactColumnsWindow_fast contact05 136 4 271174464878 (by decide +kernel)
private theorem arithBundle02_columns_140 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 140 4 = 211240698379 :=
  contactColumnsWindow_fast contact05 140 4 211240698379 (by decide +kernel)
private theorem arithBundle02_columns_144 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 144 4 = 160285008782 :=
  contactColumnsWindow_fast contact05 144 4 160285008782 (by decide +kernel)
private theorem arithBundle02_columns_148 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 148 4 = 117972596709 :=
  contactColumnsWindow_fast contact05 148 4 117972596709 (by decide +kernel)
private theorem arithBundle02_columns_152 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 152 4 = 83822716236 :=
  contactColumnsWindow_fast contact05 152 4 83822716236 (by decide +kernel)
private theorem arithBundle02_columns_156 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 156 4 = 57192319324 :=
  contactColumnsWindow_fast contact05 156 4 57192319324 (by decide +kernel)
private theorem arithBundle02_columns_160 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 160 4 = 37227291222 :=
  contactColumnsWindow_fast contact05 160 4 37227291222 (by decide +kernel)
private theorem arithBundle02_columns_164 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 164 4 = 22942136558 :=
  contactColumnsWindow_fast contact05 164 4 22942136558 (by decide +kernel)
private theorem arithBundle02_prefix_columns_00 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 8 = 15117180944800 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 4 4 7743819487120 7373361457680 arithBundle02_columns_000 arithBundle02_columns_004
private theorem arithBundle02_prefix_columns_01 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 12 = 22129200404176 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 8 4 15117180944800 7012019459376 arithBundle02_prefix_columns_00 arithBundle02_columns_008
private theorem arithBundle02_prefix_columns_02 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 16 = 28788994026401 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 12 4 22129200404176 6659793622225 arithBundle02_prefix_columns_01 arithBundle02_columns_012
private theorem arithBundle02_prefix_columns_03 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 20 = 35105712402061 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 16 4 28788994026401 6316718375660 arithBundle02_prefix_columns_02 arithBundle02_columns_016
private theorem arithBundle02_prefix_columns_04 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 24 = 41088492780703 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 20 4 35105712402061 5982780378642 arithBundle02_prefix_columns_03 arithBundle02_columns_020
private theorem arithBundle02_prefix_columns_05 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 28 = 46746455065943 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 24 4 41088492780703 5657962285240 arithBundle02_prefix_columns_04 arithBundle02_columns_024
private theorem arithBundle02_prefix_columns_06 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 32 = 52088717662589 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 28 4 46746455065943 5342262596646 arithBundle02_prefix_columns_05 arithBundle02_columns_028
private theorem arithBundle02_prefix_columns_07 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 36 = 57124401918968 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 32 4 52088717662589 5035684256379 arithBundle02_prefix_columns_06 arithBundle02_columns_032
private theorem arithBundle02_prefix_columns_08 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 40 = 61862662925656 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 36 4 57124401918968 4738261006688 arithBundle02_prefix_columns_07 arithBundle02_columns_036
private theorem arithBundle02_prefix_columns_09 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 44 = 66312639010802 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 40 4 61862662925656 4449976085146 arithBundle02_prefix_columns_08 arithBundle02_columns_040
private theorem arithBundle02_prefix_columns_10 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 48 = 70483451964007 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 44 4 66312639010802 4170812953205 arithBundle02_prefix_columns_09 arithBundle02_columns_044
private theorem arithBundle02_prefix_columns_11 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 52 = 74384224887649 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 48 4 70483451964007 3900772923642 arithBundle02_prefix_columns_10 arithBundle02_columns_048
private theorem arithBundle02_prefix_columns_12 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 56 = 78024082428012 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 52 4 74384224887649 3639857540363 arithBundle02_prefix_columns_11 arithBundle02_columns_052
private theorem arithBundle02_prefix_columns_13 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 60 = 81412186620244 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 56 4 78024082428012 3388104192232 arithBundle02_prefix_columns_12 arithBundle02_columns_056
private theorem arithBundle02_prefix_columns_14 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 64 = 84557675392296 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 60 4 81412186620244 3145488772052 arithBundle02_prefix_columns_13 arithBundle02_columns_060
private theorem arithBundle02_prefix_columns_15 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 68 = 87469674206831 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 64 4 84557675392296 2911998814535 arithBundle02_prefix_columns_14 arithBundle02_columns_064
private theorem arithBundle02_prefix_columns_16 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 72 = 90157306110497 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 68 4 87469674206831 2687631903666 arithBundle02_prefix_columns_15 arithBundle02_columns_068
private theorem arithBundle02_prefix_columns_17 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 76 = 92629697578715 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 72 4 90157306110497 2472391468218 arithBundle02_prefix_columns_16 arithBundle02_columns_072
private theorem arithBundle02_prefix_columns_18 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 80 = 94896012147972 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 76 4 92629697578715 2266314569257 arithBundle02_prefix_columns_17 arithBundle02_columns_076
private theorem arithBundle02_prefix_columns_19 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 84 = 96965384984732 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 80 4 94896012147972 2069372836760 arithBundle02_prefix_columns_18 arithBundle02_columns_080
private theorem arithBundle02_prefix_columns_20 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 88 = 98846941021213 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 84 4 96965384984732 1881556036481 arithBundle02_prefix_columns_19 arithBundle02_columns_084
private theorem arithBundle02_prefix_columns_21 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 92 = 100549803336502 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 88 4 98846941021213 1702862315289 arithBundle02_prefix_columns_20 arithBundle02_columns_088
private theorem arithBundle02_prefix_columns_22 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 96 = 102083101005496 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 92 4 100549803336502 1533297668994 arithBundle02_prefix_columns_21 arithBundle02_columns_092
private theorem arithBundle02_prefix_columns_23 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 100 = 103455997312859 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 96 4 102083101005496 1372896307363 arithBundle02_prefix_columns_22 arithBundle02_columns_096
private theorem arithBundle02_prefix_columns_24 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 104 = 104677625586513 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 100 4 103455997312859 1221628273654 arithBundle02_prefix_columns_23 arithBundle02_columns_100
private theorem arithBundle02_prefix_columns_25 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 108 = 105757110411389 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 104 4 104677625586513 1079484824876 arithBundle02_prefix_columns_24 arithBundle02_columns_104
private theorem arithBundle02_prefix_columns_26 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 112 = 106703574558020 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 108 4 105757110411389 946464146631 arithBundle02_prefix_columns_25 arithBundle02_columns_108
private theorem arithBundle02_prefix_columns_27 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 116 = 107526149788406 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 112 4 106703574558020 822575230386 arithBundle02_prefix_columns_26 arithBundle02_columns_112
private theorem arithBundle02_prefix_columns_28 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 120 = 108233999403219 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 116 4 107526149788406 707849614813 arithBundle02_prefix_columns_27 arithBundle02_columns_116
private theorem arithBundle02_prefix_columns_29 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 124 = 108836254588081 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 120 4 108233999403219 602255184862 arithBundle02_prefix_columns_28 arithBundle02_columns_120
private theorem arithBundle02_prefix_columns_30 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 128 = 109342039611489 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 124 4 108836254588081 505785023408 arithBundle02_prefix_columns_29 arithBundle02_columns_124
private theorem arithBundle02_prefix_columns_31 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 132 = 109760477002788 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 128 4 109342039611489 418437391299 arithBundle02_prefix_columns_30 arithBundle02_columns_128
private theorem arithBundle02_prefix_columns_32 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 136 = 110100701996987 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 132 4 109760477002788 340224994199 arithBundle02_prefix_columns_31 arithBundle02_columns_132
private theorem arithBundle02_prefix_columns_33 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 140 = 110371876461865 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 136 4 110100701996987 271174464878 arithBundle02_prefix_columns_32 arithBundle02_columns_136
private theorem arithBundle02_prefix_columns_34 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 144 = 110583117160244 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 140 4 110371876461865 211240698379 arithBundle02_prefix_columns_33 arithBundle02_columns_140
private theorem arithBundle02_prefix_columns_35 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 148 = 110743402169026 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 144 4 110583117160244 160285008782 arithBundle02_prefix_columns_34 arithBundle02_columns_144
private theorem arithBundle02_prefix_columns_36 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 152 = 110861374765735 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 148 4 110743402169026 117972596709 arithBundle02_prefix_columns_35 arithBundle02_columns_148
private theorem arithBundle02_prefix_columns_37 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 156 = 110945197481971 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 152 4 110861374765735 83822716236 arithBundle02_prefix_columns_36 arithBundle02_columns_152
private theorem arithBundle02_prefix_columns_38 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 160 = 111002389801295 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 156 4 110945197481971 57192319324 arithBundle02_prefix_columns_37 arithBundle02_columns_156
private theorem arithBundle02_prefix_columns_39 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 164 = 111039617092517 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 160 4 111002389801295 37227291222 arithBundle02_prefix_columns_38 arithBundle02_columns_160
private theorem arithBundle02_prefix_columns_40 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact05) 0 168 = 111062559229075 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact05) 0 164 4 111039617092517 22942136558 arithBundle02_prefix_columns_39 arithBundle02_columns_164

private theorem arithBundle02_ordinary_ranks : ordinaryRankBound contact05 = 8137647610 := by decide +kernel
private theorem arithBundle02_ranks_000 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 4 = 29183538 :=
  contactRankWindow_of_rec contact05 0 4 29183538 (by decide +kernel)
private theorem arithBundle02_ranks_004 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 4 4 = 27361410 :=
  contactRankWindow_of_rec contact05 4 4 27361410 (by decide +kernel)
private theorem arithBundle02_ranks_008 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 8 4 = 25602386 :=
  contactRankWindow_of_rec contact05 8 4 25602386 (by decide +kernel)
private theorem arithBundle02_ranks_012 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 12 4 = 23906466 :=
  contactRankWindow_of_rec contact05 12 4 23906466 (by decide +kernel)
private theorem arithBundle02_ranks_016 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 16 4 = 22273650 :=
  contactRankWindow_of_rec contact05 16 4 22273650 (by decide +kernel)
private theorem arithBundle02_ranks_020 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 20 4 = 20703938 :=
  contactRankWindow_of_rec contact05 20 4 20703938 (by decide +kernel)
private theorem arithBundle02_ranks_024 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 24 4 = 19197330 :=
  contactRankWindow_of_rec contact05 24 4 19197330 (by decide +kernel)
private theorem arithBundle02_ranks_028 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 28 4 = 17753826 :=
  contactRankWindow_of_rec contact05 28 4 17753826 (by decide +kernel)
private theorem arithBundle02_ranks_032 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 32 4 = 16373426 :=
  contactRankWindow_of_rec contact05 32 4 16373426 (by decide +kernel)
private theorem arithBundle02_ranks_036 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 36 4 = 15056130 :=
  contactRankWindow_of_rec contact05 36 4 15056130 (by decide +kernel)
private theorem arithBundle02_ranks_040 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 40 4 = 13801938 :=
  contactRankWindow_of_rec contact05 40 4 13801938 (by decide +kernel)
private theorem arithBundle02_ranks_044 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 44 4 = 12610850 :=
  contactRankWindow_of_rec contact05 44 4 12610850 (by decide +kernel)
private theorem arithBundle02_ranks_048 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 48 4 = 11482866 :=
  contactRankWindow_of_rec contact05 48 4 11482866 (by decide +kernel)
private theorem arithBundle02_ranks_052 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 52 4 = 10417986 :=
  contactRankWindow_of_rec contact05 52 4 10417986 (by decide +kernel)
private theorem arithBundle02_ranks_056 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 56 4 = 9416006 :=
  contactRankWindow_of_rec contact05 56 4 9416006 (by decide +kernel)
private theorem arithBundle02_ranks_060 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 60 4 = 8475868 :=
  contactRankWindow_of_rec contact05 60 4 8475868 (by decide +kernel)
private theorem arithBundle02_ranks_064 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 64 4 = 7596310 :=
  contactRankWindow_of_rec contact05 64 4 7596310 (by decide +kernel)
private theorem arithBundle02_ranks_068 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 68 4 = 6775747 :=
  contactRankWindow_of_rec contact05 68 4 6775747 (by decide +kernel)
private theorem arithBundle02_ranks_072 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 72 4 = 6012456 :=
  contactRankWindow_of_rec contact05 72 4 6012456 (by decide +kernel)
private theorem arithBundle02_ranks_076 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 76 4 = 5304598 :=
  contactRankWindow_of_rec contact05 76 4 5304598 (by decide +kernel)
private theorem arithBundle02_ranks_080 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 80 4 = 4650315 :=
  contactRankWindow_of_rec contact05 80 4 4650315 (by decide +kernel)
private theorem arithBundle02_ranks_084 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 84 4 = 4048020 :=
  contactRankWindow_of_rec contact05 84 4 4048020 (by decide +kernel)
private theorem arithBundle02_ranks_088 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 88 4 = 3495734 :=
  contactRankWindow_of_rec contact05 88 4 3495734 (by decide +kernel)
private theorem arithBundle02_ranks_092 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 92 4 = 2991603 :=
  contactRankWindow_of_rec contact05 92 4 2991603 (by decide +kernel)
private theorem arithBundle02_ranks_096 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 96 4 = 2534176 :=
  contactRankWindow_of_rec contact05 96 4 2534176 (by decide +kernel)
private theorem arithBundle02_ranks_100 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 100 4 = 2121334 :=
  contactRankWindow_of_rec contact05 100 4 2121334 (by decide +kernel)
private theorem arithBundle02_ranks_104 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 104 4 = 1751227 :=
  contactRankWindow_of_rec contact05 104 4 1751227 (by decide +kernel)
private theorem arithBundle02_ranks_108 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 108 4 = 1422540 :=
  contactRankWindow_of_rec contact05 108 4 1422540 (by decide +kernel)
private theorem arithBundle02_ranks_112 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 112 4 = 1133014 :=
  contactRankWindow_of_rec contact05 112 4 1133014 (by decide +kernel)
private theorem arithBundle02_ranks_116 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 116 4 = 880803 :=
  contactRankWindow_of_rec contact05 116 4 880803 (by decide +kernel)
private theorem arithBundle02_ranks_120 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 120 4 = 664728 :=
  contactRankWindow_of_rec contact05 120 4 664728 (by decide +kernel)
private theorem arithBundle02_ranks_124 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 124 4 = 482390 :=
  contactRankWindow_of_rec contact05 124 4 482390 (by decide +kernel)
private theorem arithBundle02_ranks_128 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 128 4 = 331947 :=
  contactRankWindow_of_rec contact05 128 4 331947 (by decide +kernel)
private theorem arithBundle02_ranks_132 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 132 4 = 212356 :=
  contactRankWindow_of_rec contact05 132 4 212356 (by decide +kernel)
private theorem arithBundle02_ranks_136 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 136 4 = 121078 :=
  contactRankWindow_of_rec contact05 136 4 121078 (by decide +kernel)
private theorem arithBundle02_ranks_140 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 140 4 = 56275 :=
  contactRankWindow_of_rec contact05 140 4 56275 (by decide +kernel)
private theorem arithBundle02_ranks_144 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 144 4 = 17102 :=
  contactRankWindow_of_rec contact05 144 4 17102 (by decide +kernel)
private theorem arithBundle02_ranks_148 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 148 4 = 965 :=
  contactRankWindow_of_rec contact05 148 4 965 (by decide +kernel)
private theorem arithBundle02_ranks_152 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 152 16 = 0 :=
  contactRankWindow_of_rec contact05 152 16 0 (by decide +kernel)
private theorem arithBundle02_prefix_ranks_00 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 8 = 56544948 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 4 4 29183538 27361410 arithBundle02_ranks_000 arithBundle02_ranks_004
private theorem arithBundle02_prefix_ranks_01 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 12 = 82147334 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 8 4 56544948 25602386 arithBundle02_prefix_ranks_00 arithBundle02_ranks_008
private theorem arithBundle02_prefix_ranks_02 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 16 = 106053800 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 12 4 82147334 23906466 arithBundle02_prefix_ranks_01 arithBundle02_ranks_012
private theorem arithBundle02_prefix_ranks_03 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 20 = 128327450 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 16 4 106053800 22273650 arithBundle02_prefix_ranks_02 arithBundle02_ranks_016
private theorem arithBundle02_prefix_ranks_04 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 24 = 149031388 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 20 4 128327450 20703938 arithBundle02_prefix_ranks_03 arithBundle02_ranks_020
private theorem arithBundle02_prefix_ranks_05 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 28 = 168228718 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 24 4 149031388 19197330 arithBundle02_prefix_ranks_04 arithBundle02_ranks_024
private theorem arithBundle02_prefix_ranks_06 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 32 = 185982544 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 28 4 168228718 17753826 arithBundle02_prefix_ranks_05 arithBundle02_ranks_028
private theorem arithBundle02_prefix_ranks_07 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 36 = 202355970 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 32 4 185982544 16373426 arithBundle02_prefix_ranks_06 arithBundle02_ranks_032
private theorem arithBundle02_prefix_ranks_08 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 40 = 217412100 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 36 4 202355970 15056130 arithBundle02_prefix_ranks_07 arithBundle02_ranks_036
private theorem arithBundle02_prefix_ranks_09 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 44 = 231214038 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 40 4 217412100 13801938 arithBundle02_prefix_ranks_08 arithBundle02_ranks_040
private theorem arithBundle02_prefix_ranks_10 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 48 = 243824888 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 44 4 231214038 12610850 arithBundle02_prefix_ranks_09 arithBundle02_ranks_044
private theorem arithBundle02_prefix_ranks_11 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 52 = 255307754 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 48 4 243824888 11482866 arithBundle02_prefix_ranks_10 arithBundle02_ranks_048
private theorem arithBundle02_prefix_ranks_12 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 56 = 265725740 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 52 4 255307754 10417986 arithBundle02_prefix_ranks_11 arithBundle02_ranks_052
private theorem arithBundle02_prefix_ranks_13 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 60 = 275141746 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 56 4 265725740 9416006 arithBundle02_prefix_ranks_12 arithBundle02_ranks_056
private theorem arithBundle02_prefix_ranks_14 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 64 = 283617614 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 60 4 275141746 8475868 arithBundle02_prefix_ranks_13 arithBundle02_ranks_060
private theorem arithBundle02_prefix_ranks_15 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 68 = 291213924 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 64 4 283617614 7596310 arithBundle02_prefix_ranks_14 arithBundle02_ranks_064
private theorem arithBundle02_prefix_ranks_16 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 72 = 297989671 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 68 4 291213924 6775747 arithBundle02_prefix_ranks_15 arithBundle02_ranks_068
private theorem arithBundle02_prefix_ranks_17 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 76 = 304002127 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 72 4 297989671 6012456 arithBundle02_prefix_ranks_16 arithBundle02_ranks_072
private theorem arithBundle02_prefix_ranks_18 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 80 = 309306725 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 76 4 304002127 5304598 arithBundle02_prefix_ranks_17 arithBundle02_ranks_076
private theorem arithBundle02_prefix_ranks_19 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 84 = 313957040 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 80 4 309306725 4650315 arithBundle02_prefix_ranks_18 arithBundle02_ranks_080
private theorem arithBundle02_prefix_ranks_20 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 88 = 318005060 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 84 4 313957040 4048020 arithBundle02_prefix_ranks_19 arithBundle02_ranks_084
private theorem arithBundle02_prefix_ranks_21 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 92 = 321500794 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 88 4 318005060 3495734 arithBundle02_prefix_ranks_20 arithBundle02_ranks_088
private theorem arithBundle02_prefix_ranks_22 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 96 = 324492397 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 92 4 321500794 2991603 arithBundle02_prefix_ranks_21 arithBundle02_ranks_092
private theorem arithBundle02_prefix_ranks_23 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 100 = 327026573 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 96 4 324492397 2534176 arithBundle02_prefix_ranks_22 arithBundle02_ranks_096
private theorem arithBundle02_prefix_ranks_24 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 104 = 329147907 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 100 4 327026573 2121334 arithBundle02_prefix_ranks_23 arithBundle02_ranks_100
private theorem arithBundle02_prefix_ranks_25 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 108 = 330899134 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 104 4 329147907 1751227 arithBundle02_prefix_ranks_24 arithBundle02_ranks_104
private theorem arithBundle02_prefix_ranks_26 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 112 = 332321674 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 108 4 330899134 1422540 arithBundle02_prefix_ranks_25 arithBundle02_ranks_108
private theorem arithBundle02_prefix_ranks_27 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 116 = 333454688 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 112 4 332321674 1133014 arithBundle02_prefix_ranks_26 arithBundle02_ranks_112
private theorem arithBundle02_prefix_ranks_28 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 120 = 334335491 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 116 4 333454688 880803 arithBundle02_prefix_ranks_27 arithBundle02_ranks_116
private theorem arithBundle02_prefix_ranks_29 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 124 = 335000219 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 120 4 334335491 664728 arithBundle02_prefix_ranks_28 arithBundle02_ranks_120
private theorem arithBundle02_prefix_ranks_30 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 128 = 335482609 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 124 4 335000219 482390 arithBundle02_prefix_ranks_29 arithBundle02_ranks_124
private theorem arithBundle02_prefix_ranks_31 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 132 = 335814556 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 128 4 335482609 331947 arithBundle02_prefix_ranks_30 arithBundle02_ranks_128
private theorem arithBundle02_prefix_ranks_32 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 136 = 336026912 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 132 4 335814556 212356 arithBundle02_prefix_ranks_31 arithBundle02_ranks_132
private theorem arithBundle02_prefix_ranks_33 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 140 = 336147990 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 136 4 336026912 121078 arithBundle02_prefix_ranks_32 arithBundle02_ranks_136
private theorem arithBundle02_prefix_ranks_34 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 144 = 336204265 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 140 4 336147990 56275 arithBundle02_prefix_ranks_33 arithBundle02_ranks_140
private theorem arithBundle02_prefix_ranks_35 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 148 = 336221367 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 144 4 336204265 17102 arithBundle02_prefix_ranks_34 arithBundle02_ranks_144
private theorem arithBundle02_prefix_ranks_36 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 152 = 336222332 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 148 4 336221367 965 arithBundle02_prefix_ranks_35 arithBundle02_ranks_148
private theorem arithBundle02_prefix_ranks_37 : arithBundle02_sliceWindow (auxiliaryRankSlice contact05) 0 168 = 336222332 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact05) 0 152 16 336222332 0 arithBundle02_prefix_ranks_36 arithBundle02_ranks_152

theorem contact05_margin : sourceMargin contact05 :=
  arithBundle02_margin_of_checked_counts contact05 168 2110312870615866 111062559229075 8137647610 336222332
    rfl arithBundle02_ordinary_columns arithBundle02_prefix_columns_40 arithBundle02_ordinary_ranks arithBundle02_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle03_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle03_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle03_sliceWindow f a b = x) (hy : arithBundle03_sliceWindow f (a+b) c = y) :
    arithBundle03_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle03_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle03_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle03_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle03_sliceWindow,Nat.zero_add]

private theorem arithBundle03_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle03_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle03_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle03_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle03_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle03_ordinary_columns : ordinaryColumnCount contact06 = 2041314203461594 := by decide +kernel
private theorem arithBundle03_columns_000 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 4 = 7926766620478 :=
  contactColumnsWindow_fast contact06 0 4 7926766620478 (by decide +kernel)
private theorem arithBundle03_columns_004 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 4 4 = 7546542478046 :=
  contactColumnsWindow_fast contact06 4 4 7546542478046 (by decide +kernel)
private theorem arithBundle03_columns_008 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 8 4 = 7175702462786 :=
  contactColumnsWindow_fast contact06 8 4 7175702462786 (by decide +kernel)
private theorem arithBundle03_columns_012 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 12 4 = 6814246711323 :=
  contactColumnsWindow_fast contact06 12 4 6814246711323 (by decide +kernel)
private theorem arithBundle03_columns_016 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 16 4 = 6462211010786 :=
  contactColumnsWindow_fast contact06 16 4 6462211010786 (by decide +kernel)
private theorem arithBundle03_columns_020 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 20 4 = 6119581470596 :=
  contactColumnsWindow_fast contact06 20 4 6119581470596 (by decide +kernel)
private theorem arithBundle03_columns_024 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 24 4 = 5786340007018 :=
  contactColumnsWindow_fast contact06 24 4 5786340007018 (by decide +kernel)
private theorem arithBundle03_columns_028 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 28 4 = 5462485090382 :=
  contactColumnsWindow_fast contact06 28 4 5462485090382 (by decide +kernel)
private theorem arithBundle03_columns_032 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 32 4 = 5148019745758 :=
  contactColumnsWindow_fast contact06 32 4 5148019745758 (by decide +kernel)
private theorem arithBundle03_columns_036 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 36 4 = 4842979086924 :=
  contactColumnsWindow_fast contact06 36 4 4842979086924 (by decide +kernel)
private theorem arithBundle03_columns_040 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 40 4 = 4547345607405 :=
  contactColumnsWindow_fast contact06 40 4 4547345607405 (by decide +kernel)
private theorem arithBundle03_columns_044 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 44 4 = 4261102122147 :=
  contactColumnsWindow_fast contact06 44 4 4261102122147 (by decide +kernel)
private theorem arithBundle03_columns_048 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 48 4 = 3984249963144 :=
  contactColumnsWindow_fast contact06 48 4 3984249963144 (by decide +kernel)
private theorem arithBundle03_columns_052 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 52 4 = 3716790756105 :=
  contactColumnsWindow_fast contact06 52 4 3716790756105 (by decide +kernel)
private theorem arithBundle03_columns_056 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 56 4 = 3458763352209 :=
  contactColumnsWindow_fast contact06 56 4 3458763352209 (by decide +kernel)
private theorem arithBundle03_columns_060 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 60 4 = 3210142636192 :=
  contactColumnsWindow_fast contact06 60 4 3210142636192 (by decide +kernel)
private theorem arithBundle03_columns_064 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 64 4 = 2970915645225 :=
  contactColumnsWindow_fast contact06 64 4 2970915645225 (by decide +kernel)
private theorem arithBundle03_columns_068 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 68 4 = 2741079924426 :=
  contactColumnsWindow_fast contact06 68 4 2741079924426 (by decide +kernel)
private theorem arithBundle03_columns_072 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 72 4 = 2520639053384 :=
  contactColumnsWindow_fast contact06 72 4 2520639053384 (by decide +kernel)
private theorem arithBundle03_columns_076 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 76 4 = 2309631547019 :=
  contactColumnsWindow_fast contact06 76 4 2309631547019 (by decide +kernel)
private theorem arithBundle03_columns_080 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 80 4 = 2108027847862 :=
  contactColumnsWindow_fast contact06 80 4 2108027847862 (by decide +kernel)
private theorem arithBundle03_columns_084 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 84 4 = 1915817333643 :=
  contactColumnsWindow_fast contact06 84 4 1915817333643 (by decide +kernel)
private theorem arithBundle03_columns_088 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 88 4 = 1732998123318 :=
  contactColumnsWindow_fast contact06 88 4 1732998123318 (by decide +kernel)
private theorem arithBundle03_columns_092 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 92 4 = 1559576460830 :=
  contactColumnsWindow_fast contact06 92 4 1559576460830 (by decide +kernel)
private theorem arithBundle03_columns_096 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 96 4 = 1395587907665 :=
  contactColumnsWindow_fast contact06 96 4 1395587907665 (by decide +kernel)
private theorem arithBundle03_columns_100 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 100 4 = 1241001236638 :=
  contactColumnsWindow_fast contact06 100 4 1241001236638 (by decide +kernel)
private theorem arithBundle03_columns_104 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 104 4 = 1095807397126 :=
  contactColumnsWindow_fast contact06 104 4 1095807397126 (by decide +kernel)
private theorem arithBundle03_columns_108 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 108 4 = 960004547775 :=
  contactColumnsWindow_fast contact06 108 4 960004547775 (by decide +kernel)
private theorem arithBundle03_columns_112 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 112 4 = 833602033616 :=
  contactColumnsWindow_fast contact06 112 4 833602033616 (by decide +kernel)
private theorem arithBundle03_columns_116 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 116 4 = 716632646028 :=
  contactColumnsWindow_fast contact06 116 4 716632646028 (by decide +kernel)
private theorem arithBundle03_columns_120 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 120 4 = 609062906665 :=
  contactColumnsWindow_fast contact06 120 4 609062906665 (by decide +kernel)
private theorem arithBundle03_columns_124 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 124 4 = 510885676396 :=
  contactColumnsWindow_fast contact06 124 4 510885676396 (by decide +kernel)
private theorem arithBundle03_columns_128 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 128 4 = 422099191130 :=
  contactColumnsWindow_fast contact06 128 4 422099191130 (by decide +kernel)
private theorem arithBundle03_columns_132 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 132 4 = 342716645341 :=
  contactColumnsWindow_fast contact06 132 4 342716645341 (by decide +kernel)
private theorem arithBundle03_columns_136 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 136 4 = 272765541301 :=
  contactColumnsWindow_fast contact06 136 4 272765541301 (by decide +kernel)
private theorem arithBundle03_columns_140 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 140 4 = 212184988031 :=
  contactColumnsWindow_fast contact06 140 4 212184988031 (by decide +kernel)
private theorem arithBundle03_columns_144 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 144 4 = 160788106197 :=
  contactColumnsWindow_fast contact06 144 4 160788106197 (by decide +kernel)
private theorem arithBundle03_columns_148 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 148 4 = 118198954888 :=
  contactColumnsWindow_fast contact06 148 4 118198954888 (by decide +kernel)
private theorem arithBundle03_columns_152 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 152 4 = 83899057006 :=
  contactColumnsWindow_fast contact06 152 4 83899057006 (by decide +kernel)
private theorem arithBundle03_columns_156 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 156 4 = 57206580053 :=
  contactColumnsWindow_fast contact06 156 4 57206580053 (by decide +kernel)
private theorem arithBundle03_columns_160 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 160 4 = 37227737339 :=
  contactColumnsWindow_fast contact06 160 4 37227737339 (by decide +kernel)
private theorem arithBundle03_columns_164 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 164 4 = 22942136558 :=
  contactColumnsWindow_fast contact06 164 4 22942136558 (by decide +kernel)
private theorem arithBundle03_prefix_columns_00 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 8 = 15473309098524 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 4 4 7926766620478 7546542478046 arithBundle03_columns_000 arithBundle03_columns_004
private theorem arithBundle03_prefix_columns_01 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 12 = 22649011561310 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 8 4 15473309098524 7175702462786 arithBundle03_prefix_columns_00 arithBundle03_columns_008
private theorem arithBundle03_prefix_columns_02 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 16 = 29463258272633 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 12 4 22649011561310 6814246711323 arithBundle03_prefix_columns_01 arithBundle03_columns_012
private theorem arithBundle03_prefix_columns_03 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 20 = 35925469283419 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 16 4 29463258272633 6462211010786 arithBundle03_prefix_columns_02 arithBundle03_columns_016
private theorem arithBundle03_prefix_columns_04 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 24 = 42045050754015 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 20 4 35925469283419 6119581470596 arithBundle03_prefix_columns_03 arithBundle03_columns_020
private theorem arithBundle03_prefix_columns_05 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 28 = 47831390761033 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 24 4 42045050754015 5786340007018 arithBundle03_prefix_columns_04 arithBundle03_columns_024
private theorem arithBundle03_prefix_columns_06 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 32 = 53293875851415 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 28 4 47831390761033 5462485090382 arithBundle03_prefix_columns_05 arithBundle03_columns_028
private theorem arithBundle03_prefix_columns_07 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 36 = 58441895597173 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 32 4 53293875851415 5148019745758 arithBundle03_prefix_columns_06 arithBundle03_columns_032
private theorem arithBundle03_prefix_columns_08 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 40 = 63284874684097 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 36 4 58441895597173 4842979086924 arithBundle03_prefix_columns_07 arithBundle03_columns_036
private theorem arithBundle03_prefix_columns_09 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 44 = 67832220291502 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 40 4 63284874684097 4547345607405 arithBundle03_prefix_columns_08 arithBundle03_columns_040
private theorem arithBundle03_prefix_columns_10 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 48 = 72093322413649 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 44 4 67832220291502 4261102122147 arithBundle03_prefix_columns_09 arithBundle03_columns_044
private theorem arithBundle03_prefix_columns_11 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 52 = 76077572376793 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 48 4 72093322413649 3984249963144 arithBundle03_prefix_columns_10 arithBundle03_columns_048
private theorem arithBundle03_prefix_columns_12 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 56 = 79794363132898 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 52 4 76077572376793 3716790756105 arithBundle03_prefix_columns_11 arithBundle03_columns_052
private theorem arithBundle03_prefix_columns_13 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 60 = 83253126485107 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 56 4 79794363132898 3458763352209 arithBundle03_prefix_columns_12 arithBundle03_columns_056
private theorem arithBundle03_prefix_columns_14 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 64 = 86463269121299 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 60 4 83253126485107 3210142636192 arithBundle03_prefix_columns_13 arithBundle03_columns_060
private theorem arithBundle03_prefix_columns_15 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 68 = 89434184766524 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 64 4 86463269121299 2970915645225 arithBundle03_prefix_columns_14 arithBundle03_columns_064
private theorem arithBundle03_prefix_columns_16 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 72 = 92175264690950 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 68 4 89434184766524 2741079924426 arithBundle03_prefix_columns_15 arithBundle03_columns_068
private theorem arithBundle03_prefix_columns_17 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 76 = 94695903744334 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 72 4 92175264690950 2520639053384 arithBundle03_prefix_columns_16 arithBundle03_columns_072
private theorem arithBundle03_prefix_columns_18 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 80 = 97005535291353 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 76 4 94695903744334 2309631547019 arithBundle03_prefix_columns_17 arithBundle03_columns_076
private theorem arithBundle03_prefix_columns_19 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 84 = 99113563139215 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 80 4 97005535291353 2108027847862 arithBundle03_prefix_columns_18 arithBundle03_columns_080
private theorem arithBundle03_prefix_columns_20 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 88 = 101029380472858 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 84 4 99113563139215 1915817333643 arithBundle03_prefix_columns_19 arithBundle03_columns_084
private theorem arithBundle03_prefix_columns_21 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 92 = 102762378596176 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 88 4 101029380472858 1732998123318 arithBundle03_prefix_columns_20 arithBundle03_columns_088
private theorem arithBundle03_prefix_columns_22 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 96 = 104321955057006 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 92 4 102762378596176 1559576460830 arithBundle03_prefix_columns_21 arithBundle03_columns_092
private theorem arithBundle03_prefix_columns_23 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 100 = 105717542964671 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 96 4 104321955057006 1395587907665 arithBundle03_prefix_columns_22 arithBundle03_columns_096
private theorem arithBundle03_prefix_columns_24 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 104 = 106958544201309 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 100 4 105717542964671 1241001236638 arithBundle03_prefix_columns_23 arithBundle03_columns_100
private theorem arithBundle03_prefix_columns_25 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 108 = 108054351598435 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 104 4 106958544201309 1095807397126 arithBundle03_prefix_columns_24 arithBundle03_columns_104
private theorem arithBundle03_prefix_columns_26 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 112 = 109014356146210 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 108 4 108054351598435 960004547775 arithBundle03_prefix_columns_25 arithBundle03_columns_108
private theorem arithBundle03_prefix_columns_27 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 116 = 109847958179826 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 112 4 109014356146210 833602033616 arithBundle03_prefix_columns_26 arithBundle03_columns_112
private theorem arithBundle03_prefix_columns_28 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 120 = 110564590825854 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 116 4 109847958179826 716632646028 arithBundle03_prefix_columns_27 arithBundle03_columns_116
private theorem arithBundle03_prefix_columns_29 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 124 = 111173653732519 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 120 4 110564590825854 609062906665 arithBundle03_prefix_columns_28 arithBundle03_columns_120
private theorem arithBundle03_prefix_columns_30 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 128 = 111684539408915 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 124 4 111173653732519 510885676396 arithBundle03_prefix_columns_29 arithBundle03_columns_124
private theorem arithBundle03_prefix_columns_31 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 132 = 112106638600045 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 128 4 111684539408915 422099191130 arithBundle03_prefix_columns_30 arithBundle03_columns_128
private theorem arithBundle03_prefix_columns_32 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 136 = 112449355245386 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 132 4 112106638600045 342716645341 arithBundle03_prefix_columns_31 arithBundle03_columns_132
private theorem arithBundle03_prefix_columns_33 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 140 = 112722120786687 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 136 4 112449355245386 272765541301 arithBundle03_prefix_columns_32 arithBundle03_columns_136
private theorem arithBundle03_prefix_columns_34 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 144 = 112934305774718 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 140 4 112722120786687 212184988031 arithBundle03_prefix_columns_33 arithBundle03_columns_140
private theorem arithBundle03_prefix_columns_35 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 148 = 113095093880915 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 144 4 112934305774718 160788106197 arithBundle03_prefix_columns_34 arithBundle03_columns_144
private theorem arithBundle03_prefix_columns_36 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 152 = 113213292835803 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 148 4 113095093880915 118198954888 arithBundle03_prefix_columns_35 arithBundle03_columns_148
private theorem arithBundle03_prefix_columns_37 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 156 = 113297191892809 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 152 4 113213292835803 83899057006 arithBundle03_prefix_columns_36 arithBundle03_columns_152
private theorem arithBundle03_prefix_columns_38 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 160 = 113354398472862 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 156 4 113297191892809 57206580053 arithBundle03_prefix_columns_37 arithBundle03_columns_156
private theorem arithBundle03_prefix_columns_39 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 164 = 113391626210201 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 160 4 113354398472862 37227737339 arithBundle03_prefix_columns_38 arithBundle03_columns_160
private theorem arithBundle03_prefix_columns_40 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact06) 0 168 = 113414568346759 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact06) 0 164 4 113391626210201 22942136558 arithBundle03_prefix_columns_39 arithBundle03_columns_164

private theorem arithBundle03_ordinary_ranks : ordinaryRankBound contact06 = 7875595001 := by decide +kernel
private theorem arithBundle03_ranks_000 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 4 = 29869000 :=
  contactRankWindow_of_rec contact06 0 4 29869000 (by decide +kernel)
private theorem arithBundle03_ranks_004 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 4 4 = 28001400 :=
  contactRankWindow_of_rec contact06 4 4 28001400 (by decide +kernel)
private theorem arithBundle03_ranks_008 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 8 4 = 26198760 :=
  contactRankWindow_of_rec contact06 8 4 26198760 (by decide +kernel)
private theorem arithBundle03_ranks_012 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 12 4 = 24461080 :=
  contactRankWindow_of_rec contact06 12 4 24461080 (by decide +kernel)
private theorem arithBundle03_ranks_016 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 16 4 = 22788360 :=
  contactRankWindow_of_rec contact06 16 4 22788360 (by decide +kernel)
private theorem arithBundle03_ranks_020 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 20 4 = 21180600 :=
  contactRankWindow_of_rec contact06 20 4 21180600 (by decide +kernel)
private theorem arithBundle03_ranks_024 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 24 4 = 19637800 :=
  contactRankWindow_of_rec contact06 24 4 19637800 (by decide +kernel)
private theorem arithBundle03_ranks_028 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 28 4 = 18159960 :=
  contactRankWindow_of_rec contact06 28 4 18159960 (by decide +kernel)
private theorem arithBundle03_ranks_032 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 32 4 = 16747080 :=
  contactRankWindow_of_rec contact06 32 4 16747080 (by decide +kernel)
private theorem arithBundle03_ranks_036 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 36 4 = 15399160 :=
  contactRankWindow_of_rec contact06 36 4 15399160 (by decide +kernel)
private theorem arithBundle03_ranks_040 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 40 4 = 14116200 :=
  contactRankWindow_of_rec contact06 40 4 14116200 (by decide +kernel)
private theorem arithBundle03_ranks_044 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 44 4 = 12898200 :=
  contactRankWindow_of_rec contact06 44 4 12898200 (by decide +kernel)
private theorem arithBundle03_ranks_048 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 48 4 = 11745160 :=
  contactRankWindow_of_rec contact06 48 4 11745160 (by decide +kernel)
private theorem arithBundle03_ranks_052 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 52 4 = 10657051 :=
  contactRankWindow_of_rec contact06 52 4 10657051 (by decide +kernel)
private theorem arithBundle03_ranks_056 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 56 4 = 9633259 :=
  contactRankWindow_of_rec contact06 56 4 9633259 (by decide +kernel)
private theorem arithBundle03_ranks_060 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 60 4 = 8672537 :=
  contactRankWindow_of_rec contact06 60 4 8672537 (by decide +kernel)
private theorem arithBundle03_ranks_064 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 64 4 = 7773583 :=
  contactRankWindow_of_rec contact06 64 4 7773583 (by decide +kernel)
private theorem arithBundle03_ranks_068 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 68 4 = 6934816 :=
  contactRankWindow_of_rec contact06 68 4 6934816 (by decide +kernel)
private theorem arithBundle03_ranks_072 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 72 4 = 6154485 :=
  contactRankWindow_of_rec contact06 72 4 6154485 (by decide +kernel)
private theorem arithBundle03_ranks_076 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 76 4 = 5430699 :=
  contactRankWindow_of_rec contact06 76 4 5430699 (by decide +kernel)
private theorem arithBundle03_ranks_080 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 80 4 = 4761592 :=
  contactRankWindow_of_rec contact06 80 4 4761592 (by decide +kernel)
private theorem arithBundle03_ranks_084 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 84 4 = 4145553 :=
  contactRankWindow_of_rec contact06 84 4 4145553 (by decide +kernel)
private theorem arithBundle03_ranks_088 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 88 4 = 3580551 :=
  contactRankWindow_of_rec contact06 88 4 3580551 (by decide +kernel)
private theorem arithBundle03_ranks_092 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 92 4 = 3064720 :=
  contactRankWindow_of_rec contact06 92 4 3064720 (by decide +kernel)
private theorem arithBundle03_ranks_096 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 96 4 = 2596589 :=
  contactRankWindow_of_rec contact06 96 4 2596589 (by decide +kernel)
private theorem arithBundle03_ranks_100 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 100 4 = 2173987 :=
  contactRankWindow_of_rec contact06 100 4 2173987 (by decide +kernel)
private theorem arithBundle03_ranks_104 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 104 4 = 1795048 :=
  contactRankWindow_of_rec contact06 104 4 1795048 (by decide +kernel)
private theorem arithBundle03_ranks_108 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 108 4 = 1458441 :=
  contactRankWindow_of_rec contact06 108 4 1458441 (by decide +kernel)
private theorem arithBundle03_ranks_112 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 112 4 = 1161855 :=
  contactRankWindow_of_rec contact06 112 4 1161855 (by decide +kernel)
private theorem arithBundle03_ranks_116 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 116 4 = 903424 :=
  contactRankWindow_of_rec contact06 116 4 903424 (by decide +kernel)
private theorem arithBundle03_ranks_120 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 120 4 = 681957 :=
  contactRankWindow_of_rec contact06 120 4 681957 (by decide +kernel)
private theorem arithBundle03_ranks_124 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 124 4 = 495003 :=
  contactRankWindow_of_rec contact06 124 4 495003 (by decide +kernel)
private theorem arithBundle03_ranks_128 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 128 4 = 340696 :=
  contactRankWindow_of_rec contact06 128 4 340696 (by decide +kernel)
private theorem arithBundle03_ranks_132 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 132 4 = 217985 :=
  contactRankWindow_of_rec contact06 132 4 217985 (by decide +kernel)
private theorem arithBundle03_ranks_136 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 136 4 = 124279 :=
  contactRankWindow_of_rec contact06 136 4 124279 (by decide +kernel)
private theorem arithBundle03_ranks_140 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 140 4 = 57715 :=
  contactRankWindow_of_rec contact06 140 4 57715 (by decide +kernel)
private theorem arithBundle03_ranks_144 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 144 4 = 17510 :=
  contactRankWindow_of_rec contact06 144 4 17510 (by decide +kernel)
private theorem arithBundle03_ranks_148 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 148 4 = 987 :=
  contactRankWindow_of_rec contact06 148 4 987 (by decide +kernel)
private theorem arithBundle03_ranks_152 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 152 16 = 0 :=
  contactRankWindow_of_rec contact06 152 16 0 (by decide +kernel)
private theorem arithBundle03_prefix_ranks_00 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 8 = 57870400 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 4 4 29869000 28001400 arithBundle03_ranks_000 arithBundle03_ranks_004
private theorem arithBundle03_prefix_ranks_01 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 12 = 84069160 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 8 4 57870400 26198760 arithBundle03_prefix_ranks_00 arithBundle03_ranks_008
private theorem arithBundle03_prefix_ranks_02 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 16 = 108530240 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 12 4 84069160 24461080 arithBundle03_prefix_ranks_01 arithBundle03_ranks_012
private theorem arithBundle03_prefix_ranks_03 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 20 = 131318600 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 16 4 108530240 22788360 arithBundle03_prefix_ranks_02 arithBundle03_ranks_016
private theorem arithBundle03_prefix_ranks_04 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 24 = 152499200 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 20 4 131318600 21180600 arithBundle03_prefix_ranks_03 arithBundle03_ranks_020
private theorem arithBundle03_prefix_ranks_05 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 28 = 172137000 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 24 4 152499200 19637800 arithBundle03_prefix_ranks_04 arithBundle03_ranks_024
private theorem arithBundle03_prefix_ranks_06 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 32 = 190296960 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 28 4 172137000 18159960 arithBundle03_prefix_ranks_05 arithBundle03_ranks_028
private theorem arithBundle03_prefix_ranks_07 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 36 = 207044040 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 32 4 190296960 16747080 arithBundle03_prefix_ranks_06 arithBundle03_ranks_032
private theorem arithBundle03_prefix_ranks_08 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 40 = 222443200 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 36 4 207044040 15399160 arithBundle03_prefix_ranks_07 arithBundle03_ranks_036
private theorem arithBundle03_prefix_ranks_09 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 44 = 236559400 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 40 4 222443200 14116200 arithBundle03_prefix_ranks_08 arithBundle03_ranks_040
private theorem arithBundle03_prefix_ranks_10 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 48 = 249457600 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 44 4 236559400 12898200 arithBundle03_prefix_ranks_09 arithBundle03_ranks_044
private theorem arithBundle03_prefix_ranks_11 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 52 = 261202760 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 48 4 249457600 11745160 arithBundle03_prefix_ranks_10 arithBundle03_ranks_048
private theorem arithBundle03_prefix_ranks_12 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 56 = 271859811 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 52 4 261202760 10657051 arithBundle03_prefix_ranks_11 arithBundle03_ranks_052
private theorem arithBundle03_prefix_ranks_13 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 60 = 281493070 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 56 4 271859811 9633259 arithBundle03_prefix_ranks_12 arithBundle03_ranks_056
private theorem arithBundle03_prefix_ranks_14 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 64 = 290165607 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 60 4 281493070 8672537 arithBundle03_prefix_ranks_13 arithBundle03_ranks_060
private theorem arithBundle03_prefix_ranks_15 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 68 = 297939190 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 64 4 290165607 7773583 arithBundle03_prefix_ranks_14 arithBundle03_ranks_064
private theorem arithBundle03_prefix_ranks_16 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 72 = 304874006 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 68 4 297939190 6934816 arithBundle03_prefix_ranks_15 arithBundle03_ranks_068
private theorem arithBundle03_prefix_ranks_17 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 76 = 311028491 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 72 4 304874006 6154485 arithBundle03_prefix_ranks_16 arithBundle03_ranks_072
private theorem arithBundle03_prefix_ranks_18 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 80 = 316459190 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 76 4 311028491 5430699 arithBundle03_prefix_ranks_17 arithBundle03_ranks_076
private theorem arithBundle03_prefix_ranks_19 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 84 = 321220782 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 80 4 316459190 4761592 arithBundle03_prefix_ranks_18 arithBundle03_ranks_080
private theorem arithBundle03_prefix_ranks_20 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 88 = 325366335 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 84 4 321220782 4145553 arithBundle03_prefix_ranks_19 arithBundle03_ranks_084
private theorem arithBundle03_prefix_ranks_21 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 92 = 328946886 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 88 4 325366335 3580551 arithBundle03_prefix_ranks_20 arithBundle03_ranks_088
private theorem arithBundle03_prefix_ranks_22 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 96 = 332011606 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 92 4 328946886 3064720 arithBundle03_prefix_ranks_21 arithBundle03_ranks_092
private theorem arithBundle03_prefix_ranks_23 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 100 = 334608195 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 96 4 332011606 2596589 arithBundle03_prefix_ranks_22 arithBundle03_ranks_096
private theorem arithBundle03_prefix_ranks_24 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 104 = 336782182 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 100 4 334608195 2173987 arithBundle03_prefix_ranks_23 arithBundle03_ranks_100
private theorem arithBundle03_prefix_ranks_25 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 108 = 338577230 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 104 4 336782182 1795048 arithBundle03_prefix_ranks_24 arithBundle03_ranks_104
private theorem arithBundle03_prefix_ranks_26 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 112 = 340035671 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 108 4 338577230 1458441 arithBundle03_prefix_ranks_25 arithBundle03_ranks_108
private theorem arithBundle03_prefix_ranks_27 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 116 = 341197526 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 112 4 340035671 1161855 arithBundle03_prefix_ranks_26 arithBundle03_ranks_112
private theorem arithBundle03_prefix_ranks_28 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 120 = 342100950 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 116 4 341197526 903424 arithBundle03_prefix_ranks_27 arithBundle03_ranks_116
private theorem arithBundle03_prefix_ranks_29 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 124 = 342782907 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 120 4 342100950 681957 arithBundle03_prefix_ranks_28 arithBundle03_ranks_120
private theorem arithBundle03_prefix_ranks_30 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 128 = 343277910 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 124 4 342782907 495003 arithBundle03_prefix_ranks_29 arithBundle03_ranks_124
private theorem arithBundle03_prefix_ranks_31 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 132 = 343618606 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 128 4 343277910 340696 arithBundle03_prefix_ranks_30 arithBundle03_ranks_128
private theorem arithBundle03_prefix_ranks_32 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 136 = 343836591 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 132 4 343618606 217985 arithBundle03_prefix_ranks_31 arithBundle03_ranks_132
private theorem arithBundle03_prefix_ranks_33 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 140 = 343960870 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 136 4 343836591 124279 arithBundle03_prefix_ranks_32 arithBundle03_ranks_136
private theorem arithBundle03_prefix_ranks_34 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 144 = 344018585 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 140 4 343960870 57715 arithBundle03_prefix_ranks_33 arithBundle03_ranks_140
private theorem arithBundle03_prefix_ranks_35 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 148 = 344036095 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 144 4 344018585 17510 arithBundle03_prefix_ranks_34 arithBundle03_ranks_144
private theorem arithBundle03_prefix_ranks_36 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 152 = 344037082 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 148 4 344036095 987 arithBundle03_prefix_ranks_35 arithBundle03_ranks_148
private theorem arithBundle03_prefix_ranks_37 : arithBundle03_sliceWindow (auxiliaryRankSlice contact06) 0 168 = 344037082 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact06) 0 152 16 344037082 0 arithBundle03_prefix_ranks_36 arithBundle03_ranks_152

theorem contact06_margin : sourceMargin contact06 :=
  arithBundle03_margin_of_checked_counts contact06 168 2041314203461594 113414568346759 7875595001 344037082
    rfl arithBundle03_ordinary_columns arithBundle03_prefix_columns_40 arithBundle03_ordinary_ranks arithBundle03_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle04_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle04_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle04_sliceWindow f a b = x) (hy : arithBundle04_sliceWindow f (a+b) c = y) :
    arithBundle04_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle04_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle04_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle04_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle04_sliceWindow,Nat.zero_add]

private theorem arithBundle04_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle04_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle04_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle04_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle04_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle04_ordinary_columns : ordinaryColumnCount contact09 = 2632191881638212 := by decide +kernel
private theorem arithBundle04_columns_000 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 4 = 6675188143704 :=
  contactColumnsWindow_fast contact09 0 4 6675188143704 (by decide +kernel)
private theorem arithBundle04_columns_004 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 4 4 = 6348322489032 :=
  contactColumnsWindow_fast contact09 4 4 6348322489032 (by decide +kernel)
private theorem arithBundle04_columns_008 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 8 4 = 6029692837188 :=
  contactColumnsWindow_fast contact09 8 4 6029692837188 (by decide +kernel)
private theorem arithBundle04_columns_012 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 12 4 = 5719301978184 :=
  contactColumnsWindow_fast contact09 12 4 5719301978184 (by decide +kernel)
private theorem arithBundle04_columns_016 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 16 4 = 5417148010802 :=
  contactColumnsWindow_fast contact09 16 4 5417148010802 (by decide +kernel)
private theorem arithBundle04_columns_020 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 20 4 = 5123232898156 :=
  contactColumnsWindow_fast contact09 20 4 5123232898156 (by decide +kernel)
private theorem arithBundle04_columns_024 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 24 4 = 4837569564438 :=
  contactColumnsWindow_fast contact09 24 4 4837569564438 (by decide +kernel)
private theorem arithBundle04_columns_028 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 28 4 = 4560176411009 :=
  contactColumnsWindow_fast contact09 28 4 4560176411009 (by decide +kernel)
private theorem arithBundle04_columns_032 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 32 4 = 4291025291232 :=
  contactColumnsWindow_fast contact09 32 4 4291025291232 (by decide +kernel)
private theorem arithBundle04_columns_036 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 36 4 = 4030114173289 :=
  contactColumnsWindow_fast contact09 36 4 4030114173289 (by decide +kernel)
private theorem arithBundle04_columns_040 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 40 4 = 3777444739400 :=
  contactColumnsWindow_fast contact09 40 4 3777444739400 (by decide +kernel)
private theorem arithBundle04_columns_044 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 44 4 = 3533033083380 :=
  contactColumnsWindow_fast contact09 44 4 3533033083380 (by decide +kernel)
private theorem arithBundle04_columns_048 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 48 4 = 3296893026639 :=
  contactColumnsWindow_fast contact09 48 4 3296893026639 (by decide +kernel)
private theorem arithBundle04_columns_052 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 52 4 = 3068996401299 :=
  contactColumnsWindow_fast contact09 52 4 3068996401299 (by decide +kernel)
private theorem arithBundle04_columns_056 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 56 4 = 2849343808572 :=
  contactColumnsWindow_fast contact09 56 4 2849343808572 (by decide +kernel)
private theorem arithBundle04_columns_060 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 60 4 = 2637935061030 :=
  contactColumnsWindow_fast contact09 60 4 2637935061030 (by decide +kernel)
private theorem arithBundle04_columns_064 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 64 4 = 2434792833309 :=
  contactColumnsWindow_fast contact09 64 4 2434792833309 (by decide +kernel)
private theorem arithBundle04_columns_068 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 68 4 = 2239920111780 :=
  contactColumnsWindow_fast contact09 68 4 2239920111780 (by decide +kernel)
private theorem arithBundle04_columns_072 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 72 4 = 2053295615418 :=
  contactColumnsWindow_fast contact09 72 4 2053295615418 (by decide +kernel)
private theorem arithBundle04_columns_076 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 76 4 = 1874915777979 :=
  contactColumnsWindow_fast contact09 76 4 1874915777979 (by decide +kernel)
private theorem arithBundle04_columns_080 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 80 4 = 1704779597844 :=
  contactColumnsWindow_fast contact09 80 4 1704779597844 (by decide +kernel)
private theorem arithBundle04_columns_084 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 84 4 = 1542914277894 :=
  contactColumnsWindow_fast contact09 84 4 1542914277894 (by decide +kernel)
private theorem arithBundle04_columns_088 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 88 4 = 1389314622107 :=
  contactColumnsWindow_fast contact09 88 4 1389314622107 (by decide +kernel)
private theorem arithBundle04_columns_092 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 92 4 = 1243962942708 :=
  contactColumnsWindow_fast contact09 92 4 1243962942708 (by decide +kernel)
private theorem arithBundle04_columns_096 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 96 4 = 1106855816562 :=
  contactColumnsWindow_fast contact09 96 4 1106855816562 (by decide +kernel)
private theorem arithBundle04_columns_100 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 100 4 = 977992599994 :=
  contactColumnsWindow_fast contact09 100 4 977992599994 (by decide +kernel)
private theorem arithBundle04_columns_104 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 104 4 = 857403879228 :=
  contactColumnsWindow_fast contact09 104 4 857403879228 (by decide +kernel)
private theorem arithBundle04_columns_108 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 108 4 = 745077333125 :=
  contactColumnsWindow_fast contact09 108 4 745077333125 (by decide +kernel)
private theorem arithBundle04_columns_112 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 112 4 = 640998304794 :=
  contactColumnsWindow_fast contact09 112 4 640998304794 (by decide +kernel)
private theorem arithBundle04_columns_116 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 116 4 = 545163951600 :=
  contactColumnsWindow_fast contact09 116 4 545163951600 (by decide +kernel)
private theorem arithBundle04_columns_120 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 120 4 = 457574497624 :=
  contactColumnsWindow_fast contact09 120 4 457574497624 (by decide +kernel)
private theorem arithBundle04_columns_124 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 124 4 = 378261521082 :=
  contactColumnsWindow_fast contact09 124 4 378261521082 (by decide +kernel)
private theorem arithBundle04_columns_128 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 128 4 = 307208084672 :=
  contactColumnsWindow_fast contact09 128 4 307208084672 (by decide +kernel)
private theorem arithBundle04_columns_132 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 132 4 = 244401885121 :=
  contactColumnsWindow_fast contact09 132 4 244401885121 (by decide +kernel)
private theorem arithBundle04_columns_136 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 136 4 = 189837824577 :=
  contactColumnsWindow_fast contact09 136 4 189837824577 (by decide +kernel)
private theorem arithBundle04_columns_140 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 140 4 = 143451442042 :=
  contactColumnsWindow_fast contact09 140 4 143451442042 (by decide +kernel)
private theorem arithBundle04_columns_144 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 144 4 = 105018756101 :=
  contactColumnsWindow_fast contact09 144 4 105018756101 (by decide +kernel)
private theorem arithBundle04_columns_148 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 148 4 = 74083293136 :=
  contactColumnsWindow_fast contact09 148 4 74083293136 (by decide +kernel)
private theorem arithBundle04_columns_152 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 152 4 = 50040186603 :=
  contactColumnsWindow_fast contact09 152 4 50040186603 (by decide +kernel)
private theorem arithBundle04_columns_156 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 156 4 = 32131907925 :=
  contactColumnsWindow_fast contact09 156 4 32131907925 (by decide +kernel)
private theorem arithBundle04_columns_160 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 160 4 = 19445533266 :=
  contactColumnsWindow_fast contact09 160 4 19445533266 (by decide +kernel)
private theorem arithBundle04_columns_164 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 164 3 = 8829811394 :=
  contactColumnsWindow_fast contact09 164 3 8829811394 (by decide +kernel)
private theorem arithBundle04_prefix_columns_00 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 8 = 13023510632736 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 4 4 6675188143704 6348322489032 arithBundle04_columns_000 arithBundle04_columns_004
private theorem arithBundle04_prefix_columns_01 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 12 = 19053203469924 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 8 4 13023510632736 6029692837188 arithBundle04_prefix_columns_00 arithBundle04_columns_008
private theorem arithBundle04_prefix_columns_02 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 16 = 24772505448108 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 12 4 19053203469924 5719301978184 arithBundle04_prefix_columns_01 arithBundle04_columns_012
private theorem arithBundle04_prefix_columns_03 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 20 = 30189653458910 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 16 4 24772505448108 5417148010802 arithBundle04_prefix_columns_02 arithBundle04_columns_016
private theorem arithBundle04_prefix_columns_04 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 24 = 35312886357066 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 20 4 30189653458910 5123232898156 arithBundle04_prefix_columns_03 arithBundle04_columns_020
private theorem arithBundle04_prefix_columns_05 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 28 = 40150455921504 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 24 4 35312886357066 4837569564438 arithBundle04_prefix_columns_04 arithBundle04_columns_024
private theorem arithBundle04_prefix_columns_06 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 32 = 44710632332513 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 28 4 40150455921504 4560176411009 arithBundle04_prefix_columns_05 arithBundle04_columns_028
private theorem arithBundle04_prefix_columns_07 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 36 = 49001657623745 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 32 4 44710632332513 4291025291232 arithBundle04_prefix_columns_06 arithBundle04_columns_032
private theorem arithBundle04_prefix_columns_08 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 40 = 53031771797034 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 36 4 49001657623745 4030114173289 arithBundle04_prefix_columns_07 arithBundle04_columns_036
private theorem arithBundle04_prefix_columns_09 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 44 = 56809216536434 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 40 4 53031771797034 3777444739400 arithBundle04_prefix_columns_08 arithBundle04_columns_040
private theorem arithBundle04_prefix_columns_10 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 48 = 60342249619814 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 44 4 56809216536434 3533033083380 arithBundle04_prefix_columns_09 arithBundle04_columns_044
private theorem arithBundle04_prefix_columns_11 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 52 = 63639142646453 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 48 4 60342249619814 3296893026639 arithBundle04_prefix_columns_10 arithBundle04_columns_048
private theorem arithBundle04_prefix_columns_12 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 56 = 66708139047752 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 52 4 63639142646453 3068996401299 arithBundle04_prefix_columns_11 arithBundle04_columns_052
private theorem arithBundle04_prefix_columns_13 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 60 = 69557482856324 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 56 4 66708139047752 2849343808572 arithBundle04_prefix_columns_12 arithBundle04_columns_056
private theorem arithBundle04_prefix_columns_14 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 64 = 72195417917354 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 60 4 69557482856324 2637935061030 arithBundle04_prefix_columns_13 arithBundle04_columns_060
private theorem arithBundle04_prefix_columns_15 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 68 = 74630210750663 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 64 4 72195417917354 2434792833309 arithBundle04_prefix_columns_14 arithBundle04_columns_064
private theorem arithBundle04_prefix_columns_16 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 72 = 76870130862443 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 68 4 74630210750663 2239920111780 arithBundle04_prefix_columns_15 arithBundle04_columns_068
private theorem arithBundle04_prefix_columns_17 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 76 = 78923426477861 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 72 4 76870130862443 2053295615418 arithBundle04_prefix_columns_16 arithBundle04_columns_072
private theorem arithBundle04_prefix_columns_18 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 80 = 80798342255840 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 76 4 78923426477861 1874915777979 arithBundle04_prefix_columns_17 arithBundle04_columns_076
private theorem arithBundle04_prefix_columns_19 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 84 = 82503121853684 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 80 4 80798342255840 1704779597844 arithBundle04_prefix_columns_18 arithBundle04_columns_080
private theorem arithBundle04_prefix_columns_20 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 88 = 84046036131578 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 84 4 82503121853684 1542914277894 arithBundle04_prefix_columns_19 arithBundle04_columns_084
private theorem arithBundle04_prefix_columns_21 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 92 = 85435350753685 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 88 4 84046036131578 1389314622107 arithBundle04_prefix_columns_20 arithBundle04_columns_088
private theorem arithBundle04_prefix_columns_22 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 96 = 86679313696393 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 92 4 85435350753685 1243962942708 arithBundle04_prefix_columns_21 arithBundle04_columns_092
private theorem arithBundle04_prefix_columns_23 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 100 = 87786169512955 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 96 4 86679313696393 1106855816562 arithBundle04_prefix_columns_22 arithBundle04_columns_096
private theorem arithBundle04_prefix_columns_24 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 104 = 88764162112949 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 100 4 87786169512955 977992599994 arithBundle04_prefix_columns_23 arithBundle04_columns_100
private theorem arithBundle04_prefix_columns_25 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 108 = 89621565992177 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 104 4 88764162112949 857403879228 arithBundle04_prefix_columns_24 arithBundle04_columns_104
private theorem arithBundle04_prefix_columns_26 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 112 = 90366643325302 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 108 4 89621565992177 745077333125 arithBundle04_prefix_columns_25 arithBundle04_columns_108
private theorem arithBundle04_prefix_columns_27 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 116 = 91007641630096 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 112 4 90366643325302 640998304794 arithBundle04_prefix_columns_26 arithBundle04_columns_112
private theorem arithBundle04_prefix_columns_28 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 120 = 91552805581696 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 116 4 91007641630096 545163951600 arithBundle04_prefix_columns_27 arithBundle04_columns_116
private theorem arithBundle04_prefix_columns_29 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 124 = 92010380079320 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 120 4 91552805581696 457574497624 arithBundle04_prefix_columns_28 arithBundle04_columns_120
private theorem arithBundle04_prefix_columns_30 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 128 = 92388641600402 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 124 4 92010380079320 378261521082 arithBundle04_prefix_columns_29 arithBundle04_columns_124
private theorem arithBundle04_prefix_columns_31 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 132 = 92695849685074 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 128 4 92388641600402 307208084672 arithBundle04_prefix_columns_30 arithBundle04_columns_128
private theorem arithBundle04_prefix_columns_32 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 136 = 92940251570195 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 132 4 92695849685074 244401885121 arithBundle04_prefix_columns_31 arithBundle04_columns_132
private theorem arithBundle04_prefix_columns_33 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 140 = 93130089394772 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 136 4 92940251570195 189837824577 arithBundle04_prefix_columns_32 arithBundle04_columns_136
private theorem arithBundle04_prefix_columns_34 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 144 = 93273540836814 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 140 4 93130089394772 143451442042 arithBundle04_prefix_columns_33 arithBundle04_columns_140
private theorem arithBundle04_prefix_columns_35 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 148 = 93378559592915 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 144 4 93273540836814 105018756101 arithBundle04_prefix_columns_34 arithBundle04_columns_144
private theorem arithBundle04_prefix_columns_36 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 152 = 93452642886051 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 148 4 93378559592915 74083293136 arithBundle04_prefix_columns_35 arithBundle04_columns_148
private theorem arithBundle04_prefix_columns_37 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 156 = 93502683072654 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 152 4 93452642886051 50040186603 arithBundle04_prefix_columns_36 arithBundle04_columns_152
private theorem arithBundle04_prefix_columns_38 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 160 = 93534814980579 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 156 4 93502683072654 32131907925 arithBundle04_prefix_columns_37 arithBundle04_columns_156
private theorem arithBundle04_prefix_columns_39 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 164 = 93554260513845 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 160 4 93534814980579 19445533266 arithBundle04_prefix_columns_38 arithBundle04_columns_160
private theorem arithBundle04_prefix_columns_40 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact09) 0 167 = 93563090325239 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact09) 0 164 3 93554260513845 8829811394 arithBundle04_prefix_columns_39 arithBundle04_columns_164

private theorem arithBundle04_ordinary_ranks : ordinaryRankBound contact09 = 10115258601 := by decide +kernel
private theorem arithBundle04_ranks_000 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 4 = 25172484 :=
  contactRankWindow_of_rec contact09 0 4 25172484 (by decide +kernel)
private theorem arithBundle04_ranks_004 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 4 4 = 23561556 :=
  contactRankWindow_of_rec contact09 4 4 23561556 (by decide +kernel)
private theorem arithBundle04_ranks_008 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 8 4 = 22007652 :=
  contactRankWindow_of_rec contact09 8 4 22007652 (by decide +kernel)
private theorem arithBundle04_ranks_012 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 12 4 = 20510772 :=
  contactRankWindow_of_rec contact09 12 4 20510772 (by decide +kernel)
private theorem arithBundle04_ranks_016 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 16 4 = 19070916 :=
  contactRankWindow_of_rec contact09 16 4 19070916 (by decide +kernel)
private theorem arithBundle04_ranks_020 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 20 4 = 17688084 :=
  contactRankWindow_of_rec contact09 20 4 17688084 (by decide +kernel)
private theorem arithBundle04_ranks_024 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 24 4 = 16362276 :=
  contactRankWindow_of_rec contact09 24 4 16362276 (by decide +kernel)
private theorem arithBundle04_ranks_028 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 28 4 = 15093492 :=
  contactRankWindow_of_rec contact09 28 4 15093492 (by decide +kernel)
private theorem arithBundle04_ranks_032 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 32 4 = 13881732 :=
  contactRankWindow_of_rec contact09 32 4 13881732 (by decide +kernel)
private theorem arithBundle04_ranks_036 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 36 4 = 12726996 :=
  contactRankWindow_of_rec contact09 36 4 12726996 (by decide +kernel)
private theorem arithBundle04_ranks_040 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 40 4 = 11629284 :=
  contactRankWindow_of_rec contact09 40 4 11629284 (by decide +kernel)
private theorem arithBundle04_ranks_044 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 44 4 = 10588596 :=
  contactRankWindow_of_rec contact09 44 4 10588596 (by decide +kernel)
private theorem arithBundle04_ranks_048 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 48 4 = 9604932 :=
  contactRankWindow_of_rec contact09 48 4 9604932 (by decide +kernel)
private theorem arithBundle04_ranks_052 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 52 4 = 8678292 :=
  contactRankWindow_of_rec contact09 52 4 8678292 (by decide +kernel)
private theorem arithBundle04_ranks_056 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 56 4 = 7808486 :=
  contactRankWindow_of_rec contact09 56 4 7808486 (by decide +kernel)
private theorem arithBundle04_ranks_060 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 60 4 = 6994528 :=
  contactRankWindow_of_rec contact09 60 4 6994528 (by decide +kernel)
private theorem arithBundle04_ranks_064 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 64 4 = 6235240 :=
  contactRankWindow_of_rec contact09 64 4 6235240 (by decide +kernel)
private theorem arithBundle04_ranks_068 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 68 4 = 5529325 :=
  contactRankWindow_of_rec contact09 68 4 5529325 (by decide +kernel)
private theorem arithBundle04_ranks_072 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 72 4 = 4875143 :=
  contactRankWindow_of_rec contact09 72 4 4875143 (by decide +kernel)
private theorem arithBundle04_ranks_076 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 76 4 = 4270944 :=
  contactRankWindow_of_rec contact09 76 4 4270944 (by decide +kernel)
private theorem arithBundle04_ranks_080 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 80 4 = 3715153 :=
  contactRankWindow_of_rec contact09 80 4 3715153 (by decide +kernel)
private theorem arithBundle04_ranks_084 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 84 4 = 3205931 :=
  contactRankWindow_of_rec contact09 84 4 3205931 (by decide +kernel)
private theorem arithBundle04_ranks_088 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 88 4 = 2741528 :=
  contactRankWindow_of_rec contact09 88 4 2741528 (by decide +kernel)
private theorem arithBundle04_ranks_092 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 92 4 = 2320501 :=
  contactRankWindow_of_rec contact09 92 4 2320501 (by decide +kernel)
private theorem arithBundle04_ranks_096 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 96 4 = 1940879 :=
  contactRankWindow_of_rec contact09 96 4 1940879 (by decide +kernel)
private theorem arithBundle04_ranks_100 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 100 4 = 1600912 :=
  contactRankWindow_of_rec contact09 100 4 1600912 (by decide +kernel)
private theorem arithBundle04_ranks_104 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 104 4 = 1299289 :=
  contactRankWindow_of_rec contact09 104 4 1299289 (by decide +kernel)
private theorem arithBundle04_ranks_108 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 108 4 = 1033907 :=
  contactRankWindow_of_rec contact09 108 4 1033907 (by decide +kernel)
private theorem arithBundle04_ranks_112 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 112 4 = 803016 :=
  contactRankWindow_of_rec contact09 112 4 803016 (by decide +kernel)
private theorem arithBundle04_ranks_116 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 116 4 = 605437 :=
  contactRankWindow_of_rec contact09 116 4 605437 (by decide +kernel)
private theorem arithBundle04_ranks_120 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 120 4 = 438935 :=
  contactRankWindow_of_rec contact09 120 4 438935 (by decide +kernel)
private theorem arithBundle04_ranks_124 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 124 4 = 301760 :=
  contactRankWindow_of_rec contact09 124 4 301760 (by decide +kernel)
private theorem arithBundle04_ranks_128 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 128 4 = 192865 :=
  contactRankWindow_of_rec contact09 128 4 192865 (by decide +kernel)
private theorem arithBundle04_ranks_132 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 132 4 = 109883 :=
  contactRankWindow_of_rec contact09 132 4 109883 (by decide +kernel)
private theorem arithBundle04_ranks_136 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 136 4 = 51064 :=
  contactRankWindow_of_rec contact09 136 4 51064 (by decide +kernel)
private theorem arithBundle04_ranks_140 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 140 4 = 15527 :=
  contactRankWindow_of_rec contact09 140 4 15527 (by decide +kernel)
private theorem arithBundle04_ranks_144 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 144 4 = 876 :=
  contactRankWindow_of_rec contact09 144 4 876 (by decide +kernel)
private theorem arithBundle04_ranks_148 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 148 19 = 0 :=
  contactRankWindow_of_rec contact09 148 19 0 (by decide +kernel)
private theorem arithBundle04_prefix_ranks_00 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 8 = 48734040 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 4 4 25172484 23561556 arithBundle04_ranks_000 arithBundle04_ranks_004
private theorem arithBundle04_prefix_ranks_01 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 12 = 70741692 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 8 4 48734040 22007652 arithBundle04_prefix_ranks_00 arithBundle04_ranks_008
private theorem arithBundle04_prefix_ranks_02 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 16 = 91252464 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 12 4 70741692 20510772 arithBundle04_prefix_ranks_01 arithBundle04_ranks_012
private theorem arithBundle04_prefix_ranks_03 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 20 = 110323380 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 16 4 91252464 19070916 arithBundle04_prefix_ranks_02 arithBundle04_ranks_016
private theorem arithBundle04_prefix_ranks_04 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 24 = 128011464 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 20 4 110323380 17688084 arithBundle04_prefix_ranks_03 arithBundle04_ranks_020
private theorem arithBundle04_prefix_ranks_05 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 28 = 144373740 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 24 4 128011464 16362276 arithBundle04_prefix_ranks_04 arithBundle04_ranks_024
private theorem arithBundle04_prefix_ranks_06 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 32 = 159467232 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 28 4 144373740 15093492 arithBundle04_prefix_ranks_05 arithBundle04_ranks_028
private theorem arithBundle04_prefix_ranks_07 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 36 = 173348964 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 32 4 159467232 13881732 arithBundle04_prefix_ranks_06 arithBundle04_ranks_032
private theorem arithBundle04_prefix_ranks_08 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 40 = 186075960 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 36 4 173348964 12726996 arithBundle04_prefix_ranks_07 arithBundle04_ranks_036
private theorem arithBundle04_prefix_ranks_09 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 44 = 197705244 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 40 4 186075960 11629284 arithBundle04_prefix_ranks_08 arithBundle04_ranks_040
private theorem arithBundle04_prefix_ranks_10 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 48 = 208293840 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 44 4 197705244 10588596 arithBundle04_prefix_ranks_09 arithBundle04_ranks_044
private theorem arithBundle04_prefix_ranks_11 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 52 = 217898772 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 48 4 208293840 9604932 arithBundle04_prefix_ranks_10 arithBundle04_ranks_048
private theorem arithBundle04_prefix_ranks_12 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 56 = 226577064 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 52 4 217898772 8678292 arithBundle04_prefix_ranks_11 arithBundle04_ranks_052
private theorem arithBundle04_prefix_ranks_13 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 60 = 234385550 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 56 4 226577064 7808486 arithBundle04_prefix_ranks_12 arithBundle04_ranks_056
private theorem arithBundle04_prefix_ranks_14 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 64 = 241380078 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 60 4 234385550 6994528 arithBundle04_prefix_ranks_13 arithBundle04_ranks_060
private theorem arithBundle04_prefix_ranks_15 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 68 = 247615318 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 64 4 241380078 6235240 arithBundle04_prefix_ranks_14 arithBundle04_ranks_064
private theorem arithBundle04_prefix_ranks_16 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 72 = 253144643 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 68 4 247615318 5529325 arithBundle04_prefix_ranks_15 arithBundle04_ranks_068
private theorem arithBundle04_prefix_ranks_17 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 76 = 258019786 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 72 4 253144643 4875143 arithBundle04_prefix_ranks_16 arithBundle04_ranks_072
private theorem arithBundle04_prefix_ranks_18 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 80 = 262290730 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 76 4 258019786 4270944 arithBundle04_prefix_ranks_17 arithBundle04_ranks_076
private theorem arithBundle04_prefix_ranks_19 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 84 = 266005883 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 80 4 262290730 3715153 arithBundle04_prefix_ranks_18 arithBundle04_ranks_080
private theorem arithBundle04_prefix_ranks_20 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 88 = 269211814 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 84 4 266005883 3205931 arithBundle04_prefix_ranks_19 arithBundle04_ranks_084
private theorem arithBundle04_prefix_ranks_21 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 92 = 271953342 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 88 4 269211814 2741528 arithBundle04_prefix_ranks_20 arithBundle04_ranks_088
private theorem arithBundle04_prefix_ranks_22 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 96 = 274273843 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 92 4 271953342 2320501 arithBundle04_prefix_ranks_21 arithBundle04_ranks_092
private theorem arithBundle04_prefix_ranks_23 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 100 = 276214722 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 96 4 274273843 1940879 arithBundle04_prefix_ranks_22 arithBundle04_ranks_096
private theorem arithBundle04_prefix_ranks_24 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 104 = 277815634 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 100 4 276214722 1600912 arithBundle04_prefix_ranks_23 arithBundle04_ranks_100
private theorem arithBundle04_prefix_ranks_25 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 108 = 279114923 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 104 4 277815634 1299289 arithBundle04_prefix_ranks_24 arithBundle04_ranks_104
private theorem arithBundle04_prefix_ranks_26 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 112 = 280148830 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 108 4 279114923 1033907 arithBundle04_prefix_ranks_25 arithBundle04_ranks_108
private theorem arithBundle04_prefix_ranks_27 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 116 = 280951846 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 112 4 280148830 803016 arithBundle04_prefix_ranks_26 arithBundle04_ranks_112
private theorem arithBundle04_prefix_ranks_28 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 120 = 281557283 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 116 4 280951846 605437 arithBundle04_prefix_ranks_27 arithBundle04_ranks_116
private theorem arithBundle04_prefix_ranks_29 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 124 = 281996218 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 120 4 281557283 438935 arithBundle04_prefix_ranks_28 arithBundle04_ranks_120
private theorem arithBundle04_prefix_ranks_30 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 128 = 282297978 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 124 4 281996218 301760 arithBundle04_prefix_ranks_29 arithBundle04_ranks_124
private theorem arithBundle04_prefix_ranks_31 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 132 = 282490843 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 128 4 282297978 192865 arithBundle04_prefix_ranks_30 arithBundle04_ranks_128
private theorem arithBundle04_prefix_ranks_32 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 136 = 282600726 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 132 4 282490843 109883 arithBundle04_prefix_ranks_31 arithBundle04_ranks_132
private theorem arithBundle04_prefix_ranks_33 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 140 = 282651790 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 136 4 282600726 51064 arithBundle04_prefix_ranks_32 arithBundle04_ranks_136
private theorem arithBundle04_prefix_ranks_34 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 144 = 282667317 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 140 4 282651790 15527 arithBundle04_prefix_ranks_33 arithBundle04_ranks_140
private theorem arithBundle04_prefix_ranks_35 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 148 = 282668193 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 144 4 282667317 876 arithBundle04_prefix_ranks_34 arithBundle04_ranks_144
private theorem arithBundle04_prefix_ranks_36 : arithBundle04_sliceWindow (auxiliaryRankSlice contact09) 0 167 = 282668193 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact09) 0 148 19 282668193 0 arithBundle04_prefix_ranks_35 arithBundle04_ranks_148

theorem contact09_margin : sourceMargin contact09 :=
  arithBundle04_margin_of_checked_counts contact09 167 2632191881638212 93563090325239 10115258601 282668193
    rfl arithBundle04_ordinary_columns arithBundle04_prefix_columns_40 arithBundle04_ordinary_ranks arithBundle04_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle05_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle05_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle05_sliceWindow f a b = x) (hy : arithBundle05_sliceWindow f (a+b) c = y) :
    arithBundle05_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle05_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle05_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle05_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle05_sliceWindow,Nat.zero_add]

private theorem arithBundle05_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle05_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle05_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle05_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle05_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle05_ordinary_columns : ordinaryColumnCount contact10 = 3730140481054016 := by decide +kernel
private theorem arithBundle05_columns_000 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 4 = 10383905292608 :=
  contactColumnsWindow_fast contact10 0 4 10383905292608 (by decide +kernel)
private theorem arithBundle05_columns_004 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 4 4 = 9907534026048 :=
  contactColumnsWindow_fast contact10 4 4 9907534026048 (by decide +kernel)
private theorem arithBundle05_columns_008 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 8 4 = 9442402023744 :=
  contactColumnsWindow_fast contact10 8 4 9442402023744 (by decide +kernel)
private theorem arithBundle05_columns_012 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 12 4 = 8988509285696 :=
  contactColumnsWindow_fast contact10 12 4 8988509285696 (by decide +kernel)
private theorem arithBundle05_columns_016 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 16 4 = 8545855811904 :=
  contactColumnsWindow_fast contact10 16 4 8545855811904 (by decide +kernel)
private theorem arithBundle05_columns_020 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 20 4 = 8114441602368 :=
  contactColumnsWindow_fast contact10 20 4 8114441602368 (by decide +kernel)
private theorem arithBundle05_columns_024 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 24 4 = 7694266657088 :=
  contactColumnsWindow_fast contact10 24 4 7694266657088 (by decide +kernel)
private theorem arithBundle05_columns_028 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 28 4 = 7285362308864 :=
  contactColumnsWindow_fast contact10 28 4 7285362308864 (by decide +kernel)
private theorem arithBundle05_columns_032 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 32 4 = 6887748649696 :=
  contactColumnsWindow_fast contact10 32 4 6887748649696 (by decide +kernel)
private theorem arithBundle05_columns_036 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 36 4 = 6501377359460 :=
  contactColumnsWindow_fast contact10 36 4 6501377359460 (by decide +kernel)
private theorem arithBundle05_columns_040 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 40 4 = 6126248341039 :=
  contactColumnsWindow_fast contact10 40 4 6126248341039 (by decide +kernel)
private theorem arithBundle05_columns_044 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 44 4 = 5762362575628 :=
  contactColumnsWindow_fast contact10 44 4 5762362575628 (by decide +kernel)
private theorem arithBundle05_columns_048 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 48 4 = 5409757401102 :=
  contactColumnsWindow_fast contact10 48 4 5409757401102 (by decide +kernel)
private theorem arithBundle05_columns_052 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 52 4 = 5068439998820 :=
  contactColumnsWindow_fast contact10 52 4 5068439998820 (by decide +kernel)
private theorem arithBundle05_columns_056 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 56 4 = 4738367753832 :=
  contactColumnsWindow_fast contact10 56 4 4738367753832 (by decide +kernel)
private theorem arithBundle05_columns_060 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 60 4 = 4419542419082 :=
  contactColumnsWindow_fast contact10 60 4 4419542419082 (by decide +kernel)
private theorem arithBundle05_columns_064 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 64 4 = 4111962774974 :=
  contactColumnsWindow_fast contact10 64 4 4111962774974 (by decide +kernel)
private theorem arithBundle05_columns_068 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 68 4 = 3815676115927 :=
  contactColumnsWindow_fast contact10 68 4 3815676115927 (by decide +kernel)
private theorem arithBundle05_columns_072 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 72 4 = 3530672462605 :=
  contactColumnsWindow_fast contact10 72 4 3530672462605 (by decide +kernel)
private theorem arithBundle05_columns_076 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 76 4 = 3256919398986 :=
  contactColumnsWindow_fast contact10 76 4 3256919398986 (by decide +kernel)
private theorem arithBundle05_columns_080 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 80 4 = 2994415644077 :=
  contactColumnsWindow_fast contact10 80 4 2994415644077 (by decide +kernel)
private theorem arithBundle05_columns_084 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 84 4 = 2743163270045 :=
  contactColumnsWindow_fast contact10 84 4 2743163270045 (by decide +kernel)
private theorem arithBundle05_columns_088 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 88 4 = 2503210332714 :=
  contactColumnsWindow_fast contact10 88 4 2503210332714 (by decide +kernel)
private theorem arithBundle05_columns_092 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 92 4 = 2274533785627 :=
  contactColumnsWindow_fast contact10 92 4 2274533785627 (by decide +kernel)
private theorem arithBundle05_columns_096 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 96 4 = 2057107769508 :=
  contactColumnsWindow_fast contact10 96 4 2057107769508 (by decide +kernel)
private theorem arithBundle05_columns_100 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 100 4 = 1850931210150 :=
  contactColumnsWindow_fast contact10 100 4 1850931210150 (by decide +kernel)
private theorem arithBundle05_columns_104 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 104 4 = 1656007854857 :=
  contactColumnsWindow_fast contact10 104 4 1656007854857 (by decide +kernel)
private theorem arithBundle05_columns_108 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 108 4 = 1472387140188 :=
  contactColumnsWindow_fast contact10 108 4 1472387140188 (by decide +kernel)
private theorem arithBundle05_columns_112 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 112 4 = 1300037679145 :=
  contactColumnsWindow_fast contact10 112 4 1300037679145 (by decide +kernel)
private theorem arithBundle05_columns_116 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 116 4 = 1138938793308 :=
  contactColumnsWindow_fast contact10 116 4 1138938793308 (by decide +kernel)
private theorem arithBundle05_columns_120 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 120 4 = 989089574472 :=
  contactColumnsWindow_fast contact10 120 4 989089574472 (by decide +kernel)
private theorem arithBundle05_columns_124 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 124 4 = 850495010795 :=
  contactColumnsWindow_fast contact10 124 4 850495010795 (by decide +kernel)
private theorem arithBundle05_columns_128 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 128 4 = 723206531700 :=
  contactColumnsWindow_fast contact10 128 4 723206531700 (by decide +kernel)
private theorem arithBundle05_columns_132 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 132 4 = 607184384444 :=
  contactColumnsWindow_fast contact10 132 4 607184384444 (by decide +kernel)
private theorem arithBundle05_columns_136 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 136 4 = 502412456589 :=
  contactColumnsWindow_fast contact10 136 4 502412456589 (by decide +kernel)
private theorem arithBundle05_columns_140 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 140 4 = 408890484159 :=
  contactColumnsWindow_fast contact10 140 4 408890484159 (by decide +kernel)
private theorem arithBundle05_columns_144 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 144 4 = 326611075063 :=
  contactColumnsWindow_fast contact10 144 4 326611075063 (by decide +kernel)
private theorem arithBundle05_columns_148 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 148 4 = 255484810239 :=
  contactColumnsWindow_fast contact10 148 4 255484810239 (by decide +kernel)
private theorem arithBundle05_columns_152 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 152 4 = 195120324315 :=
  contactColumnsWindow_fast contact10 152 4 195120324315 (by decide +kernel)
private theorem arithBundle05_columns_156 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 156 4 = 144988298228 :=
  contactColumnsWindow_fast contact10 156 4 144988298228 (by decide +kernel)
private theorem arithBundle05_columns_160 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 160 4 = 104410184827 :=
  contactColumnsWindow_fast contact10 160 4 104410184827 (by decide +kernel)
private theorem arithBundle05_columns_164 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 164 4 = 72552700301 :=
  contactColumnsWindow_fast contact10 164 4 72552700301 (by decide +kernel)
private theorem arithBundle05_columns_168 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 168 4 = 48438490424 :=
  contactColumnsWindow_fast contact10 168 4 48438490424 (by decide +kernel)
private theorem arithBundle05_columns_172 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 172 4 = 30868259737 :=
  contactColumnsWindow_fast contact10 172 4 30868259737 (by decide +kernel)
private theorem arithBundle05_columns_176 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 176 1 = 5620597436 :=
  contactColumnsWindow_fast contact10 176 1 5620597436 (by decide +kernel)
private theorem arithBundle05_prefix_columns_00 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 8 = 20291439318656 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 4 4 10383905292608 9907534026048 arithBundle05_columns_000 arithBundle05_columns_004
private theorem arithBundle05_prefix_columns_01 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 12 = 29733841342400 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 8 4 20291439318656 9442402023744 arithBundle05_prefix_columns_00 arithBundle05_columns_008
private theorem arithBundle05_prefix_columns_02 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 16 = 38722350628096 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 12 4 29733841342400 8988509285696 arithBundle05_prefix_columns_01 arithBundle05_columns_012
private theorem arithBundle05_prefix_columns_03 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 20 = 47268206440000 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 16 4 38722350628096 8545855811904 arithBundle05_prefix_columns_02 arithBundle05_columns_016
private theorem arithBundle05_prefix_columns_04 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 24 = 55382648042368 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 20 4 47268206440000 8114441602368 arithBundle05_prefix_columns_03 arithBundle05_columns_020
private theorem arithBundle05_prefix_columns_05 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 28 = 63076914699456 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 24 4 55382648042368 7694266657088 arithBundle05_prefix_columns_04 arithBundle05_columns_024
private theorem arithBundle05_prefix_columns_06 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 32 = 70362277008320 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 28 4 63076914699456 7285362308864 arithBundle05_prefix_columns_05 arithBundle05_columns_028
private theorem arithBundle05_prefix_columns_07 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 36 = 77250025658016 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 32 4 70362277008320 6887748649696 arithBundle05_prefix_columns_06 arithBundle05_columns_032
private theorem arithBundle05_prefix_columns_08 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 40 = 83751403017476 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 36 4 77250025658016 6501377359460 arithBundle05_prefix_columns_07 arithBundle05_columns_036
private theorem arithBundle05_prefix_columns_09 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 44 = 89877651358515 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 40 4 83751403017476 6126248341039 arithBundle05_prefix_columns_08 arithBundle05_columns_040
private theorem arithBundle05_prefix_columns_10 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 48 = 95640013934143 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 44 4 89877651358515 5762362575628 arithBundle05_prefix_columns_09 arithBundle05_columns_044
private theorem arithBundle05_prefix_columns_11 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 52 = 101049771335245 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 48 4 95640013934143 5409757401102 arithBundle05_prefix_columns_10 arithBundle05_columns_048
private theorem arithBundle05_prefix_columns_12 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 56 = 106118211334065 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 52 4 101049771335245 5068439998820 arithBundle05_prefix_columns_11 arithBundle05_columns_052
private theorem arithBundle05_prefix_columns_13 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 60 = 110856579087897 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 56 4 106118211334065 4738367753832 arithBundle05_prefix_columns_12 arithBundle05_columns_056
private theorem arithBundle05_prefix_columns_14 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 64 = 115276121506979 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 60 4 110856579087897 4419542419082 arithBundle05_prefix_columns_13 arithBundle05_columns_060
private theorem arithBundle05_prefix_columns_15 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 68 = 119388084281953 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 64 4 115276121506979 4111962774974 arithBundle05_prefix_columns_14 arithBundle05_columns_064
private theorem arithBundle05_prefix_columns_16 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 72 = 123203760397880 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 68 4 119388084281953 3815676115927 arithBundle05_prefix_columns_15 arithBundle05_columns_068
private theorem arithBundle05_prefix_columns_17 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 76 = 126734432860485 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 72 4 123203760397880 3530672462605 arithBundle05_prefix_columns_16 arithBundle05_columns_072
private theorem arithBundle05_prefix_columns_18 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 80 = 129991352259471 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 76 4 126734432860485 3256919398986 arithBundle05_prefix_columns_17 arithBundle05_columns_076
private theorem arithBundle05_prefix_columns_19 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 84 = 132985767903548 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 80 4 129991352259471 2994415644077 arithBundle05_prefix_columns_18 arithBundle05_columns_080
private theorem arithBundle05_prefix_columns_20 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 88 = 135728931173593 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 84 4 132985767903548 2743163270045 arithBundle05_prefix_columns_19 arithBundle05_columns_084
private theorem arithBundle05_prefix_columns_21 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 92 = 138232141506307 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 88 4 135728931173593 2503210332714 arithBundle05_prefix_columns_20 arithBundle05_columns_088
private theorem arithBundle05_prefix_columns_22 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 96 = 140506675291934 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 92 4 138232141506307 2274533785627 arithBundle05_prefix_columns_21 arithBundle05_columns_092
private theorem arithBundle05_prefix_columns_23 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 100 = 142563783061442 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 96 4 140506675291934 2057107769508 arithBundle05_prefix_columns_22 arithBundle05_columns_096
private theorem arithBundle05_prefix_columns_24 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 104 = 144414714271592 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 100 4 142563783061442 1850931210150 arithBundle05_prefix_columns_23 arithBundle05_columns_100
private theorem arithBundle05_prefix_columns_25 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 108 = 146070722126449 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 104 4 144414714271592 1656007854857 arithBundle05_prefix_columns_24 arithBundle05_columns_104
private theorem arithBundle05_prefix_columns_26 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 112 = 147543109266637 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 108 4 146070722126449 1472387140188 arithBundle05_prefix_columns_25 arithBundle05_columns_108
private theorem arithBundle05_prefix_columns_27 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 116 = 148843146945782 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 112 4 147543109266637 1300037679145 arithBundle05_prefix_columns_26 arithBundle05_columns_112
private theorem arithBundle05_prefix_columns_28 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 120 = 149982085739090 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 116 4 148843146945782 1138938793308 arithBundle05_prefix_columns_27 arithBundle05_columns_116
private theorem arithBundle05_prefix_columns_29 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 124 = 150971175313562 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 120 4 149982085739090 989089574472 arithBundle05_prefix_columns_28 arithBundle05_columns_120
private theorem arithBundle05_prefix_columns_30 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 128 = 151821670324357 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 124 4 150971175313562 850495010795 arithBundle05_prefix_columns_29 arithBundle05_columns_124
private theorem arithBundle05_prefix_columns_31 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 132 = 152544876856057 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 128 4 151821670324357 723206531700 arithBundle05_prefix_columns_30 arithBundle05_columns_128
private theorem arithBundle05_prefix_columns_32 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 136 = 153152061240501 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 132 4 152544876856057 607184384444 arithBundle05_prefix_columns_31 arithBundle05_columns_132
private theorem arithBundle05_prefix_columns_33 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 140 = 153654473697090 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 136 4 153152061240501 502412456589 arithBundle05_prefix_columns_32 arithBundle05_columns_136
private theorem arithBundle05_prefix_columns_34 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 144 = 154063364181249 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 140 4 153654473697090 408890484159 arithBundle05_prefix_columns_33 arithBundle05_columns_140
private theorem arithBundle05_prefix_columns_35 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 148 = 154389975256312 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 144 4 154063364181249 326611075063 arithBundle05_prefix_columns_34 arithBundle05_columns_144
private theorem arithBundle05_prefix_columns_36 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 152 = 154645460066551 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 148 4 154389975256312 255484810239 arithBundle05_prefix_columns_35 arithBundle05_columns_148
private theorem arithBundle05_prefix_columns_37 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 156 = 154840580390866 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 152 4 154645460066551 195120324315 arithBundle05_prefix_columns_36 arithBundle05_columns_152
private theorem arithBundle05_prefix_columns_38 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 160 = 154985568689094 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 156 4 154840580390866 144988298228 arithBundle05_prefix_columns_37 arithBundle05_columns_156
private theorem arithBundle05_prefix_columns_39 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 164 = 155089978873921 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 160 4 154985568689094 104410184827 arithBundle05_prefix_columns_38 arithBundle05_columns_160
private theorem arithBundle05_prefix_columns_40 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 168 = 155162531574222 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 164 4 155089978873921 72552700301 arithBundle05_prefix_columns_39 arithBundle05_columns_164
private theorem arithBundle05_prefix_columns_41 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 172 = 155210970064646 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 168 4 155162531574222 48438490424 arithBundle05_prefix_columns_40 arithBundle05_columns_168
private theorem arithBundle05_prefix_columns_42 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 176 = 155241838324383 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 172 4 155210970064646 30868259737 arithBundle05_prefix_columns_41 arithBundle05_columns_172
private theorem arithBundle05_prefix_columns_43 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact10) 0 177 = 155247458921819 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact10) 0 176 1 155241838324383 5620597436 arithBundle05_prefix_columns_42 arithBundle05_columns_176

private theorem arithBundle05_ordinary_ranks : ordinaryRankBound contact10 = 14347345999 := by decide +kernel
private theorem arithBundle05_ranks_000 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 4 = 39177548 :=
  contactRankWindow_of_rec contact10 0 4 39177548 (by decide +kernel)
private theorem arithBundle05_ranks_004 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 4 4 = 36842828 :=
  contactRankWindow_of_rec contact10 4 4 36842828 (by decide +kernel)
private theorem arithBundle05_ranks_008 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 8 4 = 34585932 :=
  contactRankWindow_of_rec contact10 8 4 34585932 (by decide +kernel)
private theorem arithBundle05_ranks_012 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 12 4 = 32406860 :=
  contactRankWindow_of_rec contact10 12 4 32406860 (by decide +kernel)
private theorem arithBundle05_ranks_016 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 16 4 = 30305612 :=
  contactRankWindow_of_rec contact10 16 4 30305612 (by decide +kernel)
private theorem arithBundle05_ranks_020 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 20 4 = 28282188 :=
  contactRankWindow_of_rec contact10 20 4 28282188 (by decide +kernel)
private theorem arithBundle05_ranks_024 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 24 4 = 26336588 :=
  contactRankWindow_of_rec contact10 24 4 26336588 (by decide +kernel)
private theorem arithBundle05_ranks_028 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 28 4 = 24468812 :=
  contactRankWindow_of_rec contact10 28 4 24468812 (by decide +kernel)
private theorem arithBundle05_ranks_032 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 32 4 = 22678860 :=
  contactRankWindow_of_rec contact10 32 4 22678860 (by decide +kernel)
private theorem arithBundle05_ranks_036 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 36 4 = 20966732 :=
  contactRankWindow_of_rec contact10 36 4 20966732 (by decide +kernel)
private theorem arithBundle05_ranks_040 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 40 4 = 19332428 :=
  contactRankWindow_of_rec contact10 40 4 19332428 (by decide +kernel)
private theorem arithBundle05_ranks_044 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 44 4 = 17775948 :=
  contactRankWindow_of_rec contact10 44 4 17775948 (by decide +kernel)
private theorem arithBundle05_ranks_048 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 48 4 = 16297292 :=
  contactRankWindow_of_rec contact10 48 4 16297292 (by decide +kernel)
private theorem arithBundle05_ranks_052 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 52 4 = 14896364 :=
  contactRankWindow_of_rec contact10 52 4 14896364 (by decide +kernel)
private theorem arithBundle05_ranks_056 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 56 4 = 13572226 :=
  contactRankWindow_of_rec contact10 56 4 13572226 (by decide +kernel)
private theorem arithBundle05_ranks_060 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 60 4 = 12323468 :=
  contactRankWindow_of_rec contact10 60 4 12323468 (by decide +kernel)
private theorem arithBundle05_ranks_064 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 64 4 = 11148642 :=
  contactRankWindow_of_rec contact10 64 4 11148642 (by decide +kernel)
private theorem arithBundle05_ranks_068 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 68 4 = 10045948 :=
  contactRankWindow_of_rec contact10 68 4 10045948 (by decide +kernel)
private theorem arithBundle05_ranks_072 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 72 4 = 9013356 :=
  contactRankWindow_of_rec contact10 72 4 9013356 (by decide +kernel)
private theorem arithBundle05_ranks_076 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 76 4 = 8048826 :=
  contactRankWindow_of_rec contact10 76 4 8048826 (by decide +kernel)
private theorem arithBundle05_ranks_080 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 80 4 = 7150556 :=
  contactRankWindow_of_rec contact10 80 4 7150556 (by decide +kernel)
private theorem arithBundle05_ranks_084 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 84 4 = 6316364 :=
  contactRankWindow_of_rec contact10 84 4 6316364 (by decide +kernel)
private theorem arithBundle05_ranks_088 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 88 4 = 5544210 :=
  contactRankWindow_of_rec contact10 88 4 5544210 (by decide +kernel)
private theorem arithBundle05_ranks_092 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 92 4 = 4832444 :=
  contactRankWindow_of_rec contact10 92 4 4832444 (by decide +kernel)
private theorem arithBundle05_ranks_096 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 96 4 = 4178732 :=
  contactRankWindow_of_rec contact10 96 4 4178732 (by decide +kernel)
private theorem arithBundle05_ranks_100 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 100 4 = 3581034 :=
  contactRankWindow_of_rec contact10 100 4 3581034 (by decide +kernel)
private theorem arithBundle05_ranks_104 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 104 4 = 3037852 :=
  contactRankWindow_of_rec contact10 104 4 3037852 (by decide +kernel)
private theorem arithBundle05_ranks_108 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 108 4 = 2546700 :=
  contactRankWindow_of_rec contact10 108 4 2546700 (by decide +kernel)
private theorem arithBundle05_ranks_112 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 112 4 = 2105538 :=
  contactRankWindow_of_rec contact10 112 4 2105538 (by decide +kernel)
private theorem arithBundle05_ranks_116 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 116 4 = 1713020 :=
  contactRankWindow_of_rec contact10 116 4 1713020 (by decide +kernel)
private theorem arithBundle05_ranks_120 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 120 4 = 1366508 :=
  contactRankWindow_of_rec contact10 120 4 1366508 (by decide +kernel)
private theorem arithBundle05_ranks_124 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 124 4 = 1063962 :=
  contactRankWindow_of_rec contact10 124 4 1063962 (by decide +kernel)
private theorem arithBundle05_ranks_128 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 128 4 = 804188 :=
  contactRankWindow_of_rec contact10 128 4 804188 (by decide +kernel)
private theorem arithBundle05_ranks_132 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 132 4 = 584396 :=
  contactRankWindow_of_rec contact10 132 4 584396 (by decide +kernel)
private theorem arithBundle05_ranks_136 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 136 4 = 402546 :=
  contactRankWindow_of_rec contact10 136 4 402546 (by decide +kernel)
private theorem arithBundle05_ranks_140 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 140 4 = 257596 :=
  contactRankWindow_of_rec contact10 140 4 257596 (by decide +kernel)
private theorem arithBundle05_ranks_144 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 144 4 = 146608 :=
  contactRankWindow_of_rec contact10 144 4 146608 (by decide +kernel)
private theorem arithBundle05_ranks_148 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 148 4 = 67753 :=
  contactRankWindow_of_rec contact10 148 4 67753 (by decide +kernel)
private theorem arithBundle05_ranks_152 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 152 4 = 20455 :=
  contactRankWindow_of_rec contact10 152 4 20455 (by decide +kernel)
private theorem arithBundle05_ranks_156 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 156 4 = 1150 :=
  contactRankWindow_of_rec contact10 156 4 1150 (by decide +kernel)
private theorem arithBundle05_ranks_160 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 160 17 = 0 :=
  contactRankWindow_of_rec contact10 160 17 0 (by decide +kernel)
private theorem arithBundle05_prefix_ranks_00 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 8 = 76020376 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 4 4 39177548 36842828 arithBundle05_ranks_000 arithBundle05_ranks_004
private theorem arithBundle05_prefix_ranks_01 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 12 = 110606308 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 8 4 76020376 34585932 arithBundle05_prefix_ranks_00 arithBundle05_ranks_008
private theorem arithBundle05_prefix_ranks_02 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 16 = 143013168 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 12 4 110606308 32406860 arithBundle05_prefix_ranks_01 arithBundle05_ranks_012
private theorem arithBundle05_prefix_ranks_03 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 20 = 173318780 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 16 4 143013168 30305612 arithBundle05_prefix_ranks_02 arithBundle05_ranks_016
private theorem arithBundle05_prefix_ranks_04 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 24 = 201600968 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 20 4 173318780 28282188 arithBundle05_prefix_ranks_03 arithBundle05_ranks_020
private theorem arithBundle05_prefix_ranks_05 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 28 = 227937556 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 24 4 201600968 26336588 arithBundle05_prefix_ranks_04 arithBundle05_ranks_024
private theorem arithBundle05_prefix_ranks_06 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 32 = 252406368 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 28 4 227937556 24468812 arithBundle05_prefix_ranks_05 arithBundle05_ranks_028
private theorem arithBundle05_prefix_ranks_07 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 36 = 275085228 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 32 4 252406368 22678860 arithBundle05_prefix_ranks_06 arithBundle05_ranks_032
private theorem arithBundle05_prefix_ranks_08 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 40 = 296051960 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 36 4 275085228 20966732 arithBundle05_prefix_ranks_07 arithBundle05_ranks_036
private theorem arithBundle05_prefix_ranks_09 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 44 = 315384388 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 40 4 296051960 19332428 arithBundle05_prefix_ranks_08 arithBundle05_ranks_040
private theorem arithBundle05_prefix_ranks_10 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 48 = 333160336 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 44 4 315384388 17775948 arithBundle05_prefix_ranks_09 arithBundle05_ranks_044
private theorem arithBundle05_prefix_ranks_11 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 52 = 349457628 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 48 4 333160336 16297292 arithBundle05_prefix_ranks_10 arithBundle05_ranks_048
private theorem arithBundle05_prefix_ranks_12 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 56 = 364353992 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 52 4 349457628 14896364 arithBundle05_prefix_ranks_11 arithBundle05_ranks_052
private theorem arithBundle05_prefix_ranks_13 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 60 = 377926218 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 56 4 364353992 13572226 arithBundle05_prefix_ranks_12 arithBundle05_ranks_056
private theorem arithBundle05_prefix_ranks_14 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 64 = 390249686 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 60 4 377926218 12323468 arithBundle05_prefix_ranks_13 arithBundle05_ranks_060
private theorem arithBundle05_prefix_ranks_15 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 68 = 401398328 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 64 4 390249686 11148642 arithBundle05_prefix_ranks_14 arithBundle05_ranks_064
private theorem arithBundle05_prefix_ranks_16 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 72 = 411444276 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 68 4 401398328 10045948 arithBundle05_prefix_ranks_15 arithBundle05_ranks_068
private theorem arithBundle05_prefix_ranks_17 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 76 = 420457632 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 72 4 411444276 9013356 arithBundle05_prefix_ranks_16 arithBundle05_ranks_072
private theorem arithBundle05_prefix_ranks_18 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 80 = 428506458 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 76 4 420457632 8048826 arithBundle05_prefix_ranks_17 arithBundle05_ranks_076
private theorem arithBundle05_prefix_ranks_19 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 84 = 435657014 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 80 4 428506458 7150556 arithBundle05_prefix_ranks_18 arithBundle05_ranks_080
private theorem arithBundle05_prefix_ranks_20 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 88 = 441973378 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 84 4 435657014 6316364 arithBundle05_prefix_ranks_19 arithBundle05_ranks_084
private theorem arithBundle05_prefix_ranks_21 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 92 = 447517588 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 88 4 441973378 5544210 arithBundle05_prefix_ranks_20 arithBundle05_ranks_088
private theorem arithBundle05_prefix_ranks_22 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 96 = 452350032 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 92 4 447517588 4832444 arithBundle05_prefix_ranks_21 arithBundle05_ranks_092
private theorem arithBundle05_prefix_ranks_23 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 100 = 456528764 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 96 4 452350032 4178732 arithBundle05_prefix_ranks_22 arithBundle05_ranks_096
private theorem arithBundle05_prefix_ranks_24 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 104 = 460109798 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 100 4 456528764 3581034 arithBundle05_prefix_ranks_23 arithBundle05_ranks_100
private theorem arithBundle05_prefix_ranks_25 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 108 = 463147650 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 104 4 460109798 3037852 arithBundle05_prefix_ranks_24 arithBundle05_ranks_104
private theorem arithBundle05_prefix_ranks_26 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 112 = 465694350 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 108 4 463147650 2546700 arithBundle05_prefix_ranks_25 arithBundle05_ranks_108
private theorem arithBundle05_prefix_ranks_27 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 116 = 467799888 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 112 4 465694350 2105538 arithBundle05_prefix_ranks_26 arithBundle05_ranks_112
private theorem arithBundle05_prefix_ranks_28 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 120 = 469512908 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 116 4 467799888 1713020 arithBundle05_prefix_ranks_27 arithBundle05_ranks_116
private theorem arithBundle05_prefix_ranks_29 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 124 = 470879416 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 120 4 469512908 1366508 arithBundle05_prefix_ranks_28 arithBundle05_ranks_120
private theorem arithBundle05_prefix_ranks_30 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 128 = 471943378 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 124 4 470879416 1063962 arithBundle05_prefix_ranks_29 arithBundle05_ranks_124
private theorem arithBundle05_prefix_ranks_31 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 132 = 472747566 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 128 4 471943378 804188 arithBundle05_prefix_ranks_30 arithBundle05_ranks_128
private theorem arithBundle05_prefix_ranks_32 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 136 = 473331962 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 132 4 472747566 584396 arithBundle05_prefix_ranks_31 arithBundle05_ranks_132
private theorem arithBundle05_prefix_ranks_33 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 140 = 473734508 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 136 4 473331962 402546 arithBundle05_prefix_ranks_32 arithBundle05_ranks_136
private theorem arithBundle05_prefix_ranks_34 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 144 = 473992104 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 140 4 473734508 257596 arithBundle05_prefix_ranks_33 arithBundle05_ranks_140
private theorem arithBundle05_prefix_ranks_35 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 148 = 474138712 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 144 4 473992104 146608 arithBundle05_prefix_ranks_34 arithBundle05_ranks_144
private theorem arithBundle05_prefix_ranks_36 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 152 = 474206465 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 148 4 474138712 67753 arithBundle05_prefix_ranks_35 arithBundle05_ranks_148
private theorem arithBundle05_prefix_ranks_37 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 156 = 474226920 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 152 4 474206465 20455 arithBundle05_prefix_ranks_36 arithBundle05_ranks_152
private theorem arithBundle05_prefix_ranks_38 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 160 = 474228070 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 156 4 474226920 1150 arithBundle05_prefix_ranks_37 arithBundle05_ranks_156
private theorem arithBundle05_prefix_ranks_39 : arithBundle05_sliceWindow (auxiliaryRankSlice contact10) 0 177 = 474228070 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact10) 0 160 17 474228070 0 arithBundle05_prefix_ranks_38 arithBundle05_ranks_160

theorem contact10_margin : sourceMargin contact10 :=
  arithBundle05_margin_of_checked_counts contact10 177 3730140481054016 155247458921819 14347345999 474228070
    rfl arithBundle05_ordinary_columns arithBundle05_prefix_columns_43 arithBundle05_ordinary_ranks arithBundle05_prefix_ranks_39 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle06_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle06_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle06_sliceWindow f a b = x) (hy : arithBundle06_sliceWindow f (a+b) c = y) :
    arithBundle06_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle06_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle06_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle06_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle06_sliceWindow,Nat.zero_add]

private theorem arithBundle06_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle06_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle06_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle06_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle06_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle06_ordinary_columns : ordinaryColumnCount contact11 = 206043637395349 := by decide +kernel
private theorem arithBundle06_columns_000 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 4 = 913694404200 :=
  contactColumnsWindow_fast contact11 0 4 913694404200 (by decide +kernel)
private theorem arithBundle06_columns_004 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 4 4 = 839613660886 :=
  contactColumnsWindow_fast contact11 4 4 839613660886 (by decide +kernel)
private theorem arithBundle06_columns_008 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 8 4 = 768694535956 :=
  contactColumnsWindow_fast contact11 8 4 768694535956 (by decide +kernel)
private theorem arithBundle06_columns_012 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 12 4 = 700923039412 :=
  contactColumnsWindow_fast contact11 12 4 700923039412 (by decide +kernel)
private theorem arithBundle06_columns_016 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 16 4 = 636296663124 :=
  contactColumnsWindow_fast contact11 16 4 636296663124 (by decide +kernel)
private theorem arithBundle06_columns_020 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 20 4 = 574813987489 :=
  contactColumnsWindow_fast contact11 20 4 574813987489 (by decide +kernel)
private theorem arithBundle06_columns_024 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 24 4 = 516479435698 :=
  contactColumnsWindow_fast contact11 24 4 516479435698 (by decide +kernel)
private theorem arithBundle06_columns_028 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 28 4 = 461307876466 :=
  contactColumnsWindow_fast contact11 28 4 461307876466 (by decide +kernel)
private theorem arithBundle06_columns_032 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 32 4 = 409285537156 :=
  contactColumnsWindow_fast contact11 32 4 409285537156 (by decide +kernel)
private theorem arithBundle06_columns_036 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 36 4 = 360408408804 :=
  contactColumnsWindow_fast contact11 36 4 360408408804 (by decide +kernel)
private theorem arithBundle06_columns_040 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 40 4 = 314675072647 :=
  contactColumnsWindow_fast contact11 40 4 314675072647 (by decide +kernel)
private theorem arithBundle06_columns_044 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 44 4 = 272090843206 :=
  contactColumnsWindow_fast contact11 44 4 272090843206 (by decide +kernel)
private theorem arithBundle06_columns_048 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 48 4 = 232669784590 :=
  contactColumnsWindow_fast contact11 48 4 232669784590 (by decide +kernel)
private theorem arithBundle06_columns_052 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 52 4 = 196396842996 :=
  contactColumnsWindow_fast contact11 52 4 196396842996 (by decide +kernel)
private theorem arithBundle06_columns_056 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 56 4 = 163268899524 :=
  contactColumnsWindow_fast contact11 56 4 163268899524 (by decide +kernel)
private theorem arithBundle06_columns_060 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 60 4 = 133284902845 :=
  contactColumnsWindow_fast contact11 60 4 133284902845 (by decide +kernel)
private theorem arithBundle06_columns_064 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 64 4 = 106451203745 :=
  contactColumnsWindow_fast contact11 64 4 106451203745 (by decide +kernel)
private theorem arithBundle06_columns_068 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 68 4 = 82780520500 :=
  contactColumnsWindow_fast contact11 68 4 82780520500 (by decide +kernel)
private theorem arithBundle06_columns_072 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 72 4 = 62256907908 :=
  contactColumnsWindow_fast contact11 72 4 62256907908 (by decide +kernel)
private theorem arithBundle06_columns_076 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 76 4 = 44878135284 :=
  contactColumnsWindow_fast contact11 76 4 44878135284 (by decide +kernel)
private theorem arithBundle06_columns_080 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 80 4 = 30643395501 :=
  contactColumnsWindow_fast contact11 80 4 30643395501 (by decide +kernel)
private theorem arithBundle06_columns_084 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 84 4 = 19538876129 :=
  contactColumnsWindow_fast contact11 84 4 19538876129 (by decide +kernel)
private theorem arithBundle06_columns_088 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 88 4 = 11428444721 :=
  contactColumnsWindow_fast contact11 88 4 11428444721 (by decide +kernel)
private theorem arithBundle06_columns_092 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 92 4 = 5978648251 :=
  contactColumnsWindow_fast contact11 92 4 5978648251 (by decide +kernel)
private theorem arithBundle06_columns_096 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 96 4 = 2709086910 :=
  contactColumnsWindow_fast contact11 96 4 2709086910 (by decide +kernel)
private theorem arithBundle06_columns_100 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 100 1 = 364479020 :=
  contactColumnsWindow_fast contact11 100 1 364479020 (by decide +kernel)
private theorem arithBundle06_prefix_columns_00 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 8 = 1753308065086 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 4 4 913694404200 839613660886 arithBundle06_columns_000 arithBundle06_columns_004
private theorem arithBundle06_prefix_columns_01 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 12 = 2522002601042 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 8 4 1753308065086 768694535956 arithBundle06_prefix_columns_00 arithBundle06_columns_008
private theorem arithBundle06_prefix_columns_02 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 16 = 3222925640454 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 12 4 2522002601042 700923039412 arithBundle06_prefix_columns_01 arithBundle06_columns_012
private theorem arithBundle06_prefix_columns_03 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 20 = 3859222303578 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 16 4 3222925640454 636296663124 arithBundle06_prefix_columns_02 arithBundle06_columns_016
private theorem arithBundle06_prefix_columns_04 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 24 = 4434036291067 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 20 4 3859222303578 574813987489 arithBundle06_prefix_columns_03 arithBundle06_columns_020
private theorem arithBundle06_prefix_columns_05 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 28 = 4950515726765 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 24 4 4434036291067 516479435698 arithBundle06_prefix_columns_04 arithBundle06_columns_024
private theorem arithBundle06_prefix_columns_06 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 32 = 5411823603231 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 28 4 4950515726765 461307876466 arithBundle06_prefix_columns_05 arithBundle06_columns_028
private theorem arithBundle06_prefix_columns_07 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 36 = 5821109140387 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 32 4 5411823603231 409285537156 arithBundle06_prefix_columns_06 arithBundle06_columns_032
private theorem arithBundle06_prefix_columns_08 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 40 = 6181517549191 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 36 4 5821109140387 360408408804 arithBundle06_prefix_columns_07 arithBundle06_columns_036
private theorem arithBundle06_prefix_columns_09 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 44 = 6496192621838 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 40 4 6181517549191 314675072647 arithBundle06_prefix_columns_08 arithBundle06_columns_040
private theorem arithBundle06_prefix_columns_10 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 48 = 6768283465044 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 44 4 6496192621838 272090843206 arithBundle06_prefix_columns_09 arithBundle06_columns_044
private theorem arithBundle06_prefix_columns_11 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 52 = 7000953249634 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 48 4 6768283465044 232669784590 arithBundle06_prefix_columns_10 arithBundle06_columns_048
private theorem arithBundle06_prefix_columns_12 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 56 = 7197350092630 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 52 4 7000953249634 196396842996 arithBundle06_prefix_columns_11 arithBundle06_columns_052
private theorem arithBundle06_prefix_columns_13 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 60 = 7360618992154 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 56 4 7197350092630 163268899524 arithBundle06_prefix_columns_12 arithBundle06_columns_056
private theorem arithBundle06_prefix_columns_14 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 64 = 7493903894999 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 60 4 7360618992154 133284902845 arithBundle06_prefix_columns_13 arithBundle06_columns_060
private theorem arithBundle06_prefix_columns_15 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 68 = 7600355098744 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 64 4 7493903894999 106451203745 arithBundle06_prefix_columns_14 arithBundle06_columns_064
private theorem arithBundle06_prefix_columns_16 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 72 = 7683135619244 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 68 4 7600355098744 82780520500 arithBundle06_prefix_columns_15 arithBundle06_columns_068
private theorem arithBundle06_prefix_columns_17 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 76 = 7745392527152 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 72 4 7683135619244 62256907908 arithBundle06_prefix_columns_16 arithBundle06_columns_072
private theorem arithBundle06_prefix_columns_18 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 80 = 7790270662436 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 76 4 7745392527152 44878135284 arithBundle06_prefix_columns_17 arithBundle06_columns_076
private theorem arithBundle06_prefix_columns_19 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 84 = 7820914057937 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 80 4 7790270662436 30643395501 arithBundle06_prefix_columns_18 arithBundle06_columns_080
private theorem arithBundle06_prefix_columns_20 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 88 = 7840452934066 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 84 4 7820914057937 19538876129 arithBundle06_prefix_columns_19 arithBundle06_columns_084
private theorem arithBundle06_prefix_columns_21 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 92 = 7851881378787 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 88 4 7840452934066 11428444721 arithBundle06_prefix_columns_20 arithBundle06_columns_088
private theorem arithBundle06_prefix_columns_22 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 96 = 7857860027038 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 92 4 7851881378787 5978648251 arithBundle06_prefix_columns_21 arithBundle06_columns_092
private theorem arithBundle06_prefix_columns_23 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 100 = 7860569113948 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 96 4 7857860027038 2709086910 arithBundle06_prefix_columns_22 arithBundle06_columns_096
private theorem arithBundle06_prefix_columns_24 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact11) 0 101 = 7860933592968 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact11) 0 100 1 7860569113948 364479020 arithBundle06_prefix_columns_23 arithBundle06_columns_100

private theorem arithBundle06_ordinary_ranks : ordinaryRankBound contact11 = 792218783 := by decide +kernel
private theorem arithBundle06_ranks_000 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 4 = 3423580 :=
  contactRankWindow_of_rec contact11 0 4 3423580 (by decide +kernel)
private theorem arithBundle06_ranks_004 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 4 4 = 3061820 :=
  contactRankWindow_of_rec contact11 4 4 3061820 (by decide +kernel)
private theorem arithBundle06_ranks_008 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 8 4 = 2721820 :=
  contactRankWindow_of_rec contact11 8 4 2721820 (by decide +kernel)
private theorem arithBundle06_ranks_012 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 12 4 = 2403580 :=
  contactRankWindow_of_rec contact11 12 4 2403580 (by decide +kernel)
private theorem arithBundle06_ranks_016 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 16 4 = 2107100 :=
  contactRankWindow_of_rec contact11 16 4 2107100 (by decide +kernel)
private theorem arithBundle06_ranks_020 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 20 4 = 1832380 :=
  contactRankWindow_of_rec contact11 20 4 1832380 (by decide +kernel)
private theorem arithBundle06_ranks_024 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 24 4 = 1579420 :=
  contactRankWindow_of_rec contact11 24 4 1579420 (by decide +kernel)
private theorem arithBundle06_ranks_028 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 28 4 = 1348220 :=
  contactRankWindow_of_rec contact11 28 4 1348220 (by decide +kernel)
private theorem arithBundle06_ranks_032 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 32 4 = 1138763 :=
  contactRankWindow_of_rec contact11 32 4 1138763 (by decide +kernel)
private theorem arithBundle06_ranks_036 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 36 4 = 950687 :=
  contactRankWindow_of_rec contact11 36 4 950687 (by decide +kernel)
private theorem arithBundle06_ranks_040 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 40 4 = 783210 :=
  contactRankWindow_of_rec contact11 40 4 783210 (by decide +kernel)
private theorem arithBundle06_ranks_044 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 44 4 = 635320 :=
  contactRankWindow_of_rec contact11 44 4 635320 (by decide +kernel)
private theorem arithBundle06_ranks_048 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 48 4 = 505939 :=
  contactRankWindow_of_rec contact11 48 4 505939 (by decide +kernel)
private theorem arithBundle06_ranks_052 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 52 4 = 394094 :=
  contactRankWindow_of_rec contact11 52 4 394094 (by decide +kernel)
private theorem arithBundle06_ranks_056 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 56 4 = 298652 :=
  contactRankWindow_of_rec contact11 56 4 298652 (by decide +kernel)
private theorem arithBundle06_ranks_060 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 60 4 = 218535 :=
  contactRankWindow_of_rec contact11 60 4 218535 (by decide +kernel)
private theorem arithBundle06_ranks_064 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 64 4 = 152850 :=
  contactRankWindow_of_rec contact11 64 4 152850 (by decide +kernel)
private theorem arithBundle06_ranks_068 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 68 4 = 100384 :=
  contactRankWindow_of_rec contact11 68 4 100384 (by decide +kernel)
private theorem arithBundle06_ranks_072 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 72 4 = 60059 :=
  contactRankWindow_of_rec contact11 72 4 60059 (by decide +kernel)
private theorem arithBundle06_ranks_076 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 76 4 = 31062 :=
  contactRankWindow_of_rec contact11 76 4 31062 (by decide +kernel)
private theorem arithBundle06_ranks_080 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 80 4 = 12100 :=
  contactRankWindow_of_rec contact11 80 4 12100 (by decide +kernel)
private theorem arithBundle06_ranks_084 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 84 4 = 2100 :=
  contactRankWindow_of_rec contact11 84 4 2100 (by decide +kernel)
private theorem arithBundle06_ranks_088 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 88 13 = 0 :=
  contactRankWindow_of_rec contact11 88 13 0 (by decide +kernel)
private theorem arithBundle06_prefix_ranks_00 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 8 = 6485400 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 4 4 3423580 3061820 arithBundle06_ranks_000 arithBundle06_ranks_004
private theorem arithBundle06_prefix_ranks_01 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 12 = 9207220 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 8 4 6485400 2721820 arithBundle06_prefix_ranks_00 arithBundle06_ranks_008
private theorem arithBundle06_prefix_ranks_02 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 16 = 11610800 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 12 4 9207220 2403580 arithBundle06_prefix_ranks_01 arithBundle06_ranks_012
private theorem arithBundle06_prefix_ranks_03 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 20 = 13717900 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 16 4 11610800 2107100 arithBundle06_prefix_ranks_02 arithBundle06_ranks_016
private theorem arithBundle06_prefix_ranks_04 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 24 = 15550280 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 20 4 13717900 1832380 arithBundle06_prefix_ranks_03 arithBundle06_ranks_020
private theorem arithBundle06_prefix_ranks_05 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 28 = 17129700 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 24 4 15550280 1579420 arithBundle06_prefix_ranks_04 arithBundle06_ranks_024
private theorem arithBundle06_prefix_ranks_06 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 32 = 18477920 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 28 4 17129700 1348220 arithBundle06_prefix_ranks_05 arithBundle06_ranks_028
private theorem arithBundle06_prefix_ranks_07 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 36 = 19616683 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 32 4 18477920 1138763 arithBundle06_prefix_ranks_06 arithBundle06_ranks_032
private theorem arithBundle06_prefix_ranks_08 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 40 = 20567370 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 36 4 19616683 950687 arithBundle06_prefix_ranks_07 arithBundle06_ranks_036
private theorem arithBundle06_prefix_ranks_09 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 44 = 21350580 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 40 4 20567370 783210 arithBundle06_prefix_ranks_08 arithBundle06_ranks_040
private theorem arithBundle06_prefix_ranks_10 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 48 = 21985900 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 44 4 21350580 635320 arithBundle06_prefix_ranks_09 arithBundle06_ranks_044
private theorem arithBundle06_prefix_ranks_11 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 52 = 22491839 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 48 4 21985900 505939 arithBundle06_prefix_ranks_10 arithBundle06_ranks_048
private theorem arithBundle06_prefix_ranks_12 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 56 = 22885933 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 52 4 22491839 394094 arithBundle06_prefix_ranks_11 arithBundle06_ranks_052
private theorem arithBundle06_prefix_ranks_13 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 60 = 23184585 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 56 4 22885933 298652 arithBundle06_prefix_ranks_12 arithBundle06_ranks_056
private theorem arithBundle06_prefix_ranks_14 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 64 = 23403120 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 60 4 23184585 218535 arithBundle06_prefix_ranks_13 arithBundle06_ranks_060
private theorem arithBundle06_prefix_ranks_15 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 68 = 23555970 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 64 4 23403120 152850 arithBundle06_prefix_ranks_14 arithBundle06_ranks_064
private theorem arithBundle06_prefix_ranks_16 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 72 = 23656354 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 68 4 23555970 100384 arithBundle06_prefix_ranks_15 arithBundle06_ranks_068
private theorem arithBundle06_prefix_ranks_17 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 76 = 23716413 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 72 4 23656354 60059 arithBundle06_prefix_ranks_16 arithBundle06_ranks_072
private theorem arithBundle06_prefix_ranks_18 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 80 = 23747475 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 76 4 23716413 31062 arithBundle06_prefix_ranks_17 arithBundle06_ranks_076
private theorem arithBundle06_prefix_ranks_19 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 84 = 23759575 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 80 4 23747475 12100 arithBundle06_prefix_ranks_18 arithBundle06_ranks_080
private theorem arithBundle06_prefix_ranks_20 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 88 = 23761675 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 84 4 23759575 2100 arithBundle06_prefix_ranks_19 arithBundle06_ranks_084
private theorem arithBundle06_prefix_ranks_21 : arithBundle06_sliceWindow (auxiliaryRankSlice contact11) 0 101 = 23761675 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact11) 0 88 13 23761675 0 arithBundle06_prefix_ranks_20 arithBundle06_ranks_088

theorem contact11_margin : sourceMargin contact11 :=
  arithBundle06_margin_of_checked_counts contact11 101 206043637395349 7860933592968 792218783 23761675
    rfl arithBundle06_ordinary_columns arithBundle06_prefix_columns_24 arithBundle06_ordinary_ranks arithBundle06_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle07_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle07_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle07_sliceWindow f a b = x) (hy : arithBundle07_sliceWindow f (a+b) c = y) :
    arithBundle07_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle07_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle07_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle07_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle07_sliceWindow,Nat.zero_add]

private theorem arithBundle07_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle07_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle07_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle07_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle07_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle07_ordinary_columns : ordinaryColumnCount contact12 = 175580949295062 := by decide +kernel
private theorem arithBundle07_columns_000 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 4 = 1141152222772 :=
  contactColumnsWindow_fast contact12 0 4 1141152222772 (by decide +kernel)
private theorem arithBundle07_columns_004 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 4 4 = 1049410658596 :=
  contactColumnsWindow_fast contact12 4 4 1049410658596 (by decide +kernel)
private theorem arithBundle07_columns_008 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 8 4 = 961536600254 :=
  contactColumnsWindow_fast contact12 8 4 961536600254 (by decide +kernel)
private theorem arithBundle07_columns_012 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 12 4 = 877528796492 :=
  contactColumnsWindow_fast contact12 12 4 877528796492 (by decide +kernel)
private theorem arithBundle07_columns_016 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 16 4 = 797386026181 :=
  contactColumnsWindow_fast contact12 16 4 797386026181 (by decide +kernel)
private theorem arithBundle07_columns_020 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 20 4 = 721116075448 :=
  contactColumnsWindow_fast contact12 20 4 721116075448 (by decide +kernel)
private theorem arithBundle07_columns_024 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 24 4 = 648735562192 :=
  contactColumnsWindow_fast contact12 24 4 648735562192 (by decide +kernel)
private theorem arithBundle07_columns_028 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 28 4 = 580223885174 :=
  contactColumnsWindow_fast contact12 28 4 580223885174 (by decide +kernel)
private theorem arithBundle07_columns_032 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 32 4 = 515578289288 :=
  contactColumnsWindow_fast contact12 32 4 515578289288 (by decide +kernel)
private theorem arithBundle07_columns_036 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 36 4 = 454797952052 :=
  contactColumnsWindow_fast contact12 36 4 454797952052 (by decide +kernel)
private theorem arithBundle07_columns_040 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 40 4 = 397892373724 :=
  contactColumnsWindow_fast contact12 40 4 397892373724 (by decide +kernel)
private theorem arithBundle07_columns_044 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 44 4 = 344875099396 :=
  contactColumnsWindow_fast contact12 44 4 344875099396 (by decide +kernel)
private theorem arithBundle07_columns_048 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 48 4 = 295725803702 :=
  contactColumnsWindow_fast contact12 48 4 295725803702 (by decide +kernel)
private theorem arithBundle07_columns_052 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 52 4 = 250442415692 :=
  contactColumnsWindow_fast contact12 52 4 250442415692 (by decide +kernel)
private theorem arithBundle07_columns_056 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 56 4 = 209024565776 :=
  contactColumnsWindow_fast contact12 56 4 209024565776 (by decide +kernel)
private theorem arithBundle07_columns_060 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 60 4 = 171483314308 :=
  contactColumnsWindow_fast contact12 60 4 171483314308 (by decide +kernel)
private theorem arithBundle07_columns_064 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 64 4 = 137829270208 :=
  contactColumnsWindow_fast contact12 64 4 137829270208 (by decide +kernel)
private theorem arithBundle07_columns_068 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 68 4 = 108042438584 :=
  contactColumnsWindow_fast contact12 68 4 108042438584 (by decide +kernel)
private theorem arithBundle07_columns_072 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 72 4 = 82121175704 :=
  contactColumnsWindow_fast contact12 72 4 82121175704 (by decide +kernel)
private theorem arithBundle07_columns_076 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 76 4 = 60065813108 :=
  contactColumnsWindow_fast contact12 76 4 60065813108 (by decide +kernel)
private theorem arithBundle07_columns_080 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 80 4 = 41888216405 :=
  contactColumnsWindow_fast contact12 80 4 41888216405 (by decide +kernel)
private theorem arithBundle07_columns_084 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 84 4 = 27548710482 :=
  contactColumnsWindow_fast contact12 84 4 27548710482 (by decide +kernel)
private theorem arithBundle07_columns_088 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 88 4 = 16831606876 :=
  contactColumnsWindow_fast contact12 88 4 16831606876 (by decide +kernel)
private theorem arithBundle07_columns_092 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 92 4 = 9371021726 :=
  contactColumnsWindow_fast contact12 92 4 9371021726 (by decide +kernel)
private theorem arithBundle07_columns_096 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 96 4 = 4641539176 :=
  contactColumnsWindow_fast contact12 96 4 4641539176 (by decide +kernel)
private theorem arithBundle07_columns_100 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 100 1 = 679271774 :=
  contactColumnsWindow_fast contact12 100 1 679271774 (by decide +kernel)
private theorem arithBundle07_prefix_columns_00 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 8 = 2190562881368 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 4 4 1141152222772 1049410658596 arithBundle07_columns_000 arithBundle07_columns_004
private theorem arithBundle07_prefix_columns_01 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 12 = 3152099481622 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 8 4 2190562881368 961536600254 arithBundle07_prefix_columns_00 arithBundle07_columns_008
private theorem arithBundle07_prefix_columns_02 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 16 = 4029628278114 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 12 4 3152099481622 877528796492 arithBundle07_prefix_columns_01 arithBundle07_columns_012
private theorem arithBundle07_prefix_columns_03 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 20 = 4827014304295 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 16 4 4029628278114 797386026181 arithBundle07_prefix_columns_02 arithBundle07_columns_016
private theorem arithBundle07_prefix_columns_04 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 24 = 5548130379743 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 20 4 4827014304295 721116075448 arithBundle07_prefix_columns_03 arithBundle07_columns_020
private theorem arithBundle07_prefix_columns_05 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 28 = 6196865941935 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 24 4 5548130379743 648735562192 arithBundle07_prefix_columns_04 arithBundle07_columns_024
private theorem arithBundle07_prefix_columns_06 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 32 = 6777089827109 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 28 4 6196865941935 580223885174 arithBundle07_prefix_columns_05 arithBundle07_columns_028
private theorem arithBundle07_prefix_columns_07 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 36 = 7292668116397 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 32 4 6777089827109 515578289288 arithBundle07_prefix_columns_06 arithBundle07_columns_032
private theorem arithBundle07_prefix_columns_08 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 40 = 7747466068449 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 36 4 7292668116397 454797952052 arithBundle07_prefix_columns_07 arithBundle07_columns_036
private theorem arithBundle07_prefix_columns_09 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 44 = 8145358442173 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 40 4 7747466068449 397892373724 arithBundle07_prefix_columns_08 arithBundle07_columns_040
private theorem arithBundle07_prefix_columns_10 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 48 = 8490233541569 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 44 4 8145358442173 344875099396 arithBundle07_prefix_columns_09 arithBundle07_columns_044
private theorem arithBundle07_prefix_columns_11 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 52 = 8785959345271 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 48 4 8490233541569 295725803702 arithBundle07_prefix_columns_10 arithBundle07_columns_048
private theorem arithBundle07_prefix_columns_12 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 56 = 9036401760963 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 52 4 8785959345271 250442415692 arithBundle07_prefix_columns_11 arithBundle07_columns_052
private theorem arithBundle07_prefix_columns_13 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 60 = 9245426326739 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 56 4 9036401760963 209024565776 arithBundle07_prefix_columns_12 arithBundle07_columns_056
private theorem arithBundle07_prefix_columns_14 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 64 = 9416909641047 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 60 4 9245426326739 171483314308 arithBundle07_prefix_columns_13 arithBundle07_columns_060
private theorem arithBundle07_prefix_columns_15 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 68 = 9554738911255 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 64 4 9416909641047 137829270208 arithBundle07_prefix_columns_14 arithBundle07_columns_064
private theorem arithBundle07_prefix_columns_16 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 72 = 9662781349839 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 68 4 9554738911255 108042438584 arithBundle07_prefix_columns_15 arithBundle07_columns_068
private theorem arithBundle07_prefix_columns_17 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 76 = 9744902525543 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 72 4 9662781349839 82121175704 arithBundle07_prefix_columns_16 arithBundle07_columns_072
private theorem arithBundle07_prefix_columns_18 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 80 = 9804968338651 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 76 4 9744902525543 60065813108 arithBundle07_prefix_columns_17 arithBundle07_columns_076
private theorem arithBundle07_prefix_columns_19 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 84 = 9846856555056 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 80 4 9804968338651 41888216405 arithBundle07_prefix_columns_18 arithBundle07_columns_080
private theorem arithBundle07_prefix_columns_20 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 88 = 9874405265538 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 84 4 9846856555056 27548710482 arithBundle07_prefix_columns_19 arithBundle07_columns_084
private theorem arithBundle07_prefix_columns_21 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 92 = 9891236872414 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 88 4 9874405265538 16831606876 arithBundle07_prefix_columns_20 arithBundle07_columns_088
private theorem arithBundle07_prefix_columns_22 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 96 = 9900607894140 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 92 4 9891236872414 9371021726 arithBundle07_prefix_columns_21 arithBundle07_columns_092
private theorem arithBundle07_prefix_columns_23 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 100 = 9905249433316 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 96 4 9900607894140 4641539176 arithBundle07_prefix_columns_22 arithBundle07_columns_096
private theorem arithBundle07_prefix_columns_24 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact12) 0 101 = 9905928705090 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact12) 0 100 1 9905249433316 679271774 arithBundle07_prefix_columns_23 arithBundle07_columns_100

private theorem arithBundle07_ordinary_ranks : ordinaryRankBound contact12 = 677296873 := by decide +kernel
private theorem arithBundle07_ranks_000 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 4 = 4274046 :=
  contactRankWindow_of_rec contact12 0 4 4274046 (by decide +kernel)
private theorem arithBundle07_ranks_004 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 4 4 = 3829294 :=
  contactRankWindow_of_rec contact12 4 4 3829294 (by decide +kernel)
private theorem arithBundle07_ranks_008 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 8 4 = 3411294 :=
  contactRankWindow_of_rec contact12 8 4 3411294 (by decide +kernel)
private theorem arithBundle07_ranks_012 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 12 4 = 3020046 :=
  contactRankWindow_of_rec contact12 12 4 3020046 (by decide +kernel)
private theorem arithBundle07_ranks_016 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 16 4 = 2655550 :=
  contactRankWindow_of_rec contact12 16 4 2655550 (by decide +kernel)
private theorem arithBundle07_ranks_020 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 20 4 = 2317806 :=
  contactRankWindow_of_rec contact12 20 4 2317806 (by decide +kernel)
private theorem arithBundle07_ranks_024 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 24 4 = 2006814 :=
  contactRankWindow_of_rec contact12 24 4 2006814 (by decide +kernel)
private theorem arithBundle07_ranks_028 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 28 4 = 1722555 :=
  contactRankWindow_of_rec contact12 28 4 1722555 (by decide +kernel)
private theorem arithBundle07_ranks_032 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 32 4 = 1464625 :=
  contactRankWindow_of_rec contact12 32 4 1464625 (by decide +kernel)
private theorem arithBundle07_ranks_036 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 36 4 = 1232154 :=
  contactRankWindow_of_rec contact12 36 4 1232154 (by decide +kernel)
private theorem arithBundle07_ranks_040 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 40 4 = 1024020 :=
  contactRankWindow_of_rec contact12 40 4 1024020 (by decide +kernel)
private theorem arithBundle07_ranks_044 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 44 4 = 839029 :=
  contactRankWindow_of_rec contact12 44 4 839029 (by decide +kernel)
private theorem arithBundle07_ranks_048 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 48 4 = 676102 :=
  contactRankWindow_of_rec contact12 48 4 676102 (by decide +kernel)
private theorem arithBundle07_ranks_052 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 52 4 = 533984 :=
  contactRankWindow_of_rec contact12 52 4 533984 (by decide +kernel)
private theorem arithBundle07_ranks_056 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 56 4 = 411481 :=
  contactRankWindow_of_rec contact12 56 4 411481 (by decide +kernel)
private theorem arithBundle07_ranks_060 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 60 4 = 307602 :=
  contactRankWindow_of_rec contact12 60 4 307602 (by decide +kernel)
private theorem arithBundle07_ranks_064 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 64 4 = 221004 :=
  contactRankWindow_of_rec contact12 64 4 221004 (by decide +kernel)
private theorem arithBundle07_ranks_068 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 68 4 = 150493 :=
  contactRankWindow_of_rec contact12 68 4 150493 (by decide +kernel)
private theorem arithBundle07_ranks_072 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 72 4 = 95166 :=
  contactRankWindow_of_rec contact12 72 4 95166 (by decide +kernel)
private theorem arithBundle07_ranks_076 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 76 4 = 53592 :=
  contactRankWindow_of_rec contact12 76 4 53592 (by decide +kernel)
private theorem arithBundle07_ranks_080 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 80 4 = 24577 :=
  contactRankWindow_of_rec contact12 80 4 24577 (by decide +kernel)
private theorem arithBundle07_ranks_084 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 84 4 = 7330 :=
  contactRankWindow_of_rec contact12 84 4 7330 (by decide +kernel)
private theorem arithBundle07_ranks_088 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 88 4 = 403 :=
  contactRankWindow_of_rec contact12 88 4 403 (by decide +kernel)
private theorem arithBundle07_ranks_092 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 92 9 = 0 :=
  contactRankWindow_of_rec contact12 92 9 0 (by decide +kernel)
private theorem arithBundle07_prefix_ranks_00 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 8 = 8103340 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 4 4 4274046 3829294 arithBundle07_ranks_000 arithBundle07_ranks_004
private theorem arithBundle07_prefix_ranks_01 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 12 = 11514634 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 8 4 8103340 3411294 arithBundle07_prefix_ranks_00 arithBundle07_ranks_008
private theorem arithBundle07_prefix_ranks_02 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 16 = 14534680 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 12 4 11514634 3020046 arithBundle07_prefix_ranks_01 arithBundle07_ranks_012
private theorem arithBundle07_prefix_ranks_03 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 20 = 17190230 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 16 4 14534680 2655550 arithBundle07_prefix_ranks_02 arithBundle07_ranks_016
private theorem arithBundle07_prefix_ranks_04 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 24 = 19508036 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 20 4 17190230 2317806 arithBundle07_prefix_ranks_03 arithBundle07_ranks_020
private theorem arithBundle07_prefix_ranks_05 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 28 = 21514850 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 24 4 19508036 2006814 arithBundle07_prefix_ranks_04 arithBundle07_ranks_024
private theorem arithBundle07_prefix_ranks_06 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 32 = 23237405 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 28 4 21514850 1722555 arithBundle07_prefix_ranks_05 arithBundle07_ranks_028
private theorem arithBundle07_prefix_ranks_07 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 36 = 24702030 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 32 4 23237405 1464625 arithBundle07_prefix_ranks_06 arithBundle07_ranks_032
private theorem arithBundle07_prefix_ranks_08 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 40 = 25934184 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 36 4 24702030 1232154 arithBundle07_prefix_ranks_07 arithBundle07_ranks_036
private theorem arithBundle07_prefix_ranks_09 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 44 = 26958204 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 40 4 25934184 1024020 arithBundle07_prefix_ranks_08 arithBundle07_ranks_040
private theorem arithBundle07_prefix_ranks_10 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 48 = 27797233 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 44 4 26958204 839029 arithBundle07_prefix_ranks_09 arithBundle07_ranks_044
private theorem arithBundle07_prefix_ranks_11 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 52 = 28473335 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 48 4 27797233 676102 arithBundle07_prefix_ranks_10 arithBundle07_ranks_048
private theorem arithBundle07_prefix_ranks_12 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 56 = 29007319 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 52 4 28473335 533984 arithBundle07_prefix_ranks_11 arithBundle07_ranks_052
private theorem arithBundle07_prefix_ranks_13 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 60 = 29418800 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 56 4 29007319 411481 arithBundle07_prefix_ranks_12 arithBundle07_ranks_056
private theorem arithBundle07_prefix_ranks_14 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 64 = 29726402 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 60 4 29418800 307602 arithBundle07_prefix_ranks_13 arithBundle07_ranks_060
private theorem arithBundle07_prefix_ranks_15 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 68 = 29947406 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 64 4 29726402 221004 arithBundle07_prefix_ranks_14 arithBundle07_ranks_064
private theorem arithBundle07_prefix_ranks_16 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 72 = 30097899 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 68 4 29947406 150493 arithBundle07_prefix_ranks_15 arithBundle07_ranks_068
private theorem arithBundle07_prefix_ranks_17 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 76 = 30193065 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 72 4 30097899 95166 arithBundle07_prefix_ranks_16 arithBundle07_ranks_072
private theorem arithBundle07_prefix_ranks_18 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 80 = 30246657 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 76 4 30193065 53592 arithBundle07_prefix_ranks_17 arithBundle07_ranks_076
private theorem arithBundle07_prefix_ranks_19 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 84 = 30271234 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 80 4 30246657 24577 arithBundle07_prefix_ranks_18 arithBundle07_ranks_080
private theorem arithBundle07_prefix_ranks_20 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 88 = 30278564 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 84 4 30271234 7330 arithBundle07_prefix_ranks_19 arithBundle07_ranks_084
private theorem arithBundle07_prefix_ranks_21 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 92 = 30278967 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 88 4 30278564 403 arithBundle07_prefix_ranks_20 arithBundle07_ranks_088
private theorem arithBundle07_prefix_ranks_22 : arithBundle07_sliceWindow (auxiliaryRankSlice contact12) 0 101 = 30278967 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact12) 0 92 9 30278967 0 arithBundle07_prefix_ranks_21 arithBundle07_ranks_092

theorem contact12_margin : sourceMargin contact12 :=
  arithBundle07_margin_of_checked_counts contact12 101 175580949295062 9905928705090 677296873 30278967
    rfl arithBundle07_ordinary_columns arithBundle07_prefix_columns_24 arithBundle07_ordinary_ranks arithBundle07_prefix_ranks_22 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle08_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle08_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle08_sliceWindow f a b = x) (hy : arithBundle08_sliceWindow f (a+b) c = y) :
    arithBundle08_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle08_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle08_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle08_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle08_sliceWindow,Nat.zero_add]

private theorem arithBundle08_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle08_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle08_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle08_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle08_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle08_ordinary_columns : ordinaryColumnCount contact15 = 185557226246676 := by decide +kernel
private theorem arithBundle08_columns_000 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 4 = 996307489316 :=
  contactColumnsWindow_fast contact15 0 4 996307489316 (by decide +kernel)
private theorem arithBundle08_columns_004 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 4 4 = 914789224186 :=
  contactColumnsWindow_fast contact15 4 4 914789224186 (by decide +kernel)
private theorem arithBundle08_columns_008 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 8 4 = 836786367264 :=
  contactColumnsWindow_fast contact15 8 4 836786367264 (by decide +kernel)
private theorem arithBundle08_columns_012 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 12 4 = 762283015210 :=
  contactColumnsWindow_fast contact15 12 4 762283015210 (by decide +kernel)
private theorem arithBundle08_columns_016 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 16 4 = 691276170596 :=
  contactColumnsWindow_fast contact15 16 4 691276170596 (by decide +kernel)
private theorem arithBundle08_columns_020 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 20 4 = 623764322306 :=
  contactColumnsWindow_fast contact15 20 4 623764322306 (by decide +kernel)
private theorem arithBundle08_columns_024 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 24 4 = 559752370062 :=
  contactColumnsWindow_fast contact15 24 4 559752370062 (by decide +kernel)
private theorem arithBundle08_columns_028 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 28 4 = 499257277135 :=
  contactColumnsWindow_fast contact15 28 4 499257277135 (by decide +kernel)
private theorem arithBundle08_columns_032 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 32 4 = 442263279706 :=
  contactColumnsWindow_fast contact15 32 4 442263279706 (by decide +kernel)
private theorem arithBundle08_columns_036 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 36 4 = 388765885496 :=
  contactColumnsWindow_fast contact15 36 4 388765885496 (by decide +kernel)
private theorem arithBundle08_columns_040 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 40 4 = 338763583970 :=
  contactColumnsWindow_fast contact15 40 4 338763583970 (by decide +kernel)
private theorem arithBundle08_columns_044 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 44 4 = 292262305902 :=
  contactColumnsWindow_fast contact15 44 4 292262305902 (by decide +kernel)
private theorem arithBundle08_columns_048 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 48 4 = 249278075053 :=
  contactColumnsWindow_fast contact15 48 4 249278075053 (by decide +kernel)
private theorem arithBundle08_columns_052 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 52 4 = 209793686533 :=
  contactColumnsWindow_fast contact15 52 4 209793686533 (by decide +kernel)
private theorem arithBundle08_columns_056 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 56 4 = 173805675764 :=
  contactColumnsWindow_fast contact15 56 4 173805675764 (by decide +kernel)
private theorem arithBundle08_columns_060 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 60 4 = 141312921002 :=
  contactColumnsWindow_fast contact15 60 4 141312921002 (by decide +kernel)
private theorem arithBundle08_columns_064 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 64 4 = 112322552705 :=
  contactColumnsWindow_fast contact15 64 4 112322552705 (by decide +kernel)
private theorem arithBundle08_columns_068 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 68 4 = 86849035644 :=
  contactColumnsWindow_fast contact15 68 4 86849035644 (by decide +kernel)
private theorem arithBundle08_columns_072 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 72 4 = 64874183671 :=
  contactColumnsWindow_fast contact15 72 4 64874183671 (by decide +kernel)
private theorem arithBundle08_columns_076 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 76 4 = 46395541400 :=
  contactColumnsWindow_fast contact15 76 4 46395541400 (by decide +kernel)
private theorem arithBundle08_columns_080 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 80 4 = 31409367030 :=
  contactColumnsWindow_fast contact15 80 4 31409367030 (by decide +kernel)
private theorem arithBundle08_columns_084 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 84 4 = 19858063856 :=
  contactColumnsWindow_fast contact15 84 4 19858063856 (by decide +kernel)
private theorem arithBundle08_columns_088 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 88 4 = 11523778321 :=
  contactColumnsWindow_fast contact15 88 4 11523778321 (by decide +kernel)
private theorem arithBundle08_columns_092 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 92 4 = 5992987395 :=
  contactColumnsWindow_fast contact15 92 4 5992987395 (by decide +kernel)
private theorem arithBundle08_columns_096 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 96 3 = 2241814120 :=
  contactColumnsWindow_fast contact15 96 3 2241814120 (by decide +kernel)
private theorem arithBundle08_prefix_columns_00 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 8 = 1911096713502 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 4 4 996307489316 914789224186 arithBundle08_columns_000 arithBundle08_columns_004
private theorem arithBundle08_prefix_columns_01 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 12 = 2747883080766 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 8 4 1911096713502 836786367264 arithBundle08_prefix_columns_00 arithBundle08_columns_008
private theorem arithBundle08_prefix_columns_02 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 16 = 3510166095976 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 12 4 2747883080766 762283015210 arithBundle08_prefix_columns_01 arithBundle08_columns_012
private theorem arithBundle08_prefix_columns_03 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 20 = 4201442266572 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 16 4 3510166095976 691276170596 arithBundle08_prefix_columns_02 arithBundle08_columns_016
private theorem arithBundle08_prefix_columns_04 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 24 = 4825206588878 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 20 4 4201442266572 623764322306 arithBundle08_prefix_columns_03 arithBundle08_columns_020
private theorem arithBundle08_prefix_columns_05 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 28 = 5384958958940 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 24 4 4825206588878 559752370062 arithBundle08_prefix_columns_04 arithBundle08_columns_024
private theorem arithBundle08_prefix_columns_06 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 32 = 5884216236075 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 28 4 5384958958940 499257277135 arithBundle08_prefix_columns_05 arithBundle08_columns_028
private theorem arithBundle08_prefix_columns_07 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 36 = 6326479515781 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 32 4 5884216236075 442263279706 arithBundle08_prefix_columns_06 arithBundle08_columns_032
private theorem arithBundle08_prefix_columns_08 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 40 = 6715245401277 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 36 4 6326479515781 388765885496 arithBundle08_prefix_columns_07 arithBundle08_columns_036
private theorem arithBundle08_prefix_columns_09 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 44 = 7054008985247 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 40 4 6715245401277 338763583970 arithBundle08_prefix_columns_08 arithBundle08_columns_040
private theorem arithBundle08_prefix_columns_10 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 48 = 7346271291149 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 44 4 7054008985247 292262305902 arithBundle08_prefix_columns_09 arithBundle08_columns_044
private theorem arithBundle08_prefix_columns_11 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 52 = 7595549366202 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 48 4 7346271291149 249278075053 arithBundle08_prefix_columns_10 arithBundle08_columns_048
private theorem arithBundle08_prefix_columns_12 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 56 = 7805343052735 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 52 4 7595549366202 209793686533 arithBundle08_prefix_columns_11 arithBundle08_columns_052
private theorem arithBundle08_prefix_columns_13 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 60 = 7979148728499 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 56 4 7805343052735 173805675764 arithBundle08_prefix_columns_12 arithBundle08_columns_056
private theorem arithBundle08_prefix_columns_14 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 64 = 8120461649501 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 60 4 7979148728499 141312921002 arithBundle08_prefix_columns_13 arithBundle08_columns_060
private theorem arithBundle08_prefix_columns_15 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 68 = 8232784202206 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 64 4 8120461649501 112322552705 arithBundle08_prefix_columns_14 arithBundle08_columns_064
private theorem arithBundle08_prefix_columns_16 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 72 = 8319633237850 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 68 4 8232784202206 86849035644 arithBundle08_prefix_columns_15 arithBundle08_columns_068
private theorem arithBundle08_prefix_columns_17 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 76 = 8384507421521 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 72 4 8319633237850 64874183671 arithBundle08_prefix_columns_16 arithBundle08_columns_072
private theorem arithBundle08_prefix_columns_18 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 80 = 8430902962921 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 76 4 8384507421521 46395541400 arithBundle08_prefix_columns_17 arithBundle08_columns_076
private theorem arithBundle08_prefix_columns_19 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 84 = 8462312329951 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 80 4 8430902962921 31409367030 arithBundle08_prefix_columns_18 arithBundle08_columns_080
private theorem arithBundle08_prefix_columns_20 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 88 = 8482170393807 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 84 4 8462312329951 19858063856 arithBundle08_prefix_columns_19 arithBundle08_columns_084
private theorem arithBundle08_prefix_columns_21 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 92 = 8493694172128 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 88 4 8482170393807 11523778321 arithBundle08_prefix_columns_20 arithBundle08_columns_088
private theorem arithBundle08_prefix_columns_22 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 96 = 8499687159523 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 92 4 8493694172128 5992987395 arithBundle08_prefix_columns_21 arithBundle08_columns_092
private theorem arithBundle08_prefix_columns_23 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact15) 0 99 = 8501928973643 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact15) 0 96 3 8499687159523 2241814120 arithBundle08_prefix_columns_22 arithBundle08_columns_096

private theorem arithBundle08_ordinary_ranks : ordinaryRankBound contact15 = 714386484 := by decide +kernel
private theorem arithBundle08_ranks_000 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 4 = 3732054 :=
  contactRankWindow_of_rec contact15 0 4 3732054 (by decide +kernel)
private theorem arithBundle08_ranks_004 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 4 4 = 3335910 :=
  contactRankWindow_of_rec contact15 4 4 3335910 (by decide +kernel)
private theorem arithBundle08_ranks_008 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 8 4 = 2963958 :=
  contactRankWindow_of_rec contact15 8 4 2963958 (by decide +kernel)
private theorem arithBundle08_ranks_012 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 12 4 = 2616198 :=
  contactRankWindow_of_rec contact15 12 4 2616198 (by decide +kernel)
private theorem arithBundle08_ranks_016 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 16 4 = 2292630 :=
  contactRankWindow_of_rec contact15 16 4 2292630 (by decide +kernel)
private theorem arithBundle08_ranks_020 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 20 4 = 1993254 :=
  contactRankWindow_of_rec contact15 20 4 1993254 (by decide +kernel)
private theorem arithBundle08_ranks_024 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 24 4 = 1718070 :=
  contactRankWindow_of_rec contact15 24 4 1718070 (by decide +kernel)
private theorem arithBundle08_ranks_028 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 28 4 = 1467078 :=
  contactRankWindow_of_rec contact15 28 4 1467078 (by decide +kernel)
private theorem arithBundle08_ranks_032 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 32 4 = 1240024 :=
  contactRankWindow_of_rec contact15 32 4 1240024 (by decide +kernel)
private theorem arithBundle08_ranks_036 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 36 4 = 1036163 :=
  contactRankWindow_of_rec contact15 36 4 1036163 (by decide +kernel)
private theorem arithBundle08_ranks_040 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 40 4 = 854492 :=
  contactRankWindow_of_rec contact15 40 4 854492 (by decide +kernel)
private theorem arithBundle08_ranks_044 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 44 4 = 693880 :=
  contactRankWindow_of_rec contact15 44 4 693880 (by decide +kernel)
private theorem arithBundle08_ranks_048 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 48 4 = 553191 :=
  contactRankWindow_of_rec contact15 48 4 553191 (by decide +kernel)
private theorem arithBundle08_ranks_052 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 52 4 = 431420 :=
  contactRankWindow_of_rec contact15 52 4 431420 (by decide +kernel)
private theorem arithBundle08_ranks_056 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 56 4 = 327352 :=
  contactRankWindow_of_rec contact15 56 4 327352 (by decide +kernel)
private theorem arithBundle08_ranks_060 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 60 4 = 239851 :=
  contactRankWindow_of_rec contact15 60 4 239851 (by decide +kernel)
private theorem arithBundle08_ranks_064 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 64 4 = 167996 :=
  contactRankWindow_of_rec contact15 64 4 167996 (by decide +kernel)
private theorem arithBundle08_ranks_068 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 68 4 = 110488 :=
  contactRankWindow_of_rec contact15 68 4 110488 (by decide +kernel)
private theorem arithBundle08_ranks_072 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 72 4 = 66191 :=
  contactRankWindow_of_rec contact15 72 4 66191 (by decide +kernel)
private theorem arithBundle08_ranks_076 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 76 4 = 34268 :=
  contactRankWindow_of_rec contact15 76 4 34268 (by decide +kernel)
private theorem arithBundle08_ranks_080 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 80 4 = 13336 :=
  contactRankWindow_of_rec contact15 80 4 13336 (by decide +kernel)
private theorem arithBundle08_ranks_084 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 84 4 = 2298 :=
  contactRankWindow_of_rec contact15 84 4 2298 (by decide +kernel)
private theorem arithBundle08_ranks_088 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 88 11 = 0 :=
  contactRankWindow_of_rec contact15 88 11 0 (by decide +kernel)
private theorem arithBundle08_prefix_ranks_00 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 8 = 7067964 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 4 4 3732054 3335910 arithBundle08_ranks_000 arithBundle08_ranks_004
private theorem arithBundle08_prefix_ranks_01 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 12 = 10031922 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 8 4 7067964 2963958 arithBundle08_prefix_ranks_00 arithBundle08_ranks_008
private theorem arithBundle08_prefix_ranks_02 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 16 = 12648120 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 12 4 10031922 2616198 arithBundle08_prefix_ranks_01 arithBundle08_ranks_012
private theorem arithBundle08_prefix_ranks_03 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 20 = 14940750 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 16 4 12648120 2292630 arithBundle08_prefix_ranks_02 arithBundle08_ranks_016
private theorem arithBundle08_prefix_ranks_04 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 24 = 16934004 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 20 4 14940750 1993254 arithBundle08_prefix_ranks_03 arithBundle08_ranks_020
private theorem arithBundle08_prefix_ranks_05 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 28 = 18652074 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 24 4 16934004 1718070 arithBundle08_prefix_ranks_04 arithBundle08_ranks_024
private theorem arithBundle08_prefix_ranks_06 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 32 = 20119152 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 28 4 18652074 1467078 arithBundle08_prefix_ranks_05 arithBundle08_ranks_028
private theorem arithBundle08_prefix_ranks_07 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 36 = 21359176 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 32 4 20119152 1240024 arithBundle08_prefix_ranks_06 arithBundle08_ranks_032
private theorem arithBundle08_prefix_ranks_08 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 40 = 22395339 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 36 4 21359176 1036163 arithBundle08_prefix_ranks_07 arithBundle08_ranks_036
private theorem arithBundle08_prefix_ranks_09 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 44 = 23249831 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 40 4 22395339 854492 arithBundle08_prefix_ranks_08 arithBundle08_ranks_040
private theorem arithBundle08_prefix_ranks_10 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 48 = 23943711 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 44 4 23249831 693880 arithBundle08_prefix_ranks_09 arithBundle08_ranks_044
private theorem arithBundle08_prefix_ranks_11 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 52 = 24496902 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 48 4 23943711 553191 arithBundle08_prefix_ranks_10 arithBundle08_ranks_048
private theorem arithBundle08_prefix_ranks_12 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 56 = 24928322 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 52 4 24496902 431420 arithBundle08_prefix_ranks_11 arithBundle08_ranks_052
private theorem arithBundle08_prefix_ranks_13 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 60 = 25255674 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 56 4 24928322 327352 arithBundle08_prefix_ranks_12 arithBundle08_ranks_056
private theorem arithBundle08_prefix_ranks_14 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 64 = 25495525 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 60 4 25255674 239851 arithBundle08_prefix_ranks_13 arithBundle08_ranks_060
private theorem arithBundle08_prefix_ranks_15 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 68 = 25663521 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 64 4 25495525 167996 arithBundle08_prefix_ranks_14 arithBundle08_ranks_064
private theorem arithBundle08_prefix_ranks_16 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 72 = 25774009 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 68 4 25663521 110488 arithBundle08_prefix_ranks_15 arithBundle08_ranks_068
private theorem arithBundle08_prefix_ranks_17 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 76 = 25840200 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 72 4 25774009 66191 arithBundle08_prefix_ranks_16 arithBundle08_ranks_072
private theorem arithBundle08_prefix_ranks_18 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 80 = 25874468 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 76 4 25840200 34268 arithBundle08_prefix_ranks_17 arithBundle08_ranks_076
private theorem arithBundle08_prefix_ranks_19 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 84 = 25887804 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 80 4 25874468 13336 arithBundle08_prefix_ranks_18 arithBundle08_ranks_080
private theorem arithBundle08_prefix_ranks_20 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 88 = 25890102 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 84 4 25887804 2298 arithBundle08_prefix_ranks_19 arithBundle08_ranks_084
private theorem arithBundle08_prefix_ranks_21 : arithBundle08_sliceWindow (auxiliaryRankSlice contact15) 0 99 = 25890102 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact15) 0 88 11 25890102 0 arithBundle08_prefix_ranks_20 arithBundle08_ranks_088

theorem contact15_margin : sourceMargin contact15 :=
  arithBundle08_margin_of_checked_counts contact15 99 185557226246676 8501928973643 714386484 25890102
    rfl arithBundle08_ordinary_columns arithBundle08_prefix_columns_23 arithBundle08_ordinary_ranks arithBundle08_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle09_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle09_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle09_sliceWindow f a b = x) (hy : arithBundle09_sliceWindow f (a+b) c = y) :
    arithBundle09_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle09_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle09_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle09_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle09_sliceWindow,Nat.zero_add]

private theorem arithBundle09_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle09_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle09_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle09_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle09_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle09_ordinary_columns : ordinaryColumnCount contact17 = 2609539590685311 := by decide +kernel
private theorem arithBundle09_columns_000 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 4 = 6595539034492 :=
  contactColumnsWindow_fast contact17 0 4 6595539034492 (by decide +kernel)
private theorem arithBundle09_columns_004 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 4 4 = 6259960296484 :=
  contactColumnsWindow_fast contact17 4 4 6259960296484 (by decide +kernel)
private theorem arithBundle09_columns_008 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 8 4 = 5933184123048 :=
  contactColumnsWindow_fast contact17 8 4 5933184123048 (by decide +kernel)
private theorem arithBundle09_columns_012 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 12 4 = 5615211910196 :=
  contactColumnsWindow_fast contact17 12 4 5615211910196 (by decide +kernel)
private theorem arithBundle09_columns_016 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 16 4 = 5306080544844 :=
  contactColumnsWindow_fast contact17 16 4 5306080544844 (by decide +kernel)
private theorem arithBundle09_columns_020 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 20 4 = 5005763193138 :=
  contactColumnsWindow_fast contact17 20 4 5005763193138 (by decide +kernel)
private theorem arithBundle09_columns_024 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 24 4 = 4714250899455 :=
  contactColumnsWindow_fast contact17 24 4 4714250899455 (by decide +kernel)
private theorem arithBundle09_columns_028 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 28 4 = 4431543155643 :=
  contactColumnsWindow_fast contact17 28 4 4431543155643 (by decide +kernel)
private theorem arithBundle09_columns_032 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 32 4 = 4157645622528 :=
  contactColumnsWindow_fast contact17 32 4 4157645622528 (by decide +kernel)
private theorem arithBundle09_columns_036 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 36 4 = 3892591435955 :=
  contactColumnsWindow_fast contact17 36 4 3892591435955 (by decide +kernel)
private theorem arithBundle09_columns_040 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 40 4 = 3636353042152 :=
  contactColumnsWindow_fast contact17 40 4 3636353042152 (by decide +kernel)
private theorem arithBundle09_columns_044 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 44 4 = 3388922071570 :=
  contactColumnsWindow_fast contact17 44 4 3388922071570 (by decide +kernel)
private theorem arithBundle09_columns_048 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 48 4 = 3150299652162 :=
  contactColumnsWindow_fast contact17 48 4 3150299652162 (by decide +kernel)
private theorem arithBundle09_columns_052 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 52 4 = 2920492685360 :=
  contactColumnsWindow_fast contact17 52 4 2920492685360 (by decide +kernel)
private theorem arithBundle09_columns_056 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 56 4 = 2699532517724 :=
  contactColumnsWindow_fast contact17 56 4 2699532517724 (by decide +kernel)
private theorem arithBundle09_columns_060 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 60 4 = 2487390033238 :=
  contactColumnsWindow_fast contact17 60 4 2487390033238 (by decide +kernel)
private theorem arithBundle09_columns_064 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 64 4 = 2284057479688 :=
  contactColumnsWindow_fast contact17 64 4 2284057479688 (by decide +kernel)
private theorem arithBundle09_columns_068 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 68 4 = 2089533132285 :=
  contactColumnsWindow_fast contact17 68 4 2089533132285 (by decide +kernel)
private theorem arithBundle09_columns_072 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 72 4 = 1903826959564 :=
  contactColumnsWindow_fast contact17 72 4 1903826959564 (by decide +kernel)
private theorem arithBundle09_columns_076 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 76 4 = 1726967514952 :=
  contactColumnsWindow_fast contact17 76 4 1726967514952 (by decide +kernel)
private theorem arithBundle09_columns_080 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 80 4 = 1558923566383 :=
  contactColumnsWindow_fast contact17 80 4 1558923566383 (by decide +kernel)
private theorem arithBundle09_columns_084 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 84 4 = 1399689373918 :=
  contactColumnsWindow_fast contact17 84 4 1399689373918 (by decide +kernel)
private theorem arithBundle09_columns_088 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 88 4 = 1249263243676 :=
  contactColumnsWindow_fast contact17 88 4 1249263243676 (by decide +kernel)
private theorem arithBundle09_columns_092 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 92 4 = 1107658871476 :=
  contactColumnsWindow_fast contact17 92 4 1107658871476 (by decide +kernel)
private theorem arithBundle09_columns_096 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 96 4 = 974899045447 :=
  contactColumnsWindow_fast contact17 96 4 974899045447 (by decide +kernel)
private theorem arithBundle09_columns_100 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 100 4 = 850953635572 :=
  contactColumnsWindow_fast contact17 100 4 850953635572 (by decide +kernel)
private theorem arithBundle09_columns_104 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 104 4 = 735817826499 :=
  contactColumnsWindow_fast contact17 104 4 735817826499 (by decide +kernel)
private theorem arithBundle09_columns_108 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 108 4 = 629489965831 :=
  contactColumnsWindow_fast contact17 108 4 629489965831 (by decide +kernel)
private theorem arithBundle09_columns_112 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 112 4 = 531987269500 :=
  contactColumnsWindow_fast contact17 112 4 531987269500 (by decide +kernel)
private theorem arithBundle09_columns_116 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 116 4 = 443327155523 :=
  contactColumnsWindow_fast contact17 116 4 443327155523 (by decide +kernel)
private theorem arithBundle09_columns_120 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 120 4 = 363480373369 :=
  contactColumnsWindow_fast contact17 120 4 363480373369 (by decide +kernel)
private theorem arithBundle09_columns_124 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 124 4 = 292442806176 :=
  contactColumnsWindow_fast contact17 124 4 292442806176 (by decide +kernel)
private theorem arithBundle09_columns_128 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 128 4 = 230212496489 :=
  contactColumnsWindow_fast contact17 128 4 230212496489 (by decide +kernel)
private theorem arithBundle09_columns_132 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 132 4 = 176769932000 :=
  contactColumnsWindow_fast contact17 132 4 176769932000 (by decide +kernel)
private theorem arithBundle09_columns_136 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 136 4 = 131912766155 :=
  contactColumnsWindow_fast contact17 136 4 131912766155 (by decide +kernel)
private theorem arithBundle09_columns_140 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 140 4 = 95212794228 :=
  contactColumnsWindow_fast contact17 140 4 95212794228 (by decide +kernel)
private theorem arithBundle09_columns_144 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 144 4 = 66107278616 :=
  contactColumnsWindow_fast contact17 144 4 66107278616 (by decide +kernel)
private theorem arithBundle09_columns_148 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 148 4 = 43874673107 :=
  contactColumnsWindow_fast contact17 148 4 43874673107 (by decide +kernel)
private theorem arithBundle09_columns_152 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 152 4 = 27647181875 :=
  contactColumnsWindow_fast contact17 152 4 27647181875 (by decide +kernel)
private theorem arithBundle09_columns_156 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 156 4 = 16389782323 :=
  contactColumnsWindow_fast contact17 156 4 16389782323 (by decide +kernel)
private theorem arithBundle09_columns_160 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 160 2 = 5225631255 :=
  contactColumnsWindow_fast contact17 160 2 5225631255 (by decide +kernel)
private theorem arithBundle09_prefix_columns_00 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 8 = 12855499330976 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 4 4 6595539034492 6259960296484 arithBundle09_columns_000 arithBundle09_columns_004
private theorem arithBundle09_prefix_columns_01 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 12 = 18788683454024 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 8 4 12855499330976 5933184123048 arithBundle09_prefix_columns_00 arithBundle09_columns_008
private theorem arithBundle09_prefix_columns_02 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 16 = 24403895364220 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 12 4 18788683454024 5615211910196 arithBundle09_prefix_columns_01 arithBundle09_columns_012
private theorem arithBundle09_prefix_columns_03 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 20 = 29709975909064 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 16 4 24403895364220 5306080544844 arithBundle09_prefix_columns_02 arithBundle09_columns_016
private theorem arithBundle09_prefix_columns_04 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 24 = 34715739102202 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 20 4 29709975909064 5005763193138 arithBundle09_prefix_columns_03 arithBundle09_columns_020
private theorem arithBundle09_prefix_columns_05 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 28 = 39429990001657 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 24 4 34715739102202 4714250899455 arithBundle09_prefix_columns_04 arithBundle09_columns_024
private theorem arithBundle09_prefix_columns_06 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 32 = 43861533157300 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 28 4 39429990001657 4431543155643 arithBundle09_prefix_columns_05 arithBundle09_columns_028
private theorem arithBundle09_prefix_columns_07 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 36 = 48019178779828 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 32 4 43861533157300 4157645622528 arithBundle09_prefix_columns_06 arithBundle09_columns_032
private theorem arithBundle09_prefix_columns_08 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 40 = 51911770215783 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 36 4 48019178779828 3892591435955 arithBundle09_prefix_columns_07 arithBundle09_columns_036
private theorem arithBundle09_prefix_columns_09 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 44 = 55548123257935 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 40 4 51911770215783 3636353042152 arithBundle09_prefix_columns_08 arithBundle09_columns_040
private theorem arithBundle09_prefix_columns_10 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 48 = 58937045329505 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 44 4 55548123257935 3388922071570 arithBundle09_prefix_columns_09 arithBundle09_columns_044
private theorem arithBundle09_prefix_columns_11 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 52 = 62087344981667 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 48 4 58937045329505 3150299652162 arithBundle09_prefix_columns_10 arithBundle09_columns_048
private theorem arithBundle09_prefix_columns_12 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 56 = 65007837667027 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 52 4 62087344981667 2920492685360 arithBundle09_prefix_columns_11 arithBundle09_columns_052
private theorem arithBundle09_prefix_columns_13 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 60 = 67707370184751 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 56 4 65007837667027 2699532517724 arithBundle09_prefix_columns_12 arithBundle09_columns_056
private theorem arithBundle09_prefix_columns_14 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 64 = 70194760217989 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 60 4 67707370184751 2487390033238 arithBundle09_prefix_columns_13 arithBundle09_columns_060
private theorem arithBundle09_prefix_columns_15 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 68 = 72478817697677 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 64 4 70194760217989 2284057479688 arithBundle09_prefix_columns_14 arithBundle09_columns_064
private theorem arithBundle09_prefix_columns_16 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 72 = 74568350829962 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 68 4 72478817697677 2089533132285 arithBundle09_prefix_columns_15 arithBundle09_columns_068
private theorem arithBundle09_prefix_columns_17 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 76 = 76472177789526 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 72 4 74568350829962 1903826959564 arithBundle09_prefix_columns_16 arithBundle09_columns_072
private theorem arithBundle09_prefix_columns_18 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 80 = 78199145304478 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 76 4 76472177789526 1726967514952 arithBundle09_prefix_columns_17 arithBundle09_columns_076
private theorem arithBundle09_prefix_columns_19 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 84 = 79758068870861 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 80 4 78199145304478 1558923566383 arithBundle09_prefix_columns_18 arithBundle09_columns_080
private theorem arithBundle09_prefix_columns_20 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 88 = 81157758244779 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 84 4 79758068870861 1399689373918 arithBundle09_prefix_columns_19 arithBundle09_columns_084
private theorem arithBundle09_prefix_columns_21 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 92 = 82407021488455 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 88 4 81157758244779 1249263243676 arithBundle09_prefix_columns_20 arithBundle09_columns_088
private theorem arithBundle09_prefix_columns_22 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 96 = 83514680359931 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 92 4 82407021488455 1107658871476 arithBundle09_prefix_columns_21 arithBundle09_columns_092
private theorem arithBundle09_prefix_columns_23 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 100 = 84489579405378 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 96 4 83514680359931 974899045447 arithBundle09_prefix_columns_22 arithBundle09_columns_096
private theorem arithBundle09_prefix_columns_24 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 104 = 85340533040950 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 100 4 84489579405378 850953635572 arithBundle09_prefix_columns_23 arithBundle09_columns_100
private theorem arithBundle09_prefix_columns_25 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 108 = 86076350867449 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 104 4 85340533040950 735817826499 arithBundle09_prefix_columns_24 arithBundle09_columns_104
private theorem arithBundle09_prefix_columns_26 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 112 = 86705840833280 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 108 4 86076350867449 629489965831 arithBundle09_prefix_columns_25 arithBundle09_columns_108
private theorem arithBundle09_prefix_columns_27 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 116 = 87237828102780 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 112 4 86705840833280 531987269500 arithBundle09_prefix_columns_26 arithBundle09_columns_112
private theorem arithBundle09_prefix_columns_28 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 120 = 87681155258303 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 116 4 87237828102780 443327155523 arithBundle09_prefix_columns_27 arithBundle09_columns_116
private theorem arithBundle09_prefix_columns_29 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 124 = 88044635631672 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 120 4 87681155258303 363480373369 arithBundle09_prefix_columns_28 arithBundle09_columns_120
private theorem arithBundle09_prefix_columns_30 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 128 = 88337078437848 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 124 4 88044635631672 292442806176 arithBundle09_prefix_columns_29 arithBundle09_columns_124
private theorem arithBundle09_prefix_columns_31 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 132 = 88567290934337 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 128 4 88337078437848 230212496489 arithBundle09_prefix_columns_30 arithBundle09_columns_128
private theorem arithBundle09_prefix_columns_32 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 136 = 88744060866337 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 132 4 88567290934337 176769932000 arithBundle09_prefix_columns_31 arithBundle09_columns_132
private theorem arithBundle09_prefix_columns_33 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 140 = 88875973632492 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 136 4 88744060866337 131912766155 arithBundle09_prefix_columns_32 arithBundle09_columns_136
private theorem arithBundle09_prefix_columns_34 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 144 = 88971186426720 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 140 4 88875973632492 95212794228 arithBundle09_prefix_columns_33 arithBundle09_columns_140
private theorem arithBundle09_prefix_columns_35 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 148 = 89037293705336 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 144 4 88971186426720 66107278616 arithBundle09_prefix_columns_34 arithBundle09_columns_144
private theorem arithBundle09_prefix_columns_36 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 152 = 89081168378443 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 148 4 89037293705336 43874673107 arithBundle09_prefix_columns_35 arithBundle09_columns_148
private theorem arithBundle09_prefix_columns_37 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 156 = 89108815560318 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 152 4 89081168378443 27647181875 arithBundle09_prefix_columns_36 arithBundle09_columns_152
private theorem arithBundle09_prefix_columns_38 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 160 = 89125205342641 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 156 4 89108815560318 16389782323 arithBundle09_prefix_columns_37 arithBundle09_columns_156
private theorem arithBundle09_prefix_columns_39 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact17) 0 162 = 89130430973896 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact17) 0 160 2 89125205342641 5225631255 arithBundle09_prefix_columns_38 arithBundle09_columns_160

private theorem arithBundle09_ordinary_ranks : ordinaryRankBound contact17 = 10022924642 := by decide +kernel
private theorem arithBundle09_ranks_000 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 4 = 24869468 :=
  contactRankWindow_of_rec contact17 0 4 24869468 (by decide +kernel)
private theorem arithBundle09_ranks_004 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 4 4 = 23224412 :=
  contactRankWindow_of_rec contact17 4 4 23224412 (by decide +kernel)
private theorem arithBundle09_ranks_008 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 8 4 = 21640284 :=
  contactRankWindow_of_rec contact17 8 4 21640284 (by decide +kernel)
private theorem arithBundle09_ranks_012 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 12 4 = 20117084 :=
  contactRankWindow_of_rec contact17 12 4 20117084 (by decide +kernel)
private theorem arithBundle09_ranks_016 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 16 4 = 18654812 :=
  contactRankWindow_of_rec contact17 16 4 18654812 (by decide +kernel)
private theorem arithBundle09_ranks_020 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 20 4 = 17253468 :=
  contactRankWindow_of_rec contact17 20 4 17253468 (by decide +kernel)
private theorem arithBundle09_ranks_024 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 24 4 = 15913052 :=
  contactRankWindow_of_rec contact17 24 4 15913052 (by decide +kernel)
private theorem arithBundle09_ranks_028 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 28 4 = 14633564 :=
  contactRankWindow_of_rec contact17 28 4 14633564 (by decide +kernel)
private theorem arithBundle09_ranks_032 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 32 4 = 13415004 :=
  contactRankWindow_of_rec contact17 32 4 13415004 (by decide +kernel)
private theorem arithBundle09_ranks_036 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 36 4 = 12257372 :=
  contactRankWindow_of_rec contact17 36 4 12257372 (by decide +kernel)
private theorem arithBundle09_ranks_040 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 40 4 = 11160668 :=
  contactRankWindow_of_rec contact17 40 4 11160668 (by decide +kernel)
private theorem arithBundle09_ranks_044 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 44 4 = 10124892 :=
  contactRankWindow_of_rec contact17 44 4 10124892 (by decide +kernel)
private theorem arithBundle09_ranks_048 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 48 4 = 9149960 :=
  contactRankWindow_of_rec contact17 48 4 9149960 (by decide +kernel)
private theorem arithBundle09_ranks_052 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 52 4 = 8235050 :=
  contactRankWindow_of_rec contact17 52 4 8235050 (by decide +kernel)
private theorem arithBundle09_ranks_056 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 56 4 = 7378924 :=
  contactRankWindow_of_rec contact17 56 4 7378924 (by decide +kernel)
private theorem arithBundle09_ranks_060 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 60 4 = 6580306 :=
  contactRankWindow_of_rec contact17 60 4 6580306 (by decide +kernel)
private theorem arithBundle09_ranks_064 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 64 4 = 5837604 :=
  contactRankWindow_of_rec contact17 64 4 5837604 (by decide +kernel)
private theorem arithBundle09_ranks_068 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 68 4 = 5149020 :=
  contactRankWindow_of_rec contact17 68 4 5149020 (by decide +kernel)
private theorem arithBundle09_ranks_072 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 72 4 = 4512746 :=
  contactRankWindow_of_rec contact17 72 4 4512746 (by decide +kernel)
private theorem arithBundle09_ranks_076 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 76 4 = 3927188 :=
  contactRankWindow_of_rec contact17 76 4 3927188 (by decide +kernel)
private theorem arithBundle09_ranks_080 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 80 4 = 3390412 :=
  contactRankWindow_of_rec contact17 80 4 3390412 (by decide +kernel)
private theorem arithBundle09_ranks_084 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 84 4 = 2900610 :=
  contactRankWindow_of_rec contact17 84 4 2900610 (by decide +kernel)
private theorem arithBundle09_ranks_088 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 88 4 = 2456324 :=
  contactRankWindow_of_rec contact17 88 4 2456324 (by decide +kernel)
private theorem arithBundle09_ranks_092 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 92 4 = 2055484 :=
  contactRankWindow_of_rec contact17 92 4 2055484 (by decide +kernel)
private theorem arithBundle09_ranks_096 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 96 4 = 1696282 :=
  contactRankWindow_of_rec contact17 96 4 1696282 (by decide +kernel)
private theorem arithBundle09_ranks_100 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 100 4 = 1377396 :=
  contactRankWindow_of_rec contact17 100 4 1377396 (by decide +kernel)
private theorem arithBundle09_ranks_104 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 104 4 = 1096620 :=
  contactRankWindow_of_rec contact17 104 4 1096620 (by decide +kernel)
private theorem arithBundle09_ranks_108 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 108 4 = 852146 :=
  contactRankWindow_of_rec contact17 108 4 852146 (by decide +kernel)
private theorem arithBundle09_ranks_112 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 112 4 = 642788 :=
  contactRankWindow_of_rec contact17 112 4 642788 (by decide +kernel)
private theorem arithBundle09_ranks_116 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 116 4 = 466204 :=
  contactRankWindow_of_rec contact17 116 4 466204 (by decide +kernel)
private theorem arithBundle09_ranks_120 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 120 4 = 320586 :=
  contactRankWindow_of_rec contact17 120 4 320586 (by decide +kernel)
private theorem arithBundle09_ranks_124 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 124 4 = 204884 :=
  contactRankWindow_of_rec contact17 124 4 204884 (by decide +kernel)
private theorem arithBundle09_ranks_128 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 128 4 = 116620 :=
  contactRankWindow_of_rec contact17 128 4 116620 (by decide +kernel)
private theorem arithBundle09_ranks_132 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 132 4 = 54001 :=
  contactRankWindow_of_rec contact17 132 4 54001 (by decide +kernel)
private theorem arithBundle09_ranks_136 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 136 4 = 16315 :=
  contactRankWindow_of_rec contact17 136 4 16315 (by decide +kernel)
private theorem arithBundle09_ranks_140 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 140 4 = 916 :=
  contactRankWindow_of_rec contact17 140 4 916 (by decide +kernel)
private theorem arithBundle09_ranks_144 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 144 18 = 0 :=
  contactRankWindow_of_rec contact17 144 18 0 (by decide +kernel)
private theorem arithBundle09_prefix_ranks_00 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 8 = 48093880 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 4 4 24869468 23224412 arithBundle09_ranks_000 arithBundle09_ranks_004
private theorem arithBundle09_prefix_ranks_01 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 12 = 69734164 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 8 4 48093880 21640284 arithBundle09_prefix_ranks_00 arithBundle09_ranks_008
private theorem arithBundle09_prefix_ranks_02 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 16 = 89851248 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 12 4 69734164 20117084 arithBundle09_prefix_ranks_01 arithBundle09_ranks_012
private theorem arithBundle09_prefix_ranks_03 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 20 = 108506060 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 16 4 89851248 18654812 arithBundle09_prefix_ranks_02 arithBundle09_ranks_016
private theorem arithBundle09_prefix_ranks_04 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 24 = 125759528 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 20 4 108506060 17253468 arithBundle09_prefix_ranks_03 arithBundle09_ranks_020
private theorem arithBundle09_prefix_ranks_05 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 28 = 141672580 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 24 4 125759528 15913052 arithBundle09_prefix_ranks_04 arithBundle09_ranks_024
private theorem arithBundle09_prefix_ranks_06 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 32 = 156306144 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 28 4 141672580 14633564 arithBundle09_prefix_ranks_05 arithBundle09_ranks_028
private theorem arithBundle09_prefix_ranks_07 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 36 = 169721148 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 32 4 156306144 13415004 arithBundle09_prefix_ranks_06 arithBundle09_ranks_032
private theorem arithBundle09_prefix_ranks_08 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 40 = 181978520 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 36 4 169721148 12257372 arithBundle09_prefix_ranks_07 arithBundle09_ranks_036
private theorem arithBundle09_prefix_ranks_09 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 44 = 193139188 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 40 4 181978520 11160668 arithBundle09_prefix_ranks_08 arithBundle09_ranks_040
private theorem arithBundle09_prefix_ranks_10 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 48 = 203264080 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 44 4 193139188 10124892 arithBundle09_prefix_ranks_09 arithBundle09_ranks_044
private theorem arithBundle09_prefix_ranks_11 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 52 = 212414040 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 48 4 203264080 9149960 arithBundle09_prefix_ranks_10 arithBundle09_ranks_048
private theorem arithBundle09_prefix_ranks_12 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 56 = 220649090 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 52 4 212414040 8235050 arithBundle09_prefix_ranks_11 arithBundle09_ranks_052
private theorem arithBundle09_prefix_ranks_13 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 60 = 228028014 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 56 4 220649090 7378924 arithBundle09_prefix_ranks_12 arithBundle09_ranks_056
private theorem arithBundle09_prefix_ranks_14 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 64 = 234608320 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 60 4 228028014 6580306 arithBundle09_prefix_ranks_13 arithBundle09_ranks_060
private theorem arithBundle09_prefix_ranks_15 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 68 = 240445924 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 64 4 234608320 5837604 arithBundle09_prefix_ranks_14 arithBundle09_ranks_064
private theorem arithBundle09_prefix_ranks_16 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 72 = 245594944 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 68 4 240445924 5149020 arithBundle09_prefix_ranks_15 arithBundle09_ranks_068
private theorem arithBundle09_prefix_ranks_17 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 76 = 250107690 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 72 4 245594944 4512746 arithBundle09_prefix_ranks_16 arithBundle09_ranks_072
private theorem arithBundle09_prefix_ranks_18 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 80 = 254034878 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 76 4 250107690 3927188 arithBundle09_prefix_ranks_17 arithBundle09_ranks_076
private theorem arithBundle09_prefix_ranks_19 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 84 = 257425290 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 80 4 254034878 3390412 arithBundle09_prefix_ranks_18 arithBundle09_ranks_080
private theorem arithBundle09_prefix_ranks_20 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 88 = 260325900 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 84 4 257425290 2900610 arithBundle09_prefix_ranks_19 arithBundle09_ranks_084
private theorem arithBundle09_prefix_ranks_21 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 92 = 262782224 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 88 4 260325900 2456324 arithBundle09_prefix_ranks_20 arithBundle09_ranks_088
private theorem arithBundle09_prefix_ranks_22 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 96 = 264837708 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 92 4 262782224 2055484 arithBundle09_prefix_ranks_21 arithBundle09_ranks_092
private theorem arithBundle09_prefix_ranks_23 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 100 = 266533990 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 96 4 264837708 1696282 arithBundle09_prefix_ranks_22 arithBundle09_ranks_096
private theorem arithBundle09_prefix_ranks_24 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 104 = 267911386 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 100 4 266533990 1377396 arithBundle09_prefix_ranks_23 arithBundle09_ranks_100
private theorem arithBundle09_prefix_ranks_25 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 108 = 269008006 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 104 4 267911386 1096620 arithBundle09_prefix_ranks_24 arithBundle09_ranks_104
private theorem arithBundle09_prefix_ranks_26 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 112 = 269860152 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 108 4 269008006 852146 arithBundle09_prefix_ranks_25 arithBundle09_ranks_108
private theorem arithBundle09_prefix_ranks_27 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 116 = 270502940 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 112 4 269860152 642788 arithBundle09_prefix_ranks_26 arithBundle09_ranks_112
private theorem arithBundle09_prefix_ranks_28 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 120 = 270969144 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 116 4 270502940 466204 arithBundle09_prefix_ranks_27 arithBundle09_ranks_116
private theorem arithBundle09_prefix_ranks_29 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 124 = 271289730 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 120 4 270969144 320586 arithBundle09_prefix_ranks_28 arithBundle09_ranks_120
private theorem arithBundle09_prefix_ranks_30 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 128 = 271494614 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 124 4 271289730 204884 arithBundle09_prefix_ranks_29 arithBundle09_ranks_124
private theorem arithBundle09_prefix_ranks_31 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 132 = 271611234 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 128 4 271494614 116620 arithBundle09_prefix_ranks_30 arithBundle09_ranks_128
private theorem arithBundle09_prefix_ranks_32 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 136 = 271665235 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 132 4 271611234 54001 arithBundle09_prefix_ranks_31 arithBundle09_ranks_132
private theorem arithBundle09_prefix_ranks_33 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 140 = 271681550 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 136 4 271665235 16315 arithBundle09_prefix_ranks_32 arithBundle09_ranks_136
private theorem arithBundle09_prefix_ranks_34 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 144 = 271682466 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 140 4 271681550 916 arithBundle09_prefix_ranks_33 arithBundle09_ranks_140
private theorem arithBundle09_prefix_ranks_35 : arithBundle09_sliceWindow (auxiliaryRankSlice contact17) 0 162 = 271682466 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact17) 0 144 18 271682466 0 arithBundle09_prefix_ranks_34 arithBundle09_ranks_144

theorem contact17_margin : sourceMargin contact17 :=
  arithBundle09_margin_of_checked_counts contact17 162 2609539590685311 89130430973896 10022924642 271682466
    rfl arithBundle09_ordinary_columns arithBundle09_prefix_columns_39 arithBundle09_ordinary_ranks arithBundle09_prefix_ranks_35 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle10_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle10_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle10_sliceWindow f a b = x) (hy : arithBundle10_sliceWindow f (a+b) c = y) :
    arithBundle10_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle10_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle10_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle10_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle10_sliceWindow,Nat.zero_add]

private theorem arithBundle10_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle10_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle10_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle10_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle10_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle10_ordinary_columns : ordinaryColumnCount contact20 = 52671931010188 := by decide +kernel
private theorem arithBundle10_columns_000 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 4 = 448620447632 :=
  contactColumnsWindow_fast contact20 0 4 448620447632 (by decide +kernel)
private theorem arithBundle10_columns_004 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 4 4 = 403914119360 :=
  contactColumnsWindow_fast contact20 4 4 403914119360 (by decide +kernel)
private theorem arithBundle10_columns_008 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 8 4 = 361564709168 :=
  contactColumnsWindow_fast contact20 8 4 361564709168 (by decide +kernel)
private theorem arithBundle10_columns_012 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 12 4 = 321581812512 :=
  contactColumnsWindow_fast contact20 12 4 321581812512 (by decide +kernel)
private theorem arithBundle10_columns_016 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 16 4 = 283967061360 :=
  contactColumnsWindow_fast contact20 16 4 283967061360 (by decide +kernel)
private theorem arithBundle10_columns_020 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 20 4 = 248711061900 :=
  contactColumnsWindow_fast contact20 20 4 248711061900 (by decide +kernel)
private theorem arithBundle10_columns_024 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 24 4 = 215813324957 :=
  contactColumnsWindow_fast contact20 24 4 215813324957 (by decide +kernel)
private theorem arithBundle10_columns_028 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 28 4 = 185274737660 :=
  contactColumnsWindow_fast contact20 28 4 185274737660 (by decide +kernel)
private theorem arithBundle10_columns_032 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 32 4 = 157105540344 :=
  contactColumnsWindow_fast contact20 32 4 157105540344 (by decide +kernel)
private theorem arithBundle10_columns_036 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 36 4 = 131302653911 :=
  contactColumnsWindow_fast contact20 36 4 131302653911 (by decide +kernel)
private theorem arithBundle10_columns_040 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 40 4 = 107858709816 :=
  contactColumnsWindow_fast contact20 40 4 107858709816 (by decide +kernel)
private theorem arithBundle10_columns_044 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 44 4 = 86772867872 :=
  contactColumnsWindow_fast contact20 44 4 86772867872 (by decide +kernel)
private theorem arithBundle10_columns_048 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 48 4 = 68046409731 :=
  contactColumnsWindow_fast contact20 48 4 68046409731 (by decide +kernel)
private theorem arithBundle10_columns_052 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 52 4 = 51690826956 :=
  contactColumnsWindow_fast contact20 52 4 51690826956 (by decide +kernel)
private theorem arithBundle10_columns_056 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 56 4 = 37699830704 :=
  contactColumnsWindow_fast contact20 56 4 37699830704 (by decide +kernel)
private theorem arithBundle10_columns_060 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 60 4 = 26067916512 :=
  contactColumnsWindow_fast contact20 60 4 26067916512 (by decide +kernel)
private theorem arithBundle10_columns_064 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 64 4 = 16793781924 :=
  contactColumnsWindow_fast contact20 64 4 16793781924 (by decide +kernel)
private theorem arithBundle10_columns_068 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 68 4 = 9854982233 :=
  contactColumnsWindow_fast contact20 68 4 9854982233 (by decide +kernel)
private theorem arithBundle10_columns_072 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 72 4 = 5115333677 :=
  contactColumnsWindow_fast contact20 72 4 5115333677 (by decide +kernel)
private theorem arithBundle10_columns_076 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 76 4 = 2252455213 :=
  contactColumnsWindow_fast contact20 76 4 2252455213 (by decide +kernel)
private theorem arithBundle10_columns_080 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 80 2 = 512561029 :=
  contactColumnsWindow_fast contact20 80 2 512561029 (by decide +kernel)
private theorem arithBundle10_prefix_columns_00 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 8 = 852534566992 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 4 4 448620447632 403914119360 arithBundle10_columns_000 arithBundle10_columns_004
private theorem arithBundle10_prefix_columns_01 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 12 = 1214099276160 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 8 4 852534566992 361564709168 arithBundle10_prefix_columns_00 arithBundle10_columns_008
private theorem arithBundle10_prefix_columns_02 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 16 = 1535681088672 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 12 4 1214099276160 321581812512 arithBundle10_prefix_columns_01 arithBundle10_columns_012
private theorem arithBundle10_prefix_columns_03 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 20 = 1819648150032 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 16 4 1535681088672 283967061360 arithBundle10_prefix_columns_02 arithBundle10_columns_016
private theorem arithBundle10_prefix_columns_04 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 24 = 2068359211932 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 20 4 1819648150032 248711061900 arithBundle10_prefix_columns_03 arithBundle10_columns_020
private theorem arithBundle10_prefix_columns_05 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 28 = 2284172536889 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 24 4 2068359211932 215813324957 arithBundle10_prefix_columns_04 arithBundle10_columns_024
private theorem arithBundle10_prefix_columns_06 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 32 = 2469447274549 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 28 4 2284172536889 185274737660 arithBundle10_prefix_columns_05 arithBundle10_columns_028
private theorem arithBundle10_prefix_columns_07 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 36 = 2626552814893 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 32 4 2469447274549 157105540344 arithBundle10_prefix_columns_06 arithBundle10_columns_032
private theorem arithBundle10_prefix_columns_08 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 40 = 2757855468804 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 36 4 2626552814893 131302653911 arithBundle10_prefix_columns_07 arithBundle10_columns_036
private theorem arithBundle10_prefix_columns_09 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 44 = 2865714178620 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 40 4 2757855468804 107858709816 arithBundle10_prefix_columns_08 arithBundle10_columns_040
private theorem arithBundle10_prefix_columns_10 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 48 = 2952487046492 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 44 4 2865714178620 86772867872 arithBundle10_prefix_columns_09 arithBundle10_columns_044
private theorem arithBundle10_prefix_columns_11 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 52 = 3020533456223 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 48 4 2952487046492 68046409731 arithBundle10_prefix_columns_10 arithBundle10_columns_048
private theorem arithBundle10_prefix_columns_12 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 56 = 3072224283179 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 52 4 3020533456223 51690826956 arithBundle10_prefix_columns_11 arithBundle10_columns_052
private theorem arithBundle10_prefix_columns_13 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 60 = 3109924113883 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 56 4 3072224283179 37699830704 arithBundle10_prefix_columns_12 arithBundle10_columns_056
private theorem arithBundle10_prefix_columns_14 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 64 = 3135992030395 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 60 4 3109924113883 26067916512 arithBundle10_prefix_columns_13 arithBundle10_columns_060
private theorem arithBundle10_prefix_columns_15 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 68 = 3152785812319 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 64 4 3135992030395 16793781924 arithBundle10_prefix_columns_14 arithBundle10_columns_064
private theorem arithBundle10_prefix_columns_16 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 72 = 3162640794552 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 68 4 3152785812319 9854982233 arithBundle10_prefix_columns_15 arithBundle10_columns_068
private theorem arithBundle10_prefix_columns_17 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 76 = 3167756128229 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 72 4 3162640794552 5115333677 arithBundle10_prefix_columns_16 arithBundle10_columns_072
private theorem arithBundle10_prefix_columns_18 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 80 = 3170008583442 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 76 4 3167756128229 2252455213 arithBundle10_prefix_columns_17 arithBundle10_columns_076
private theorem arithBundle10_prefix_columns_19 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact20) 0 82 = 3170521144471 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact20) 0 80 2 3170008583442 512561029 arithBundle10_prefix_columns_18 arithBundle10_columns_080

private theorem arithBundle10_ordinary_ranks : ordinaryRankBound contact20 = 203388225 := by decide +kernel
private theorem arithBundle10_ranks_000 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 4 = 1673300 :=
  contactRankWindow_of_rec contact20 0 4 1673300 (by decide +kernel)
private theorem arithBundle10_ranks_004 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 4 4 = 1457060 :=
  contactRankWindow_of_rec contact20 4 4 1457060 (by decide +kernel)
private theorem arithBundle10_ranks_008 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 8 4 = 1257140 :=
  contactRankWindow_of_rec contact20 8 4 1257140 (by decide +kernel)
private theorem arithBundle10_ranks_012 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 12 4 = 1073540 :=
  contactRankWindow_of_rec contact20 12 4 1073540 (by decide +kernel)
private theorem arithBundle10_ranks_016 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 16 4 = 906260 :=
  contactRankWindow_of_rec contact20 16 4 906260 (by decide +kernel)
private theorem arithBundle10_ranks_020 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 20 4 = 755300 :=
  contactRankWindow_of_rec contact20 20 4 755300 (by decide +kernel)
private theorem arithBundle10_ranks_024 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 24 4 = 620645 :=
  contactRankWindow_of_rec contact20 24 4 620645 (by decide +kernel)
private theorem arithBundle10_ranks_028 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 28 4 = 501975 :=
  contactRankWindow_of_rec contact20 28 4 501975 (by decide +kernel)
private theorem arithBundle10_ranks_032 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 32 4 = 398500 :=
  contactRankWindow_of_rec contact20 32 4 398500 (by decide +kernel)
private theorem arithBundle10_ranks_036 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 36 4 = 309345 :=
  contactRankWindow_of_rec contact20 36 4 309345 (by decide +kernel)
private theorem arithBundle10_ranks_040 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 40 4 = 233575 :=
  contactRankWindow_of_rec contact20 40 4 233575 (by decide +kernel)
private theorem arithBundle10_ranks_044 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 44 4 = 170248 :=
  contactRankWindow_of_rec contact20 44 4 170248 (by decide +kernel)
private theorem arithBundle10_ranks_048 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 48 4 = 118557 :=
  contactRankWindow_of_rec contact20 48 4 118557 (by decide +kernel)
private theorem arithBundle10_ranks_052 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 52 4 = 77495 :=
  contactRankWindow_of_rec contact20 52 4 77495 (by decide +kernel)
private theorem arithBundle10_ranks_056 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 56 4 = 46124 :=
  contactRankWindow_of_rec contact20 56 4 46124 (by decide +kernel)
private theorem arithBundle10_ranks_060 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 60 4 = 23705 :=
  contactRankWindow_of_rec contact20 60 4 23705 (by decide +kernel)
private theorem arithBundle10_ranks_064 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 64 4 = 9159 :=
  contactRankWindow_of_rec contact20 64 4 9159 (by decide +kernel)
private theorem arithBundle10_ranks_068 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 68 4 = 1567 :=
  contactRankWindow_of_rec contact20 68 4 1567 (by decide +kernel)
private theorem arithBundle10_ranks_072 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 72 10 = 0 :=
  contactRankWindow_of_rec contact20 72 10 0 (by decide +kernel)
private theorem arithBundle10_prefix_ranks_00 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 8 = 3130360 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 4 4 1673300 1457060 arithBundle10_ranks_000 arithBundle10_ranks_004
private theorem arithBundle10_prefix_ranks_01 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 12 = 4387500 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 8 4 3130360 1257140 arithBundle10_prefix_ranks_00 arithBundle10_ranks_008
private theorem arithBundle10_prefix_ranks_02 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 16 = 5461040 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 12 4 4387500 1073540 arithBundle10_prefix_ranks_01 arithBundle10_ranks_012
private theorem arithBundle10_prefix_ranks_03 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 20 = 6367300 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 16 4 5461040 906260 arithBundle10_prefix_ranks_02 arithBundle10_ranks_016
private theorem arithBundle10_prefix_ranks_04 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 24 = 7122600 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 20 4 6367300 755300 arithBundle10_prefix_ranks_03 arithBundle10_ranks_020
private theorem arithBundle10_prefix_ranks_05 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 28 = 7743245 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 24 4 7122600 620645 arithBundle10_prefix_ranks_04 arithBundle10_ranks_024
private theorem arithBundle10_prefix_ranks_06 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 32 = 8245220 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 28 4 7743245 501975 arithBundle10_prefix_ranks_05 arithBundle10_ranks_028
private theorem arithBundle10_prefix_ranks_07 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 36 = 8643720 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 32 4 8245220 398500 arithBundle10_prefix_ranks_06 arithBundle10_ranks_032
private theorem arithBundle10_prefix_ranks_08 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 40 = 8953065 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 36 4 8643720 309345 arithBundle10_prefix_ranks_07 arithBundle10_ranks_036
private theorem arithBundle10_prefix_ranks_09 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 44 = 9186640 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 40 4 8953065 233575 arithBundle10_prefix_ranks_08 arithBundle10_ranks_040
private theorem arithBundle10_prefix_ranks_10 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 48 = 9356888 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 44 4 9186640 170248 arithBundle10_prefix_ranks_09 arithBundle10_ranks_044
private theorem arithBundle10_prefix_ranks_11 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 52 = 9475445 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 48 4 9356888 118557 arithBundle10_prefix_ranks_10 arithBundle10_ranks_048
private theorem arithBundle10_prefix_ranks_12 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 56 = 9552940 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 52 4 9475445 77495 arithBundle10_prefix_ranks_11 arithBundle10_ranks_052
private theorem arithBundle10_prefix_ranks_13 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 60 = 9599064 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 56 4 9552940 46124 arithBundle10_prefix_ranks_12 arithBundle10_ranks_056
private theorem arithBundle10_prefix_ranks_14 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 64 = 9622769 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 60 4 9599064 23705 arithBundle10_prefix_ranks_13 arithBundle10_ranks_060
private theorem arithBundle10_prefix_ranks_15 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 68 = 9631928 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 64 4 9622769 9159 arithBundle10_prefix_ranks_14 arithBundle10_ranks_064
private theorem arithBundle10_prefix_ranks_16 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 72 = 9633495 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 68 4 9631928 1567 arithBundle10_prefix_ranks_15 arithBundle10_ranks_068
private theorem arithBundle10_prefix_ranks_17 : arithBundle10_sliceWindow (auxiliaryRankSlice contact20) 0 82 = 9633495 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact20) 0 72 10 9633495 0 arithBundle10_prefix_ranks_16 arithBundle10_ranks_072

theorem contact20_margin : sourceMargin contact20 :=
  arithBundle10_margin_of_checked_counts contact20 82 52671931010188 3170521144471 203388225 9633495
    rfl arithBundle10_ordinary_columns arithBundle10_prefix_columns_19 arithBundle10_ordinary_ranks arithBundle10_prefix_ranks_17 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle11_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle11_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle11_sliceWindow f a b = x) (hy : arithBundle11_sliceWindow f (a+b) c = y) :
    arithBundle11_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle11_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle11_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle11_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle11_sliceWindow,Nat.zero_add]

private theorem arithBundle11_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle11_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle11_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle11_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle11_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle11_ordinary_columns : ordinaryColumnCount contact22 = 155315709839479 := by decide +kernel
private theorem arithBundle11_columns_000 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 4 = 1567175609248 :=
  contactColumnsWindow_fast contact22 0 4 1567175609248 (by decide +kernel)
private theorem arithBundle11_columns_004 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 4 4 = 1451740478952 :=
  contactColumnsWindow_fast contact22 4 4 1451740478952 (by decide +kernel)
private theorem arithBundle11_columns_008 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 8 4 = 1340750570744 :=
  contactColumnsWindow_fast contact22 8 4 1340750570744 (by decide +kernel)
private theorem arithBundle11_columns_012 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 12 4 = 1234200337648 :=
  contactColumnsWindow_fast contact22 12 4 1234200337648 (by decide +kernel)
private theorem arithBundle11_columns_016 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 16 4 = 1132088007850 :=
  contactColumnsWindow_fast contact22 16 4 1132088007850 (by decide +kernel)
private theorem arithBundle11_columns_020 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 20 4 = 1034418905044 :=
  contactColumnsWindow_fast contact22 20 4 1034418905044 (by decide +kernel)
private theorem arithBundle11_columns_024 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 24 4 = 941216500429 :=
  contactColumnsWindow_fast contact22 24 4 941216500429 (by decide +kernel)
private theorem arithBundle11_columns_028 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 28 4 = 852460629938 :=
  contactColumnsWindow_fast contact22 28 4 852460629938 (by decide +kernel)
private theorem arithBundle11_columns_032 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 32 4 = 768144599464 :=
  contactColumnsWindow_fast contact22 32 4 768144599464 (by decide +kernel)
private theorem arithBundle11_columns_036 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 36 4 = 688266553551 :=
  contactColumnsWindow_fast contact22 36 4 688266553551 (by decide +kernel)
private theorem arithBundle11_columns_040 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 40 4 = 612833311402 :=
  contactColumnsWindow_fast contact22 40 4 612833311402 (by decide +kernel)
private theorem arithBundle11_columns_044 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 44 4 = 541866952294 :=
  contactColumnsWindow_fast contact22 44 4 541866952294 (by decide +kernel)
private theorem arithBundle11_columns_048 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 48 4 = 475345413557 :=
  contactColumnsWindow_fast contact22 48 4 475345413557 (by decide +kernel)
private theorem arithBundle11_columns_052 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 52 4 = 413263560160 :=
  contactColumnsWindow_fast contact22 52 4 413263560160 (by decide +kernel)
private theorem arithBundle11_columns_056 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 56 4 = 355619825274 :=
  contactColumnsWindow_fast contact22 56 4 355619825274 (by decide +kernel)
private theorem arithBundle11_columns_060 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 60 4 = 302422416640 :=
  contactColumnsWindow_fast contact22 60 4 302422416640 (by decide +kernel)
private theorem arithBundle11_columns_064 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 64 4 = 253692145308 :=
  contactColumnsWindow_fast contact22 64 4 253692145308 (by decide +kernel)
private theorem arithBundle11_columns_068 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 68 4 = 209404964462 :=
  contactColumnsWindow_fast contact22 68 4 209404964462 (by decide +kernel)
private theorem arithBundle11_columns_072 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 72 4 = 169557219736 :=
  contactColumnsWindow_fast contact22 72 4 169557219736 (by decide +kernel)
private theorem arithBundle11_columns_076 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 76 4 = 134147795877 :=
  contactColumnsWindow_fast contact22 76 4 134147795877 (by decide +kernel)
private theorem arithBundle11_columns_080 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 80 4 = 103186922722 :=
  contactColumnsWindow_fast contact22 80 4 103186922722 (by decide +kernel)
private theorem arithBundle11_columns_084 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 84 4 = 76692098520 :=
  contactColumnsWindow_fast contact22 84 4 76692098520 (by decide +kernel)
private theorem arithBundle11_columns_088 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 88 4 = 54637298745 :=
  contactColumnsWindow_fast contact22 88 4 54637298745 (by decide +kernel)
private theorem arithBundle11_columns_092 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 92 4 = 36964668498 :=
  contactColumnsWindow_fast contact22 92 4 36964668498 (by decide +kernel)
private theorem arithBundle11_columns_096 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 96 4 = 23462609582 :=
  contactColumnsWindow_fast contact22 96 4 23462609582 (by decide +kernel)
private theorem arithBundle11_columns_100 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 100 4 = 13763448902 :=
  contactColumnsWindow_fast contact22 100 4 13763448902 (by decide +kernel)
private theorem arithBundle11_columns_104 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 104 3 = 5949313304 :=
  contactColumnsWindow_fast contact22 104 3 5949313304 (by decide +kernel)
private theorem arithBundle11_prefix_columns_00 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 8 = 3018916088200 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 4 4 1567175609248 1451740478952 arithBundle11_columns_000 arithBundle11_columns_004
private theorem arithBundle11_prefix_columns_01 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 12 = 4359666658944 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 8 4 3018916088200 1340750570744 arithBundle11_prefix_columns_00 arithBundle11_columns_008
private theorem arithBundle11_prefix_columns_02 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 16 = 5593866996592 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 12 4 4359666658944 1234200337648 arithBundle11_prefix_columns_01 arithBundle11_columns_012
private theorem arithBundle11_prefix_columns_03 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 20 = 6725955004442 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 16 4 5593866996592 1132088007850 arithBundle11_prefix_columns_02 arithBundle11_columns_016
private theorem arithBundle11_prefix_columns_04 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 24 = 7760373909486 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 20 4 6725955004442 1034418905044 arithBundle11_prefix_columns_03 arithBundle11_columns_020
private theorem arithBundle11_prefix_columns_05 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 28 = 8701590409915 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 24 4 7760373909486 941216500429 arithBundle11_prefix_columns_04 arithBundle11_columns_024
private theorem arithBundle11_prefix_columns_06 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 32 = 9554051039853 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 28 4 8701590409915 852460629938 arithBundle11_prefix_columns_05 arithBundle11_columns_028
private theorem arithBundle11_prefix_columns_07 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 36 = 10322195639317 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 32 4 9554051039853 768144599464 arithBundle11_prefix_columns_06 arithBundle11_columns_032
private theorem arithBundle11_prefix_columns_08 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 40 = 11010462192868 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 36 4 10322195639317 688266553551 arithBundle11_prefix_columns_07 arithBundle11_columns_036
private theorem arithBundle11_prefix_columns_09 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 44 = 11623295504270 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 40 4 11010462192868 612833311402 arithBundle11_prefix_columns_08 arithBundle11_columns_040
private theorem arithBundle11_prefix_columns_10 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 48 = 12165162456564 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 44 4 11623295504270 541866952294 arithBundle11_prefix_columns_09 arithBundle11_columns_044
private theorem arithBundle11_prefix_columns_11 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 52 = 12640507870121 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 48 4 12165162456564 475345413557 arithBundle11_prefix_columns_10 arithBundle11_columns_048
private theorem arithBundle11_prefix_columns_12 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 56 = 13053771430281 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 52 4 12640507870121 413263560160 arithBundle11_prefix_columns_11 arithBundle11_columns_052
private theorem arithBundle11_prefix_columns_13 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 60 = 13409391255555 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 56 4 13053771430281 355619825274 arithBundle11_prefix_columns_12 arithBundle11_columns_056
private theorem arithBundle11_prefix_columns_14 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 64 = 13711813672195 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 60 4 13409391255555 302422416640 arithBundle11_prefix_columns_13 arithBundle11_columns_060
private theorem arithBundle11_prefix_columns_15 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 68 = 13965505817503 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 64 4 13711813672195 253692145308 arithBundle11_prefix_columns_14 arithBundle11_columns_064
private theorem arithBundle11_prefix_columns_16 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 72 = 14174910781965 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 68 4 13965505817503 209404964462 arithBundle11_prefix_columns_15 arithBundle11_columns_068
private theorem arithBundle11_prefix_columns_17 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 76 = 14344468001701 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 72 4 14174910781965 169557219736 arithBundle11_prefix_columns_16 arithBundle11_columns_072
private theorem arithBundle11_prefix_columns_18 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 80 = 14478615797578 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 76 4 14344468001701 134147795877 arithBundle11_prefix_columns_17 arithBundle11_columns_076
private theorem arithBundle11_prefix_columns_19 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 84 = 14581802720300 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 80 4 14478615797578 103186922722 arithBundle11_prefix_columns_18 arithBundle11_columns_080
private theorem arithBundle11_prefix_columns_20 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 88 = 14658494818820 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 84 4 14581802720300 76692098520 arithBundle11_prefix_columns_19 arithBundle11_columns_084
private theorem arithBundle11_prefix_columns_21 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 92 = 14713132117565 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 88 4 14658494818820 54637298745 arithBundle11_prefix_columns_20 arithBundle11_columns_088
private theorem arithBundle11_prefix_columns_22 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 96 = 14750096786063 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 92 4 14713132117565 36964668498 arithBundle11_prefix_columns_21 arithBundle11_columns_092
private theorem arithBundle11_prefix_columns_23 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 100 = 14773559395645 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 96 4 14750096786063 23462609582 arithBundle11_prefix_columns_22 arithBundle11_columns_096
private theorem arithBundle11_prefix_columns_24 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 104 = 14787322844547 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 100 4 14773559395645 13763448902 arithBundle11_prefix_columns_23 arithBundle11_columns_100
private theorem arithBundle11_prefix_columns_25 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact22) 0 107 = 14793272157851 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact22) 0 104 3 14787322844547 5949313304 arithBundle11_prefix_columns_24 arithBundle11_columns_104

private theorem arithBundle11_ordinary_ranks : ordinaryRankBound contact22 = 603903577 := by decide +kernel
private theorem arithBundle11_ranks_000 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 4 = 5864884 :=
  contactRankWindow_of_rec contact22 0 4 5864884 (by decide +kernel)
private theorem arithBundle11_ranks_004 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 4 4 = 5304244 :=
  contactRankWindow_of_rec contact22 4 4 5304244 (by decide +kernel)
private theorem arithBundle11_ranks_008 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 8 4 = 4774324 :=
  contactRankWindow_of_rec contact22 8 4 4774324 (by decide +kernel)
private theorem arithBundle11_ranks_012 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 12 4 = 4275124 :=
  contactRankWindow_of_rec contact22 12 4 4275124 (by decide +kernel)
private theorem arithBundle11_ranks_016 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 16 4 = 3806644 :=
  contactRankWindow_of_rec contact22 16 4 3806644 (by decide +kernel)
private theorem arithBundle11_ranks_020 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 20 4 = 3368884 :=
  contactRankWindow_of_rec contact22 20 4 3368884 (by decide +kernel)
private theorem arithBundle11_ranks_024 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 24 4 = 2961844 :=
  contactRankWindow_of_rec contact22 24 4 2961844 (by decide +kernel)
private theorem arithBundle11_ranks_028 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 28 4 = 2585524 :=
  contactRankWindow_of_rec contact22 28 4 2585524 (by decide +kernel)
private theorem arithBundle11_ranks_032 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 32 4 = 2239864 :=
  contactRankWindow_of_rec contact22 32 4 2239864 (by decide +kernel)
private theorem arithBundle11_ranks_036 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 36 4 = 1924274 :=
  contactRankWindow_of_rec contact22 36 4 1924274 (by decide +kernel)
private theorem arithBundle11_ranks_040 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 40 4 = 1637836 :=
  contactRankWindow_of_rec contact22 40 4 1637836 (by decide +kernel)
private theorem arithBundle11_ranks_044 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 44 4 = 1379438 :=
  contactRankWindow_of_rec contact22 44 4 1379438 (by decide +kernel)
private theorem arithBundle11_ranks_048 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 48 4 = 1147802 :=
  contactRankWindow_of_rec contact22 48 4 1147802 (by decide +kernel)
private theorem arithBundle11_ranks_052 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 52 4 = 941632 :=
  contactRankWindow_of_rec contact22 52 4 941632 (by decide +kernel)
private theorem arithBundle11_ranks_056 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 56 4 = 759810 :=
  contactRankWindow_of_rec contact22 56 4 759810 (by decide +kernel)
private theorem arithBundle11_ranks_060 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 60 4 = 600962 :=
  contactRankWindow_of_rec contact22 60 4 600962 (by decide +kernel)
private theorem arithBundle11_ranks_064 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 64 4 = 463796 :=
  contactRankWindow_of_rec contact22 64 4 463796 (by decide +kernel)
private theorem arithBundle11_ranks_068 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 68 4 = 347286 :=
  contactRankWindow_of_rec contact22 68 4 347286 (by decide +kernel)
private theorem arithBundle11_ranks_072 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 72 4 = 249962 :=
  contactRankWindow_of_rec contact22 72 4 249962 (by decide +kernel)
private theorem arithBundle11_ranks_076 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 76 4 = 170536 :=
  contactRankWindow_of_rec contact22 76 4 170536 (by decide +kernel)
private theorem arithBundle11_ranks_080 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 80 4 = 108074 :=
  contactRankWindow_of_rec contact22 80 4 108074 (by decide +kernel)
private theorem arithBundle11_ranks_084 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 84 4 = 61010 :=
  contactRankWindow_of_rec contact22 84 4 61010 (by decide +kernel)
private theorem arithBundle11_ranks_088 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 88 4 = 28060 :=
  contactRankWindow_of_rec contact22 88 4 28060 (by decide +kernel)
private theorem arithBundle11_ranks_092 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 92 4 = 8406 :=
  contactRankWindow_of_rec contact22 92 4 8406 (by decide +kernel)
private theorem arithBundle11_ranks_096 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 96 4 = 465 :=
  contactRankWindow_of_rec contact22 96 4 465 (by decide +kernel)
private theorem arithBundle11_ranks_100 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 100 7 = 0 :=
  contactRankWindow_of_rec contact22 100 7 0 (by decide +kernel)
private theorem arithBundle11_prefix_ranks_00 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 8 = 11169128 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 4 4 5864884 5304244 arithBundle11_ranks_000 arithBundle11_ranks_004
private theorem arithBundle11_prefix_ranks_01 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 12 = 15943452 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 8 4 11169128 4774324 arithBundle11_prefix_ranks_00 arithBundle11_ranks_008
private theorem arithBundle11_prefix_ranks_02 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 16 = 20218576 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 12 4 15943452 4275124 arithBundle11_prefix_ranks_01 arithBundle11_ranks_012
private theorem arithBundle11_prefix_ranks_03 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 20 = 24025220 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 16 4 20218576 3806644 arithBundle11_prefix_ranks_02 arithBundle11_ranks_016
private theorem arithBundle11_prefix_ranks_04 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 24 = 27394104 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 20 4 24025220 3368884 arithBundle11_prefix_ranks_03 arithBundle11_ranks_020
private theorem arithBundle11_prefix_ranks_05 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 28 = 30355948 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 24 4 27394104 2961844 arithBundle11_prefix_ranks_04 arithBundle11_ranks_024
private theorem arithBundle11_prefix_ranks_06 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 32 = 32941472 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 28 4 30355948 2585524 arithBundle11_prefix_ranks_05 arithBundle11_ranks_028
private theorem arithBundle11_prefix_ranks_07 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 36 = 35181336 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 32 4 32941472 2239864 arithBundle11_prefix_ranks_06 arithBundle11_ranks_032
private theorem arithBundle11_prefix_ranks_08 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 40 = 37105610 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 36 4 35181336 1924274 arithBundle11_prefix_ranks_07 arithBundle11_ranks_036
private theorem arithBundle11_prefix_ranks_09 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 44 = 38743446 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 40 4 37105610 1637836 arithBundle11_prefix_ranks_08 arithBundle11_ranks_040
private theorem arithBundle11_prefix_ranks_10 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 48 = 40122884 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 44 4 38743446 1379438 arithBundle11_prefix_ranks_09 arithBundle11_ranks_044
private theorem arithBundle11_prefix_ranks_11 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 52 = 41270686 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 48 4 40122884 1147802 arithBundle11_prefix_ranks_10 arithBundle11_ranks_048
private theorem arithBundle11_prefix_ranks_12 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 56 = 42212318 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 52 4 41270686 941632 arithBundle11_prefix_ranks_11 arithBundle11_ranks_052
private theorem arithBundle11_prefix_ranks_13 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 60 = 42972128 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 56 4 42212318 759810 arithBundle11_prefix_ranks_12 arithBundle11_ranks_056
private theorem arithBundle11_prefix_ranks_14 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 64 = 43573090 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 60 4 42972128 600962 arithBundle11_prefix_ranks_13 arithBundle11_ranks_060
private theorem arithBundle11_prefix_ranks_15 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 68 = 44036886 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 64 4 43573090 463796 arithBundle11_prefix_ranks_14 arithBundle11_ranks_064
private theorem arithBundle11_prefix_ranks_16 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 72 = 44384172 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 68 4 44036886 347286 arithBundle11_prefix_ranks_15 arithBundle11_ranks_068
private theorem arithBundle11_prefix_ranks_17 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 76 = 44634134 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 72 4 44384172 249962 arithBundle11_prefix_ranks_16 arithBundle11_ranks_072
private theorem arithBundle11_prefix_ranks_18 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 80 = 44804670 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 76 4 44634134 170536 arithBundle11_prefix_ranks_17 arithBundle11_ranks_076
private theorem arithBundle11_prefix_ranks_19 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 84 = 44912744 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 80 4 44804670 108074 arithBundle11_prefix_ranks_18 arithBundle11_ranks_080
private theorem arithBundle11_prefix_ranks_20 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 88 = 44973754 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 84 4 44912744 61010 arithBundle11_prefix_ranks_19 arithBundle11_ranks_084
private theorem arithBundle11_prefix_ranks_21 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 92 = 45001814 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 88 4 44973754 28060 arithBundle11_prefix_ranks_20 arithBundle11_ranks_088
private theorem arithBundle11_prefix_ranks_22 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 96 = 45010220 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 92 4 45001814 8406 arithBundle11_prefix_ranks_21 arithBundle11_ranks_092
private theorem arithBundle11_prefix_ranks_23 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 100 = 45010685 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 96 4 45010220 465 arithBundle11_prefix_ranks_22 arithBundle11_ranks_096
private theorem arithBundle11_prefix_ranks_24 : arithBundle11_sliceWindow (auxiliaryRankSlice contact22) 0 107 = 45010685 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact22) 0 100 7 45010685 0 arithBundle11_prefix_ranks_23 arithBundle11_ranks_100

theorem contact22_margin : sourceMargin contact22 :=
  arithBundle11_margin_of_checked_counts contact22 107 155315709839479 14793272157851 603903577 45010685
    rfl arithBundle11_ordinary_columns arithBundle11_prefix_columns_25 arithBundle11_ordinary_ranks arithBundle11_prefix_ranks_24 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle12_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle12_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle12_sliceWindow f a b = x) (hy : arithBundle12_sliceWindow f (a+b) c = y) :
    arithBundle12_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle12_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle12_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle12_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle12_sliceWindow,Nat.zero_add]

private theorem arithBundle12_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle12_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle12_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle12_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle12_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle12_ordinary_columns : ordinaryColumnCount contact23 = 2256837891596265 := by decide +kernel
private theorem arithBundle12_columns_000 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 4 = 7258730397348 :=
  contactColumnsWindow_fast contact23 0 4 7258730397348 (by decide +kernel)
private theorem arithBundle12_columns_004 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 4 4 = 6900318552932 :=
  contactColumnsWindow_fast contact23 4 4 6900318552932 (by decide +kernel)
private theorem arithBundle12_columns_008 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 8 4 = 6551020824338 :=
  contactColumnsWindow_fast contact23 8 4 6551020824338 (by decide +kernel)
private theorem arithBundle12_columns_012 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 12 4 = 6210840196368 :=
  contactColumnsWindow_fast contact23 12 4 6210840196368 (by decide +kernel)
private theorem arithBundle12_columns_016 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 16 4 = 5879774631832 :=
  contactColumnsWindow_fast contact23 16 4 5879774631832 (by decide +kernel)
private theorem arithBundle12_columns_020 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 20 4 = 5557826223408 :=
  contactColumnsWindow_fast contact23 20 4 5557826223408 (by decide +kernel)
private theorem arithBundle12_columns_024 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 24 4 = 5245010072883 :=
  contactColumnsWindow_fast contact23 24 4 5245010072883 (by decide +kernel)
private theorem arithBundle12_columns_028 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 28 4 = 4941347267629 :=
  contactColumnsWindow_fast contact23 28 4 4941347267629 (by decide +kernel)
private theorem arithBundle12_columns_032 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 32 4 = 4646805090168 :=
  contactColumnsWindow_fast contact23 32 4 4646805090168 (by decide +kernel)
private theorem arithBundle12_columns_036 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 36 4 = 4361381277072 :=
  contactColumnsWindow_fast contact23 36 4 4361381277072 (by decide +kernel)
private theorem arithBundle12_columns_040 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 40 4 = 4085077613812 :=
  contactColumnsWindow_fast contact23 40 4 4085077613812 (by decide +kernel)
private theorem arithBundle12_columns_044 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 44 4 = 3817912881476 :=
  contactColumnsWindow_fast contact23 44 4 3817912881476 (by decide +kernel)
private theorem arithBundle12_columns_048 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 48 4 = 3559902760391 :=
  contactColumnsWindow_fast contact23 48 4 3559902760391 (by decide +kernel)
private theorem arithBundle12_columns_052 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 52 4 = 3311014650255 :=
  contactColumnsWindow_fast contact23 52 4 3311014650255 (by decide +kernel)
private theorem arithBundle12_columns_056 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 56 4 = 3071249154167 :=
  contactColumnsWindow_fast contact23 56 4 3071249154167 (by decide +kernel)
private theorem arithBundle12_columns_060 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 60 4 = 2840606085176 :=
  contactColumnsWindow_fast contact23 60 4 2840606085176 (by decide +kernel)
private theorem arithBundle12_columns_064 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 64 4 = 2619111586460 :=
  contactColumnsWindow_fast contact23 64 4 2619111586460 (by decide +kernel)
private theorem arithBundle12_columns_068 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 68 4 = 2406769058975 :=
  contactColumnsWindow_fast contact23 68 4 2406769058975 (by decide +kernel)
private theorem arithBundle12_columns_072 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 72 4 = 2203553579334 :=
  contactColumnsWindow_fast contact23 72 4 2203553579334 (by decide +kernel)
private theorem arithBundle12_columns_076 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 76 4 = 2009461373201 :=
  contactColumnsWindow_fast contact23 76 4 2009461373201 (by decide +kernel)
private theorem arithBundle12_columns_080 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 80 4 = 1824491392196 :=
  contactColumnsWindow_fast contact23 80 4 1824491392196 (by decide +kernel)
private theorem arithBundle12_columns_084 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 84 4 = 1648674989168 :=
  contactColumnsWindow_fast contact23 84 4 1648674989168 (by decide +kernel)
private theorem arithBundle12_columns_088 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 88 4 = 1482006078595 :=
  contactColumnsWindow_fast contact23 88 4 1482006078595 (by decide +kernel)
private theorem arithBundle12_columns_092 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 92 4 = 1324463951766 :=
  contactColumnsWindow_fast contact23 92 4 1324463951766 (by decide +kernel)
private theorem arithBundle12_columns_096 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 96 4 = 1176044989595 :=
  contactColumnsWindow_fast contact23 96 4 1176044989595 (by decide +kernel)
private theorem arithBundle12_columns_100 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 100 4 = 1036748551747 :=
  contactColumnsWindow_fast contact23 100 4 1036748551747 (by decide +kernel)
private theorem arithBundle12_columns_104 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 104 4 = 906609881264 :=
  contactColumnsWindow_fast contact23 104 4 906609881264 (by decide +kernel)
private theorem arithBundle12_columns_108 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 108 4 = 785614635133 :=
  contactColumnsWindow_fast contact23 108 4 785614635133 (by decide +kernel)
private theorem arithBundle12_columns_112 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 112 4 = 673745684814 :=
  contactColumnsWindow_fast contact23 112 4 673745684814 (by decide +kernel)
private theorem arithBundle12_columns_116 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 116 4 = 571000031810 :=
  contactColumnsWindow_fast contact23 116 4 571000031810 (by decide +kernel)
private theorem arithBundle12_columns_120 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 120 4 = 477378049489 :=
  contactColumnsWindow_fast contact23 120 4 477378049489 (by decide +kernel)
private theorem arithBundle12_columns_124 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 124 4 = 392916140108 :=
  contactColumnsWindow_fast contact23 124 4 392916140108 (by decide +kernel)
private theorem arithBundle12_columns_128 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 128 4 = 317594558293 :=
  contactColumnsWindow_fast contact23 128 4 317594558293 (by decide +kernel)
private theorem arithBundle12_columns_132 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 132 4 = 251398553114 :=
  contactColumnsWindow_fast contact23 132 4 251398553114 (by decide +kernel)
private theorem arithBundle12_columns_136 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 136 4 = 194291786114 :=
  contactColumnsWindow_fast contact23 136 4 194291786114 (by decide +kernel)
private theorem arithBundle12_columns_140 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 140 4 = 146079250401 :=
  contactColumnsWindow_fast contact23 140 4 146079250401 (by decide +kernel)
private theorem arithBundle12_columns_144 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 144 4 = 106410642030 :=
  contactColumnsWindow_fast contact23 144 4 106410642030 (by decide +kernel)
private theorem arithBundle12_columns_148 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 148 4 = 74711209357 :=
  contactColumnsWindow_fast contact23 148 4 74711209357 (by decide +kernel)
private theorem arithBundle12_columns_152 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 152 4 = 50258524380 :=
  contactColumnsWindow_fast contact23 152 4 50258524380 (by decide +kernel)
private theorem arithBundle12_columns_156 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 156 4 = 32179019098 :=
  contactColumnsWindow_fast contact23 156 4 32179019098 (by decide +kernel)
private theorem arithBundle12_columns_160 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 160 4 = 19448391567 :=
  contactColumnsWindow_fast contact23 160 4 19448391567 (by decide +kernel)
private theorem arithBundle12_prefix_columns_00 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 8 = 14159048950280 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 4 4 7258730397348 6900318552932 arithBundle12_columns_000 arithBundle12_columns_004
private theorem arithBundle12_prefix_columns_01 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 12 = 20710069774618 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 8 4 14159048950280 6551020824338 arithBundle12_prefix_columns_00 arithBundle12_columns_008
private theorem arithBundle12_prefix_columns_02 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 16 = 26920909970986 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 12 4 20710069774618 6210840196368 arithBundle12_prefix_columns_01 arithBundle12_columns_012
private theorem arithBundle12_prefix_columns_03 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 20 = 32800684602818 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 16 4 26920909970986 5879774631832 arithBundle12_prefix_columns_02 arithBundle12_columns_016
private theorem arithBundle12_prefix_columns_04 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 24 = 38358510826226 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 20 4 32800684602818 5557826223408 arithBundle12_prefix_columns_03 arithBundle12_columns_020
private theorem arithBundle12_prefix_columns_05 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 28 = 43603520899109 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 24 4 38358510826226 5245010072883 arithBundle12_prefix_columns_04 arithBundle12_columns_024
private theorem arithBundle12_prefix_columns_06 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 32 = 48544868166738 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 28 4 43603520899109 4941347267629 arithBundle12_prefix_columns_05 arithBundle12_columns_028
private theorem arithBundle12_prefix_columns_07 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 36 = 53191673256906 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 32 4 48544868166738 4646805090168 arithBundle12_prefix_columns_06 arithBundle12_columns_032
private theorem arithBundle12_prefix_columns_08 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 40 = 57553054533978 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 36 4 53191673256906 4361381277072 arithBundle12_prefix_columns_07 arithBundle12_columns_036
private theorem arithBundle12_prefix_columns_09 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 44 = 61638132147790 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 40 4 57553054533978 4085077613812 arithBundle12_prefix_columns_08 arithBundle12_columns_040
private theorem arithBundle12_prefix_columns_10 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 48 = 65456045029266 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 44 4 61638132147790 3817912881476 arithBundle12_prefix_columns_09 arithBundle12_columns_044
private theorem arithBundle12_prefix_columns_11 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 52 = 69015947789657 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 48 4 65456045029266 3559902760391 arithBundle12_prefix_columns_10 arithBundle12_columns_048
private theorem arithBundle12_prefix_columns_12 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 56 = 72326962439912 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 52 4 69015947789657 3311014650255 arithBundle12_prefix_columns_11 arithBundle12_columns_052
private theorem arithBundle12_prefix_columns_13 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 60 = 75398211594079 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 56 4 72326962439912 3071249154167 arithBundle12_prefix_columns_12 arithBundle12_columns_056
private theorem arithBundle12_prefix_columns_14 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 64 = 78238817679255 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 60 4 75398211594079 2840606085176 arithBundle12_prefix_columns_13 arithBundle12_columns_060
private theorem arithBundle12_prefix_columns_15 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 68 = 80857929265715 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 64 4 78238817679255 2619111586460 arithBundle12_prefix_columns_14 arithBundle12_columns_064
private theorem arithBundle12_prefix_columns_16 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 72 = 83264698324690 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 68 4 80857929265715 2406769058975 arithBundle12_prefix_columns_15 arithBundle12_columns_068
private theorem arithBundle12_prefix_columns_17 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 76 = 85468251904024 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 72 4 83264698324690 2203553579334 arithBundle12_prefix_columns_16 arithBundle12_columns_072
private theorem arithBundle12_prefix_columns_18 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 80 = 87477713277225 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 76 4 85468251904024 2009461373201 arithBundle12_prefix_columns_17 arithBundle12_columns_076
private theorem arithBundle12_prefix_columns_19 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 84 = 89302204669421 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 80 4 87477713277225 1824491392196 arithBundle12_prefix_columns_18 arithBundle12_columns_080
private theorem arithBundle12_prefix_columns_20 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 88 = 90950879658589 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 84 4 89302204669421 1648674989168 arithBundle12_prefix_columns_19 arithBundle12_columns_084
private theorem arithBundle12_prefix_columns_21 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 92 = 92432885737184 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 88 4 90950879658589 1482006078595 arithBundle12_prefix_columns_20 arithBundle12_columns_088
private theorem arithBundle12_prefix_columns_22 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 96 = 93757349688950 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 92 4 92432885737184 1324463951766 arithBundle12_prefix_columns_21 arithBundle12_columns_092
private theorem arithBundle12_prefix_columns_23 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 100 = 94933394678545 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 96 4 93757349688950 1176044989595 arithBundle12_prefix_columns_22 arithBundle12_columns_096
private theorem arithBundle12_prefix_columns_24 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 104 = 95970143230292 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 100 4 94933394678545 1036748551747 arithBundle12_prefix_columns_23 arithBundle12_columns_100
private theorem arithBundle12_prefix_columns_25 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 108 = 96876753111556 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 104 4 95970143230292 906609881264 arithBundle12_prefix_columns_24 arithBundle12_columns_104
private theorem arithBundle12_prefix_columns_26 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 112 = 97662367746689 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 108 4 96876753111556 785614635133 arithBundle12_prefix_columns_25 arithBundle12_columns_108
private theorem arithBundle12_prefix_columns_27 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 116 = 98336113431503 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 112 4 97662367746689 673745684814 arithBundle12_prefix_columns_26 arithBundle12_columns_112
private theorem arithBundle12_prefix_columns_28 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 120 = 98907113463313 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 116 4 98336113431503 571000031810 arithBundle12_prefix_columns_27 arithBundle12_columns_116
private theorem arithBundle12_prefix_columns_29 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 124 = 99384491512802 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 120 4 98907113463313 477378049489 arithBundle12_prefix_columns_28 arithBundle12_columns_120
private theorem arithBundle12_prefix_columns_30 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 128 = 99777407652910 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 124 4 99384491512802 392916140108 arithBundle12_prefix_columns_29 arithBundle12_columns_124
private theorem arithBundle12_prefix_columns_31 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 132 = 100095002211203 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 128 4 99777407652910 317594558293 arithBundle12_prefix_columns_30 arithBundle12_columns_128
private theorem arithBundle12_prefix_columns_32 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 136 = 100346400764317 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 132 4 100095002211203 251398553114 arithBundle12_prefix_columns_31 arithBundle12_columns_132
private theorem arithBundle12_prefix_columns_33 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 140 = 100540692550431 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 136 4 100346400764317 194291786114 arithBundle12_prefix_columns_32 arithBundle12_columns_136
private theorem arithBundle12_prefix_columns_34 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 144 = 100686771800832 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 140 4 100540692550431 146079250401 arithBundle12_prefix_columns_33 arithBundle12_columns_140
private theorem arithBundle12_prefix_columns_35 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 148 = 100793182442862 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 144 4 100686771800832 106410642030 arithBundle12_prefix_columns_34 arithBundle12_columns_144
private theorem arithBundle12_prefix_columns_36 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 152 = 100867893652219 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 148 4 100793182442862 74711209357 arithBundle12_prefix_columns_35 arithBundle12_columns_148
private theorem arithBundle12_prefix_columns_37 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 156 = 100918152176599 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 152 4 100867893652219 50258524380 arithBundle12_prefix_columns_36 arithBundle12_columns_152
private theorem arithBundle12_prefix_columns_38 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 160 = 100950331195697 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 156 4 100918152176599 32179019098 arithBundle12_prefix_columns_37 arithBundle12_columns_156
private theorem arithBundle12_prefix_columns_39 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact23) 0 164 = 100969779587264 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact23) 0 160 4 100950331195697 19448391567 arithBundle12_prefix_columns_38 arithBundle12_columns_160

private theorem arithBundle12_ordinary_ranks : ordinaryRankBound contact23 = 8687293427 := by decide +kernel
private theorem arithBundle12_ranks_000 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 4 = 27361038 :=
  contactRankWindow_of_rec contact23 0 4 27361038 (by decide +kernel)
private theorem arithBundle12_ranks_004 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 4 4 = 25602014 :=
  contactRankWindow_of_rec contact23 4 4 25602014 (by decide +kernel)
private theorem arithBundle12_ranks_008 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 8 4 = 23906094 :=
  contactRankWindow_of_rec contact23 8 4 23906094 (by decide +kernel)
private theorem arithBundle12_ranks_012 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 12 4 = 22273278 :=
  contactRankWindow_of_rec contact23 12 4 22273278 (by decide +kernel)
private theorem arithBundle12_ranks_016 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 16 4 = 20703566 :=
  contactRankWindow_of_rec contact23 16 4 20703566 (by decide +kernel)
private theorem arithBundle12_ranks_020 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 20 4 = 19196958 :=
  contactRankWindow_of_rec contact23 20 4 19196958 (by decide +kernel)
private theorem arithBundle12_ranks_024 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 24 4 = 17753454 :=
  contactRankWindow_of_rec contact23 24 4 17753454 (by decide +kernel)
private theorem arithBundle12_ranks_028 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 28 4 = 16373054 :=
  contactRankWindow_of_rec contact23 28 4 16373054 (by decide +kernel)
private theorem arithBundle12_ranks_032 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 32 4 = 15055758 :=
  contactRankWindow_of_rec contact23 32 4 15055758 (by decide +kernel)
private theorem arithBundle12_ranks_036 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 36 4 = 13801566 :=
  contactRankWindow_of_rec contact23 36 4 13801566 (by decide +kernel)
private theorem arithBundle12_ranks_040 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 40 4 = 12610478 :=
  contactRankWindow_of_rec contact23 40 4 12610478 (by decide +kernel)
private theorem arithBundle12_ranks_044 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 44 4 = 11482494 :=
  contactRankWindow_of_rec contact23 44 4 11482494 (by decide +kernel)
private theorem arithBundle12_ranks_048 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 48 4 = 10417614 :=
  contactRankWindow_of_rec contact23 48 4 10417614 (by decide +kernel)
private theorem arithBundle12_ranks_052 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 52 4 = 9415634 :=
  contactRankWindow_of_rec contact23 52 4 9415634 (by decide +kernel)
private theorem arithBundle12_ranks_056 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 56 4 = 8475496 :=
  contactRankWindow_of_rec contact23 56 4 8475496 (by decide +kernel)
private theorem arithBundle12_ranks_060 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 60 4 = 7595938 :=
  contactRankWindow_of_rec contact23 60 4 7595938 (by decide +kernel)
private theorem arithBundle12_ranks_064 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 64 4 = 6775375 :=
  contactRankWindow_of_rec contact23 64 4 6775375 (by decide +kernel)
private theorem arithBundle12_ranks_068 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 68 4 = 6012084 :=
  contactRankWindow_of_rec contact23 68 4 6012084 (by decide +kernel)
private theorem arithBundle12_ranks_072 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 72 4 = 5304226 :=
  contactRankWindow_of_rec contact23 72 4 5304226 (by decide +kernel)
private theorem arithBundle12_ranks_076 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 76 4 = 4649943 :=
  contactRankWindow_of_rec contact23 76 4 4649943 (by decide +kernel)
private theorem arithBundle12_ranks_080 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 80 4 = 4047648 :=
  contactRankWindow_of_rec contact23 80 4 4047648 (by decide +kernel)
private theorem arithBundle12_ranks_084 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 84 4 = 3495362 :=
  contactRankWindow_of_rec contact23 84 4 3495362 (by decide +kernel)
private theorem arithBundle12_ranks_088 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 88 4 = 2991231 :=
  contactRankWindow_of_rec contact23 88 4 2991231 (by decide +kernel)
private theorem arithBundle12_ranks_092 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 92 4 = 2533804 :=
  contactRankWindow_of_rec contact23 92 4 2533804 (by decide +kernel)
private theorem arithBundle12_ranks_096 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 96 4 = 2120962 :=
  contactRankWindow_of_rec contact23 96 4 2120962 (by decide +kernel)
private theorem arithBundle12_ranks_100 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 100 4 = 1750855 :=
  contactRankWindow_of_rec contact23 100 4 1750855 (by decide +kernel)
private theorem arithBundle12_ranks_104 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 104 4 = 1422168 :=
  contactRankWindow_of_rec contact23 104 4 1422168 (by decide +kernel)
private theorem arithBundle12_ranks_108 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 108 4 = 1132642 :=
  contactRankWindow_of_rec contact23 108 4 1132642 (by decide +kernel)
private theorem arithBundle12_ranks_112 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 112 4 = 880431 :=
  contactRankWindow_of_rec contact23 112 4 880431 (by decide +kernel)
private theorem arithBundle12_ranks_116 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 116 4 = 664356 :=
  contactRankWindow_of_rec contact23 116 4 664356 (by decide +kernel)
private theorem arithBundle12_ranks_120 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 120 4 = 482018 :=
  contactRankWindow_of_rec contact23 120 4 482018 (by decide +kernel)
private theorem arithBundle12_ranks_124 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 124 4 = 331575 :=
  contactRankWindow_of_rec contact23 124 4 331575 (by decide +kernel)
private theorem arithBundle12_ranks_128 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 128 4 = 211984 :=
  contactRankWindow_of_rec contact23 128 4 211984 (by decide +kernel)
private theorem arithBundle12_ranks_132 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 132 4 = 120706 :=
  contactRankWindow_of_rec contact23 132 4 120706 (by decide +kernel)
private theorem arithBundle12_ranks_136 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 136 4 = 55918 :=
  contactRankWindow_of_rec contact23 136 4 55918 (by decide +kernel)
private theorem arithBundle12_ranks_140 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 140 4 = 16907 :=
  contactRankWindow_of_rec contact23 140 4 16907 (by decide +kernel)
private theorem arithBundle12_ranks_144 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 144 4 = 950 :=
  contactRankWindow_of_rec contact23 144 4 950 (by decide +kernel)
private theorem arithBundle12_ranks_148 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 148 16 = 0 :=
  contactRankWindow_of_rec contact23 148 16 0 (by decide +kernel)
private theorem arithBundle12_prefix_ranks_00 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 8 = 52963052 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 4 4 27361038 25602014 arithBundle12_ranks_000 arithBundle12_ranks_004
private theorem arithBundle12_prefix_ranks_01 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 12 = 76869146 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 8 4 52963052 23906094 arithBundle12_prefix_ranks_00 arithBundle12_ranks_008
private theorem arithBundle12_prefix_ranks_02 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 16 = 99142424 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 12 4 76869146 22273278 arithBundle12_prefix_ranks_01 arithBundle12_ranks_012
private theorem arithBundle12_prefix_ranks_03 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 20 = 119845990 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 16 4 99142424 20703566 arithBundle12_prefix_ranks_02 arithBundle12_ranks_016
private theorem arithBundle12_prefix_ranks_04 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 24 = 139042948 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 20 4 119845990 19196958 arithBundle12_prefix_ranks_03 arithBundle12_ranks_020
private theorem arithBundle12_prefix_ranks_05 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 28 = 156796402 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 24 4 139042948 17753454 arithBundle12_prefix_ranks_04 arithBundle12_ranks_024
private theorem arithBundle12_prefix_ranks_06 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 32 = 173169456 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 28 4 156796402 16373054 arithBundle12_prefix_ranks_05 arithBundle12_ranks_028
private theorem arithBundle12_prefix_ranks_07 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 36 = 188225214 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 32 4 173169456 15055758 arithBundle12_prefix_ranks_06 arithBundle12_ranks_032
private theorem arithBundle12_prefix_ranks_08 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 40 = 202026780 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 36 4 188225214 13801566 arithBundle12_prefix_ranks_07 arithBundle12_ranks_036
private theorem arithBundle12_prefix_ranks_09 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 44 = 214637258 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 40 4 202026780 12610478 arithBundle12_prefix_ranks_08 arithBundle12_ranks_040
private theorem arithBundle12_prefix_ranks_10 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 48 = 226119752 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 44 4 214637258 11482494 arithBundle12_prefix_ranks_09 arithBundle12_ranks_044
private theorem arithBundle12_prefix_ranks_11 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 52 = 236537366 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 48 4 226119752 10417614 arithBundle12_prefix_ranks_10 arithBundle12_ranks_048
private theorem arithBundle12_prefix_ranks_12 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 56 = 245953000 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 52 4 236537366 9415634 arithBundle12_prefix_ranks_11 arithBundle12_ranks_052
private theorem arithBundle12_prefix_ranks_13 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 60 = 254428496 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 56 4 245953000 8475496 arithBundle12_prefix_ranks_12 arithBundle12_ranks_056
private theorem arithBundle12_prefix_ranks_14 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 64 = 262024434 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 60 4 254428496 7595938 arithBundle12_prefix_ranks_13 arithBundle12_ranks_060
private theorem arithBundle12_prefix_ranks_15 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 68 = 268799809 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 64 4 262024434 6775375 arithBundle12_prefix_ranks_14 arithBundle12_ranks_064
private theorem arithBundle12_prefix_ranks_16 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 72 = 274811893 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 68 4 268799809 6012084 arithBundle12_prefix_ranks_15 arithBundle12_ranks_068
private theorem arithBundle12_prefix_ranks_17 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 76 = 280116119 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 72 4 274811893 5304226 arithBundle12_prefix_ranks_16 arithBundle12_ranks_072
private theorem arithBundle12_prefix_ranks_18 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 80 = 284766062 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 76 4 280116119 4649943 arithBundle12_prefix_ranks_17 arithBundle12_ranks_076
private theorem arithBundle12_prefix_ranks_19 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 84 = 288813710 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 80 4 284766062 4047648 arithBundle12_prefix_ranks_18 arithBundle12_ranks_080
private theorem arithBundle12_prefix_ranks_20 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 88 = 292309072 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 84 4 288813710 3495362 arithBundle12_prefix_ranks_19 arithBundle12_ranks_084
private theorem arithBundle12_prefix_ranks_21 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 92 = 295300303 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 88 4 292309072 2991231 arithBundle12_prefix_ranks_20 arithBundle12_ranks_088
private theorem arithBundle12_prefix_ranks_22 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 96 = 297834107 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 92 4 295300303 2533804 arithBundle12_prefix_ranks_21 arithBundle12_ranks_092
private theorem arithBundle12_prefix_ranks_23 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 100 = 299955069 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 96 4 297834107 2120962 arithBundle12_prefix_ranks_22 arithBundle12_ranks_096
private theorem arithBundle12_prefix_ranks_24 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 104 = 301705924 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 100 4 299955069 1750855 arithBundle12_prefix_ranks_23 arithBundle12_ranks_100
private theorem arithBundle12_prefix_ranks_25 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 108 = 303128092 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 104 4 301705924 1422168 arithBundle12_prefix_ranks_24 arithBundle12_ranks_104
private theorem arithBundle12_prefix_ranks_26 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 112 = 304260734 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 108 4 303128092 1132642 arithBundle12_prefix_ranks_25 arithBundle12_ranks_108
private theorem arithBundle12_prefix_ranks_27 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 116 = 305141165 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 112 4 304260734 880431 arithBundle12_prefix_ranks_26 arithBundle12_ranks_112
private theorem arithBundle12_prefix_ranks_28 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 120 = 305805521 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 116 4 305141165 664356 arithBundle12_prefix_ranks_27 arithBundle12_ranks_116
private theorem arithBundle12_prefix_ranks_29 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 124 = 306287539 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 120 4 305805521 482018 arithBundle12_prefix_ranks_28 arithBundle12_ranks_120
private theorem arithBundle12_prefix_ranks_30 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 128 = 306619114 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 124 4 306287539 331575 arithBundle12_prefix_ranks_29 arithBundle12_ranks_124
private theorem arithBundle12_prefix_ranks_31 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 132 = 306831098 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 128 4 306619114 211984 arithBundle12_prefix_ranks_30 arithBundle12_ranks_128
private theorem arithBundle12_prefix_ranks_32 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 136 = 306951804 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 132 4 306831098 120706 arithBundle12_prefix_ranks_31 arithBundle12_ranks_132
private theorem arithBundle12_prefix_ranks_33 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 140 = 307007722 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 136 4 306951804 55918 arithBundle12_prefix_ranks_32 arithBundle12_ranks_136
private theorem arithBundle12_prefix_ranks_34 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 144 = 307024629 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 140 4 307007722 16907 arithBundle12_prefix_ranks_33 arithBundle12_ranks_140
private theorem arithBundle12_prefix_ranks_35 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 148 = 307025579 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 144 4 307024629 950 arithBundle12_prefix_ranks_34 arithBundle12_ranks_144
private theorem arithBundle12_prefix_ranks_36 : arithBundle12_sliceWindow (auxiliaryRankSlice contact23) 0 164 = 307025579 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact23) 0 148 16 307025579 0 arithBundle12_prefix_ranks_35 arithBundle12_ranks_148

theorem contact23_margin : sourceMargin contact23 :=
  arithBundle12_margin_of_checked_counts contact23 164 2256837891596265 100969779587264 8687293427 307025579
    rfl arithBundle12_ordinary_columns arithBundle12_prefix_columns_39 arithBundle12_ordinary_ranks arithBundle12_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle13_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle13_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle13_sliceWindow f a b = x) (hy : arithBundle13_sliceWindow f (a+b) c = y) :
    arithBundle13_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle13_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle13_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle13_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle13_sliceWindow,Nat.zero_add]

private theorem arithBundle13_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle13_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle13_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle13_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle13_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle13_ordinary_columns : ordinaryColumnCount contact26 = 160116275649966 := by decide +kernel
private theorem arithBundle13_columns_000 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 4 = 1856144218418 :=
  contactColumnsWindow_fast contact26 0 4 1856144218418 (by decide +kernel)
private theorem arithBundle13_columns_004 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 4 4 = 1724659912594 :=
  contactColumnsWindow_fast contact26 4 4 1724659912594 (by decide +kernel)
private theorem arithBundle13_columns_008 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 8 4 = 1598028085170 :=
  contactColumnsWindow_fast contact26 8 4 1598028085170 (by decide +kernel)
private theorem arithBundle13_columns_012 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 12 4 = 1476261331259 :=
  contactColumnsWindow_fast contact26 12 4 1476261331259 (by decide +kernel)
private theorem arithBundle13_columns_016 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 16 4 = 1359375659662 :=
  contactColumnsWindow_fast contact26 16 4 1359375659662 (by decide +kernel)
private theorem arithBundle13_columns_020 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 20 4 = 1247345320510 :=
  contactColumnsWindow_fast contact26 20 4 1247345320510 (by decide +kernel)
private theorem arithBundle13_columns_024 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 24 4 = 1140170071294 :=
  contactColumnsWindow_fast contact26 24 4 1140170071294 (by decide +kernel)
private theorem arithBundle13_columns_028 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 28 4 = 1037849755434 :=
  contactColumnsWindow_fast contact26 28 4 1037849755434 (by decide +kernel)
private theorem arithBundle13_columns_032 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 32 4 = 940399560740 :=
  contactColumnsWindow_fast contact26 32 4 940399560740 (by decide +kernel)
private theorem arithBundle13_columns_036 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 36 4 = 847831641742 :=
  contactColumnsWindow_fast contact26 36 4 847831641742 (by decide +kernel)
private theorem arithBundle13_columns_040 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 40 4 = 760120151266 :=
  contactColumnsWindow_fast contact26 40 4 760120151266 (by decide +kernel)
private theorem arithBundle13_columns_044 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 44 4 = 677263355821 :=
  contactColumnsWindow_fast contact26 44 4 677263355821 (by decide +kernel)
private theorem arithBundle13_columns_048 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 48 4 = 599261907738 :=
  contactColumnsWindow_fast contact26 48 4 599261907738 (by decide +kernel)
private theorem arithBundle13_columns_052 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 52 4 = 526133957432 :=
  contactColumnsWindow_fast contact26 52 4 526133957432 (by decide +kernel)
private theorem arithBundle13_columns_056 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 56 4 = 457884950722 :=
  contactColumnsWindow_fast contact26 56 4 457884950722 (by decide +kernel)
private theorem arithBundle13_columns_060 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 60 4 = 394492308922 :=
  contactColumnsWindow_fast contact26 60 4 394492308922 (by decide +kernel)
private theorem arithBundle13_columns_064 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 64 4 = 335954070364 :=
  contactColumnsWindow_fast contact26 64 4 335954070364 (by decide +kernel)
private theorem arithBundle13_columns_068 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 68 4 = 282271386942 :=
  contactColumnsWindow_fast contact26 68 4 282271386942 (by decide +kernel)
private theorem arithBundle13_columns_072 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 72 4 = 233465814497 :=
  contactColumnsWindow_fast contact26 72 4 233465814497 (by decide +kernel)
private theorem arithBundle13_columns_076 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 76 4 = 189535640476 :=
  contactColumnsWindow_fast contact26 76 4 189535640476 (by decide +kernel)
private theorem arithBundle13_columns_080 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 80 4 = 150461793478 :=
  contactColumnsWindow_fast contact26 80 4 150461793478 (by decide +kernel)
private theorem arithBundle13_columns_084 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 84 4 = 116242112107 :=
  contactColumnsWindow_fast contact26 84 4 116242112107 (by decide +kernel)
private theorem arithBundle13_columns_088 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 88 4 = 86878278561 :=
  contactColumnsWindow_fast contact26 88 4 86878278561 (by decide +kernel)
private theorem arithBundle13_columns_092 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 92 4 = 62390999214 :=
  contactColumnsWindow_fast contact26 92 4 62390999214 (by decide +kernel)
private theorem arithBundle13_columns_096 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 96 4 = 42695918448 :=
  contactColumnsWindow_fast contact26 96 4 42695918448 (by decide +kernel)
private theorem arithBundle13_columns_100 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 100 4 = 27537164913 :=
  contactColumnsWindow_fast contact26 100 4 27537164913 (by decide +kernel)
private theorem arithBundle13_columns_104 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 104 4 = 16508193071 :=
  contactColumnsWindow_fast contact26 104 4 16508193071 (by decide +kernel)
private theorem arithBundle13_columns_108 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 108 2 = 5258876278 :=
  contactColumnsWindow_fast contact26 108 2 5258876278 (by decide +kernel)
private theorem arithBundle13_prefix_columns_00 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 8 = 3580804131012 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 4 4 1856144218418 1724659912594 arithBundle13_columns_000 arithBundle13_columns_004
private theorem arithBundle13_prefix_columns_01 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 12 = 5178832216182 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 8 4 3580804131012 1598028085170 arithBundle13_prefix_columns_00 arithBundle13_columns_008
private theorem arithBundle13_prefix_columns_02 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 16 = 6655093547441 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 12 4 5178832216182 1476261331259 arithBundle13_prefix_columns_01 arithBundle13_columns_012
private theorem arithBundle13_prefix_columns_03 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 20 = 8014469207103 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 16 4 6655093547441 1359375659662 arithBundle13_prefix_columns_02 arithBundle13_columns_016
private theorem arithBundle13_prefix_columns_04 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 24 = 9261814527613 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 20 4 8014469207103 1247345320510 arithBundle13_prefix_columns_03 arithBundle13_columns_020
private theorem arithBundle13_prefix_columns_05 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 28 = 10401984598907 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 24 4 9261814527613 1140170071294 arithBundle13_prefix_columns_04 arithBundle13_columns_024
private theorem arithBundle13_prefix_columns_06 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 32 = 11439834354341 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 28 4 10401984598907 1037849755434 arithBundle13_prefix_columns_05 arithBundle13_columns_028
private theorem arithBundle13_prefix_columns_07 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 36 = 12380233915081 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 32 4 11439834354341 940399560740 arithBundle13_prefix_columns_06 arithBundle13_columns_032
private theorem arithBundle13_prefix_columns_08 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 40 = 13228065556823 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 36 4 12380233915081 847831641742 arithBundle13_prefix_columns_07 arithBundle13_columns_036
private theorem arithBundle13_prefix_columns_09 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 44 = 13988185708089 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 40 4 13228065556823 760120151266 arithBundle13_prefix_columns_08 arithBundle13_columns_040
private theorem arithBundle13_prefix_columns_10 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 48 = 14665449063910 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 44 4 13988185708089 677263355821 arithBundle13_prefix_columns_09 arithBundle13_columns_044
private theorem arithBundle13_prefix_columns_11 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 52 = 15264710971648 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 48 4 14665449063910 599261907738 arithBundle13_prefix_columns_10 arithBundle13_columns_048
private theorem arithBundle13_prefix_columns_12 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 56 = 15790844929080 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 52 4 15264710971648 526133957432 arithBundle13_prefix_columns_11 arithBundle13_columns_052
private theorem arithBundle13_prefix_columns_13 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 60 = 16248729879802 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 56 4 15790844929080 457884950722 arithBundle13_prefix_columns_12 arithBundle13_columns_056
private theorem arithBundle13_prefix_columns_14 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 64 = 16643222188724 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 60 4 16248729879802 394492308922 arithBundle13_prefix_columns_13 arithBundle13_columns_060
private theorem arithBundle13_prefix_columns_15 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 68 = 16979176259088 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 64 4 16643222188724 335954070364 arithBundle13_prefix_columns_14 arithBundle13_columns_064
private theorem arithBundle13_prefix_columns_16 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 72 = 17261447646030 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 68 4 16979176259088 282271386942 arithBundle13_prefix_columns_15 arithBundle13_columns_068
private theorem arithBundle13_prefix_columns_17 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 76 = 17494913460527 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 72 4 17261447646030 233465814497 arithBundle13_prefix_columns_16 arithBundle13_columns_072
private theorem arithBundle13_prefix_columns_18 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 80 = 17684449101003 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 76 4 17494913460527 189535640476 arithBundle13_prefix_columns_17 arithBundle13_columns_076
private theorem arithBundle13_prefix_columns_19 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 84 = 17834910894481 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 80 4 17684449101003 150461793478 arithBundle13_prefix_columns_18 arithBundle13_columns_080
private theorem arithBundle13_prefix_columns_20 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 88 = 17951153006588 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 84 4 17834910894481 116242112107 arithBundle13_prefix_columns_19 arithBundle13_columns_084
private theorem arithBundle13_prefix_columns_21 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 92 = 18038031285149 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 88 4 17951153006588 86878278561 arithBundle13_prefix_columns_20 arithBundle13_columns_088
private theorem arithBundle13_prefix_columns_22 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 96 = 18100422284363 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 92 4 18038031285149 62390999214 arithBundle13_prefix_columns_21 arithBundle13_columns_092
private theorem arithBundle13_prefix_columns_23 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 100 = 18143118202811 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 96 4 18100422284363 42695918448 arithBundle13_prefix_columns_22 arithBundle13_columns_096
private theorem arithBundle13_prefix_columns_24 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 104 = 18170655367724 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 100 4 18143118202811 27537164913 arithBundle13_prefix_columns_23 arithBundle13_columns_100
private theorem arithBundle13_prefix_columns_25 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 108 = 18187163560795 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 104 4 18170655367724 16508193071 arithBundle13_prefix_columns_24 arithBundle13_columns_104
private theorem arithBundle13_prefix_columns_26 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact26) 0 110 = 18192422437073 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact26) 0 108 2 18187163560795 5258876278 arithBundle13_prefix_columns_25 arithBundle13_columns_108

private theorem arithBundle13_ordinary_ranks : ordinaryRankBound contact26 = 624852890 := by decide +kernel
private theorem arithBundle13_ranks_000 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 4 = 6943806 :=
  contactRankWindow_of_rec contact26 0 4 6943806 (by decide +kernel)
private theorem arithBundle13_ranks_004 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 4 4 = 6305406 :=
  contactRankWindow_of_rec contact26 4 4 6305406 (by decide +kernel)
private theorem arithBundle13_ranks_008 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 8 4 = 5700606 :=
  contactRankWindow_of_rec contact26 8 4 5700606 (by decide +kernel)
private theorem arithBundle13_ranks_012 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 12 4 = 5129406 :=
  contactRankWindow_of_rec contact26 12 4 5129406 (by decide +kernel)
private theorem arithBundle13_ranks_016 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 16 4 = 4591806 :=
  contactRankWindow_of_rec contact26 16 4 4591806 (by decide +kernel)
private theorem arithBundle13_ranks_020 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 20 4 = 4087806 :=
  contactRankWindow_of_rec contact26 20 4 4087806 (by decide +kernel)
private theorem arithBundle13_ranks_024 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 24 4 = 3617406 :=
  contactRankWindow_of_rec contact26 24 4 3617406 (by decide +kernel)
private theorem arithBundle13_ranks_028 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 28 4 = 3180606 :=
  contactRankWindow_of_rec contact26 28 4 3180606 (by decide +kernel)
private theorem arithBundle13_ranks_032 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 32 4 = 2777385 :=
  contactRankWindow_of_rec contact26 32 4 2777385 (by decide +kernel)
private theorem arithBundle13_ranks_036 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 36 4 = 2407297 :=
  contactRankWindow_of_rec contact26 36 4 2407297 (by decide +kernel)
private theorem arithBundle13_ranks_040 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 40 4 = 2069431 :=
  contactRankWindow_of_rec contact26 40 4 2069431 (by decide +kernel)
private theorem arithBundle13_ranks_044 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 44 4 = 1762634 :=
  contactRankWindow_of_rec contact26 44 4 1762634 (by decide +kernel)
private theorem arithBundle13_ranks_048 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 48 4 = 1485665 :=
  contactRankWindow_of_rec contact26 48 4 1485665 (by decide +kernel)
private theorem arithBundle13_ranks_052 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 52 4 = 1237163 :=
  contactRankWindow_of_rec contact26 52 4 1237163 (by decide +kernel)
private theorem arithBundle13_ranks_056 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 56 4 = 1015774 :=
  contactRankWindow_of_rec contact26 56 4 1015774 (by decide +kernel)
private theorem arithBundle13_ranks_060 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 60 4 = 820353 :=
  contactRankWindow_of_rec contact26 60 4 820353 (by decide +kernel)
private theorem arithBundle13_ranks_064 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 64 4 = 649439 :=
  contactRankWindow_of_rec contact26 64 4 649439 (by decide +kernel)
private theorem arithBundle13_ranks_068 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 68 4 = 501682 :=
  contactRankWindow_of_rec contact26 68 4 501682 (by decide +kernel)
private theorem arithBundle13_ranks_072 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 72 4 = 376033 :=
  contactRankWindow_of_rec contact26 72 4 376033 (by decide +kernel)
private theorem arithBundle13_ranks_076 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 76 4 = 270931 :=
  contactRankWindow_of_rec contact26 76 4 270931 (by decide +kernel)
private theorem arithBundle13_ranks_080 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 80 4 = 185030 :=
  contactRankWindow_of_rec contact26 80 4 185030 (by decide +kernel)
private theorem arithBundle13_ranks_084 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 84 4 = 117377 :=
  contactRankWindow_of_rec contact26 84 4 117377 (by decide +kernel)
private theorem arithBundle13_ranks_088 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 88 4 = 66311 :=
  contactRankWindow_of_rec contact26 88 4 66311 (by decide +kernel)
private theorem arithBundle13_ranks_092 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 92 4 = 30490 :=
  contactRankWindow_of_rec contact26 92 4 30490 (by decide +kernel)
private theorem arithBundle13_ranks_096 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 96 4 = 9117 :=
  contactRankWindow_of_rec contact26 96 4 9117 (by decide +kernel)
private theorem arithBundle13_ranks_100 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 100 4 = 504 :=
  contactRankWindow_of_rec contact26 100 4 504 (by decide +kernel)
private theorem arithBundle13_ranks_104 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 104 6 = 0 :=
  contactRankWindow_of_rec contact26 104 6 0 (by decide +kernel)
private theorem arithBundle13_prefix_ranks_00 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 8 = 13249212 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 4 4 6943806 6305406 arithBundle13_ranks_000 arithBundle13_ranks_004
private theorem arithBundle13_prefix_ranks_01 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 12 = 18949818 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 8 4 13249212 5700606 arithBundle13_prefix_ranks_00 arithBundle13_ranks_008
private theorem arithBundle13_prefix_ranks_02 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 16 = 24079224 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 12 4 18949818 5129406 arithBundle13_prefix_ranks_01 arithBundle13_ranks_012
private theorem arithBundle13_prefix_ranks_03 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 20 = 28671030 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 16 4 24079224 4591806 arithBundle13_prefix_ranks_02 arithBundle13_ranks_016
private theorem arithBundle13_prefix_ranks_04 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 24 = 32758836 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 20 4 28671030 4087806 arithBundle13_prefix_ranks_03 arithBundle13_ranks_020
private theorem arithBundle13_prefix_ranks_05 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 28 = 36376242 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 24 4 32758836 3617406 arithBundle13_prefix_ranks_04 arithBundle13_ranks_024
private theorem arithBundle13_prefix_ranks_06 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 32 = 39556848 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 28 4 36376242 3180606 arithBundle13_prefix_ranks_05 arithBundle13_ranks_028
private theorem arithBundle13_prefix_ranks_07 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 36 = 42334233 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 32 4 39556848 2777385 arithBundle13_prefix_ranks_06 arithBundle13_ranks_032
private theorem arithBundle13_prefix_ranks_08 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 40 = 44741530 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 36 4 42334233 2407297 arithBundle13_prefix_ranks_07 arithBundle13_ranks_036
private theorem arithBundle13_prefix_ranks_09 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 44 = 46810961 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 40 4 44741530 2069431 arithBundle13_prefix_ranks_08 arithBundle13_ranks_040
private theorem arithBundle13_prefix_ranks_10 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 48 = 48573595 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 44 4 46810961 1762634 arithBundle13_prefix_ranks_09 arithBundle13_ranks_044
private theorem arithBundle13_prefix_ranks_11 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 52 = 50059260 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 48 4 48573595 1485665 arithBundle13_prefix_ranks_10 arithBundle13_ranks_048
private theorem arithBundle13_prefix_ranks_12 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 56 = 51296423 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 52 4 50059260 1237163 arithBundle13_prefix_ranks_11 arithBundle13_ranks_052
private theorem arithBundle13_prefix_ranks_13 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 60 = 52312197 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 56 4 51296423 1015774 arithBundle13_prefix_ranks_12 arithBundle13_ranks_056
private theorem arithBundle13_prefix_ranks_14 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 64 = 53132550 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 60 4 52312197 820353 arithBundle13_prefix_ranks_13 arithBundle13_ranks_060
private theorem arithBundle13_prefix_ranks_15 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 68 = 53781989 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 64 4 53132550 649439 arithBundle13_prefix_ranks_14 arithBundle13_ranks_064
private theorem arithBundle13_prefix_ranks_16 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 72 = 54283671 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 68 4 53781989 501682 arithBundle13_prefix_ranks_15 arithBundle13_ranks_068
private theorem arithBundle13_prefix_ranks_17 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 76 = 54659704 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 72 4 54283671 376033 arithBundle13_prefix_ranks_16 arithBundle13_ranks_072
private theorem arithBundle13_prefix_ranks_18 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 80 = 54930635 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 76 4 54659704 270931 arithBundle13_prefix_ranks_17 arithBundle13_ranks_076
private theorem arithBundle13_prefix_ranks_19 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 84 = 55115665 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 80 4 54930635 185030 arithBundle13_prefix_ranks_18 arithBundle13_ranks_080
private theorem arithBundle13_prefix_ranks_20 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 88 = 55233042 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 84 4 55115665 117377 arithBundle13_prefix_ranks_19 arithBundle13_ranks_084
private theorem arithBundle13_prefix_ranks_21 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 92 = 55299353 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 88 4 55233042 66311 arithBundle13_prefix_ranks_20 arithBundle13_ranks_088
private theorem arithBundle13_prefix_ranks_22 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 96 = 55329843 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 92 4 55299353 30490 arithBundle13_prefix_ranks_21 arithBundle13_ranks_092
private theorem arithBundle13_prefix_ranks_23 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 100 = 55338960 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 96 4 55329843 9117 arithBundle13_prefix_ranks_22 arithBundle13_ranks_096
private theorem arithBundle13_prefix_ranks_24 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 104 = 55339464 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 100 4 55338960 504 arithBundle13_prefix_ranks_23 arithBundle13_ranks_100
private theorem arithBundle13_prefix_ranks_25 : arithBundle13_sliceWindow (auxiliaryRankSlice contact26) 0 110 = 55339464 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact26) 0 104 6 55339464 0 arithBundle13_prefix_ranks_24 arithBundle13_ranks_104

theorem contact26_margin : sourceMargin contact26 :=
  arithBundle13_margin_of_checked_counts contact26 110 160116275649966 18192422437073 624852890 55339464
    rfl arithBundle13_ordinary_columns arithBundle13_prefix_columns_26 arithBundle13_ordinary_ranks arithBundle13_prefix_ranks_25 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle14_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle14_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle14_sliceWindow f a b = x) (hy : arithBundle14_sliceWindow f (a+b) c = y) :
    arithBundle14_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle14_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle14_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle14_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle14_sliceWindow,Nat.zero_add]

private theorem arithBundle14_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle14_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle14_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle14_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle14_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle14_ordinary_columns : ordinaryColumnCount contact27 = 2230853035480739 := by decide +kernel
private theorem arithBundle14_columns_000 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 4 = 7428896511770 :=
  contactColumnsWindow_fast contact27 0 4 7428896511770 (by decide +kernel)
private theorem arithBundle14_columns_004 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 4 4 = 7061072891610 :=
  contactColumnsWindow_fast contact27 4 4 7061072891610 (by decide +kernel)
private theorem arithBundle14_columns_008 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 8 4 = 6702631444090 :=
  contactColumnsWindow_fast contact27 8 4 6702631444090 (by decide +kernel)
private theorem arithBundle14_columns_012 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 12 4 = 6353575218946 :=
  contactColumnsWindow_fast contact27 12 4 6353575218946 (by decide +kernel)
private theorem arithBundle14_columns_016 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 16 4 = 6013902133662 :=
  contactColumnsWindow_fast contact27 16 4 6013902133662 (by decide +kernel)
private theorem arithBundle14_columns_020 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 20 4 = 5683614324110 :=
  contactColumnsWindow_fast contact27 20 4 5683614324110 (by decide +kernel)
private theorem arithBundle14_columns_024 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 24 4 = 5362727527849 :=
  contactColumnsWindow_fast contact27 24 4 5362727527849 (by decide +kernel)
private theorem arithBundle14_columns_028 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 28 4 = 5051263628571 :=
  contactColumnsWindow_fast contact27 28 4 5051263628571 (by decide +kernel)
private theorem arithBundle14_columns_032 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 32 4 = 4749188568718 :=
  contactColumnsWindow_fast contact27 32 4 4749188568718 (by decide +kernel)
private theorem arithBundle14_columns_036 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 36 4 = 4456500013237 :=
  contactColumnsWindow_fast contact27 36 4 4456500013237 (by decide +kernel)
private theorem arithBundle14_columns_040 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 40 4 = 4173199782006 :=
  contactColumnsWindow_fast contact27 40 4 4173199782006 (by decide +kernel)
private theorem arithBundle14_columns_044 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 44 4 = 3899307441660 :=
  contactColumnsWindow_fast contact27 44 4 3899307441660 (by decide +kernel)
private theorem arithBundle14_columns_048 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 48 4 = 3634839227835 :=
  contactColumnsWindow_fast contact27 48 4 3634839227835 (by decide +kernel)
private theorem arithBundle14_columns_052 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 52 4 = 3379761237299 :=
  contactColumnsWindow_fast contact27 52 4 3379761237299 (by decide +kernel)
private theorem arithBundle14_columns_056 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 56 4 = 3134074073778 :=
  contactColumnsWindow_fast contact27 56 4 3134074073778 (by decide +kernel)
private theorem arithBundle14_columns_060 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 60 4 = 2897777550484 :=
  contactColumnsWindow_fast contact27 60 4 2897777550484 (by decide +kernel)
private theorem arithBundle14_columns_064 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 64 4 = 2670898830861 :=
  contactColumnsWindow_fast contact27 64 4 2670898830861 (by decide +kernel)
private theorem arithBundle14_columns_068 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 68 4 = 2453441441124 :=
  contactColumnsWindow_fast contact27 68 4 2453441441124 (by decide +kernel)
private theorem arithBundle14_columns_072 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 72 4 = 2245379392612 :=
  contactColumnsWindow_fast contact27 72 4 2245379392612 (by decide +kernel)
private theorem arithBundle14_columns_076 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 76 4 = 2046708841631 :=
  contactColumnsWindow_fast contact27 76 4 2046708841631 (by decide +kernel)
private theorem arithBundle14_columns_080 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 80 4 = 1857428724214 :=
  contactColumnsWindow_fast contact27 80 4 1857428724214 (by decide +kernel)
private theorem arithBundle14_columns_084 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 84 4 = 1677571614918 :=
  contactColumnsWindow_fast contact27 84 4 1677571614918 (by decide +kernel)
private theorem arithBundle14_columns_088 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 88 4 = 1507131170173 :=
  contactColumnsWindow_fast contact27 88 4 1507131170173 (by decide +kernel)
private theorem arithBundle14_columns_092 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 92 4 = 1346085797458 :=
  contactColumnsWindow_fast contact27 92 4 1346085797458 (by decide +kernel)
private theorem arithBundle14_columns_096 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 96 4 = 1194431812358 :=
  contactColumnsWindow_fast contact27 96 4 1194431812358 (by decide +kernel)
private theorem arithBundle14_columns_100 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 100 4 = 1052168573321 :=
  contactColumnsWindow_fast contact27 100 4 1052168573321 (by decide +kernel)
private theorem arithBundle14_columns_104 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 104 4 = 919332695358 :=
  contactColumnsWindow_fast contact27 104 4 919332695358 (by decide +kernel)
private theorem arithBundle14_columns_108 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 108 4 = 795909244339 :=
  contactColumnsWindow_fast contact27 108 4 795909244339 (by decide +kernel)
private theorem arithBundle14_columns_112 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 112 4 = 681880367644 :=
  contactColumnsWindow_fast contact27 112 4 681880367644 (by decide +kernel)
private theorem arithBundle14_columns_116 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 116 4 = 577243014810 :=
  contactColumnsWindow_fast contact27 116 4 577243014810 (by decide +kernel)
private theorem arithBundle14_columns_120 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 120 4 = 481997600219 :=
  contactColumnsWindow_fast contact27 120 4 481997600219 (by decide +kernel)
private theorem arithBundle14_columns_124 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 124 4 = 396181947408 :=
  contactColumnsWindow_fast contact27 124 4 396181947408 (by decide +kernel)
private theorem arithBundle14_columns_128 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 128 4 = 319775489940 :=
  contactColumnsWindow_fast contact27 128 4 319775489940 (by decide +kernel)
private theorem arithBundle14_columns_132 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 132 4 = 252761460849 :=
  contactColumnsWindow_fast contact27 132 4 252761460849 (by decide +kernel)
private theorem arithBundle14_columns_136 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 136 4 = 195077427027 :=
  contactColumnsWindow_fast contact27 136 4 195077427027 (by decide +kernel)
private theorem arithBundle14_columns_140 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 140 4 = 146478909166 :=
  contactColumnsWindow_fast contact27 140 4 146478909166 (by decide +kernel)
private theorem arithBundle14_columns_144 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 144 4 = 106578228015 :=
  contactColumnsWindow_fast contact27 144 4 106578228015 (by decide +kernel)
private theorem arithBundle14_columns_148 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 148 4 = 74760804602 :=
  contactColumnsWindow_fast contact27 148 4 74760804602 (by decide +kernel)
private theorem arithBundle14_columns_152 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 152 4 = 50265126293 :=
  contactColumnsWindow_fast contact27 152 4 50265126293 (by decide +kernel)
private theorem arithBundle14_columns_156 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 156 4 = 32179057735 :=
  contactColumnsWindow_fast contact27 156 4 32179057735 (by decide +kernel)
private theorem arithBundle14_columns_160 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 160 2 = 11023744973 :=
  contactColumnsWindow_fast contact27 160 2 11023744973 (by decide +kernel)
private theorem arithBundle14_prefix_columns_00 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 8 = 14489969403380 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 4 4 7428896511770 7061072891610 arithBundle14_columns_000 arithBundle14_columns_004
private theorem arithBundle14_prefix_columns_01 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 12 = 21192600847470 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 8 4 14489969403380 6702631444090 arithBundle14_prefix_columns_00 arithBundle14_columns_008
private theorem arithBundle14_prefix_columns_02 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 16 = 27546176066416 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 12 4 21192600847470 6353575218946 arithBundle14_prefix_columns_01 arithBundle14_columns_012
private theorem arithBundle14_prefix_columns_03 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 20 = 33560078200078 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 16 4 27546176066416 6013902133662 arithBundle14_prefix_columns_02 arithBundle14_columns_016
private theorem arithBundle14_prefix_columns_04 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 24 = 39243692524188 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 20 4 33560078200078 5683614324110 arithBundle14_prefix_columns_03 arithBundle14_columns_020
private theorem arithBundle14_prefix_columns_05 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 28 = 44606420052037 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 24 4 39243692524188 5362727527849 arithBundle14_prefix_columns_04 arithBundle14_columns_024
private theorem arithBundle14_prefix_columns_06 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 32 = 49657683680608 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 28 4 44606420052037 5051263628571 arithBundle14_prefix_columns_05 arithBundle14_columns_028
private theorem arithBundle14_prefix_columns_07 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 36 = 54406872249326 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 32 4 49657683680608 4749188568718 arithBundle14_prefix_columns_06 arithBundle14_columns_032
private theorem arithBundle14_prefix_columns_08 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 40 = 58863372262563 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 36 4 54406872249326 4456500013237 arithBundle14_prefix_columns_07 arithBundle14_columns_036
private theorem arithBundle14_prefix_columns_09 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 44 = 63036572044569 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 40 4 58863372262563 4173199782006 arithBundle14_prefix_columns_08 arithBundle14_columns_040
private theorem arithBundle14_prefix_columns_10 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 48 = 66935879486229 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 44 4 63036572044569 3899307441660 arithBundle14_prefix_columns_09 arithBundle14_columns_044
private theorem arithBundle14_prefix_columns_11 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 52 = 70570718714064 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 48 4 66935879486229 3634839227835 arithBundle14_prefix_columns_10 arithBundle14_columns_048
private theorem arithBundle14_prefix_columns_12 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 56 = 73950479951363 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 52 4 70570718714064 3379761237299 arithBundle14_prefix_columns_11 arithBundle14_columns_052
private theorem arithBundle14_prefix_columns_13 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 60 = 77084554025141 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 56 4 73950479951363 3134074073778 arithBundle14_prefix_columns_12 arithBundle14_columns_056
private theorem arithBundle14_prefix_columns_14 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 64 = 79982331575625 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 60 4 77084554025141 2897777550484 arithBundle14_prefix_columns_13 arithBundle14_columns_060
private theorem arithBundle14_prefix_columns_15 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 68 = 82653230406486 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 64 4 79982331575625 2670898830861 arithBundle14_prefix_columns_14 arithBundle14_columns_064
private theorem arithBundle14_prefix_columns_16 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 72 = 85106671847610 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 68 4 82653230406486 2453441441124 arithBundle14_prefix_columns_15 arithBundle14_columns_068
private theorem arithBundle14_prefix_columns_17 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 76 = 87352051240222 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 72 4 85106671847610 2245379392612 arithBundle14_prefix_columns_16 arithBundle14_columns_072
private theorem arithBundle14_prefix_columns_18 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 80 = 89398760081853 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 76 4 87352051240222 2046708841631 arithBundle14_prefix_columns_17 arithBundle14_columns_076
private theorem arithBundle14_prefix_columns_19 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 84 = 91256188806067 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 80 4 89398760081853 1857428724214 arithBundle14_prefix_columns_18 arithBundle14_columns_080
private theorem arithBundle14_prefix_columns_20 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 88 = 92933760420985 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 84 4 91256188806067 1677571614918 arithBundle14_prefix_columns_19 arithBundle14_columns_084
private theorem arithBundle14_prefix_columns_21 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 92 = 94440891591158 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 88 4 92933760420985 1507131170173 arithBundle14_prefix_columns_20 arithBundle14_columns_088
private theorem arithBundle14_prefix_columns_22 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 96 = 95786977388616 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 92 4 94440891591158 1346085797458 arithBundle14_prefix_columns_21 arithBundle14_columns_092
private theorem arithBundle14_prefix_columns_23 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 100 = 96981409200974 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 96 4 95786977388616 1194431812358 arithBundle14_prefix_columns_22 arithBundle14_columns_096
private theorem arithBundle14_prefix_columns_24 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 104 = 98033577774295 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 100 4 96981409200974 1052168573321 arithBundle14_prefix_columns_23 arithBundle14_columns_100
private theorem arithBundle14_prefix_columns_25 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 108 = 98952910469653 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 104 4 98033577774295 919332695358 arithBundle14_prefix_columns_24 arithBundle14_columns_104
private theorem arithBundle14_prefix_columns_26 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 112 = 99748819713992 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 108 4 98952910469653 795909244339 arithBundle14_prefix_columns_25 arithBundle14_columns_108
private theorem arithBundle14_prefix_columns_27 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 116 = 100430700081636 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 112 4 99748819713992 681880367644 arithBundle14_prefix_columns_26 arithBundle14_columns_112
private theorem arithBundle14_prefix_columns_28 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 120 = 101007943096446 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 116 4 100430700081636 577243014810 arithBundle14_prefix_columns_27 arithBundle14_columns_116
private theorem arithBundle14_prefix_columns_29 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 124 = 101489940696665 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 120 4 101007943096446 481997600219 arithBundle14_prefix_columns_28 arithBundle14_columns_120
private theorem arithBundle14_prefix_columns_30 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 128 = 101886122644073 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 124 4 101489940696665 396181947408 arithBundle14_prefix_columns_29 arithBundle14_columns_124
private theorem arithBundle14_prefix_columns_31 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 132 = 102205898134013 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 128 4 101886122644073 319775489940 arithBundle14_prefix_columns_30 arithBundle14_columns_128
private theorem arithBundle14_prefix_columns_32 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 136 = 102458659594862 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 132 4 102205898134013 252761460849 arithBundle14_prefix_columns_31 arithBundle14_columns_132
private theorem arithBundle14_prefix_columns_33 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 140 = 102653737021889 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 136 4 102458659594862 195077427027 arithBundle14_prefix_columns_32 arithBundle14_columns_136
private theorem arithBundle14_prefix_columns_34 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 144 = 102800215931055 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 140 4 102653737021889 146478909166 arithBundle14_prefix_columns_33 arithBundle14_columns_140
private theorem arithBundle14_prefix_columns_35 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 148 = 102906794159070 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 144 4 102800215931055 106578228015 arithBundle14_prefix_columns_34 arithBundle14_columns_144
private theorem arithBundle14_prefix_columns_36 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 152 = 102981554963672 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 148 4 102906794159070 74760804602 arithBundle14_prefix_columns_35 arithBundle14_columns_148
private theorem arithBundle14_prefix_columns_37 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 156 = 103031820089965 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 152 4 102981554963672 50265126293 arithBundle14_prefix_columns_36 arithBundle14_columns_152
private theorem arithBundle14_prefix_columns_38 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 160 = 103063999147700 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 156 4 103031820089965 32179057735 arithBundle14_prefix_columns_37 arithBundle14_columns_156
private theorem arithBundle14_prefix_columns_39 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact27) 0 162 = 103075022892673 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact27) 0 160 2 103063999147700 11023744973 arithBundle14_prefix_columns_38 arithBundle14_columns_160

private theorem arithBundle14_ordinary_ranks : ordinaryRankBound contact27 = 8589077384 := by decide +kernel
private theorem arithBundle14_ranks_000 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 4 = 28000896 :=
  contactRankWindow_of_rec contact27 0 4 28000896 (by decide +kernel)
private theorem arithBundle14_ranks_004 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 4 4 = 26198256 :=
  contactRankWindow_of_rec contact27 4 4 26198256 (by decide +kernel)
private theorem arithBundle14_ranks_008 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 8 4 = 24460576 :=
  contactRankWindow_of_rec contact27 8 4 24460576 (by decide +kernel)
private theorem arithBundle14_ranks_012 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 12 4 = 22787856 :=
  contactRankWindow_of_rec contact27 12 4 22787856 (by decide +kernel)
private theorem arithBundle14_ranks_016 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 16 4 = 21180096 :=
  contactRankWindow_of_rec contact27 16 4 21180096 (by decide +kernel)
private theorem arithBundle14_ranks_020 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 20 4 = 19637296 :=
  contactRankWindow_of_rec contact27 20 4 19637296 (by decide +kernel)
private theorem arithBundle14_ranks_024 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 24 4 = 18159456 :=
  contactRankWindow_of_rec contact27 24 4 18159456 (by decide +kernel)
private theorem arithBundle14_ranks_028 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 28 4 = 16746576 :=
  contactRankWindow_of_rec contact27 28 4 16746576 (by decide +kernel)
private theorem arithBundle14_ranks_032 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 32 4 = 15398656 :=
  contactRankWindow_of_rec contact27 32 4 15398656 (by decide +kernel)
private theorem arithBundle14_ranks_036 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 36 4 = 14115696 :=
  contactRankWindow_of_rec contact27 36 4 14115696 (by decide +kernel)
private theorem arithBundle14_ranks_040 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 40 4 = 12897696 :=
  contactRankWindow_of_rec contact27 40 4 12897696 (by decide +kernel)
private theorem arithBundle14_ranks_044 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 44 4 = 11744656 :=
  contactRankWindow_of_rec contact27 44 4 11744656 (by decide +kernel)
private theorem arithBundle14_ranks_048 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 48 4 = 10656547 :=
  contactRankWindow_of_rec contact27 48 4 10656547 (by decide +kernel)
private theorem arithBundle14_ranks_052 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 52 4 = 9632755 :=
  contactRankWindow_of_rec contact27 52 4 9632755 (by decide +kernel)
private theorem arithBundle14_ranks_056 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 56 4 = 8672033 :=
  contactRankWindow_of_rec contact27 56 4 8672033 (by decide +kernel)
private theorem arithBundle14_ranks_060 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 60 4 = 7773079 :=
  contactRankWindow_of_rec contact27 60 4 7773079 (by decide +kernel)
private theorem arithBundle14_ranks_064 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 64 4 = 6934312 :=
  contactRankWindow_of_rec contact27 64 4 6934312 (by decide +kernel)
private theorem arithBundle14_ranks_068 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 68 4 = 6153981 :=
  contactRankWindow_of_rec contact27 68 4 6153981 (by decide +kernel)
private theorem arithBundle14_ranks_072 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 72 4 = 5430195 :=
  contactRankWindow_of_rec contact27 72 4 5430195 (by decide +kernel)
private theorem arithBundle14_ranks_076 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 76 4 = 4761088 :=
  contactRankWindow_of_rec contact27 76 4 4761088 (by decide +kernel)
private theorem arithBundle14_ranks_080 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 80 4 = 4145049 :=
  contactRankWindow_of_rec contact27 80 4 4145049 (by decide +kernel)
private theorem arithBundle14_ranks_084 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 84 4 = 3580047 :=
  contactRankWindow_of_rec contact27 84 4 3580047 (by decide +kernel)
private theorem arithBundle14_ranks_088 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 88 4 = 3064216 :=
  contactRankWindow_of_rec contact27 88 4 3064216 (by decide +kernel)
private theorem arithBundle14_ranks_092 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 92 4 = 2596085 :=
  contactRankWindow_of_rec contact27 92 4 2596085 (by decide +kernel)
private theorem arithBundle14_ranks_096 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 96 4 = 2173483 :=
  contactRankWindow_of_rec contact27 96 4 2173483 (by decide +kernel)
private theorem arithBundle14_ranks_100 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 100 4 = 1794544 :=
  contactRankWindow_of_rec contact27 100 4 1794544 (by decide +kernel)
private theorem arithBundle14_ranks_104 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 104 4 = 1457937 :=
  contactRankWindow_of_rec contact27 104 4 1457937 (by decide +kernel)
private theorem arithBundle14_ranks_108 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 108 4 = 1161351 :=
  contactRankWindow_of_rec contact27 108 4 1161351 (by decide +kernel)
private theorem arithBundle14_ranks_112 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 112 4 = 902920 :=
  contactRankWindow_of_rec contact27 112 4 902920 (by decide +kernel)
private theorem arithBundle14_ranks_116 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 116 4 = 681453 :=
  contactRankWindow_of_rec contact27 116 4 681453 (by decide +kernel)
private theorem arithBundle14_ranks_120 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 120 4 = 494499 :=
  contactRankWindow_of_rec contact27 120 4 494499 (by decide +kernel)
private theorem arithBundle14_ranks_124 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 124 4 = 340192 :=
  contactRankWindow_of_rec contact27 124 4 340192 (by decide +kernel)
private theorem arithBundle14_ranks_128 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 128 4 = 217481 :=
  contactRankWindow_of_rec contact27 128 4 217481 (by decide +kernel)
private theorem arithBundle14_ranks_132 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 132 4 = 123775 :=
  contactRankWindow_of_rec contact27 132 4 123775 (by decide +kernel)
private theorem arithBundle14_ranks_136 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 136 4 = 57253 :=
  contactRankWindow_of_rec contact27 136 4 57253 (by decide +kernel)
private theorem arithBundle14_ranks_140 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 140 4 = 17281 :=
  contactRankWindow_of_rec contact27 140 4 17281 (by decide +kernel)
private theorem arithBundle14_ranks_144 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 144 4 = 970 :=
  contactRankWindow_of_rec contact27 144 4 970 (by decide +kernel)
private theorem arithBundle14_ranks_148 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 148 14 = 0 :=
  contactRankWindow_of_rec contact27 148 14 0 (by decide +kernel)
private theorem arithBundle14_prefix_ranks_00 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 8 = 54199152 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 4 4 28000896 26198256 arithBundle14_ranks_000 arithBundle14_ranks_004
private theorem arithBundle14_prefix_ranks_01 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 12 = 78659728 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 8 4 54199152 24460576 arithBundle14_prefix_ranks_00 arithBundle14_ranks_008
private theorem arithBundle14_prefix_ranks_02 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 16 = 101447584 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 12 4 78659728 22787856 arithBundle14_prefix_ranks_01 arithBundle14_ranks_012
private theorem arithBundle14_prefix_ranks_03 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 20 = 122627680 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 16 4 101447584 21180096 arithBundle14_prefix_ranks_02 arithBundle14_ranks_016
private theorem arithBundle14_prefix_ranks_04 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 24 = 142264976 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 20 4 122627680 19637296 arithBundle14_prefix_ranks_03 arithBundle14_ranks_020
private theorem arithBundle14_prefix_ranks_05 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 28 = 160424432 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 24 4 142264976 18159456 arithBundle14_prefix_ranks_04 arithBundle14_ranks_024
private theorem arithBundle14_prefix_ranks_06 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 32 = 177171008 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 28 4 160424432 16746576 arithBundle14_prefix_ranks_05 arithBundle14_ranks_028
private theorem arithBundle14_prefix_ranks_07 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 36 = 192569664 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 32 4 177171008 15398656 arithBundle14_prefix_ranks_06 arithBundle14_ranks_032
private theorem arithBundle14_prefix_ranks_08 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 40 = 206685360 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 36 4 192569664 14115696 arithBundle14_prefix_ranks_07 arithBundle14_ranks_036
private theorem arithBundle14_prefix_ranks_09 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 44 = 219583056 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 40 4 206685360 12897696 arithBundle14_prefix_ranks_08 arithBundle14_ranks_040
private theorem arithBundle14_prefix_ranks_10 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 48 = 231327712 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 44 4 219583056 11744656 arithBundle14_prefix_ranks_09 arithBundle14_ranks_044
private theorem arithBundle14_prefix_ranks_11 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 52 = 241984259 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 48 4 231327712 10656547 arithBundle14_prefix_ranks_10 arithBundle14_ranks_048
private theorem arithBundle14_prefix_ranks_12 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 56 = 251617014 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 52 4 241984259 9632755 arithBundle14_prefix_ranks_11 arithBundle14_ranks_052
private theorem arithBundle14_prefix_ranks_13 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 60 = 260289047 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 56 4 251617014 8672033 arithBundle14_prefix_ranks_12 arithBundle14_ranks_056
private theorem arithBundle14_prefix_ranks_14 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 64 = 268062126 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 60 4 260289047 7773079 arithBundle14_prefix_ranks_13 arithBundle14_ranks_060
private theorem arithBundle14_prefix_ranks_15 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 68 = 274996438 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 64 4 268062126 6934312 arithBundle14_prefix_ranks_14 arithBundle14_ranks_064
private theorem arithBundle14_prefix_ranks_16 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 72 = 281150419 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 68 4 274996438 6153981 arithBundle14_prefix_ranks_15 arithBundle14_ranks_068
private theorem arithBundle14_prefix_ranks_17 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 76 = 286580614 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 72 4 281150419 5430195 arithBundle14_prefix_ranks_16 arithBundle14_ranks_072
private theorem arithBundle14_prefix_ranks_18 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 80 = 291341702 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 76 4 286580614 4761088 arithBundle14_prefix_ranks_17 arithBundle14_ranks_076
private theorem arithBundle14_prefix_ranks_19 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 84 = 295486751 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 80 4 291341702 4145049 arithBundle14_prefix_ranks_18 arithBundle14_ranks_080
private theorem arithBundle14_prefix_ranks_20 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 88 = 299066798 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 84 4 295486751 3580047 arithBundle14_prefix_ranks_19 arithBundle14_ranks_084
private theorem arithBundle14_prefix_ranks_21 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 92 = 302131014 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 88 4 299066798 3064216 arithBundle14_prefix_ranks_20 arithBundle14_ranks_088
private theorem arithBundle14_prefix_ranks_22 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 96 = 304727099 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 92 4 302131014 2596085 arithBundle14_prefix_ranks_21 arithBundle14_ranks_092
private theorem arithBundle14_prefix_ranks_23 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 100 = 306900582 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 96 4 304727099 2173483 arithBundle14_prefix_ranks_22 arithBundle14_ranks_096
private theorem arithBundle14_prefix_ranks_24 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 104 = 308695126 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 100 4 306900582 1794544 arithBundle14_prefix_ranks_23 arithBundle14_ranks_100
private theorem arithBundle14_prefix_ranks_25 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 108 = 310153063 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 104 4 308695126 1457937 arithBundle14_prefix_ranks_24 arithBundle14_ranks_104
private theorem arithBundle14_prefix_ranks_26 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 112 = 311314414 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 108 4 310153063 1161351 arithBundle14_prefix_ranks_25 arithBundle14_ranks_108
private theorem arithBundle14_prefix_ranks_27 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 116 = 312217334 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 112 4 311314414 902920 arithBundle14_prefix_ranks_26 arithBundle14_ranks_112
private theorem arithBundle14_prefix_ranks_28 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 120 = 312898787 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 116 4 312217334 681453 arithBundle14_prefix_ranks_27 arithBundle14_ranks_116
private theorem arithBundle14_prefix_ranks_29 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 124 = 313393286 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 120 4 312898787 494499 arithBundle14_prefix_ranks_28 arithBundle14_ranks_120
private theorem arithBundle14_prefix_ranks_30 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 128 = 313733478 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 124 4 313393286 340192 arithBundle14_prefix_ranks_29 arithBundle14_ranks_124
private theorem arithBundle14_prefix_ranks_31 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 132 = 313950959 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 128 4 313733478 217481 arithBundle14_prefix_ranks_30 arithBundle14_ranks_128
private theorem arithBundle14_prefix_ranks_32 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 136 = 314074734 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 132 4 313950959 123775 arithBundle14_prefix_ranks_31 arithBundle14_ranks_132
private theorem arithBundle14_prefix_ranks_33 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 140 = 314131987 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 136 4 314074734 57253 arithBundle14_prefix_ranks_32 arithBundle14_ranks_136
private theorem arithBundle14_prefix_ranks_34 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 144 = 314149268 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 140 4 314131987 17281 arithBundle14_prefix_ranks_33 arithBundle14_ranks_140
private theorem arithBundle14_prefix_ranks_35 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 148 = 314150238 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 144 4 314149268 970 arithBundle14_prefix_ranks_34 arithBundle14_ranks_144
private theorem arithBundle14_prefix_ranks_36 : arithBundle14_sliceWindow (auxiliaryRankSlice contact27) 0 162 = 314150238 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact27) 0 148 14 314150238 0 arithBundle14_prefix_ranks_35 arithBundle14_ranks_148

theorem contact27_margin : sourceMargin contact27 :=
  arithBundle14_margin_of_checked_counts contact27 162 2230853035480739 103075022892673 8589077384 314150238
    rfl arithBundle14_ordinary_columns arithBundle14_prefix_columns_39 arithBundle14_ordinary_ranks arithBundle14_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle15_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle15_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle15_sliceWindow f a b = x) (hy : arithBundle15_sliceWindow f (a+b) c = y) :
    arithBundle15_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle15_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle15_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle15_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle15_sliceWindow,Nat.zero_add]

private theorem arithBundle15_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle15_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle15_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle15_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle15_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle15_ordinary_columns : ordinaryColumnCount contact30 = 516970197448924 := by decide +kernel
private theorem arithBundle15_columns_000 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 4 = 1936742548952 :=
  contactColumnsWindow_fast contact30 0 4 1936742548952 (by decide +kernel)
private theorem arithBundle15_columns_004 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 4 4 = 1802372428858 :=
  contactColumnsWindow_fast contact30 4 4 1802372428858 (by decide +kernel)
private theorem arithBundle15_columns_008 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 8 4 = 1672857227922 :=
  contactColumnsWindow_fast contact30 8 4 1672857227922 (by decide +kernel)
private theorem arithBundle15_columns_012 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 12 4 = 1548196818866 :=
  contactColumnsWindow_fast contact30 12 4 1548196818866 (by decide +kernel)
private theorem arithBundle15_columns_016 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 16 4 = 1428391408398 :=
  contactColumnsWindow_fast contact30 16 4 1428391408398 (by decide +kernel)
private theorem arithBundle15_columns_020 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 20 4 = 1313455805267 :=
  contactColumnsWindow_fast contact30 20 4 1313455805267 (by decide +kernel)
private theorem arithBundle15_columns_024 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 24 4 = 1203398482870 :=
  contactColumnsWindow_fast contact30 24 4 1203398482870 (by decide +kernel)
private theorem arithBundle15_columns_028 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 28 4 = 1098197561838 :=
  contactColumnsWindow_fast contact30 28 4 1098197561838 (by decide +kernel)
private theorem arithBundle15_columns_032 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 32 4 = 997854616473 :=
  contactColumnsWindow_fast contact30 32 4 997854616473 (by decide +kernel)
private theorem arithBundle15_columns_036 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 36 4 = 902368009950 :=
  contactColumnsWindow_fast contact30 36 4 902368009950 (by decide +kernel)
private theorem arithBundle15_columns_040 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 40 4 = 811754404058 :=
  contactColumnsWindow_fast contact30 40 4 811754404058 (by decide +kernel)
private theorem arithBundle15_columns_044 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 44 4 = 726015846193 :=
  contactColumnsWindow_fast contact30 44 4 726015846193 (by decide +kernel)
private theorem arithBundle15_columns_048 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 48 4 = 645133926654 :=
  contactColumnsWindow_fast contact30 48 4 645133926654 (by decide +kernel)
private theorem arithBundle15_columns_052 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 52 4 = 569109795018 :=
  contactColumnsWindow_fast contact30 52 4 569109795018 (by decide +kernel)
private theorem arithBundle15_columns_056 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 56 4 = 497941938402 :=
  contactColumnsWindow_fast contact30 56 4 497941938402 (by decide +kernel)
private theorem arithBundle15_columns_060 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 60 4 = 431650343810 :=
  contactColumnsWindow_fast contact30 60 4 431650343810 (by decide +kernel)
private theorem arithBundle15_columns_064 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 64 4 = 370230629986 :=
  contactColumnsWindow_fast contact30 64 4 370230629986 (by decide +kernel)
private theorem arithBundle15_columns_068 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 68 4 = 313667662920 :=
  contactColumnsWindow_fast contact30 68 4 313667662920 (by decide +kernel)
private theorem arithBundle15_columns_072 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 72 4 = 261962300463 :=
  contactColumnsWindow_fast contact30 72 4 261962300463 (by decide +kernel)
private theorem arithBundle15_columns_076 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 76 4 = 215113661526 :=
  contactColumnsWindow_fast contact30 76 4 215113661526 (by decide +kernel)
private theorem arithBundle15_columns_080 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 80 4 = 173143699988 :=
  contactColumnsWindow_fast contact30 80 4 173143699988 (by decide +kernel)
private theorem arithBundle15_columns_084 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 84 4 = 136042740889 :=
  contactColumnsWindow_fast contact30 84 4 136042740889 (by decide +kernel)
private theorem arithBundle15_columns_088 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 88 4 = 103798726086 :=
  contactColumnsWindow_fast contact30 88 4 103798726086 (by decide +kernel)
private theorem arithBundle15_columns_092 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 92 4 = 76412160627 :=
  contactColumnsWindow_fast contact30 92 4 76412160627 (by decide +kernel)
private theorem arithBundle15_columns_096 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 96 4 = 53867422947 :=
  contactColumnsWindow_fast contact30 96 4 53867422947 (by decide +kernel)
private theorem arithBundle15_columns_100 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 100 4 = 36053970969 :=
  contactColumnsWindow_fast contact30 100 4 36053970969 (by decide +kernel)
private theorem arithBundle15_columns_104 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 104 4 = 22644844249 :=
  contactColumnsWindow_fast contact30 104 4 22644844249 (by decide +kernel)
private theorem arithBundle15_columns_108 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 108 4 = 13153889128 :=
  contactColumnsWindow_fast contact30 108 4 13153889128 (by decide +kernel)
private theorem arithBundle15_columns_112 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 112 4 = 6943589927 :=
  contactColumnsWindow_fast contact30 112 4 6943589927 (by decide +kernel)
private theorem arithBundle15_columns_116 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 116 3 = 2673063666 :=
  contactColumnsWindow_fast contact30 116 3 2673063666 (by decide +kernel)
private theorem arithBundle15_prefix_columns_00 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 8 = 3739114977810 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 4 4 1936742548952 1802372428858 arithBundle15_columns_000 arithBundle15_columns_004
private theorem arithBundle15_prefix_columns_01 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 12 = 5411972205732 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 8 4 3739114977810 1672857227922 arithBundle15_prefix_columns_00 arithBundle15_columns_008
private theorem arithBundle15_prefix_columns_02 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 16 = 6960169024598 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 12 4 5411972205732 1548196818866 arithBundle15_prefix_columns_01 arithBundle15_columns_012
private theorem arithBundle15_prefix_columns_03 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 20 = 8388560432996 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 16 4 6960169024598 1428391408398 arithBundle15_prefix_columns_02 arithBundle15_columns_016
private theorem arithBundle15_prefix_columns_04 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 24 = 9702016238263 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 20 4 8388560432996 1313455805267 arithBundle15_prefix_columns_03 arithBundle15_columns_020
private theorem arithBundle15_prefix_columns_05 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 28 = 10905414721133 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 24 4 9702016238263 1203398482870 arithBundle15_prefix_columns_04 arithBundle15_columns_024
private theorem arithBundle15_prefix_columns_06 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 32 = 12003612282971 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 28 4 10905414721133 1098197561838 arithBundle15_prefix_columns_05 arithBundle15_columns_028
private theorem arithBundle15_prefix_columns_07 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 36 = 13001466899444 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 32 4 12003612282971 997854616473 arithBundle15_prefix_columns_06 arithBundle15_columns_032
private theorem arithBundle15_prefix_columns_08 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 40 = 13903834909394 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 36 4 13001466899444 902368009950 arithBundle15_prefix_columns_07 arithBundle15_columns_036
private theorem arithBundle15_prefix_columns_09 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 44 = 14715589313452 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 40 4 13903834909394 811754404058 arithBundle15_prefix_columns_08 arithBundle15_columns_040
private theorem arithBundle15_prefix_columns_10 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 48 = 15441605159645 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 44 4 14715589313452 726015846193 arithBundle15_prefix_columns_09 arithBundle15_columns_044
private theorem arithBundle15_prefix_columns_11 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 52 = 16086739086299 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 48 4 15441605159645 645133926654 arithBundle15_prefix_columns_10 arithBundle15_columns_048
private theorem arithBundle15_prefix_columns_12 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 56 = 16655848881317 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 52 4 16086739086299 569109795018 arithBundle15_prefix_columns_11 arithBundle15_columns_052
private theorem arithBundle15_prefix_columns_13 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 60 = 17153790819719 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 56 4 16655848881317 497941938402 arithBundle15_prefix_columns_12 arithBundle15_columns_056
private theorem arithBundle15_prefix_columns_14 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 64 = 17585441163529 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 60 4 17153790819719 431650343810 arithBundle15_prefix_columns_13 arithBundle15_columns_060
private theorem arithBundle15_prefix_columns_15 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 68 = 17955671793515 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 64 4 17585441163529 370230629986 arithBundle15_prefix_columns_14 arithBundle15_columns_064
private theorem arithBundle15_prefix_columns_16 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 72 = 18269339456435 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 68 4 17955671793515 313667662920 arithBundle15_prefix_columns_15 arithBundle15_columns_068
private theorem arithBundle15_prefix_columns_17 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 76 = 18531301756898 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 72 4 18269339456435 261962300463 arithBundle15_prefix_columns_16 arithBundle15_columns_072
private theorem arithBundle15_prefix_columns_18 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 80 = 18746415418424 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 76 4 18531301756898 215113661526 arithBundle15_prefix_columns_17 arithBundle15_columns_076
private theorem arithBundle15_prefix_columns_19 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 84 = 18919559118412 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 80 4 18746415418424 173143699988 arithBundle15_prefix_columns_18 arithBundle15_columns_080
private theorem arithBundle15_prefix_columns_20 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 88 = 19055601859301 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 84 4 18919559118412 136042740889 arithBundle15_prefix_columns_19 arithBundle15_columns_084
private theorem arithBundle15_prefix_columns_21 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 92 = 19159400585387 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 88 4 19055601859301 103798726086 arithBundle15_prefix_columns_20 arithBundle15_columns_088
private theorem arithBundle15_prefix_columns_22 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 96 = 19235812746014 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 92 4 19159400585387 76412160627 arithBundle15_prefix_columns_21 arithBundle15_columns_092
private theorem arithBundle15_prefix_columns_23 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 100 = 19289680168961 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 96 4 19235812746014 53867422947 arithBundle15_prefix_columns_22 arithBundle15_columns_096
private theorem arithBundle15_prefix_columns_24 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 104 = 19325734139930 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 100 4 19289680168961 36053970969 arithBundle15_prefix_columns_23 arithBundle15_columns_100
private theorem arithBundle15_prefix_columns_25 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 108 = 19348378984179 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 104 4 19325734139930 22644844249 arithBundle15_prefix_columns_24 arithBundle15_columns_104
private theorem arithBundle15_prefix_columns_26 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 112 = 19361532873307 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 108 4 19348378984179 13153889128 arithBundle15_prefix_columns_25 arithBundle15_columns_108
private theorem arithBundle15_prefix_columns_27 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 116 = 19368476463234 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 112 4 19361532873307 6943589927 arithBundle15_prefix_columns_26 arithBundle15_columns_112
private theorem arithBundle15_prefix_columns_28 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact30) 0 119 = 19371149526900 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact30) 0 116 3 19368476463234 2673063666 arithBundle15_prefix_columns_27 arithBundle15_columns_116

private theorem arithBundle15_ordinary_ranks : ordinaryRankBound contact30 = 1986914496 := by decide +kernel
private theorem arithBundle15_ranks_000 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 4 = 7275714 :=
  contactRankWindow_of_rec contact30 0 4 7275714 (by decide +kernel)
private theorem arithBundle15_ranks_004 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 4 4 = 6620514 :=
  contactRankWindow_of_rec contact30 4 4 6620514 (by decide +kernel)
private theorem arithBundle15_ranks_008 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 8 4 = 5998914 :=
  contactRankWindow_of_rec contact30 8 4 5998914 (by decide +kernel)
private theorem arithBundle15_ranks_012 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 12 4 = 5410914 :=
  contactRankWindow_of_rec contact30 12 4 5410914 (by decide +kernel)
private theorem arithBundle15_ranks_016 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 16 4 = 4856514 :=
  contactRankWindow_of_rec contact30 16 4 4856514 (by decide +kernel)
private theorem arithBundle15_ranks_020 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 20 4 = 4335714 :=
  contactRankWindow_of_rec contact30 20 4 4335714 (by decide +kernel)
private theorem arithBundle15_ranks_024 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 24 4 = 3848514 :=
  contactRankWindow_of_rec contact30 24 4 3848514 (by decide +kernel)
private theorem arithBundle15_ranks_028 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 28 4 = 3394914 :=
  contactRankWindow_of_rec contact30 28 4 3394914 (by decide +kernel)
private theorem arithBundle15_ranks_032 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 32 4 = 2974914 :=
  contactRankWindow_of_rec contact30 32 4 2974914 (by decide +kernel)
private theorem arithBundle15_ranks_036 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 36 4 = 2588366 :=
  contactRankWindow_of_rec contact30 36 4 2588366 (by decide +kernel)
private theorem arithBundle15_ranks_040 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 40 4 = 2234500 :=
  contactRankWindow_of_rec contact30 40 4 2234500 (by decide +kernel)
private theorem arithBundle15_ranks_044 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 44 4 = 1912341 :=
  contactRankWindow_of_rec contact30 44 4 1912341 (by decide +kernel)
private theorem arithBundle15_ranks_048 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 48 4 = 1620629 :=
  contactRankWindow_of_rec contact30 48 4 1620629 (by decide +kernel)
private theorem arithBundle15_ranks_052 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 52 4 = 1358008 :=
  contactRankWindow_of_rec contact30 52 4 1358008 (by decide +kernel)
private theorem arithBundle15_ranks_056 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 56 4 = 1123285 :=
  contactRankWindow_of_rec contact30 56 4 1123285 (by decide +kernel)
private theorem arithBundle15_ranks_060 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 60 4 = 915049 :=
  contactRankWindow_of_rec contact30 60 4 915049 (by decide +kernel)
private theorem arithBundle15_ranks_064 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 64 4 = 731948 :=
  contactRankWindow_of_rec contact30 64 4 731948 (by decide +kernel)
private theorem arithBundle15_ranks_068 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 68 4 = 572885 :=
  contactRankWindow_of_rec contact30 68 4 572885 (by decide +kernel)
private theorem arithBundle15_ranks_072 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 72 4 = 436349 :=
  contactRankWindow_of_rec contact30 72 4 436349 (by decide +kernel)
private theorem arithBundle15_ranks_076 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 76 4 = 320992 :=
  contactRankWindow_of_rec contact30 76 4 320992 (by decide +kernel)
private theorem arithBundle15_ranks_080 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 80 4 = 225813 :=
  contactRankWindow_of_rec contact30 80 4 225813 (by decide +kernel)
private theorem arithBundle15_ranks_084 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 84 4 = 149201 :=
  contactRankWindow_of_rec contact30 84 4 149201 (by decide +kernel)
private theorem arithBundle15_ranks_088 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 88 4 = 89812 :=
  contactRankWindow_of_rec contact30 88 4 89812 (by decide +kernel)
private theorem arithBundle15_ranks_092 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 92 4 = 46741 :=
  contactRankWindow_of_rec contact30 92 4 46741 (by decide +kernel)
private theorem arithBundle15_ranks_096 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 96 4 = 18279 :=
  contactRankWindow_of_rec contact30 96 4 18279 (by decide +kernel)
private theorem arithBundle15_ranks_100 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 100 4 = 3167 :=
  contactRankWindow_of_rec contact30 100 4 3167 (by decide +kernel)
private theorem arithBundle15_ranks_104 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 104 15 = 0 :=
  contactRankWindow_of_rec contact30 104 15 0 (by decide +kernel)
private theorem arithBundle15_prefix_ranks_00 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 8 = 13896228 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 4 4 7275714 6620514 arithBundle15_ranks_000 arithBundle15_ranks_004
private theorem arithBundle15_prefix_ranks_01 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 12 = 19895142 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 8 4 13896228 5998914 arithBundle15_prefix_ranks_00 arithBundle15_ranks_008
private theorem arithBundle15_prefix_ranks_02 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 16 = 25306056 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 12 4 19895142 5410914 arithBundle15_prefix_ranks_01 arithBundle15_ranks_012
private theorem arithBundle15_prefix_ranks_03 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 20 = 30162570 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 16 4 25306056 4856514 arithBundle15_prefix_ranks_02 arithBundle15_ranks_016
private theorem arithBundle15_prefix_ranks_04 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 24 = 34498284 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 20 4 30162570 4335714 arithBundle15_prefix_ranks_03 arithBundle15_ranks_020
private theorem arithBundle15_prefix_ranks_05 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 28 = 38346798 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 24 4 34498284 3848514 arithBundle15_prefix_ranks_04 arithBundle15_ranks_024
private theorem arithBundle15_prefix_ranks_06 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 32 = 41741712 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 28 4 38346798 3394914 arithBundle15_prefix_ranks_05 arithBundle15_ranks_028
private theorem arithBundle15_prefix_ranks_07 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 36 = 44716626 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 32 4 41741712 2974914 arithBundle15_prefix_ranks_06 arithBundle15_ranks_032
private theorem arithBundle15_prefix_ranks_08 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 40 = 47304992 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 36 4 44716626 2588366 arithBundle15_prefix_ranks_07 arithBundle15_ranks_036
private theorem arithBundle15_prefix_ranks_09 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 44 = 49539492 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 40 4 47304992 2234500 arithBundle15_prefix_ranks_08 arithBundle15_ranks_040
private theorem arithBundle15_prefix_ranks_10 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 48 = 51451833 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 44 4 49539492 1912341 arithBundle15_prefix_ranks_09 arithBundle15_ranks_044
private theorem arithBundle15_prefix_ranks_11 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 52 = 53072462 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 48 4 51451833 1620629 arithBundle15_prefix_ranks_10 arithBundle15_ranks_048
private theorem arithBundle15_prefix_ranks_12 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 56 = 54430470 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 52 4 53072462 1358008 arithBundle15_prefix_ranks_11 arithBundle15_ranks_052
private theorem arithBundle15_prefix_ranks_13 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 60 = 55553755 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 56 4 54430470 1123285 arithBundle15_prefix_ranks_12 arithBundle15_ranks_056
private theorem arithBundle15_prefix_ranks_14 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 64 = 56468804 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 60 4 55553755 915049 arithBundle15_prefix_ranks_13 arithBundle15_ranks_060
private theorem arithBundle15_prefix_ranks_15 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 68 = 57200752 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 64 4 56468804 731948 arithBundle15_prefix_ranks_14 arithBundle15_ranks_064
private theorem arithBundle15_prefix_ranks_16 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 72 = 57773637 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 68 4 57200752 572885 arithBundle15_prefix_ranks_15 arithBundle15_ranks_068
private theorem arithBundle15_prefix_ranks_17 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 76 = 58209986 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 72 4 57773637 436349 arithBundle15_prefix_ranks_16 arithBundle15_ranks_072
private theorem arithBundle15_prefix_ranks_18 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 80 = 58530978 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 76 4 58209986 320992 arithBundle15_prefix_ranks_17 arithBundle15_ranks_076
private theorem arithBundle15_prefix_ranks_19 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 84 = 58756791 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 80 4 58530978 225813 arithBundle15_prefix_ranks_18 arithBundle15_ranks_080
private theorem arithBundle15_prefix_ranks_20 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 88 = 58905992 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 84 4 58756791 149201 arithBundle15_prefix_ranks_19 arithBundle15_ranks_084
private theorem arithBundle15_prefix_ranks_21 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 92 = 58995804 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 88 4 58905992 89812 arithBundle15_prefix_ranks_20 arithBundle15_ranks_088
private theorem arithBundle15_prefix_ranks_22 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 96 = 59042545 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 92 4 58995804 46741 arithBundle15_prefix_ranks_21 arithBundle15_ranks_092
private theorem arithBundle15_prefix_ranks_23 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 100 = 59060824 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 96 4 59042545 18279 arithBundle15_prefix_ranks_22 arithBundle15_ranks_096
private theorem arithBundle15_prefix_ranks_24 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 104 = 59063991 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 100 4 59060824 3167 arithBundle15_prefix_ranks_23 arithBundle15_ranks_100
private theorem arithBundle15_prefix_ranks_25 : arithBundle15_sliceWindow (auxiliaryRankSlice contact30) 0 119 = 59063991 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact30) 0 104 15 59063991 0 arithBundle15_prefix_ranks_24 arithBundle15_ranks_104

theorem contact30_margin : sourceMargin contact30 :=
  arithBundle15_margin_of_checked_counts contact30 119 516970197448924 19371149526900 1986914496 59063991
    rfl arithBundle15_ordinary_columns arithBundle15_prefix_columns_28 arithBundle15_ordinary_ranks arithBundle15_prefix_ranks_25 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle16_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle16_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle16_sliceWindow f a b = x) (hy : arithBundle16_sliceWindow f (a+b) c = y) :
    arithBundle16_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle16_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle16_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle16_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle16_sliceWindow,Nat.zero_add]

private theorem arithBundle16_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle16_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle16_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle16_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle16_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle16_ordinary_columns : ordinaryColumnCount contact31 = 53972633606880 := by decide +kernel
private theorem arithBundle16_columns_000 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 4 = 469416769272 :=
  contactColumnsWindow_fast contact31 0 4 469416769272 (by decide +kernel)
private theorem arithBundle16_columns_004 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 4 4 = 422380061784 :=
  contactColumnsWindow_fast contact31 4 4 422380061784 (by decide +kernel)
private theorem arithBundle16_columns_008 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 8 4 = 377838914616 :=
  contactColumnsWindow_fast contact31 8 4 377838914616 (by decide +kernel)
private theorem arithBundle16_columns_012 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 12 4 = 335803562408 :=
  contactColumnsWindow_fast contact31 12 4 335803562408 (by decide +kernel)
private theorem arithBundle16_columns_016 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 16 4 = 296275746952 :=
  contactColumnsWindow_fast contact31 16 4 296275746952 (by decide +kernel)
private theorem arithBundle16_columns_020 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 20 4 = 259245388596 :=
  contactColumnsWindow_fast contact31 20 4 259245388596 (by decide +kernel)
private theorem arithBundle16_columns_024 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 24 4 = 224711981220 :=
  contactColumnsWindow_fast contact31 24 4 224711981220 (by decide +kernel)
private theorem arithBundle16_columns_028 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 28 4 = 192676437684 :=
  contactColumnsWindow_fast contact31 28 4 192676437684 (by decide +kernel)
private theorem arithBundle16_columns_032 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 32 4 = 163149723044 :=
  contactColumnsWindow_fast contact31 32 4 163149723044 (by decide +kernel)
private theorem arithBundle16_columns_036 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 36 4 = 136128586783 :=
  contactColumnsWindow_fast contact31 36 4 136128586783 (by decide +kernel)
private theorem arithBundle16_columns_040 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 40 4 = 111605104872 :=
  contactColumnsWindow_fast contact31 40 4 111605104872 (by decide +kernel)
private theorem arithBundle16_columns_044 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 44 4 = 89578407864 :=
  contactColumnsWindow_fast contact31 44 4 89578407864 (by decide +kernel)
private theorem arithBundle16_columns_048 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 48 4 = 70049819196 :=
  contactColumnsWindow_fast contact31 48 4 70049819196 (by decide +kernel)
private theorem arithBundle16_columns_052 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 52 4 = 53031651800 :=
  contactColumnsWindow_fast contact31 52 4 53031651800 (by decide +kernel)
private theorem arithBundle16_columns_056 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 56 4 = 38517221089 :=
  contactColumnsWindow_fast contact31 56 4 38517221089 (by decide +kernel)
private theorem arithBundle16_columns_060 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 60 4 = 26500589268 :=
  contactColumnsWindow_fast contact31 60 4 26500589268 (by decide +kernel)
private theorem arithBundle16_columns_064 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 64 4 = 16979464118 :=
  contactColumnsWindow_fast contact31 64 4 16979464118 (by decide +kernel)
private theorem arithBundle16_columns_068 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 68 4 = 9912184604 :=
  contactColumnsWindow_fast contact31 68 4 9912184604 (by decide +kernel)
private theorem arithBundle16_columns_072 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 72 4 = 5123847410 :=
  contactColumnsWindow_fast contact31 72 4 5123847410 (by decide +kernel)
private theorem arithBundle16_columns_076 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 76 4 = 2252550080 :=
  contactColumnsWindow_fast contact31 76 4 2252550080 (by decide +kernel)
private theorem arithBundle16_prefix_columns_00 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 8 = 891796831056 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 4 4 469416769272 422380061784 arithBundle16_columns_000 arithBundle16_columns_004
private theorem arithBundle16_prefix_columns_01 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 12 = 1269635745672 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 8 4 891796831056 377838914616 arithBundle16_prefix_columns_00 arithBundle16_columns_008
private theorem arithBundle16_prefix_columns_02 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 16 = 1605439308080 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 12 4 1269635745672 335803562408 arithBundle16_prefix_columns_01 arithBundle16_columns_012
private theorem arithBundle16_prefix_columns_03 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 20 = 1901715055032 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 16 4 1605439308080 296275746952 arithBundle16_prefix_columns_02 arithBundle16_columns_016
private theorem arithBundle16_prefix_columns_04 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 24 = 2160960443628 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 20 4 1901715055032 259245388596 arithBundle16_prefix_columns_03 arithBundle16_columns_020
private theorem arithBundle16_prefix_columns_05 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 28 = 2385672424848 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 24 4 2160960443628 224711981220 arithBundle16_prefix_columns_04 arithBundle16_columns_024
private theorem arithBundle16_prefix_columns_06 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 32 = 2578348862532 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 28 4 2385672424848 192676437684 arithBundle16_prefix_columns_05 arithBundle16_columns_028
private theorem arithBundle16_prefix_columns_07 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 36 = 2741498585576 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 32 4 2578348862532 163149723044 arithBundle16_prefix_columns_06 arithBundle16_columns_032
private theorem arithBundle16_prefix_columns_08 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 40 = 2877627172359 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 36 4 2741498585576 136128586783 arithBundle16_prefix_columns_07 arithBundle16_columns_036
private theorem arithBundle16_prefix_columns_09 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 44 = 2989232277231 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 40 4 2877627172359 111605104872 arithBundle16_prefix_columns_08 arithBundle16_columns_040
private theorem arithBundle16_prefix_columns_10 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 48 = 3078810685095 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 44 4 2989232277231 89578407864 arithBundle16_prefix_columns_09 arithBundle16_columns_044
private theorem arithBundle16_prefix_columns_11 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 52 = 3148860504291 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 48 4 3078810685095 70049819196 arithBundle16_prefix_columns_10 arithBundle16_columns_048
private theorem arithBundle16_prefix_columns_12 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 56 = 3201892156091 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 52 4 3148860504291 53031651800 arithBundle16_prefix_columns_11 arithBundle16_columns_052
private theorem arithBundle16_prefix_columns_13 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 60 = 3240409377180 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 56 4 3201892156091 38517221089 arithBundle16_prefix_columns_12 arithBundle16_columns_056
private theorem arithBundle16_prefix_columns_14 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 64 = 3266909966448 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 60 4 3240409377180 26500589268 arithBundle16_prefix_columns_13 arithBundle16_columns_060
private theorem arithBundle16_prefix_columns_15 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 68 = 3283889430566 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 64 4 3266909966448 16979464118 arithBundle16_prefix_columns_14 arithBundle16_columns_064
private theorem arithBundle16_prefix_columns_16 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 72 = 3293801615170 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 68 4 3283889430566 9912184604 arithBundle16_prefix_columns_15 arithBundle16_columns_068
private theorem arithBundle16_prefix_columns_17 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 76 = 3298925462580 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 72 4 3293801615170 5123847410 arithBundle16_prefix_columns_16 arithBundle16_columns_072
private theorem arithBundle16_prefix_columns_18 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact31) 0 80 = 3301178012660 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact31) 0 76 4 3298925462580 2252550080 arithBundle16_prefix_columns_17 arithBundle16_columns_076

private theorem arithBundle16_ordinary_ranks : ordinaryRankBound contact31 = 208402215 := by decide +kernel
private theorem arithBundle16_ranks_000 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 4 = 1750986 :=
  contactRankWindow_of_rec contact31 0 4 1750986 (by decide +kernel)
private theorem arithBundle16_ranks_004 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 4 4 = 1524186 :=
  contactRankWindow_of_rec contact31 4 4 1524186 (by decide +kernel)
private theorem arithBundle16_ranks_008 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 8 4 = 1314666 :=
  contactRankWindow_of_rec contact31 8 4 1314666 (by decide +kernel)
private theorem arithBundle16_ranks_012 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 12 4 = 1122426 :=
  contactRankWindow_of_rec contact31 12 4 1122426 (by decide +kernel)
private theorem arithBundle16_ranks_016 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 16 4 = 947466 :=
  contactRankWindow_of_rec contact31 16 4 947466 (by decide +kernel)
private theorem arithBundle16_ranks_020 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 20 4 = 789786 :=
  contactRankWindow_of_rec contact31 20 4 789786 (by decide +kernel)
private theorem arithBundle16_ranks_024 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 24 4 = 649280 :=
  contactRankWindow_of_rec contact31 24 4 649280 (by decide +kernel)
private theorem arithBundle16_ranks_028 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 28 4 = 525394 :=
  contactRankWindow_of_rec contact31 28 4 525394 (by decide +kernel)
private theorem arithBundle16_ranks_032 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 32 4 = 417315 :=
  contactRankWindow_of_rec contact31 32 4 417315 (by decide +kernel)
private theorem arithBundle16_ranks_036 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 36 4 = 324140 :=
  contactRankWindow_of_rec contact31 36 4 324140 (by decide +kernel)
private theorem arithBundle16_ranks_040 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 40 4 = 244894 :=
  contactRankWindow_of_rec contact31 40 4 244894 (by decide +kernel)
private theorem arithBundle16_ranks_044 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 44 4 = 178615 :=
  contactRankWindow_of_rec contact31 44 4 178615 (by decide +kernel)
private theorem arithBundle16_ranks_048 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 48 4 = 124472 :=
  contactRankWindow_of_rec contact31 48 4 124472 (by decide +kernel)
private theorem arithBundle16_ranks_052 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 52 4 = 81418 :=
  contactRankWindow_of_rec contact31 52 4 81418 (by decide +kernel)
private theorem arithBundle16_ranks_056 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 56 4 = 48491 :=
  contactRankWindow_of_rec contact31 56 4 48491 (by decide +kernel)
private theorem arithBundle16_ranks_060 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 60 4 = 24932 :=
  contactRankWindow_of_rec contact31 60 4 24932 (by decide +kernel)
private theorem arithBundle16_ranks_064 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 64 4 = 9622 :=
  contactRankWindow_of_rec contact31 64 4 9622 (by decide +kernel)
private theorem arithBundle16_ranks_068 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 68 4 = 1638 :=
  contactRankWindow_of_rec contact31 68 4 1638 (by decide +kernel)
private theorem arithBundle16_ranks_072 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 72 8 = 0 :=
  contactRankWindow_of_rec contact31 72 8 0 (by decide +kernel)
private theorem arithBundle16_prefix_ranks_00 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 8 = 3275172 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 4 4 1750986 1524186 arithBundle16_ranks_000 arithBundle16_ranks_004
private theorem arithBundle16_prefix_ranks_01 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 12 = 4589838 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 8 4 3275172 1314666 arithBundle16_prefix_ranks_00 arithBundle16_ranks_008
private theorem arithBundle16_prefix_ranks_02 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 16 = 5712264 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 12 4 4589838 1122426 arithBundle16_prefix_ranks_01 arithBundle16_ranks_012
private theorem arithBundle16_prefix_ranks_03 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 20 = 6659730 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 16 4 5712264 947466 arithBundle16_prefix_ranks_02 arithBundle16_ranks_016
private theorem arithBundle16_prefix_ranks_04 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 24 = 7449516 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 20 4 6659730 789786 arithBundle16_prefix_ranks_03 arithBundle16_ranks_020
private theorem arithBundle16_prefix_ranks_05 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 28 = 8098796 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 24 4 7449516 649280 arithBundle16_prefix_ranks_04 arithBundle16_ranks_024
private theorem arithBundle16_prefix_ranks_06 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 32 = 8624190 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 28 4 8098796 525394 arithBundle16_prefix_ranks_05 arithBundle16_ranks_028
private theorem arithBundle16_prefix_ranks_07 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 36 = 9041505 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 32 4 8624190 417315 arithBundle16_prefix_ranks_06 arithBundle16_ranks_032
private theorem arithBundle16_prefix_ranks_08 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 40 = 9365645 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 36 4 9041505 324140 arithBundle16_prefix_ranks_07 arithBundle16_ranks_036
private theorem arithBundle16_prefix_ranks_09 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 44 = 9610539 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 40 4 9365645 244894 arithBundle16_prefix_ranks_08 arithBundle16_ranks_040
private theorem arithBundle16_prefix_ranks_10 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 48 = 9789154 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 44 4 9610539 178615 arithBundle16_prefix_ranks_09 arithBundle16_ranks_044
private theorem arithBundle16_prefix_ranks_11 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 52 = 9913626 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 48 4 9789154 124472 arithBundle16_prefix_ranks_10 arithBundle16_ranks_048
private theorem arithBundle16_prefix_ranks_12 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 56 = 9995044 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 52 4 9913626 81418 arithBundle16_prefix_ranks_11 arithBundle16_ranks_052
private theorem arithBundle16_prefix_ranks_13 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 60 = 10043535 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 56 4 9995044 48491 arithBundle16_prefix_ranks_12 arithBundle16_ranks_056
private theorem arithBundle16_prefix_ranks_14 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 64 = 10068467 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 60 4 10043535 24932 arithBundle16_prefix_ranks_13 arithBundle16_ranks_060
private theorem arithBundle16_prefix_ranks_15 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 68 = 10078089 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 64 4 10068467 9622 arithBundle16_prefix_ranks_14 arithBundle16_ranks_064
private theorem arithBundle16_prefix_ranks_16 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 72 = 10079727 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 68 4 10078089 1638 arithBundle16_prefix_ranks_15 arithBundle16_ranks_068
private theorem arithBundle16_prefix_ranks_17 : arithBundle16_sliceWindow (auxiliaryRankSlice contact31) 0 80 = 10079727 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact31) 0 72 8 10079727 0 arithBundle16_prefix_ranks_16 arithBundle16_ranks_072

theorem contact31_margin : sourceMargin contact31 :=
  arithBundle16_margin_of_checked_counts contact31 80 53972633606880 3301178012660 208402215 10079727
    rfl arithBundle16_ordinary_columns arithBundle16_prefix_columns_18 arithBundle16_ordinary_ranks arithBundle16_prefix_ranks_17 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle17_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle17_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle17_sliceWindow f a b = x) (hy : arithBundle17_sliceWindow f (a+b) c = y) :
    arithBundle17_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle17_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle17_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle17_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle17_sliceWindow,Nat.zero_add]

private theorem arithBundle17_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle17_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle17_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle17_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle17_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle17_ordinary_columns : ordinaryColumnCount contact33 = 217720843337430 := by decide +kernel
private theorem arithBundle17_columns_000 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 4 = 942365537096 :=
  contactColumnsWindow_fast contact33 0 4 942365537096 (by decide +kernel)
private theorem arithBundle17_columns_004 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 4 4 = 863155294728 :=
  contactColumnsWindow_fast contact33 4 4 863155294728 (by decide +kernel)
private theorem arithBundle17_columns_008 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 8 4 = 787439484423 :=
  contactColumnsWindow_fast contact33 8 4 787439484423 (by decide +kernel)
private theorem arithBundle17_columns_012 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 12 4 = 715236773596 :=
  contactColumnsWindow_fast contact33 12 4 715236773596 (by decide +kernel)
private theorem arithBundle17_columns_016 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 16 4 = 646536917005 :=
  contactColumnsWindow_fast contact33 16 4 646536917005 (by decide +kernel)
private theorem arithBundle17_columns_020 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 20 4 = 581333515528 :=
  contactColumnsWindow_fast contact33 20 4 581333515528 (by decide +kernel)
private theorem arithBundle17_columns_024 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 24 4 = 519625094668 :=
  contactColumnsWindow_fast contact33 24 4 519625094668 (by decide +kernel)
private theorem arithBundle17_columns_028 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 28 4 = 461414639469 :=
  contactColumnsWindow_fast contact33 28 4 461414639469 (by decide +kernel)
private theorem arithBundle17_columns_032 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 32 4 = 406719836014 :=
  contactColumnsWindow_fast contact33 32 4 406719836014 (by decide +kernel)
private theorem arithBundle17_columns_036 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 36 4 = 355529116498 :=
  contactColumnsWindow_fast contact33 36 4 355529116498 (by decide +kernel)
private theorem arithBundle17_columns_040 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 40 4 = 307835191588 :=
  contactColumnsWindow_fast contact33 40 4 307835191588 (by decide +kernel)
private theorem arithBundle17_columns_044 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 44 4 = 263636230768 :=
  contactColumnsWindow_fast contact33 44 4 263636230768 (by decide +kernel)
private theorem arithBundle17_columns_048 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 48 4 = 222936032534 :=
  contactColumnsWindow_fast contact33 48 4 222936032534 (by decide +kernel)
private theorem arithBundle17_columns_052 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 52 4 = 185752578315 :=
  contactColumnsWindow_fast contact33 52 4 185752578315 (by decide +kernel)
private theorem arithBundle17_columns_056 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 56 4 = 152071417522 :=
  contactColumnsWindow_fast contact33 56 4 152071417522 (by decide +kernel)
private theorem arithBundle17_columns_060 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 60 4 = 121886943016 :=
  contactColumnsWindow_fast contact33 60 4 121886943016 (by decide +kernel)
private theorem arithBundle17_columns_064 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 64 4 = 95197473754 :=
  contactColumnsWindow_fast contact33 64 4 95197473754 (by decide +kernel)
private theorem arithBundle17_columns_068 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 68 4 = 72008004902 :=
  contactColumnsWindow_fast contact33 68 4 72008004902 (by decide +kernel)
private theorem arithBundle17_columns_072 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 72 4 = 52335412761 :=
  contactColumnsWindow_fast contact33 72 4 52335412761 (by decide +kernel)
private theorem arithBundle17_columns_076 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 76 4 = 36163384499 :=
  contactColumnsWindow_fast contact33 76 4 36163384499 (by decide +kernel)
private theorem arithBundle17_columns_080 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 80 4 = 23456402021 :=
  contactColumnsWindow_fast contact33 80 4 23456402021 (by decide +kernel)
private theorem arithBundle17_columns_084 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 84 4 = 14044922895 :=
  contactColumnsWindow_fast contact33 84 4 14044922895 (by decide +kernel)
private theorem arithBundle17_columns_088 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 88 4 = 7596893261 :=
  contactColumnsWindow_fast contact33 88 4 7596893261 (by decide +kernel)
private theorem arithBundle17_columns_092 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 92 4 = 3619955228 :=
  contactColumnsWindow_fast contact33 92 4 3619955228 (by decide +kernel)
private theorem arithBundle17_columns_096 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 96 3 = 1221818574 :=
  contactColumnsWindow_fast contact33 96 3 1221818574 (by decide +kernel)
private theorem arithBundle17_prefix_columns_00 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 8 = 1805520831824 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 4 4 942365537096 863155294728 arithBundle17_columns_000 arithBundle17_columns_004
private theorem arithBundle17_prefix_columns_01 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 12 = 2592960316247 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 8 4 1805520831824 787439484423 arithBundle17_prefix_columns_00 arithBundle17_columns_008
private theorem arithBundle17_prefix_columns_02 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 16 = 3308197089843 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 12 4 2592960316247 715236773596 arithBundle17_prefix_columns_01 arithBundle17_columns_012
private theorem arithBundle17_prefix_columns_03 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 20 = 3954734006848 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 16 4 3308197089843 646536917005 arithBundle17_prefix_columns_02 arithBundle17_columns_016
private theorem arithBundle17_prefix_columns_04 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 24 = 4536067522376 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 20 4 3954734006848 581333515528 arithBundle17_prefix_columns_03 arithBundle17_columns_020
private theorem arithBundle17_prefix_columns_05 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 28 = 5055692617044 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 24 4 4536067522376 519625094668 arithBundle17_prefix_columns_04 arithBundle17_columns_024
private theorem arithBundle17_prefix_columns_06 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 32 = 5517107256513 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 28 4 5055692617044 461414639469 arithBundle17_prefix_columns_05 arithBundle17_columns_028
private theorem arithBundle17_prefix_columns_07 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 36 = 5923827092527 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 32 4 5517107256513 406719836014 arithBundle17_prefix_columns_06 arithBundle17_columns_032
private theorem arithBundle17_prefix_columns_08 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 40 = 6279356209025 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 36 4 5923827092527 355529116498 arithBundle17_prefix_columns_07 arithBundle17_columns_036
private theorem arithBundle17_prefix_columns_09 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 44 = 6587191400613 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 40 4 6279356209025 307835191588 arithBundle17_prefix_columns_08 arithBundle17_columns_040
private theorem arithBundle17_prefix_columns_10 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 48 = 6850827631381 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 44 4 6587191400613 263636230768 arithBundle17_prefix_columns_09 arithBundle17_columns_044
private theorem arithBundle17_prefix_columns_11 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 52 = 7073763663915 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 48 4 6850827631381 222936032534 arithBundle17_prefix_columns_10 arithBundle17_columns_048
private theorem arithBundle17_prefix_columns_12 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 56 = 7259516242230 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 52 4 7073763663915 185752578315 arithBundle17_prefix_columns_11 arithBundle17_columns_052
private theorem arithBundle17_prefix_columns_13 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 60 = 7411587659752 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 56 4 7259516242230 152071417522 arithBundle17_prefix_columns_12 arithBundle17_columns_056
private theorem arithBundle17_prefix_columns_14 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 64 = 7533474602768 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 60 4 7411587659752 121886943016 arithBundle17_prefix_columns_13 arithBundle17_columns_060
private theorem arithBundle17_prefix_columns_15 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 68 = 7628672076522 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 64 4 7533474602768 95197473754 arithBundle17_prefix_columns_14 arithBundle17_columns_064
private theorem arithBundle17_prefix_columns_16 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 72 = 7700680081424 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 68 4 7628672076522 72008004902 arithBundle17_prefix_columns_15 arithBundle17_columns_068
private theorem arithBundle17_prefix_columns_17 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 76 = 7753015494185 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 72 4 7700680081424 52335412761 arithBundle17_prefix_columns_16 arithBundle17_columns_072
private theorem arithBundle17_prefix_columns_18 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 80 = 7789178878684 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 76 4 7753015494185 36163384499 arithBundle17_prefix_columns_17 arithBundle17_columns_076
private theorem arithBundle17_prefix_columns_19 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 84 = 7812635280705 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 80 4 7789178878684 23456402021 arithBundle17_prefix_columns_18 arithBundle17_columns_080
private theorem arithBundle17_prefix_columns_20 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 88 = 7826680203600 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 84 4 7812635280705 14044922895 arithBundle17_prefix_columns_19 arithBundle17_columns_084
private theorem arithBundle17_prefix_columns_21 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 92 = 7834277096861 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 88 4 7826680203600 7596893261 arithBundle17_prefix_columns_20 arithBundle17_columns_088
private theorem arithBundle17_prefix_columns_22 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 96 = 7837897052089 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 92 4 7834277096861 3619955228 arithBundle17_prefix_columns_21 arithBundle17_columns_092
private theorem arithBundle17_prefix_columns_23 : arithBundle17_sliceWindow (auxiliaryColumnSlice contact33) 0 99 = 7839118870663 :=
  arithBundle17_combineSlices (auxiliaryColumnSlice contact33) 0 96 3 7837897052089 1221818574 arithBundle17_prefix_columns_22 arithBundle17_columns_096

private theorem arithBundle17_ordinary_ranks : ordinaryRankBound contact33 = 836471244 := by decide +kernel
private theorem arithBundle17_ranks_000 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 4 = 3530886 :=
  contactRankWindow_of_rec contact33 0 4 3530886 (by decide +kernel)
private theorem arithBundle17_ranks_004 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 4 4 = 3146838 :=
  contactRankWindow_of_rec contact33 4 4 3146838 (by decide +kernel)
private theorem arithBundle17_ranks_008 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 8 4 = 2786982 :=
  contactRankWindow_of_rec contact33 8 4 2786982 (by decide +kernel)
private theorem arithBundle17_ranks_012 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 12 4 = 2451318 :=
  contactRankWindow_of_rec contact33 12 4 2451318 (by decide +kernel)
private theorem arithBundle17_ranks_016 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 16 4 = 2139846 :=
  contactRankWindow_of_rec contact33 16 4 2139846 (by decide +kernel)
private theorem arithBundle17_ranks_020 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 20 4 = 1852566 :=
  contactRankWindow_of_rec contact33 20 4 1852566 (by decide +kernel)
private theorem arithBundle17_ranks_024 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 24 4 = 1589478 :=
  contactRankWindow_of_rec contact33 24 4 1589478 (by decide +kernel)
private theorem arithBundle17_ranks_028 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 28 4 = 1350528 :=
  contactRankWindow_of_rec contact33 28 4 1350528 (by decide +kernel)
private theorem arithBundle17_ranks_032 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 32 4 = 1135184 :=
  contactRankWindow_of_rec contact33 32 4 1135184 (by decide +kernel)
private theorem arithBundle17_ranks_036 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 36 4 = 942556 :=
  contactRankWindow_of_rec contact33 36 4 942556 (by decide +kernel)
private theorem arithBundle17_ranks_040 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 40 4 = 771529 :=
  contactRankWindow_of_rec contact33 40 4 771529 (by decide +kernel)
private theorem arithBundle17_ranks_044 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 44 4 = 621056 :=
  contactRankWindow_of_rec contact33 44 4 621056 (by decide +kernel)
private theorem arithBundle17_ranks_048 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 48 4 = 489964 :=
  contactRankWindow_of_rec contact33 48 4 489964 (by decide +kernel)
private theorem arithBundle17_ranks_052 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 52 4 = 377117 :=
  contactRankWindow_of_rec contact33 52 4 377117 (by decide +kernel)
private theorem arithBundle17_ranks_056 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 56 4 = 281552 :=
  contactRankWindow_of_rec contact33 56 4 281552 (by decide +kernel)
private theorem arithBundle17_ranks_060 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 60 4 = 202012 :=
  contactRankWindow_of_rec contact33 60 4 202012 (by decide +kernel)
private theorem arithBundle17_ranks_064 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 64 4 = 137361 :=
  contactRankWindow_of_rec contact33 64 4 137361 (by decide +kernel)
private theorem arithBundle17_ranks_068 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 68 4 = 86720 :=
  contactRankWindow_of_rec contact33 68 4 86720 (by decide +kernel)
private theorem arithBundle17_ranks_072 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 72 4 = 48748 :=
  contactRankWindow_of_rec contact33 72 4 48748 (by decide +kernel)
private theorem arithBundle17_ranks_076 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 76 4 = 22309 :=
  contactRankWindow_of_rec contact33 76 4 22309 (by decide +kernel)
private theorem arithBundle17_ranks_080 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 80 4 = 6632 :=
  contactRankWindow_of_rec contact33 80 4 6632 (by decide +kernel)
private theorem arithBundle17_ranks_084 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 84 4 = 363 :=
  contactRankWindow_of_rec contact33 84 4 363 (by decide +kernel)
private theorem arithBundle17_ranks_088 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 88 11 = 0 :=
  contactRankWindow_of_rec contact33 88 11 0 (by decide +kernel)
private theorem arithBundle17_prefix_ranks_00 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 8 = 6677724 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 4 4 3530886 3146838 arithBundle17_ranks_000 arithBundle17_ranks_004
private theorem arithBundle17_prefix_ranks_01 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 12 = 9464706 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 8 4 6677724 2786982 arithBundle17_prefix_ranks_00 arithBundle17_ranks_008
private theorem arithBundle17_prefix_ranks_02 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 16 = 11916024 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 12 4 9464706 2451318 arithBundle17_prefix_ranks_01 arithBundle17_ranks_012
private theorem arithBundle17_prefix_ranks_03 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 20 = 14055870 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 16 4 11916024 2139846 arithBundle17_prefix_ranks_02 arithBundle17_ranks_016
private theorem arithBundle17_prefix_ranks_04 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 24 = 15908436 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 20 4 14055870 1852566 arithBundle17_prefix_ranks_03 arithBundle17_ranks_020
private theorem arithBundle17_prefix_ranks_05 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 28 = 17497914 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 24 4 15908436 1589478 arithBundle17_prefix_ranks_04 arithBundle17_ranks_024
private theorem arithBundle17_prefix_ranks_06 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 32 = 18848442 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 28 4 17497914 1350528 arithBundle17_prefix_ranks_05 arithBundle17_ranks_028
private theorem arithBundle17_prefix_ranks_07 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 36 = 19983626 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 32 4 18848442 1135184 arithBundle17_prefix_ranks_06 arithBundle17_ranks_032
private theorem arithBundle17_prefix_ranks_08 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 40 = 20926182 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 36 4 19983626 942556 arithBundle17_prefix_ranks_07 arithBundle17_ranks_036
private theorem arithBundle17_prefix_ranks_09 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 44 = 21697711 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 40 4 20926182 771529 arithBundle17_prefix_ranks_08 arithBundle17_ranks_040
private theorem arithBundle17_prefix_ranks_10 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 48 = 22318767 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 44 4 21697711 621056 arithBundle17_prefix_ranks_09 arithBundle17_ranks_044
private theorem arithBundle17_prefix_ranks_11 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 52 = 22808731 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 48 4 22318767 489964 arithBundle17_prefix_ranks_10 arithBundle17_ranks_048
private theorem arithBundle17_prefix_ranks_12 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 56 = 23185848 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 52 4 22808731 377117 arithBundle17_prefix_ranks_11 arithBundle17_ranks_052
private theorem arithBundle17_prefix_ranks_13 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 60 = 23467400 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 56 4 23185848 281552 arithBundle17_prefix_ranks_12 arithBundle17_ranks_056
private theorem arithBundle17_prefix_ranks_14 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 64 = 23669412 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 60 4 23467400 202012 arithBundle17_prefix_ranks_13 arithBundle17_ranks_060
private theorem arithBundle17_prefix_ranks_15 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 68 = 23806773 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 64 4 23669412 137361 arithBundle17_prefix_ranks_14 arithBundle17_ranks_064
private theorem arithBundle17_prefix_ranks_16 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 72 = 23893493 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 68 4 23806773 86720 arithBundle17_prefix_ranks_15 arithBundle17_ranks_068
private theorem arithBundle17_prefix_ranks_17 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 76 = 23942241 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 72 4 23893493 48748 arithBundle17_prefix_ranks_16 arithBundle17_ranks_072
private theorem arithBundle17_prefix_ranks_18 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 80 = 23964550 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 76 4 23942241 22309 arithBundle17_prefix_ranks_17 arithBundle17_ranks_076
private theorem arithBundle17_prefix_ranks_19 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 84 = 23971182 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 80 4 23964550 6632 arithBundle17_prefix_ranks_18 arithBundle17_ranks_080
private theorem arithBundle17_prefix_ranks_20 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 88 = 23971545 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 84 4 23971182 363 arithBundle17_prefix_ranks_19 arithBundle17_ranks_084
private theorem arithBundle17_prefix_ranks_21 : arithBundle17_sliceWindow (auxiliaryRankSlice contact33) 0 99 = 23971545 :=
  arithBundle17_combineSlices (auxiliaryRankSlice contact33) 0 88 11 23971545 0 arithBundle17_prefix_ranks_20 arithBundle17_ranks_088

theorem contact33_margin : sourceMargin contact33 :=
  arithBundle17_margin_of_checked_counts contact33 99 217720843337430 7839118870663 836471244 23971545
    rfl arithBundle17_ordinary_columns arithBundle17_prefix_columns_23 arithBundle17_ordinary_ranks arithBundle17_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

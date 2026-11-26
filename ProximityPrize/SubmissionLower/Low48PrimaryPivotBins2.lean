import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup50
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1036
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part972
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part10

section Merged6967_Low48PrimaryPivotBins2
set_option Elab.async false

















set_option Elab.async false

-- merged module Low48PrimaryPivotBins2Part1612
section Merged_Low48PrimaryPivotBins2Part1612

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1612 : binChunk w2 1612 4 = 265657093856 := by decide +kernel
private theorem leaf1616 : binChunk w2 1616 4 = 266973447960 := by decide +kernel
private theorem leaf1620 : binChunk w2 1620 4 = 268293156998 := by decide +kernel
private theorem leaf1624 : binChunk w2 1624 4 = 269615915976 := by decide +kernel
private theorem leaf1628 : binChunk w2 1628 4 = 270942029888 := by decide +kernel
private theorem leaf1632 : binChunk w2 1632 4 = 272271498734 := by decide +kernel
private theorem leaf1636 : binChunk w2 1636 4 = 273604017520 := by decide +kernel
private theorem leaf1640 : binChunk w2 1640 4 = 274939891240 := by decide +kernel
private theorem leaf1644 : binChunk w2 1644 4 = 276279119894 := by decide +kernel
private theorem leaf1648 : binChunk w2 1648 3 = 208090086344 := by decide +kernel
private theorem batch2_1612_1620 : binChunk w2 1612 8 = 532630541816 :=
  binChunk_join (w := w2) (start := 1612) (left := 4) (right := 4) (x := 265657093856) (y := 266973447960) leaf1612 leaf1616
private theorem batch2_1624_1632 : binChunk w2 1624 8 = 540557945864 :=
  binChunk_join (w := w2) (start := 1624) (left := 4) (right := 4) (x := 269615915976) (y := 270942029888) leaf1624 leaf1628
private theorem batch2_1620_1632 : binChunk w2 1620 12 = 808851102862 :=
  binChunk_join (w := w2) (start := 1620) (left := 4) (right := 8) (x := 268293156998) (y := 540557945864) leaf1620 batch2_1624_1632
private theorem batch2_1612_1632 : binChunk w2 1612 20 = 1341481644678 :=
  binChunk_join (w := w2) (start := 1612) (left := 8) (right := 12) (x := 532630541816) (y := 808851102862) batch2_1612_1620 batch2_1620_1632
private theorem batch2_1632_1640 : binChunk w2 1632 8 = 545875516254 :=
  binChunk_join (w := w2) (start := 1632) (left := 4) (right := 4) (x := 272271498734) (y := 273604017520) leaf1632 leaf1636
private theorem batch2_1644_1651 : binChunk w2 1644 7 = 484369206238 :=
  binChunk_join (w := w2) (start := 1644) (left := 4) (right := 3) (x := 276279119894) (y := 208090086344) leaf1644 leaf1648
private theorem batch2_1640_1651 : binChunk w2 1640 11 = 759309097478 :=
  binChunk_join (w := w2) (start := 1640) (left := 4) (right := 7) (x := 274939891240) (y := 484369206238) leaf1640 batch2_1644_1651
private theorem batch2_1632_1651 : binChunk w2 1632 19 = 1305184613732 :=
  binChunk_join (w := w2) (start := 1632) (left := 8) (right := 11) (x := 545875516254) (y := 759309097478) batch2_1632_1640 batch2_1640_1651
theorem batch2_1612_1651 : binChunk w2 1612 39 = 2646666258410 :=
  binChunk_join (w := w2) (start := 1612) (left := 20) (right := 19) (x := 1341481644678) (y := 1305184613732) batch2_1612_1632 batch2_1632_1651

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBins2Part1612

-- merged module Low48PrimaryPivotBins2
section Merged_Low48PrimaryPivotBins2

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window2_588_716 : binChunk w2 588 128 = 15940021400 :=
  binChunk_join (w := w2) (start := 588) (left := 64) (right := 64) (x := 2275738089) (y := 13664283311) batch2_588_652 batch2_652_716
private theorem window2_716_844 : binChunk w2 716 128 = 98897485719 :=
  binChunk_join (w := w2) (start := 716) (left := 64) (right := 64) (x := 34238929886) (y := 64658555833) batch2_716_780 batch2_780_844
private theorem window2_588_844 : binChunk w2 588 256 = 114837507119 :=
  binChunk_join (w := w2) (start := 588) (left := 128) (right := 128) (x := 15940021400) (y := 98897485719) window2_588_716 window2_716_844
private theorem window2_844_972 : binChunk w2 844 128 = 280723506983 :=
  binChunk_join (w := w2) (start := 844) (left := 64) (right := 64) (x := 107991005254) (y := 172732501729) batch2_844_908 batch2_908_972
private theorem window2_972_1100 : binChunk w2 972 128 = 710333537487 :=
  binChunk_join (w := w2) (start := 972) (left := 64) (right := 64) (x := 274721008389) (y := 435612529098) batch2_972_1036 batch2_1036_1100
private theorem window2_844_1100 : binChunk w2 844 256 = 991057044470 :=
  binChunk_join (w := w2) (start := 844) (left := 128) (right := 128) (x := 280723506983) (y := 710333537487) window2_844_972 window2_972_1100
private theorem window2_588_1100 : binChunk w2 588 512 = 1105894551589 :=
  binChunk_join (w := w2) (start := 588) (left := 256) (right := 256) (x := 114837507119) (y := 991057044470) window2_588_844 window2_844_1100
private theorem window2_1100_1228 : binChunk w2 1100 128 = 1749172160308 :=
  binChunk_join (w := w2) (start := 1100) (left := 64) (right := 64) (x := 683887644365) (y := 1065284515943) batch2_1100_1164 batch2_1164_1228
private theorem window2_1228_1356 : binChunk w2 1228 128 = 4035471666511 :=
  binChunk_join (w := w2) (start := 1228) (left := 64) (right := 64) (x := 1643777913509) (y := 2391693753002) batch2_1228_1292 batch2_1292_1356
private theorem window2_1100_1356 : binChunk w2 1100 256 = 5784643826819 :=
  binChunk_join (w := w2) (start := 1100) (left := 128) (right := 128) (x := 1749172160308) (y := 4035471666511) window2_1100_1228 window2_1228_1356
private theorem window2_1356_1484 : binChunk w2 1356 128 = 6407429970534 :=
  binChunk_join (w := w2) (start := 1356) (left := 64) (right := 64) (x := 2990708504408) (y := 3416721466126) batch2_1356_1420 batch2_1420_1484
private theorem window2_1548_1651 : binChunk w2 1548 103 = 6720810879726 :=
  binChunk_join (w := w2) (start := 1548) (left := 64) (right := 39) (x := 4074144621316) (y := 2646666258410) batch2_1548_1612 batch2_1612_1651
private theorem window2_1484_1651 : binChunk w2 1484 167 = 10471694717053 :=
  binChunk_join (w := w2) (start := 1484) (left := 64) (right := 103) (x := 3750883837327) (y := 6720810879726) batch2_1484_1548 window2_1548_1651
private theorem window2_1356_1651 : binChunk w2 1356 295 = 16879124687587 :=
  binChunk_join (w := w2) (start := 1356) (left := 128) (right := 167) (x := 6407429970534) (y := 10471694717053) window2_1356_1484 window2_1484_1651
private theorem window2_1100_1651 : binChunk w2 1100 551 = 22663768514406 :=
  binChunk_join (w := w2) (start := 1100) (left := 256) (right := 295) (x := 5784643826819) (y := 16879124687587) window2_1100_1356 window2_1356_1651
private theorem window2_588_1651 : binChunk w2 588 1063 = 23769663065995 :=
  binChunk_join (w := w2) (start := 588) (left := 512) (right := 551) (x := 1105894551589) (y := 22663768514406) window2_588_1100 window2_1100_1651
theorem binCompute2 : binCompute w2 = 23769663065995 := by
  exact (binCompute_eq_chunk w2 588 (by decide) (by decide)).trans window2_588_1651

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBins2

end Merged6967_Low48PrimaryPivotBins2

section Merged6967_Low48PrimaryPivotRaw
set_option Elab.async false
























set_option Elab.async false

-- merged module Low48PrimaryPivotRawWindow3Part8
section Merged_Low48PrimaryPivotRawWindow3Part8

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At407 : rawChunk w3 407 2 = 24696165031 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 407 2 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawWindow3Part8

-- merged module Low48PrimaryPivotRaw
section Merged_Low48PrimaryPivotRaw

set_option autoImplicit false
set_option Elab.async false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

private theorem rawRange322_32 : rawChunk w2 322 32 = 697631494681 := joinRaw (w := w2) (start := 322) (a := 16) (b := 16) (x := 334716499936) (y := 362914994745) raw2At322 raw2At338
private theorem rawRange370_32 : rawChunk w2 370 32 = 855260109327 := joinRaw (w := w2) (start := 370) (a := 16) (b := 16) (x := 415482599923) (y := 439777509404) raw2At370 raw2At386
private theorem rawRange354_48 : rawChunk w2 354 48 = 1245142179173 := joinRaw (w := w2) (start := 354) (a := 16) (b := 32) (x := 389882069846) (y := 855260109327) raw2At354 rawRange370_32
private theorem rawRange322_80 : rawChunk w2 322 80 = 1942773673854 := joinRaw (w := w2) (start := 322) (a := 32) (b := 48) (x := 697631494681) (y := 1245142179173) rawRange322_32 rawRange354_48
private theorem rawRange418_32 : rawChunk w2 418 32 = 949087985135 := joinRaw (w := w2) (start := 418) (a := 16) (b := 16) (x := 470438054203) (y := 478649930932) raw2At418 raw2At434
private theorem rawRange402_48 : rawChunk w2 402 48 = 1409589563446 := joinRaw (w := w2) (start := 402) (a := 16) (b := 32) (x := 460501578311) (y := 949087985135) raw2At402 rawRange418_32
private theorem rawRange466_32 : rawChunk w2 466 32 = 993286302266 := joinRaw (w := w2) (start := 466) (a := 16) (b := 16) (x := 493358203126) (y := 499928099140) raw2At466 raw2At482
private theorem rawRange450_48 : rawChunk w2 450 48 = 1479563587499 := joinRaw (w := w2) (start := 450) (a := 16) (b := 32) (x := 486277285233) (y := 993286302266) raw2At450 rawRange466_32
private theorem rawRange402_96 : rawChunk w2 402 96 = 2889153150945 := joinRaw (w := w2) (start := 402) (a := 48) (b := 48) (x := 1409589563446) (y := 1479563587499) rawRange402_48 rawRange450_48
private theorem rawRange322_176 : rawChunk w2 322 176 = 4831926824799 := joinRaw (w := w2) (start := 322) (a := 80) (b := 96) (x := 1942773673854) (y := 2889153150945) rawRange322_80 rawRange402_96
private theorem rawRange514_32 : rawChunk w2 514 32 = 1028556346558 := joinRaw (w := w2) (start := 514) (a := 16) (b := 16) (x := 511664793208) (y := 516891553350) raw2At514 raw2At530
private theorem rawRange498_48 : rawChunk w2 498 48 = 1534576305977 := joinRaw (w := w2) (start := 498) (a := 16) (b := 32) (x := 506019959419) (y := 1028556346558) raw2At498 rawRange514_32
private theorem rawRange562_32 : rawChunk w2 562 32 = 1056526719336 := joinRaw (w := w2) (start := 562) (a := 16) (b := 16) (x := 526198452415) (y := 530328266921) raw2At562 raw2At578
private theorem rawRange546_48 : rawChunk w2 546 48 = 1578254309563 := joinRaw (w := w2) (start := 546) (a := 16) (b := 32) (x := 521727590227) (y := 1056526719336) raw2At546 rawRange562_32
private theorem rawRange498_96 : rawChunk w2 498 96 = 3112830615540 := joinRaw (w := w2) (start := 498) (a := 48) (b := 48) (x := 1534576305977) (y := 1578254309563) rawRange498_48 rawRange546_48
private theorem rawRange610_32 : rawChunk w2 610 32 = 1078544199394 := joinRaw (w := w2) (start := 610) (a := 16) (b := 16) (x := 537653642183) (y := 540890557211) raw2At610 raw2At626
private theorem rawRange594_48 : rawChunk w2 594 48 = 1612683788088 := joinRaw (w := w2) (start := 594) (a := 16) (b := 32) (x := 534139588694) (y := 1078544199394) raw2At594 rawRange610_32
private theorem rawRange658_32 : rawChunk w2 658 32 = 1095727320716 := joinRaw (w := w2) (start := 658) (a := 16) (b := 16) (x := 546606827619) (y := 549120493097) raw2At658 raw2At674
private theorem rawRange642_48 : rawChunk w2 642 48 = 1639596372223 := joinRaw (w := w2) (start := 642) (a := 16) (b := 32) (x := 543869051507) (y := 1095727320716) raw2At642 rawRange658_32
private theorem rawRange594_96 : rawChunk w2 594 96 = 3252280160311 := joinRaw (w := w2) (start := 594) (a := 48) (b := 48) (x := 1612683788088) (y := 1639596372223) rawRange594_48 rawRange642_48
private theorem rawRange498_192 : rawChunk w2 498 192 = 6365110775851 := joinRaw (w := w2) (start := 498) (a := 96) (b := 96) (x := 3112830615540) (y := 3252280160311) rawRange498_96 rawRange594_96
private theorem rawRange322_368 : rawChunk w2 322 368 = 11197037600650 := joinRaw (w := w2) (start := 322) (a := 176) (b := 192) (x := 4831926824799) (y := 6365110775851) rawRange322_176 rawRange498_192
private theorem rawRange706_32 : rawChunk w2 706 32 = 1109005680303 := joinRaw (w := w2) (start := 706) (a := 16) (b := 16) (x := 553537116024) (y := 555468564279) raw2At706 raw2At722
private theorem rawRange690_48 : rawChunk w2 690 48 = 1660431382343 := joinRaw (w := w2) (start := 690) (a := 16) (b := 32) (x := 551425702040) (y := 1109005680303) raw2At690 rawRange706_32
private theorem rawRange754_32 : rawChunk w2 754 32 = 1119151651867 := joinRaw (w := w2) (start := 754) (a := 16) (b := 16) (x := 558842694990) (y := 560308956877) raw2At754 raw2At770
private theorem rawRange738_48 : rawChunk w2 738 48 = 1676384718918 := joinRaw (w := w2) (start := 738) (a := 16) (b := 32) (x := 557233067051) (y := 1119151651867) raw2At738 rawRange754_32
private theorem rawRange690_96 : rawChunk w2 690 96 = 3336816101261 := joinRaw (w := w2) (start := 690) (a := 48) (b := 48) (x := 1660431382343) (y := 1676384718918) rawRange690_48 rawRange738_48
private theorem rawRange802_32 : rawChunk w2 802 32 = 1126805192733 := joinRaw (w := w2) (start := 802) (a := 16) (b := 16) (x := 562853628080) (y := 563951564653) raw2At802 raw2At818
private theorem rawRange786_48 : rawChunk w2 786 48 = 1688447783794 := joinRaw (w := w2) (start := 786) (a := 16) (b := 32) (x := 561642591061) (y := 1126805192733) raw2At786 rawRange802_32
private theorem rawRange850_32 : rawChunk w2 850 32 = 1132494725668 := joinRaw (w := w2) (start := 850) (a := 16) (b := 16) (x := 565842725407) (y := 566652000261) raw2At850 raw2At866
private theorem rawRange834_48 : rawChunk w2 834 48 = 1697439877836 := joinRaw (w := w2) (start := 834) (a := 16) (b := 32) (x := 564945152168) (y := 1132494725668) raw2At834 rawRange850_32
private theorem rawRange786_96 : rawChunk w2 786 96 = 3385887661630 := joinRaw (w := w2) (start := 786) (a := 48) (b := 48) (x := 1688447783794) (y := 1697439877836) rawRange786_48 rawRange834_48
private theorem rawRange690_192 : rawChunk w2 690 192 = 6722703762891 := joinRaw (w := w2) (start := 690) (a := 96) (b := 96) (x := 3336816101261) (y := 3385887661630) rawRange690_96 rawRange786_96
private theorem rawRange898_32 : rawChunk w2 898 32 = 1136654081979 := joinRaw (w := w2) (start := 898) (a := 16) (b := 16) (x := 568034115188) (y := 568619966791) raw2At898 raw2At914
private theorem rawRange882_48 : rawChunk w2 882 48 = 1704034275263 := joinRaw (w := w2) (start := 882) (a := 16) (b := 32) (x := 567380193284) (y := 1136654081979) raw2At882 rawRange898_32
private theorem rawRange946_32 : rawChunk w2 946 32 = 1139636938850 := joinRaw (w := w2) (start := 946) (a := 16) (b := 16) (x := 569610747672) (y := 570026191178) raw2At946 raw2At962
private theorem rawRange930_48 : rawChunk w2 930 48 = 1708780633140 := joinRaw (w := w2) (start := 930) (a := 16) (b := 32) (x := 569143694290) (y := 1139636938850) raw2At930 rawRange946_32
private theorem rawRange882_96 : rawChunk w2 882 96 = 3412814908403 := joinRaw (w := w2) (start := 882) (a := 48) (b := 48) (x := 1704034275263) (y := 1708780633140) rawRange882_48 rawRange930_48
private theorem rawRange994_32 : rawChunk w2 994 32 = 1075451171833 := joinRaw (w := w2) (start := 994) (a := 16) (b := 16) (x := 552786120873) (y := 522665050960) raw2At994 raw2At1010
private theorem rawRange978_48 : rawChunk w2 978 48 = 1645728308379 := joinRaw (w := w2) (start := 978) (a := 16) (b := 32) (x := 570277136546) (y := 1075451171833) raw2At978 rawRange994_32
private theorem rawRange1042_21 : rawChunk w2 1042 21 = 602136201000 := joinRaw (w := w2) (start := 1042) (a := 16) (b := 5) (x := 463246686475) (y := 138889514525) raw2At1042 raw2At1058
private theorem rawRange1026_37 : rawChunk w2 1026 37 = 1094702974771 := joinRaw (w := w2) (start := 1026) (a := 16) (b := 21) (x := 492566773771) (y := 602136201000) raw2At1026 rawRange1042_21
private theorem rawRange978_85 : rawChunk w2 978 85 = 2740431283150 := joinRaw (w := w2) (start := 978) (a := 48) (b := 37) (x := 1645728308379) (y := 1094702974771) rawRange978_48 rawRange1026_37
private theorem rawRange882_181 : rawChunk w2 882 181 = 6153246191553 := joinRaw (w := w2) (start := 882) (a := 96) (b := 85) (x := 3412814908403) (y := 2740431283150) rawRange882_96 rawRange978_85
private theorem rawRange690_373 : rawChunk w2 690 373 = 12875949954444 := joinRaw (w := w2) (start := 690) (a := 192) (b := 181) (x := 6722703762891) (y := 6153246191553) rawRange690_192 rawRange882_181
theorem computedWindow2 : rawChunk w2 322 741 = 24072987555094 := joinRaw (w := w2) (start := 322) (a := 368) (b := 373) (x := 11197037600650) (y := 12875949954444) rawRange322_368 rawRange690_373
private theorem rawRange39_32 : rawChunk w3 39 32 = 92625202846 := joinRaw (w := w3) (start := 39) (a := 16) (b := 16) (x := 38335177325) (y := 54290025521) raw3At39 raw3At55
private theorem rawRange23_48 : rawChunk w3 23 48 = 116516954252 := joinRaw (w := w3) (start := 23) (a := 16) (b := 32) (x := 23891751406) (y := 92625202846) raw3At23 rawRange39_32
private theorem rawRange87_32 : rawChunk w3 87 32 = 201264213966 := joinRaw (w := w3) (start := 87) (a := 16) (b := 16) (x := 90535524189) (y := 110728689777) raw3At87 raw3At103
private theorem rawRange71_48 : rawChunk w3 71 48 = 272970719052 := joinRaw (w := w3) (start := 71) (a := 16) (b := 32) (x := 71706505086) (y := 201264213966) raw3At71 rawRange87_32
private theorem rawRange23_96 : rawChunk w3 23 96 = 389487673304 := joinRaw (w := w3) (start := 23) (a := 48) (b := 48) (x := 116516954252) (y := 272970719052) rawRange23_48 rawRange71_48
private theorem rawRange135_32 : rawChunk w3 135 32 = 328324071442 := joinRaw (w := w3) (start := 135) (a := 16) (b := 16) (x := 154131600028) (y := 174192471414) raw3At135 raw3At151
private theorem rawRange119_48 : rawChunk w3 119 48 = 460560523343 := joinRaw (w := w3) (start := 119) (a := 16) (b := 32) (x := 132236451901) (y := 328324071442) raw3At119 rawRange135_32
private theorem rawRange183_32 : rawChunk w3 183 32 = 431298360043 := joinRaw (w := w3) (start := 183) (a := 16) (b := 16) (x := 208414391977) (y := 222883968066) raw3At183 raw3At199
private theorem rawRange167_48 : rawChunk w3 167 48 = 623530411808 := joinRaw (w := w3) (start := 167) (a := 16) (b := 32) (x := 192232051765) (y := 431298360043) raw3At167 rawRange183_32
private theorem rawRange119_96 : rawChunk w3 119 96 = 1084090935151 := joinRaw (w := w3) (start := 119) (a := 48) (b := 48) (x := 460560523343) (y := 623530411808) rawRange119_48 rawRange167_48
private theorem rawRange23_192 : rawChunk w3 23 192 = 1473578608455 := joinRaw (w := w3) (start := 23) (a := 96) (b := 96) (x := 389487673304) (y := 1084090935151) rawRange23_96 rawRange119_96
private theorem rawRange231_32 : rawChunk w3 231 32 = 504442180673 := joinRaw (w := w3) (start := 231) (a := 16) (b := 16) (x := 247190188765) (y := 257251991908) raw3At231 raw3At247
private theorem rawRange215_48 : rawChunk w3 215 48 = 740212318414 := joinRaw (w := w3) (start := 215) (a := 16) (b := 32) (x := 235770137741) (y := 504442180673) raw3At215 rawRange231_32
private theorem rawRange279_32 : rawChunk w3 279 32 = 547576787405 := joinRaw (w := w3) (start := 279) (a := 16) (b := 16) (x := 272560634689) (y := 275016152716) raw3At279 raw3At295
private theorem rawRange263_48 : rawChunk w3 263 48 = 813632464428 := joinRaw (w := w3) (start := 263) (a := 16) (b := 32) (x := 266055677023) (y := 547576787405) raw3At263 rawRange279_32
private theorem rawRange215_96 : rawChunk w3 215 96 = 1553844782842 := joinRaw (w := w3) (start := 215) (a := 48) (b := 48) (x := 740212318414) (y := 813632464428) rawRange215_48 rawRange263_48
private theorem rawRange327_32 : rawChunk w3 327 32 = 512514119957 := joinRaw (w := w3) (start := 327) (a := 16) (b := 16) (x := 264001764333) (y := 248512355624) raw3At327 raw3At343
private theorem rawRange311_48 : rawChunk w3 311 48 = 788148893868 := joinRaw (w := w3) (start := 311) (a := 16) (b := 32) (x := 275634773911) (y := 512514119957) raw3At311 rawRange327_32
private theorem rawRange359_32 : rawChunk w3 359 32 = 452613501648 := joinRaw (w := w3) (start := 359) (a := 16) (b := 16) (x := 233527456936) (y := 219086044712) raw3At359 raw3At375
private theorem rawRange391_18 : rawChunk w3 391 18 = 229876763727 := joinRaw (w := w3) (start := 391) (a := 16) (b := 2) (x := 205180598696) (y := 24696165031) raw3At391 raw3At407
private theorem rawRange359_50 : rawChunk w3 359 50 = 682490265375 := joinRaw (w := w3) (start := 359) (a := 32) (b := 18) (x := 452613501648) (y := 229876763727) rawRange359_32 rawRange391_18
private theorem rawRange311_98 : rawChunk w3 311 98 = 1470639159243 := joinRaw (w := w3) (start := 311) (a := 48) (b := 50) (x := 788148893868) (y := 682490265375) rawRange311_48 rawRange359_50
private theorem rawRange215_194 : rawChunk w3 215 194 = 3024483942085 := joinRaw (w := w3) (start := 215) (a := 96) (b := 98) (x := 1553844782842) (y := 1470639159243) rawRange215_96 rawRange311_98
theorem computedWindow3 : rawChunk w3 23 386 = 4498062550540 := joinRaw (w := w3) (start := 23) (a := 192) (b := 194) (x := 1473578608455) (y := 3024483942085) rawRange23_192 rawRange215_194

end Low48PrimaryPivot.RawReceipt

namespace Low48PrimaryPivot
open K1_13_2_3

theorem raw_eq_compute_w2 : rawWindow w2 = rawCompute w2 :=
  raw_eq_compute w2 (by decide) (by decide)

theorem rawCompute_w2 : rawCompute w2 = 24072987555094 :=
  (RawReceipt.rawCompute_eq w2).trans RawReceipt.computedWindow2

theorem rawWindow_w2 : rawWindow w2 = 24072987555094 :=
  raw_eq_compute_w2.trans rawCompute_w2

theorem raw_eq_compute_w3 : rawWindow w3 = rawCompute w3 :=
  raw_eq_compute w3 (by decide) (by decide)

theorem rawCompute_w3 : rawCompute w3 = 4498062550540 :=
  (RawReceipt.rawCompute_eq w3).trans RawReceipt.computedWindow3

theorem rawWindow_w3 : rawWindow w3 = 4498062550540 :=
  raw_eq_compute_w3.trans rawCompute_w3

#print axioms rawWindow_w2
#print axioms rawWindow_w3
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotRaw

end Merged6967_Low48PrimaryPivotRaw

import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part0
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part1
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part2
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part3
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part4
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part5
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part6
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part7
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part8
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part9
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part10
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part11
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part12
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part13
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part14
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow2Part15
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part0
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part1
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part2
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part3
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part4
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part5
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part6
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part7
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRawWindow3Part8

set_option autoImplicit false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

private theorem rawRange322_32 : rawChunk w2 322 32 = 697631494681 := joinRaw raw2At322 raw2At338
private theorem rawRange370_32 : rawChunk w2 370 32 = 855260109327 := joinRaw raw2At370 raw2At386
private theorem rawRange354_48 : rawChunk w2 354 48 = 1245142179173 := joinRaw raw2At354 rawRange370_32
private theorem rawRange322_80 : rawChunk w2 322 80 = 1942773673854 := joinRaw rawRange322_32 rawRange354_48
private theorem rawRange418_32 : rawChunk w2 418 32 = 949087985135 := joinRaw raw2At418 raw2At434
private theorem rawRange402_48 : rawChunk w2 402 48 = 1409589563446 := joinRaw raw2At402 rawRange418_32
private theorem rawRange466_32 : rawChunk w2 466 32 = 993286302266 := joinRaw raw2At466 raw2At482
private theorem rawRange450_48 : rawChunk w2 450 48 = 1479563587499 := joinRaw raw2At450 rawRange466_32
private theorem rawRange402_96 : rawChunk w2 402 96 = 2889153150945 := joinRaw rawRange402_48 rawRange450_48
private theorem rawRange322_176 : rawChunk w2 322 176 = 4831926824799 := joinRaw rawRange322_80 rawRange402_96
private theorem rawRange514_32 : rawChunk w2 514 32 = 1028556346558 := joinRaw raw2At514 raw2At530
private theorem rawRange498_48 : rawChunk w2 498 48 = 1534576305977 := joinRaw raw2At498 rawRange514_32
private theorem rawRange562_32 : rawChunk w2 562 32 = 1056526719336 := joinRaw raw2At562 raw2At578
private theorem rawRange546_48 : rawChunk w2 546 48 = 1578254309563 := joinRaw raw2At546 rawRange562_32
private theorem rawRange498_96 : rawChunk w2 498 96 = 3112830615540 := joinRaw rawRange498_48 rawRange546_48
private theorem rawRange610_32 : rawChunk w2 610 32 = 1078544199394 := joinRaw raw2At610 raw2At626
private theorem rawRange594_48 : rawChunk w2 594 48 = 1612683788088 := joinRaw raw2At594 rawRange610_32
private theorem rawRange658_32 : rawChunk w2 658 32 = 1095727320716 := joinRaw raw2At658 raw2At674
private theorem rawRange642_48 : rawChunk w2 642 48 = 1639596372223 := joinRaw raw2At642 rawRange658_32
private theorem rawRange594_96 : rawChunk w2 594 96 = 3252280160311 := joinRaw rawRange594_48 rawRange642_48
private theorem rawRange498_192 : rawChunk w2 498 192 = 6365110775851 := joinRaw rawRange498_96 rawRange594_96
private theorem rawRange322_368 : rawChunk w2 322 368 = 11197037600650 := joinRaw rawRange322_176 rawRange498_192
private theorem rawRange706_32 : rawChunk w2 706 32 = 1109005680303 := joinRaw raw2At706 raw2At722
private theorem rawRange690_48 : rawChunk w2 690 48 = 1660431382343 := joinRaw raw2At690 rawRange706_32
private theorem rawRange754_32 : rawChunk w2 754 32 = 1119151651867 := joinRaw raw2At754 raw2At770
private theorem rawRange738_48 : rawChunk w2 738 48 = 1676384718918 := joinRaw raw2At738 rawRange754_32
private theorem rawRange690_96 : rawChunk w2 690 96 = 3336816101261 := joinRaw rawRange690_48 rawRange738_48
private theorem rawRange802_32 : rawChunk w2 802 32 = 1126805192733 := joinRaw raw2At802 raw2At818
private theorem rawRange786_48 : rawChunk w2 786 48 = 1688447783794 := joinRaw raw2At786 rawRange802_32
private theorem rawRange850_32 : rawChunk w2 850 32 = 1132494725668 := joinRaw raw2At850 raw2At866
private theorem rawRange834_48 : rawChunk w2 834 48 = 1697439877836 := joinRaw raw2At834 rawRange850_32
private theorem rawRange786_96 : rawChunk w2 786 96 = 3385887661630 := joinRaw rawRange786_48 rawRange834_48
private theorem rawRange690_192 : rawChunk w2 690 192 = 6722703762891 := joinRaw rawRange690_96 rawRange786_96
private theorem rawRange898_32 : rawChunk w2 898 32 = 1136654081979 := joinRaw raw2At898 raw2At914
private theorem rawRange882_48 : rawChunk w2 882 48 = 1704034275263 := joinRaw raw2At882 rawRange898_32
private theorem rawRange946_32 : rawChunk w2 946 32 = 1139636938850 := joinRaw raw2At946 raw2At962
private theorem rawRange930_48 : rawChunk w2 930 48 = 1708780633140 := joinRaw raw2At930 rawRange946_32
private theorem rawRange882_96 : rawChunk w2 882 96 = 3412814908403 := joinRaw rawRange882_48 rawRange930_48
private theorem rawRange994_32 : rawChunk w2 994 32 = 1075451171833 := joinRaw raw2At994 raw2At1010
private theorem rawRange978_48 : rawChunk w2 978 48 = 1645728308379 := joinRaw raw2At978 rawRange994_32
private theorem rawRange1042_21 : rawChunk w2 1042 21 = 602136201000 := joinRaw raw2At1042 raw2At1058
private theorem rawRange1026_37 : rawChunk w2 1026 37 = 1094702974771 := joinRaw raw2At1026 rawRange1042_21
private theorem rawRange978_85 : rawChunk w2 978 85 = 2740431283150 := joinRaw rawRange978_48 rawRange1026_37
private theorem rawRange882_181 : rawChunk w2 882 181 = 6153246191553 := joinRaw rawRange882_96 rawRange978_85
private theorem rawRange690_373 : rawChunk w2 690 373 = 12875949954444 := joinRaw rawRange690_192 rawRange882_181
theorem computedWindow2 : rawChunk w2 322 741 = 24072987555094 := joinRaw rawRange322_368 rawRange690_373
private theorem rawRange39_32 : rawChunk w3 39 32 = 92625202846 := joinRaw raw3At39 raw3At55
private theorem rawRange23_48 : rawChunk w3 23 48 = 116516954252 := joinRaw raw3At23 rawRange39_32
private theorem rawRange87_32 : rawChunk w3 87 32 = 201264213966 := joinRaw raw3At87 raw3At103
private theorem rawRange71_48 : rawChunk w3 71 48 = 272970719052 := joinRaw raw3At71 rawRange87_32
private theorem rawRange23_96 : rawChunk w3 23 96 = 389487673304 := joinRaw rawRange23_48 rawRange71_48
private theorem rawRange135_32 : rawChunk w3 135 32 = 328324071442 := joinRaw raw3At135 raw3At151
private theorem rawRange119_48 : rawChunk w3 119 48 = 460560523343 := joinRaw raw3At119 rawRange135_32
private theorem rawRange183_32 : rawChunk w3 183 32 = 431298360043 := joinRaw raw3At183 raw3At199
private theorem rawRange167_48 : rawChunk w3 167 48 = 623530411808 := joinRaw raw3At167 rawRange183_32
private theorem rawRange119_96 : rawChunk w3 119 96 = 1084090935151 := joinRaw rawRange119_48 rawRange167_48
private theorem rawRange23_192 : rawChunk w3 23 192 = 1473578608455 := joinRaw rawRange23_96 rawRange119_96
private theorem rawRange231_32 : rawChunk w3 231 32 = 504442180673 := joinRaw raw3At231 raw3At247
private theorem rawRange215_48 : rawChunk w3 215 48 = 740212318414 := joinRaw raw3At215 rawRange231_32
private theorem rawRange279_32 : rawChunk w3 279 32 = 547576787405 := joinRaw raw3At279 raw3At295
private theorem rawRange263_48 : rawChunk w3 263 48 = 813632464428 := joinRaw raw3At263 rawRange279_32
private theorem rawRange215_96 : rawChunk w3 215 96 = 1553844782842 := joinRaw rawRange215_48 rawRange263_48
private theorem rawRange327_32 : rawChunk w3 327 32 = 512514119957 := joinRaw raw3At327 raw3At343
private theorem rawRange311_48 : rawChunk w3 311 48 = 788148893868 := joinRaw raw3At311 rawRange327_32
private theorem rawRange359_32 : rawChunk w3 359 32 = 452613501648 := joinRaw raw3At359 raw3At375
private theorem rawRange391_18 : rawChunk w3 391 18 = 229876763727 := joinRaw raw3At391 raw3At407
private theorem rawRange359_50 : rawChunk w3 359 50 = 682490265375 := joinRaw rawRange359_32 rawRange391_18
private theorem rawRange311_98 : rawChunk w3 311 98 = 1470639159243 := joinRaw rawRange311_48 rawRange359_50
private theorem rawRange215_194 : rawChunk w3 215 194 = 3024483942085 := joinRaw rawRange215_96 rawRange311_98
theorem computedWindow3 : rawChunk w3 23 386 = 4498062550540 := joinRaw rawRange23_192 rawRange215_194

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

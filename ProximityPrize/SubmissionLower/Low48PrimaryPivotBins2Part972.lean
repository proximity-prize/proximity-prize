import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup50

section Merged6967_Low48PrimaryPivotBins2Part972
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf972 : binChunk w2 972 4 = 13691872814 := by decide +kernel
private theorem leaf976 : binChunk w2 976 4 = 14094768023 := by decide +kernel
private theorem leaf980 : binChunk w2 980 4 = 14509585818 := by decide +kernel
private theorem leaf984 : binChunk w2 984 4 = 14936669298 := by decide +kernel
private theorem leaf988 : binChunk w2 988 4 = 15376236443 := by decide +kernel
private theorem leaf992 : binChunk w2 992 4 = 15828767766 := by decide +kernel
private theorem leaf996 : binChunk w2 996 4 = 16294623470 := by decide +kernel
private theorem leaf1000 : binChunk w2 1000 4 = 16774033015 := by decide +kernel
private theorem leaf1004 : binChunk w2 1004 4 = 17267499562 := by decide +kernel
private theorem leaf1008 : binChunk w2 1008 4 = 17775400418 := by decide +kernel
private theorem leaf1012 : binChunk w2 1012 4 = 18297976427 := by decide +kernel
private theorem leaf1016 : binChunk w2 1016 4 = 18835753494 := by decide +kernel
private theorem leaf1020 : binChunk w2 1020 4 = 19389126030 := by decide +kernel
private theorem leaf1024 : binChunk w2 1024 4 = 19958346167 := by decide +kernel
private theorem leaf1028 : binChunk w2 1028 4 = 20543962650 := by decide +kernel
private theorem leaf1032 : binChunk w2 1032 4 = 21146386994 := by decide +kernel
private theorem batch2_972_980 : binChunk w2 972 8 = 27786640837 :=
  binChunk_join (w := w2) (start := 972) (left := 4) (right := 4) (x := 13691872814) (y := 14094768023) leaf972 leaf976
private theorem batch2_980_988 : binChunk w2 980 8 = 29446255116 :=
  binChunk_join (w := w2) (start := 980) (left := 4) (right := 4) (x := 14509585818) (y := 14936669298) leaf980 leaf984
private theorem batch2_972_988 : binChunk w2 972 16 = 57232895953 :=
  binChunk_join (w := w2) (start := 972) (left := 8) (right := 8) (x := 27786640837) (y := 29446255116) batch2_972_980 batch2_980_988
private theorem batch2_988_996 : binChunk w2 988 8 = 31205004209 :=
  binChunk_join (w := w2) (start := 988) (left := 4) (right := 4) (x := 15376236443) (y := 15828767766) leaf988 leaf992
private theorem batch2_996_1004 : binChunk w2 996 8 = 33068656485 :=
  binChunk_join (w := w2) (start := 996) (left := 4) (right := 4) (x := 16294623470) (y := 16774033015) leaf996 leaf1000
private theorem batch2_988_1004 : binChunk w2 988 16 = 64273660694 :=
  binChunk_join (w := w2) (start := 988) (left := 8) (right := 8) (x := 31205004209) (y := 33068656485) batch2_988_996 batch2_996_1004
private theorem batch2_972_1004 : binChunk w2 972 32 = 121506556647 :=
  binChunk_join (w := w2) (start := 972) (left := 16) (right := 16) (x := 57232895953) (y := 64273660694) batch2_972_988 batch2_988_1004
private theorem batch2_1004_1012 : binChunk w2 1004 8 = 35042899980 :=
  binChunk_join (w := w2) (start := 1004) (left := 4) (right := 4) (x := 17267499562) (y := 17775400418) leaf1004 leaf1008
private theorem batch2_1012_1020 : binChunk w2 1012 8 = 37133729921 :=
  binChunk_join (w := w2) (start := 1012) (left := 4) (right := 4) (x := 18297976427) (y := 18835753494) leaf1012 leaf1016
private theorem batch2_1004_1020 : binChunk w2 1004 16 = 72176629901 :=
  binChunk_join (w := w2) (start := 1004) (left := 8) (right := 8) (x := 35042899980) (y := 37133729921) batch2_1004_1012 batch2_1012_1020
private theorem batch2_1020_1028 : binChunk w2 1020 8 = 39347472197 :=
  binChunk_join (w := w2) (start := 1020) (left := 4) (right := 4) (x := 19389126030) (y := 19958346167) leaf1020 leaf1024
private theorem batch2_1028_1036 : binChunk w2 1028 8 = 41690349644 :=
  binChunk_join (w := w2) (start := 1028) (left := 4) (right := 4) (x := 20543962650) (y := 21146386994) leaf1028 leaf1032
private theorem batch2_1020_1036 : binChunk w2 1020 16 = 81037821841 :=
  binChunk_join (w := w2) (start := 1020) (left := 8) (right := 8) (x := 39347472197) (y := 41690349644) batch2_1020_1028 batch2_1028_1036
private theorem batch2_1004_1036 : binChunk w2 1004 32 = 153214451742 :=
  binChunk_join (w := w2) (start := 1004) (left := 16) (right := 16) (x := 72176629901) (y := 81037821841) batch2_1004_1020 batch2_1020_1036
theorem batch2_972_1036 : binChunk w2 972 64 = 274721008389 :=
  binChunk_join (w := w2) (start := 972) (left := 32) (right := 32) (x := 121506556647) (y := 153214451742) batch2_972_1004 batch2_1004_1036

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins2Part972

section Merged6967_Low48PrimaryPivotBins3Part1306
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1306 : binChunk w3 1306 4 = 487947106 := by decide +kernel
private theorem leaf1310 : binChunk w3 1310 4 = 616811471 := by decide +kernel
private theorem leaf1314 : binChunk w3 1314 4 = 769677322 := by decide +kernel
private theorem leaf1318 : binChunk w3 1318 4 = 949352080 := by decide +kernel
private theorem leaf1322 : binChunk w3 1322 4 = 1158807340 := by decide +kernel
private theorem leaf1326 : binChunk w3 1326 4 = 1401160580 := by decide +kernel
private theorem leaf1330 : binChunk w3 1330 4 = 1677499764 := by decide +kernel
private theorem leaf1334 : binChunk w3 1334 4 = 1986243250 := by decide +kernel
private theorem leaf1338 : binChunk w3 1338 4 = 2328927758 := by decide +kernel
private theorem leaf1342 : binChunk w3 1342 4 = 2707408533 := by decide +kernel
private theorem leaf1346 : binChunk w3 1346 4 = 3123500719 := by decide +kernel
private theorem leaf1350 : binChunk w3 1350 4 = 3578958011 := by decide +kernel
private theorem leaf1354 : binChunk w3 1354 4 = 4075469202 := by decide +kernel
private theorem leaf1358 : binChunk w3 1358 4 = 4614686584 := by decide +kernel
private theorem leaf1362 : binChunk w3 1362 4 = 5198199236 := by decide +kernel
private theorem leaf1366 : binChunk w3 1366 4 = 5827505156 := by decide +kernel
private theorem batch3_1306_1314 : binChunk w3 1306 8 = 1104758577 :=
  binChunk_join (w := w3) (start := 1306) (left := 4) (right := 4) (x := 487947106) (y := 616811471) leaf1306 leaf1310
private theorem batch3_1314_1322 : binChunk w3 1314 8 = 1719029402 :=
  binChunk_join (w := w3) (start := 1314) (left := 4) (right := 4) (x := 769677322) (y := 949352080) leaf1314 leaf1318
private theorem batch3_1306_1322 : binChunk w3 1306 16 = 2823787979 :=
  binChunk_join (w := w3) (start := 1306) (left := 8) (right := 8) (x := 1104758577) (y := 1719029402) batch3_1306_1314 batch3_1314_1322
private theorem batch3_1322_1330 : binChunk w3 1322 8 = 2559967920 :=
  binChunk_join (w := w3) (start := 1322) (left := 4) (right := 4) (x := 1158807340) (y := 1401160580) leaf1322 leaf1326
private theorem batch3_1330_1338 : binChunk w3 1330 8 = 3663743014 :=
  binChunk_join (w := w3) (start := 1330) (left := 4) (right := 4) (x := 1677499764) (y := 1986243250) leaf1330 leaf1334
private theorem batch3_1322_1338 : binChunk w3 1322 16 = 6223710934 :=
  binChunk_join (w := w3) (start := 1322) (left := 8) (right := 8) (x := 2559967920) (y := 3663743014) batch3_1322_1330 batch3_1330_1338
private theorem batch3_1306_1338 : binChunk w3 1306 32 = 9047498913 :=
  binChunk_join (w := w3) (start := 1306) (left := 16) (right := 16) (x := 2823787979) (y := 6223710934) batch3_1306_1322 batch3_1322_1338
private theorem batch3_1338_1346 : binChunk w3 1338 8 = 5036336291 :=
  binChunk_join (w := w3) (start := 1338) (left := 4) (right := 4) (x := 2328927758) (y := 2707408533) leaf1338 leaf1342
private theorem batch3_1346_1354 : binChunk w3 1346 8 = 6702458730 :=
  binChunk_join (w := w3) (start := 1346) (left := 4) (right := 4) (x := 3123500719) (y := 3578958011) leaf1346 leaf1350
private theorem batch3_1338_1354 : binChunk w3 1338 16 = 11738795021 :=
  binChunk_join (w := w3) (start := 1338) (left := 8) (right := 8) (x := 5036336291) (y := 6702458730) batch3_1338_1346 batch3_1346_1354
private theorem batch3_1354_1362 : binChunk w3 1354 8 = 8690155786 :=
  binChunk_join (w := w3) (start := 1354) (left := 4) (right := 4) (x := 4075469202) (y := 4614686584) leaf1354 leaf1358
private theorem batch3_1362_1370 : binChunk w3 1362 8 = 11025704392 :=
  binChunk_join (w := w3) (start := 1362) (left := 4) (right := 4) (x := 5198199236) (y := 5827505156) leaf1362 leaf1366
private theorem batch3_1354_1370 : binChunk w3 1354 16 = 19715860178 :=
  binChunk_join (w := w3) (start := 1354) (left := 8) (right := 8) (x := 8690155786) (y := 11025704392) batch3_1354_1362 batch3_1362_1370
private theorem batch3_1338_1370 : binChunk w3 1338 32 = 31454655199 :=
  binChunk_join (w := w3) (start := 1338) (left := 16) (right := 16) (x := 11738795021) (y := 19715860178) batch3_1338_1354 batch3_1354_1370
theorem batch3_1306_1370 : binChunk w3 1306 64 = 40502154112 :=
  binChunk_join (w := w3) (start := 1306) (left := 32) (right := 32) (x := 9047498913) (y := 31454655199) batch3_1306_1338 batch3_1338_1370

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins3Part1306

section Merged6967_Low48PrimaryPivotBins3Part1370
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1370 : binChunk w3 1370 4 = 6503833818 := by decide +kernel
private theorem leaf1374 : binChunk w3 1374 4 = 7228100930 := by decide +kernel
private theorem leaf1378 : binChunk w3 1378 4 = 8001052622 := by decide +kernel
private theorem leaf1382 : binChunk w3 1382 4 = 8823317912 := by decide +kernel
private theorem leaf1386 : binChunk w3 1386 4 = 9695382401 := by decide +kernel
private theorem leaf1390 : binChunk w3 1390 4 = 10617599465 := by decide +kernel
private theorem leaf1394 : binChunk w3 1394 4 = 11590239416 := by decide +kernel
private theorem leaf1398 : binChunk w3 1398 4 = 12613444989 := by decide +kernel
private theorem leaf1402 : binChunk w3 1402 4 = 13687227217 := by decide +kernel
private theorem leaf1406 : binChunk w3 1406 4 = 14811518456 := by decide +kernel
private theorem leaf1410 : binChunk w3 1410 4 = 15986121337 := by decide +kernel
private theorem leaf1414 : binChunk w3 1414 4 = 17210704473 := by decide +kernel
private theorem leaf1418 : binChunk w3 1418 4 = 18484862360 := by decide +kernel
private theorem leaf1422 : binChunk w3 1422 4 = 19808057525 := by decide +kernel
private theorem leaf1426 : binChunk w3 1426 4 = 21179616065 := by decide +kernel
private theorem leaf1430 : binChunk w3 1430 4 = 22598794712 := by decide +kernel
private theorem batch3_1370_1378 : binChunk w3 1370 8 = 13731934748 :=
  binChunk_join (w := w3) (start := 1370) (left := 4) (right := 4) (x := 6503833818) (y := 7228100930) leaf1370 leaf1374
private theorem batch3_1378_1386 : binChunk w3 1378 8 = 16824370534 :=
  binChunk_join (w := w3) (start := 1378) (left := 4) (right := 4) (x := 8001052622) (y := 8823317912) leaf1378 leaf1382
private theorem batch3_1370_1386 : binChunk w3 1370 16 = 30556305282 :=
  binChunk_join (w := w3) (start := 1370) (left := 8) (right := 8) (x := 13731934748) (y := 16824370534) batch3_1370_1378 batch3_1378_1386
private theorem batch3_1386_1394 : binChunk w3 1386 8 = 20312981866 :=
  binChunk_join (w := w3) (start := 1386) (left := 4) (right := 4) (x := 9695382401) (y := 10617599465) leaf1386 leaf1390
private theorem batch3_1394_1402 : binChunk w3 1394 8 = 24203684405 :=
  binChunk_join (w := w3) (start := 1394) (left := 4) (right := 4) (x := 11590239416) (y := 12613444989) leaf1394 leaf1398
private theorem batch3_1386_1402 : binChunk w3 1386 16 = 44516666271 :=
  binChunk_join (w := w3) (start := 1386) (left := 8) (right := 8) (x := 20312981866) (y := 24203684405) batch3_1386_1394 batch3_1394_1402
private theorem batch3_1370_1402 : binChunk w3 1370 32 = 75072971553 :=
  binChunk_join (w := w3) (start := 1370) (left := 16) (right := 16) (x := 30556305282) (y := 44516666271) batch3_1370_1386 batch3_1386_1402
private theorem batch3_1402_1410 : binChunk w3 1402 8 = 28498745673 :=
  binChunk_join (w := w3) (start := 1402) (left := 4) (right := 4) (x := 13687227217) (y := 14811518456) leaf1402 leaf1406
private theorem batch3_1410_1418 : binChunk w3 1410 8 = 33196825810 :=
  binChunk_join (w := w3) (start := 1410) (left := 4) (right := 4) (x := 15986121337) (y := 17210704473) leaf1410 leaf1414
private theorem batch3_1402_1418 : binChunk w3 1402 16 = 61695571483 :=
  binChunk_join (w := w3) (start := 1402) (left := 8) (right := 8) (x := 28498745673) (y := 33196825810) batch3_1402_1410 batch3_1410_1418
private theorem batch3_1418_1426 : binChunk w3 1418 8 = 38292919885 :=
  binChunk_join (w := w3) (start := 1418) (left := 4) (right := 4) (x := 18484862360) (y := 19808057525) leaf1418 leaf1422
private theorem batch3_1426_1434 : binChunk w3 1426 8 = 43778410777 :=
  binChunk_join (w := w3) (start := 1426) (left := 4) (right := 4) (x := 21179616065) (y := 22598794712) leaf1426 leaf1430
private theorem batch3_1418_1434 : binChunk w3 1418 16 = 82071330662 :=
  binChunk_join (w := w3) (start := 1418) (left := 8) (right := 8) (x := 38292919885) (y := 43778410777) batch3_1418_1426 batch3_1426_1434
private theorem batch3_1402_1434 : binChunk w3 1402 32 = 143766902145 :=
  binChunk_join (w := w3) (start := 1402) (left := 16) (right := 16) (x := 61695571483) (y := 82071330662) batch3_1402_1418 batch3_1418_1434
theorem batch3_1370_1434 : binChunk w3 1370 64 = 218839873698 :=
  binChunk_join (w := w3) (start := 1370) (left := 32) (right := 32) (x := 75072971553) (y := 143766902145) batch3_1370_1402 batch3_1402_1434

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins3Part1370

section Merged6967_Low48PrimaryPivotBins3Part1434
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1434 : binChunk w3 1434 4 = 24064734637 := by decide +kernel
private theorem leaf1438 : binChunk w3 1438 4 = 25576581181 := by decide +kernel
private theorem leaf1442 : binChunk w3 1442 4 = 27133543108 := by decide +kernel
private theorem leaf1446 : binChunk w3 1446 4 = 28734742961 := by decide +kernel
private theorem leaf1450 : binChunk w3 1450 4 = 30379207821 := by decide +kernel
private theorem leaf1454 : binChunk w3 1454 4 = 32065951564 := by decide +kernel
private theorem leaf1458 : binChunk w3 1458 4 = 33793894992 := by decide +kernel
private theorem leaf1462 : binChunk w3 1462 4 = 35561861724 := by decide +kernel
private theorem leaf1466 : binChunk w3 1466 4 = 37368669244 := by decide +kernel
private theorem leaf1470 : binChunk w3 1470 4 = 39213041036 := by decide +kernel
private theorem leaf1474 : binChunk w3 1474 4 = 41093601436 := by decide +kernel
private theorem leaf1478 : binChunk w3 1478 4 = 43008974252 := by decide +kernel
private theorem leaf1482 : binChunk w3 1482 4 = 44957686568 := by decide +kernel
private theorem leaf1486 : binChunk w3 1486 4 = 46938163420 := by decide +kernel
private theorem leaf1490 : binChunk w3 1490 4 = 48948835036 := by decide +kernel
private theorem leaf1494 : binChunk w3 1494 4 = 50988031802 := by decide +kernel
private theorem batch3_1434_1442 : binChunk w3 1434 8 = 49641315818 :=
  binChunk_join (w := w3) (start := 1434) (left := 4) (right := 4) (x := 24064734637) (y := 25576581181) leaf1434 leaf1438
private theorem batch3_1442_1450 : binChunk w3 1442 8 = 55868286069 :=
  binChunk_join (w := w3) (start := 1442) (left := 4) (right := 4) (x := 27133543108) (y := 28734742961) leaf1442 leaf1446
private theorem batch3_1434_1450 : binChunk w3 1434 16 = 105509601887 :=
  binChunk_join (w := w3) (start := 1434) (left := 8) (right := 8) (x := 49641315818) (y := 55868286069) batch3_1434_1442 batch3_1442_1450
private theorem batch3_1450_1458 : binChunk w3 1450 8 = 62445159385 :=
  binChunk_join (w := w3) (start := 1450) (left := 4) (right := 4) (x := 30379207821) (y := 32065951564) leaf1450 leaf1454
private theorem batch3_1458_1466 : binChunk w3 1458 8 = 69355756716 :=
  binChunk_join (w := w3) (start := 1458) (left := 4) (right := 4) (x := 33793894992) (y := 35561861724) leaf1458 leaf1462
private theorem batch3_1450_1466 : binChunk w3 1450 16 = 131800916101 :=
  binChunk_join (w := w3) (start := 1450) (left := 8) (right := 8) (x := 62445159385) (y := 69355756716) batch3_1450_1458 batch3_1458_1466
private theorem batch3_1434_1466 : binChunk w3 1434 32 = 237310517988 :=
  binChunk_join (w := w3) (start := 1434) (left := 16) (right := 16) (x := 105509601887) (y := 131800916101) batch3_1434_1450 batch3_1450_1466
private theorem batch3_1466_1474 : binChunk w3 1466 8 = 76581710280 :=
  binChunk_join (w := w3) (start := 1466) (left := 4) (right := 4) (x := 37368669244) (y := 39213041036) leaf1466 leaf1470
private theorem batch3_1474_1482 : binChunk w3 1474 8 = 84102575688 :=
  binChunk_join (w := w3) (start := 1474) (left := 4) (right := 4) (x := 41093601436) (y := 43008974252) leaf1474 leaf1478
private theorem batch3_1466_1482 : binChunk w3 1466 16 = 160684285968 :=
  binChunk_join (w := w3) (start := 1466) (left := 8) (right := 8) (x := 76581710280) (y := 84102575688) batch3_1466_1474 batch3_1474_1482
private theorem batch3_1482_1490 : binChunk w3 1482 8 = 91895849988 :=
  binChunk_join (w := w3) (start := 1482) (left := 4) (right := 4) (x := 44957686568) (y := 46938163420) leaf1482 leaf1486
private theorem batch3_1490_1498 : binChunk w3 1490 8 = 99936866838 :=
  binChunk_join (w := w3) (start := 1490) (left := 4) (right := 4) (x := 48948835036) (y := 50988031802) leaf1490 leaf1494
private theorem batch3_1482_1498 : binChunk w3 1482 16 = 191832716826 :=
  binChunk_join (w := w3) (start := 1482) (left := 8) (right := 8) (x := 91895849988) (y := 99936866838) batch3_1482_1490 batch3_1490_1498
private theorem batch3_1466_1498 : binChunk w3 1466 32 = 352517002794 :=
  binChunk_join (w := w3) (start := 1466) (left := 16) (right := 16) (x := 160684285968) (y := 191832716826) batch3_1466_1482 batch3_1482_1498
theorem batch3_1434_1498 : binChunk w3 1434 64 = 589827520782 :=
  binChunk_join (w := w3) (start := 1434) (left := 32) (right := 32) (x := 237310517988) (y := 352517002794) batch3_1434_1466 batch3_1466_1498

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins3Part1434

section Merged6967_Low48PrimaryPivotBins3Part1498
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1498 : binChunk w3 1498 4 = 53053967138 := by decide +kernel
private theorem leaf1502 : binChunk w3 1502 4 = 55144817602 := by decide +kernel
private theorem leaf1506 : binChunk w3 1506 4 = 57258592550 := by decide +kernel
private theorem leaf1510 : binChunk w3 1510 4 = 59393127666 := by decide +kernel
private theorem leaf1514 : binChunk w3 1514 4 = 61546210306 := by decide +kernel
private theorem leaf1518 : binChunk w3 1518 4 = 63715456818 := by decide +kernel
private theorem leaf1522 : binChunk w3 1522 4 = 65898306435 := by decide +kernel
private theorem leaf1526 : binChunk w3 1526 4 = 68092155611 := by decide +kernel
private theorem leaf1530 : binChunk w3 1530 4 = 70294280704 := by decide +kernel
private theorem leaf1534 : binChunk w3 1534 4 = 72501963041 := by decide +kernel
private theorem leaf1538 : binChunk w3 1538 4 = 74712677938 := by decide +kernel
private theorem leaf1542 : binChunk w3 1542 4 = 76923954175 := by decide +kernel
private theorem leaf1546 : binChunk w3 1546 4 = 79133367792 := by decide +kernel
private theorem leaf1550 : binChunk w3 1550 4 = 81338696749 := by decide +kernel
private theorem leaf1554 : binChunk w3 1554 4 = 83537769170 := by decide +kernel
private theorem leaf1558 : binChunk w3 1558 4 = 85728456963 := by decide +kernel
private theorem batch3_1498_1506 : binChunk w3 1498 8 = 108198784740 :=
  binChunk_join (w := w3) (start := 1498) (left := 4) (right := 4) (x := 53053967138) (y := 55144817602) leaf1498 leaf1502
private theorem batch3_1506_1514 : binChunk w3 1506 8 = 116651720216 :=
  binChunk_join (w := w3) (start := 1506) (left := 4) (right := 4) (x := 57258592550) (y := 59393127666) leaf1506 leaf1510
private theorem batch3_1498_1514 : binChunk w3 1498 16 = 224850504956 :=
  binChunk_join (w := w3) (start := 1498) (left := 8) (right := 8) (x := 108198784740) (y := 116651720216) batch3_1498_1506 batch3_1506_1514
private theorem batch3_1514_1522 : binChunk w3 1514 8 = 125261667124 :=
  binChunk_join (w := w3) (start := 1514) (left := 4) (right := 4) (x := 61546210306) (y := 63715456818) leaf1514 leaf1518
private theorem batch3_1522_1530 : binChunk w3 1522 8 = 133990462046 :=
  binChunk_join (w := w3) (start := 1522) (left := 4) (right := 4) (x := 65898306435) (y := 68092155611) leaf1522 leaf1526
private theorem batch3_1514_1530 : binChunk w3 1514 16 = 259252129170 :=
  binChunk_join (w := w3) (start := 1514) (left := 8) (right := 8) (x := 125261667124) (y := 133990462046) batch3_1514_1522 batch3_1522_1530
private theorem batch3_1498_1530 : binChunk w3 1498 32 = 484102634126 :=
  binChunk_join (w := w3) (start := 1498) (left := 16) (right := 16) (x := 224850504956) (y := 259252129170) batch3_1498_1514 batch3_1514_1530
private theorem batch3_1530_1538 : binChunk w3 1530 8 = 142796243745 :=
  binChunk_join (w := w3) (start := 1530) (left := 4) (right := 4) (x := 70294280704) (y := 72501963041) leaf1530 leaf1534
private theorem batch3_1538_1546 : binChunk w3 1538 8 = 151636632113 :=
  binChunk_join (w := w3) (start := 1538) (left := 4) (right := 4) (x := 74712677938) (y := 76923954175) leaf1538 leaf1542
private theorem batch3_1530_1546 : binChunk w3 1530 16 = 294432875858 :=
  binChunk_join (w := w3) (start := 1530) (left := 8) (right := 8) (x := 142796243745) (y := 151636632113) batch3_1530_1538 batch3_1538_1546
private theorem batch3_1546_1554 : binChunk w3 1546 8 = 160472064541 :=
  binChunk_join (w := w3) (start := 1546) (left := 4) (right := 4) (x := 79133367792) (y := 81338696749) leaf1546 leaf1550
private theorem batch3_1554_1562 : binChunk w3 1554 8 = 169266226133 :=
  binChunk_join (w := w3) (start := 1554) (left := 4) (right := 4) (x := 83537769170) (y := 85728456963) leaf1554 leaf1558
private theorem batch3_1546_1562 : binChunk w3 1546 16 = 329738290674 :=
  binChunk_join (w := w3) (start := 1546) (left := 8) (right := 8) (x := 160472064541) (y := 169266226133) batch3_1546_1554 batch3_1554_1562
private theorem batch3_1530_1562 : binChunk w3 1530 32 = 624171166532 :=
  binChunk_join (w := w3) (start := 1530) (left := 16) (right := 16) (x := 294432875858) (y := 329738290674) batch3_1530_1546 batch3_1546_1562
theorem batch3_1498_1562 : binChunk w3 1498 64 = 1108273800658 :=
  binChunk_join (w := w3) (start := 1498) (left := 32) (right := 32) (x := 484102634126) (y := 624171166532) batch3_1498_1530 batch3_1530_1562

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins3Part1498

section Merged6967_Low48PrimaryPivotBins3Part1562
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf1562 : binChunk w3 1562 4 = 87908840828 := by decide +kernel
private theorem leaf1566 : binChunk w3 1566 4 = 90077048233 := by decide +kernel
private theorem leaf1570 : binChunk w3 1570 4 = 92231246858 := by decide +kernel
private theorem leaf1574 : binChunk w3 1574 4 = 94369820239 := by decide +kernel
private theorem leaf1578 : binChunk w3 1578 4 = 96491195188 := by decide +kernel
private theorem leaf1582 : binChunk w3 1582 4 = 98593835061 := by decide +kernel
private theorem leaf1586 : binChunk w3 1586 4 = 100676426326 := by decide +kernel
private theorem leaf1590 : binChunk w3 1590 4 = 102737695139 := by decide +kernel
private theorem leaf1594 : binChunk w3 1594 4 = 104776400436 := by decide +kernel
private theorem leaf1598 : binChunk w3 1598 4 = 106791531713 := by decide +kernel
private theorem leaf1602 : binChunk w3 1602 4 = 108782114470 := by decide +kernel
private theorem leaf1606 : binChunk w3 1606 4 = 110747203127 := by decide +kernel
private theorem leaf1610 : binChunk w3 1610 4 = 112686090304 := by decide +kernel
private theorem leaf1614 : binChunk w3 1614 4 = 114598100845 := by decide +kernel
private theorem leaf1618 : binChunk w3 1618 4 = 116482584558 := by decide +kernel
private theorem leaf1622 : binChunk w3 1622 4 = 118339131042 := by decide +kernel
private theorem batch3_1562_1570 : binChunk w3 1562 8 = 177985889061 :=
  binChunk_join (w := w3) (start := 1562) (left := 4) (right := 4) (x := 87908840828) (y := 90077048233) leaf1562 leaf1566
private theorem batch3_1570_1578 : binChunk w3 1570 8 = 186601067097 :=
  binChunk_join (w := w3) (start := 1570) (left := 4) (right := 4) (x := 92231246858) (y := 94369820239) leaf1570 leaf1574
private theorem batch3_1562_1578 : binChunk w3 1562 16 = 364586956158 :=
  binChunk_join (w := w3) (start := 1562) (left := 8) (right := 8) (x := 177985889061) (y := 186601067097) batch3_1562_1570 batch3_1570_1578
private theorem batch3_1578_1586 : binChunk w3 1578 8 = 195085030249 :=
  binChunk_join (w := w3) (start := 1578) (left := 4) (right := 4) (x := 96491195188) (y := 98593835061) leaf1578 leaf1582
private theorem batch3_1586_1594 : binChunk w3 1586 8 = 203414121465 :=
  binChunk_join (w := w3) (start := 1586) (left := 4) (right := 4) (x := 100676426326) (y := 102737695139) leaf1586 leaf1590
private theorem batch3_1578_1594 : binChunk w3 1578 16 = 398499151714 :=
  binChunk_join (w := w3) (start := 1578) (left := 8) (right := 8) (x := 195085030249) (y := 203414121465) batch3_1578_1586 batch3_1586_1594
private theorem batch3_1562_1594 : binChunk w3 1562 32 = 763086107872 :=
  binChunk_join (w := w3) (start := 1562) (left := 16) (right := 16) (x := 364586956158) (y := 398499151714) batch3_1562_1578 batch3_1578_1594
private theorem batch3_1594_1602 : binChunk w3 1594 8 = 211567932149 :=
  binChunk_join (w := w3) (start := 1594) (left := 4) (right := 4) (x := 104776400436) (y := 106791531713) leaf1594 leaf1598
private theorem batch3_1602_1610 : binChunk w3 1602 8 = 219529317597 :=
  binChunk_join (w := w3) (start := 1602) (left := 4) (right := 4) (x := 108782114470) (y := 110747203127) leaf1602 leaf1606
private theorem batch3_1594_1610 : binChunk w3 1594 16 = 431097249746 :=
  binChunk_join (w := w3) (start := 1594) (left := 8) (right := 8) (x := 211567932149) (y := 219529317597) batch3_1594_1602 batch3_1602_1610
private theorem batch3_1610_1618 : binChunk w3 1610 8 = 227284191149 :=
  binChunk_join (w := w3) (start := 1610) (left := 4) (right := 4) (x := 112686090304) (y := 114598100845) leaf1610 leaf1614
private theorem batch3_1618_1626 : binChunk w3 1618 8 = 234821715600 :=
  binChunk_join (w := w3) (start := 1618) (left := 4) (right := 4) (x := 116482584558) (y := 118339131042) leaf1618 leaf1622
private theorem batch3_1610_1626 : binChunk w3 1610 16 = 462105906749 :=
  binChunk_join (w := w3) (start := 1610) (left := 8) (right := 8) (x := 227284191149) (y := 234821715600) batch3_1610_1618 batch3_1618_1626
private theorem batch3_1594_1626 : binChunk w3 1594 32 = 893203156495 :=
  binChunk_join (w := w3) (start := 1594) (left := 16) (right := 16) (x := 431097249746) (y := 462105906749) batch3_1594_1610 batch3_1610_1626
theorem batch3_1562_1626 : binChunk w3 1562 64 = 1656289264367 :=
  binChunk_join (w := w3) (start := 1562) (left := 32) (right := 32) (x := 763086107872) (y := 893203156495) batch3_1562_1594 batch3_1594_1626

end Low48PrimaryPivot

end Merged6967_Low48PrimaryPivotBins3Part1562

section Merged6967_Low48PrimaryPivotRawWindow3Part0
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At23 : rawChunk w3 23 16 = 23891751406 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 23 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At39 : rawChunk w3 39 16 = 38335177325 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 39 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At55 : rawChunk w3 55 16 = 54290025521 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 55 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part0

section Merged6967_Low48PrimaryPivotRawWindow3Part1
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At71 : rawChunk w3 71 16 = 71706505086 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 71 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At87 : rawChunk w3 87 16 = 90535524189 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 87 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At103 : rawChunk w3 103 16 = 110728689777 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 103 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part1

section Merged6967_Low48PrimaryPivotRawWindow3Part2
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At119 : rawChunk w3 119 16 = 132236451901 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 119 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At135 : rawChunk w3 135 16 = 154131600028 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 135 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At151 : rawChunk w3 151 16 = 174192471414 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 151 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part2

section Merged6967_Low48PrimaryPivotRawWindow3Part3
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At167 : rawChunk w3 167 16 = 192232051765 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 167 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At183 : rawChunk w3 183 16 = 208414391977 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 183 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At199 : rawChunk w3 199 16 = 222883968066 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 199 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part3

section Merged6967_Low48PrimaryPivotRawWindow3Part4
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At215 : rawChunk w3 215 16 = 235770137741 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 215 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At231 : rawChunk w3 231 16 = 247190188765 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 231 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At247 : rawChunk w3 247 16 = 257251991908 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 247 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part4

section Merged6967_Low48PrimaryPivotRawWindow3Part5
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At263 : rawChunk w3 263 16 = 266055677023 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 263 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At279 : rawChunk w3 279 16 = 272560634689 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 279 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At295 : rawChunk w3 295 16 = 275016152716 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 295 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part5

section Merged6967_Low48PrimaryPivotRawWindow3Part6
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At311 : rawChunk w3 311 16 = 275634773911 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 311 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At327 : rawChunk w3 327 16 = 264001764333 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 327 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At343 : rawChunk w3 343 16 = 248512355624 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 343 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part6

section Merged6967_Low48PrimaryPivotRawWindow3Part7
set_option Elab.async false


set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

theorem raw3At359 : rawChunk w3 359 16 = 233527456936 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 359 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At375 : rawChunk w3 375 16 = 219086044712 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 375 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)
theorem raw3At391 : rawChunk w3 391 16 = 205180598696 :=
  (Low48PrimaryPivot.RawClosed.rawChunk_closed w3 391 16 (by decide) (by decide) (by decide) (by decide)).trans (by decide +kernel)

end Low48PrimaryPivot.RawReceipt

end Merged6967_Low48PrimaryPivotRawWindow3Part7

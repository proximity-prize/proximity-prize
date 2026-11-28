import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri

section Pack_R6970Height2308MainRank00

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank00_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_459_103 :
    P1_7_1.groupedPoleMoment 459 103 ≤ 1273186793 :=
  _root_.PoleAffine6970.certified 459 103 1273186793 (by decide) (by decide +kernel)

private theorem pole_460_103 :
    P1_7_1.groupedPoleMoment 460 103 ≤ 1282119717 :=
  _root_.PoleAffine6970.certified 460 103 1282119717 (by decide) (by decide +kernel)

private theorem pole_462_104 :
    P1_7_1.groupedPoleMoment 462 104 ≤ 1309815439 :=
  _root_.PoleAffine6970.certified 462 104 1309815439 (by decide) (by decide +kernel)

private theorem pole_476_107 :
    P1_7_1.groupedPoleMoment 476 107 ≤ 1473567056 :=
  _root_.PoleAffine6970.certified 476 107 1473567056 (by decide) (by decide +kernel)

private theorem pole_478_107 :
    P1_7_1.groupedPoleMoment 478 107 ≤ 1493553518 :=
  _root_.PoleAffine6970.certified 478 107 1493553518 (by decide) (by decide +kernel)

private theorem pole_484_108 :
    P1_7_1.groupedPoleMoment 484 108 ≤ 1565802843 :=
  _root_.PoleAffine6970.certified 484 108 1565802843 (by decide) (by decide +kernel)

private theorem pole_485_108 :
    P1_7_1.groupedPoleMoment 485 108 ≤ 1576220082 :=
  _root_.PoleAffine6970.certified 485 108 1576220082 (by decide) (by decide +kernel)

private theorem pole_485_109 :
    P1_7_1.groupedPoleMoment 485 109 ≤ 1587445741 :=
  _root_.PoleAffine6970.certified 485 109 1587445741 (by decide) (by decide +kernel)

private theorem pole_508_114 :
    P1_7_1.groupedPoleMoment 508 114 ≤ 1907029968 :=
  _root_.PoleAffine6970.certified 508 114 1907029968 (by decide) (by decide +kernel)

private theorem pole_512_115 :
    P1_7_1.groupedPoleMoment 512 115 ≤ 1968907529 :=
  _root_.PoleAffine6970.certified 512 115 1968907529 (by decide) (by decide +kernel)

theorem bank_331_459_103 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨331,459,103,u⟩,1130132144128,1273186793⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 331 459 103 u 1130132144128 1273186793
    (by decide) (by decide) (by decide) (by decide) pole_459_103

theorem bank_332_460_103 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨332,460,103,u⟩,1137779408896,1282119717⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 332 460 103 u 1137779408896 1282119717
    (by decide) (by decide) (by decide) (by decide) pole_460_103

theorem bank_333_462_104 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨333,462,104,u⟩,1153788805120,1309815439⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 333 462 104 u 1153788805120 1309815439
    (by decide) (by decide) (by decide) (by decide) pole_462_104

theorem bank_343_476_107 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨343,476,107,u⟩,1259288395776,1473567056⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 343 476 107 u 1259288395776 1473567056
    (by decide) (by decide) (by decide) (by decide) pole_476_107

theorem bank_345_478_107 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨345,478,107,u⟩,1275765719040,1493553518⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 345 478 107 u 1275765719040 1493553518
    (by decide) (by decide) (by decide) (by decide) pole_478_107

theorem bank_349_484_108 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨349,484,108,u⟩,1318247464960,1565802843⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 349 484 108 u 1318247464960 1565802843
    (by decide) (by decide) (by decide) (by decide) pole_484_108

theorem bank_350_485_108 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨350,485,108,u⟩,1326705278976,1576220082⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 350 485 108 u 1326705278976 1576220082
    (by decide) (by decide) (by decide) (by decide) pole_485_108

theorem bank_350_485_109 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨350,485,109,u⟩,1335921213440,1587445741⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 350 485 109 u 1335921213440 1587445741
    (by decide) (by decide) (by decide) (by decide) pole_485_109

theorem bank_366_508_114 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨366,508,114,u⟩,1526923264000,1907029968⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 366 508 114 u 1526923264000 1907029968
    (by decide) (by decide) (by decide) (by decide) pole_508_114

theorem bank_369_512_115 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨369,512,115,u⟩,1565288038400,1968907529⟩ :=
  pack_R6970Height2308MainRank00_bank_checked 369 512 115 u 1565288038400 1968907529
    (by decide) (by decide) (by decide) (by decide) pole_512_115

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank00

section Pack_R6970Height2308MainRank01

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank01_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_526_118 :
    P1_7_1.groupedPoleMoment 526 118 ≤ 2190246695 :=
  _root_.PoleAffine6970.certified 526 118 2190246695 (by decide) (by decide +kernel)

private theorem pole_531_120 :
    P1_7_1.groupedPoleMoment 531 120 ≤ 2287289170 :=
  _root_.PoleAffine6970.certified 531 120 2287289170 (by decide) (by decide +kernel)

private theorem pole_534_120 :
    P1_7_1.groupedPoleMoment 534 120 ≤ 2329089104 :=
  _root_.PoleAffine6970.certified 534 120 2329089104 (by decide) (by decide +kernel)

private theorem pole_536_123 :
    P1_7_1.groupedPoleMoment 536 123 ≤ 2402469105 :=
  _root_.PoleAffine6970.certified 536 123 2402469105 (by decide) (by decide +kernel)

private theorem pole_537_121 :
    P1_7_1.groupedPoleMoment 537 121 ≤ 2386617493 :=
  _root_.PoleAffine6970.certified 537 121 2386617493 (by decide) (by decide +kernel)

private theorem pole_539_123 :
    P1_7_1.groupedPoleMoment 539 123 ≤ 2445981139 :=
  _root_.PoleAffine6970.certified 539 123 2445981139 (by decide) (by decide +kernel)

private theorem pole_540_122 :
    P1_7_1.groupedPoleMoment 540 122 ≤ 2445193095 :=
  _root_.PoleAffine6970.certified 540 122 2445193095 (by decide) (by decide +kernel)

private theorem pole_543_122 :
    P1_7_1.groupedPoleMoment 543 122 ≤ 2489131032 :=
  _root_.PoleAffine6970.certified 543 122 2489131032 (by decide) (by decide +kernel)

private theorem pole_546_123 :
    P1_7_1.groupedPoleMoment 546 123 ≤ 2549591695 :=
  _root_.PoleAffine6970.certified 546 123 2549591695 (by decide) (by decide +kernel)

theorem bank_379_526_118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨379,526,118,u⟩,1694207836160,2190246695⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 379 526 118 u 1694207836160 2190246695
    (by decide) (by decide) (by decide) (by decide) pole_526_118

theorem bank_383_531_120 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨383,531,120,u⟩,1756494823424,2287289170⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 383 531 120 u 1756494823424 2287289170
    (by decide) (by decide) (by decide) (by decide) pole_531_120

theorem bank_385_534_120 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨385,534,120,u⟩,1777080729600,2329089104⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 385 534 120 u 1777080729600 2329089104
    (by decide) (by decide) (by decide) (by decide) pole_534_120

theorem bank_387_537_121 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨387,537,121,u⟩,1809037393920,2386617493⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 387 537 121 u 1809037393920 2386617493
    (by decide) (by decide) (by decide) (by decide) pole_537_121

theorem bank_387_536_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨387,536,123,u⟩,1831412432896,2402469105⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 387 536 123 u 1831412432896 2402469105
    (by decide) (by decide) (by decide) (by decide) pole_536_123

theorem bank_389_539_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨389,539,123,u⟩,1852671262720,2445981139⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 389 539 123 u 1852671262720 2445981139
    (by decide) (by decide) (by decide) (by decide) pole_539_123

theorem bank_390_540_122 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨390,540,122,u⟩,1851971338240,2445193095⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 390 540 122 u 1851971338240 2445193095
    (by decide) (by decide) (by decide) (by decide) pole_540_122

theorem bank_392_543_122 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨392,543,122,u⟩,1873284431872,2489131032⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 392 543 122 u 1873284431872 2489131032
    (by decide) (by decide) (by decide) (by decide) pole_543_122

theorem bank_394_546_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨394,546,123,u⟩,1906387189760,2549591695⟩ :=
  pack_R6970Height2308MainRank01_bank_checked 394 546 123 u 1906387189760 2549591695
    (by decide) (by decide) (by decide) (by decide) pole_546_123

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank01

section Pack_R6970Height2308MainRank02

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank02_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_549_124 :
    P1_7_1.groupedPoleMoment 549 124 ≤ 2611134733 :=
  _root_.PoleAffine6970.certified 549 124 2611134733 (by decide) (by decide +kernel)

private theorem pole_552_124 :
    P1_7_1.groupedPoleMoment 552 124 ≤ 2657282358 :=
  _root_.PoleAffine6970.certified 552 124 2657282358 (by decide) (by decide +kernel)

private theorem pole_567_128 :
    P1_7_1.groupedPoleMoment 567 128 ≤ 2968208542 :=
  _root_.PoleAffine6970.certified 567 128 2968208542 (by decide) (by decide +kernel)

private theorem pole_568_127 :
    P1_7_1.groupedPoleMoment 568 127 ≤ 2967080184 :=
  _root_.PoleAffine6970.certified 568 127 2967080184 (by decide) (by decide +kernel)

private theorem pole_578_130 :
    P1_7_1.groupedPoleMoment 578 130 ≤ 3195302144 :=
  _root_.PoleAffine6970.certified 578 130 3195302144 (by decide) (by decide +kernel)

private theorem pole_632_142 :
    P1_7_1.groupedPoleMoment 632 142 ≤ 4558241801 :=
  _root_.PoleAffine6970.certified 632 142 4558241801 (by decide) (by decide +kernel)

private theorem pole_664_150 :
    P1_7_1.groupedPoleMoment 664 150 ≤ 5573688426 :=
  _root_.PoleAffine6970.certified 664 150 5573688426 (by decide) (by decide +kernel)

private theorem pole_671_150 :
    P1_7_1.groupedPoleMoment 671 150 ≤ 5764871187 :=
  _root_.PoleAffine6970.certified 671 150 5764871187 (by decide) (by decide +kernel)

private theorem pole_742_167 :
    P1_7_1.groupedPoleMoment 742 167 ≤ 8655196727 :=
  _root_.PoleAffine6970.certified 742 167 8655196727 (by decide) (by decide +kernel)

private theorem pole_743_167 :
    P1_7_1.groupedPoleMoment 743 167 ≤ 8692774911 :=
  _root_.PoleAffine6970.certified 743 167 8692774911 (by decide) (by decide +kernel)

theorem bank_396_549_124 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨396,549,124,u⟩,1939865600000,2611134733⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 396 549 124 u 1939865600000 2611134733
    (by decide) (by decide) (by decide) (by decide) pole_549_124

theorem bank_398_552_124 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨398,552,124,u⟩,1961852928000,2657282358⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 398 552 124 u 1961852928000 2657282358
    (by decide) (by decide) (by decide) (by decide) pole_552_124

theorem bank_410_568_127 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨410,568,127,u⟩,2134649077760,2967080184⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 410 568 127 u 2134649077760 2967080184
    (by decide) (by decide) (by decide) (by decide) pole_568_127

theorem bank_409_567_128 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨409,567,128,u⟩,2135573135360,2968208542⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 409 567 128 u 2135573135360 2968208542
    (by decide) (by decide) (by decide) (by decide) pole_567_128

theorem bank_417_578_130 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨417,578,130,u⟩,2256297787392,3195302144⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 417 578 130 u 2256297787392 3195302144
    (by decide) (by decide) (by decide) (by decide) pole_578_130

theorem bank_456_632_142 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨456,632,142,u⟩,2945134100480,4558241801⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 456 632 142 u 2945134100480 4558241801
    (by decide) (by decide) (by decide) (by decide) pole_632_142

theorem bank_479_664_150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨479,664,150,u⟩,3426368880640,5573688426⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 479 664 150 u 3426368880640 5573688426
    (by decide) (by decide) (by decide) (by decide) pole_664_150

theorem bank_484_671_150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨484,671,150,u⟩,3506921799680,5764871187⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 484 671 150 u 3506921799680 5764871187
    (by decide) (by decide) (by decide) (by decide) pole_671_150

theorem bank_535_742_167 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨535,742,167,u⟩,4757735342080,8655196727⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 535 742 167 u 4757735342080 8655196727
    (by decide) (by decide) (by decide) (by decide) pole_742_167

theorem bank_536_743_167 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨536,743,167,u⟩,4777663528960,8692774911⟩ :=
  pack_R6970Height2308MainRank02_bank_checked 536 743 167 u 4777663528960 8692774911
    (by decide) (by decide) (by decide) (by decide) pole_743_167

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank02

section Pack_R6970Height2308MainRank03

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank03_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_754_170 :
    P1_7_1.groupedPoleMoment 754 170 ≤ 9239757637 :=
  _root_.PoleAffine6970.certified 754 170 9239757637 (by decide) (by decide +kernel)

private theorem pole_757_170 :
    P1_7_1.groupedPoleMoment 757 170 ≤ 9358541761 :=
  _root_.PoleAffine6970.certified 757 170 9358541761 (by decide) (by decide +kernel)

private theorem pole_768_173 :
    P1_7_1.groupedPoleMoment 768 173 ≤ 9936429387 :=
  _root_.PoleAffine6970.certified 768 173 9936429387 (by decide) (by decide +kernel)

private theorem pole_772_174 :
    P1_7_1.groupedPoleMoment 772 174 ≤ 10148954503 :=
  _root_.PoleAffine6970.certified 772 174 10148954503 (by decide) (by decide +kernel)

private theorem pole_773_175 :
    P1_7_1.groupedPoleMoment 773 175 ≤ 10236498384 :=
  _root_.PoleAffine6970.certified 773 175 10236498384 (by decide) (by decide +kernel)

private theorem pole_783_179 :
    P1_7_1.groupedPoleMoment 783 179 ≤ 10856426485 :=
  _root_.PoleAffine6970.certified 783 179 10856426485 (by decide) (by decide +kernel)

private theorem pole_784_176 :
    P1_7_1.groupedPoleMoment 784 176 ≤ 10759819420 :=
  _root_.PoleAffine6970.certified 784 176 10759819420 (by decide) (by decide +kernel)

private theorem pole_789_178 :
    P1_7_1.groupedPoleMoment 789 178 ≤ 11078415799 :=
  _root_.PoleAffine6970.certified 789 178 11078415799 (by decide) (by decide +kernel)

private theorem pole_790_178 :
    P1_7_1.groupedPoleMoment 790 178 ≤ 11123653753 :=
  _root_.PoleAffine6970.certified 790 178 11123653753 (by decide) (by decide +kernel)

private theorem pole_792_179 :
    P1_7_1.groupedPoleMoment 792 179 ≤ 11263133155 :=
  _root_.PoleAffine6970.certified 792 179 11263133155 (by decide) (by decide +kernel)

theorem bank_544_754_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨544,754,170,u⟩,5005415546880,9239757637⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 544 754 170 u 5005415546880 9239757637
    (by decide) (by decide) (by decide) (by decide) pole_754_170

theorem bank_546_757_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨546,757,170,u⟩,5046700867584,9358541761⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 546 757 170 u 5046700867584 9358541761
    (by decide) (by decide) (by decide) (by decide) pole_757_170

theorem bank_554_768_173 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨554,768,173,u⟩,5282866135040,9936429387⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 554 768 173 u 5282866135040 9936429387
    (by decide) (by decide) (by decide) (by decide) pole_768_173

theorem bank_557_772_174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨557,772,174,u⟩,5370380288000,10148954503⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 557 772 174 u 5370380288000 10148954503
    (by decide) (by decide) (by decide) (by decide) pole_772_174

theorem bank_558_773_175 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨558,773,175,u⟩,5415301545984,10236498384⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 558 773 175 u 5415301545984 10236498384
    (by decide) (by decide) (by decide) (by decide) pole_773_175

theorem bank_565_783_179 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨565,783,179,u⟩,5664087736320,10856426485⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 565 783 179 u 5664087736320 10856426485
    (by decide) (by decide) (by decide) (by decide) pole_783_179

theorem bank_565_784_176 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨565,784,176,u⟩,5592514822144,10759819420⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 565 784 176 u 5592514822144 10759819420
    (by decide) (by decide) (by decide) (by decide) pole_784_176

theorem bank_569_789_178 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨569,789,178,u⟩,5730096906240,11078415799⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 569 789 178 u 5730096906240 11078415799
    (by decide) (by decide) (by decide) (by decide) pole_789_178

theorem bank_570_790_178 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨570,790,178,u⟩,5752667242496,11123653753⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 570 790 178 u 5752667242496 11123653753
    (by decide) (by decide) (by decide) (by decide) pole_790_178

theorem bank_571_792_179 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨571,792,179,u⟩,5799700070400,11263133155⟩ :=
  pack_R6970Height2308MainRank03_bank_checked 571 792 179 u 5799700070400 11263133155
    (by decide) (by decide) (by decide) (by decide) pole_792_179

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank03

section Pack_R6970Height2308MainRank04

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank04_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_804_183 :
    P1_7_1.groupedPoleMoment 804 183 ≤ 12024934101 :=
  _root_.PoleAffine6970.certified 804 183 12024934101 (by decide) (by decide +kernel)

private theorem pole_808_182 :
    P1_7_1.groupedPoleMoment 808 182 ≤ 12166928347 :=
  _root_.PoleAffine6970.certified 808 182 12166928347 (by decide) (by decide +kernel)

private theorem pole_808_183 :
    P1_7_1.groupedPoleMoment 808 183 ≤ 12218519581 :=
  _root_.PoleAffine6970.certified 808 183 12218519581 (by decide) (by decide +kernel)

private theorem pole_822_186 :
    P1_7_1.groupedPoleMoment 822 186 ≤ 13076073849 :=
  _root_.PoleAffine6970.certified 822 186 13076073849 (by decide) (by decide +kernel)

private theorem pole_827_186 :
    P1_7_1.groupedPoleMoment 827 186 ≤ 13333726189 :=
  _root_.PoleAffine6970.certified 827 186 13333726189 (by decide) (by decide +kernel)

private theorem pole_869_191 :
    P1_7_1.groupedPoleMoment 869 191 ≤ 15961181802 :=
  _root_.PoleAffine6970.certified 869 191 15961181802 (by decide) (by decide +kernel)

private theorem pole_872_199 :
    P1_7_1.groupedPoleMoment 872 199 ≤ 16659415961 :=
  _root_.PoleAffine6970.certified 872 199 16659415961 (by decide) (by decide +kernel)

private theorem pole_873_189 :
    P1_7_1.groupedPoleMoment 873 189 ≤ 16066866815 :=
  _root_.PoleAffine6970.certified 873 189 16066866815 (by decide) (by decide +kernel)

private theorem pole_874_192 :
    P1_7_1.groupedPoleMoment 874 192 ≤ 16324293630 :=
  _root_.PoleAffine6970.certified 874 192 16324293630 (by decide) (by decide +kernel)

private theorem pole_876_193 :
    P1_7_1.groupedPoleMoment 876 193 ≤ 16511045844 :=
  _root_.PoleAffine6970.certified 876 193 16511045844 (by decide) (by decide +kernel)

theorem bank_583_808_182 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨583,808,182,u⟩,6152678014976,12166928347⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 583 808 182 u 6152678014976 12166928347
    (by decide) (by decide) (by decide) (by decide) pole_808_182

theorem bank_583_808_183 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨583,808,183,u⟩,6178115420160,12218519581⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 583 808 183 u 6178115420160 12218519581
    (by decide) (by decide) (by decide) (by decide) pole_808_183

theorem bank_593_822_186 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨593,822,186,u⟩,6496988692480,13076073849⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 593 822 186 u 6496988692480 13076073849
    (by decide) (by decide) (by decide) (by decide) pole_822_186

theorem bank_596_827_186 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨596,827,186,u⟩,6570814210048,13333726189⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 596 827 186 u 6570814210048 13333726189
    (by decide) (by decide) (by decide) (by decide) pole_827_186

theorem bank_580_804_183 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨580,804,183,u⟩,6107138359296,12024934101⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 580 804 183 u 6107138359296 12024934101
    (by decide) (by decide) (by decide) (by decide) pole_804_183

theorem bank_626_869_191 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨626,869,191,u⟩,7482311180288,15961181802⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 626 869 191 u 7482311180288 15961181802
    (by decide) (by decide) (by decide) (by decide) pole_869_191

theorem bank_630_874_192 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨630,874,192,u⟩,7619678044160,16324293630⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 630 874 192 u 7619678044160 16324293630
    (by decide) (by decide) (by decide) (by decide) pole_874_192

theorem bank_628_873_189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨628,873,189,u⟩,7476010024960,16066866815⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 628 873 189 u 7476010024960 16066866815
    (by decide) (by decide) (by decide) (by decide) pole_873_189

theorem bank_629_872_199 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨629,872,199,u⟩,7800514150400,16659415961⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 629 872 199 u 7800514150400 16659415961
    (by decide) (by decide) (by decide) (by decide) pole_872_199

theorem bank_631_876_193 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨631,876,193,u⟩,7676856107008,16511045844⟩ :=
  pack_R6970Height2308MainRank04_bank_checked 631 876 193 u 7676856107008 16511045844
    (by decide) (by decide) (by decide) (by decide) pole_876_193

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank04

section Pack_R6970Height2308MainRank05

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank05_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_880_193 :
    P1_7_1.groupedPoleMoment 880 193 ≤ 16754705382 :=
  _root_.PoleAffine6970.certified 880 193 16754705382 (by decide) (by decide +kernel)

private theorem pole_886_195 :
    P1_7_1.groupedPoleMoment 886 195 ≤ 17262193306 :=
  _root_.PoleAffine6970.certified 886 195 17262193306 (by decide) (by decide +kernel)

private theorem pole_889_195 :
    P1_7_1.groupedPoleMoment 889 195 ≤ 17450849480 :=
  _root_.PoleAffine6970.certified 889 195 17450849480 (by decide) (by decide +kernel)

private theorem pole_892_196 :
    P1_7_1.groupedPoleMoment 892 196 ≤ 17710998789 :=
  _root_.PoleAffine6970.certified 892 196 17710998789 (by decide) (by decide +kernel)

private theorem pole_895_196 :
    P1_7_1.groupedPoleMoment 895 196 ≤ 17903245967 :=
  _root_.PoleAffine6970.certified 895 196 17903245967 (by decide) (by decide +kernel)

private theorem pole_901_198 :
    P1_7_1.groupedPoleMoment 901 198 ≤ 18436579771 :=
  _root_.PoleAffine6970.certified 901 198 18436579771 (by decide) (by decide +kernel)

private theorem pole_904_199 :
    P1_7_1.groupedPoleMoment 904 199 ≤ 18707612761 :=
  _root_.PoleAffine6970.certified 904 199 18707612761 (by decide) (by decide +kernel)

private theorem pole_907_199 :
    P1_7_1.groupedPoleMoment 907 199 ≤ 18907987461 :=
  _root_.PoleAffine6970.certified 907 199 18907987461 (by decide) (by decide +kernel)

private theorem pole_912_201 :
    P1_7_1.groupedPoleMoment 912 201 ≤ 19394973127 :=
  _root_.PoleAffine6970.certified 912 201 19394973127 (by decide) (by decide +kernel)

private theorem pole_914_201 :
    P1_7_1.groupedPoleMoment 914 201 ≤ 19532087394 :=
  _root_.PoleAffine6970.certified 914 201 19532087394 (by decide) (by decide +kernel)

theorem bank_634_880_193 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨634,880,193,u⟩,7758708736000,16754705382⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 634 880 193 u 7758708736000 16754705382
    (by decide) (by decide) (by decide) (by decide) pole_880_193

theorem bank_638_886_195 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨638,886,195,u⟩,7930203602944,17262193306⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 638 886 195 u 7930203602944 17262193306
    (by decide) (by decide) (by decide) (by decide) pole_886_195

theorem bank_640_889_195 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨640,889,195,u⟩,7985899765760,17450849480⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 640 889 195 u 7985899765760 17450849480
    (by decide) (by decide) (by decide) (by decide) pole_889_195

theorem bank_643_892_196 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨643,892,196,u⟩,8101138268160,17710998789⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 643 892 196 u 8101138268160 17710998789
    (by decide) (by decide) (by decide) (by decide) pole_892_196

theorem bank_645_895_196 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨645,895,196,u⟩,8157583376384,17903245967⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 645 895 196 u 8157583376384 17903245967
    (by decide) (by decide) (by decide) (by decide) pole_895_196

theorem bank_649_901_198 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨649,901,198,u⟩,8334927462400,18436579771⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 649 901 198 u 8334927462400 18436579771
    (by decide) (by decide) (by decide) (by decide) pole_901_198

theorem bank_651_904_199 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨651,904,199,u⟩,8424521728000,18707612761⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 651 904 199 u 8424521728000 18707612761
    (by decide) (by decide) (by decide) (by decide) pole_904_199

theorem bank_653_907_199 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨653,907,199,u⟩,8482507980800,18907987461⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 653 907 199 u 8482507980800 18907987461
    (by decide) (by decide) (by decide) (by decide) pole_907_199

theorem bank_657_912_201 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨657,912,201,u⟩,8664449024000,19394973127⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 657 912 201 u 8664449024000 19394973127
    (by decide) (by decide) (by decide) (by decide) pole_912_201

theorem bank_658_914_201 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨658,914,201,u⟩,8693970370560,19532087394⟩ :=
  pack_R6970Height2308MainRank05_bank_checked 658 914 201 u 8693970370560 19532087394
    (by decide) (by decide) (by decide) (by decide) pole_914_201

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank05

section Pack_R6970Height2308MainRank06

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank06_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_922_207 :
    P1_7_1.groupedPoleMoment 922 207 ≤ 20550046594 :=
  _root_.PoleAffine6970.certified 922 207 20550046594 (by decide) (by decide +kernel)

private theorem pole_928_204 :
    P1_7_1.groupedPoleMoment 928 204 ≤ 20747512695 :=
  _root_.PoleAffine6970.certified 928 204 20747512695 (by decide) (by decide +kernel)

private theorem pole_931_204 :
    P1_7_1.groupedPoleMoment 931 204 ≤ 20963968915 :=
  _root_.PoleAffine6970.certified 931 204 20963968915 (by decide) (by decide +kernel)

private theorem pole_934_205 :
    P1_7_1.groupedPoleMoment 934 205 ≤ 21262440153 :=
  _root_.PoleAffine6970.certified 934 205 21262440153 (by decide) (by decide +kernel)

private theorem pole_1084_243 :
    P1_7_1.groupedPoleMoment 1084 243 ≤ 39166240361 :=
  _root_.PoleAffine6970.certified 1084 243 39166240361 (by decide) (by decide +kernel)

private theorem pole_1140_256 :
    P1_7_1.groupedPoleMoment 1140 256 ≤ 47955479838 :=
  _root_.PoleAffine6970.certified 1140 256 47955479838 (by decide) (by decide +kernel)

private theorem pole_1203_270 :
    P1_7_1.groupedPoleMoment 1203 270 ≤ 59420041004 :=
  _root_.PoleAffine6970.certified 1203 270 59420041004 (by decide) (by decide +kernel)

private theorem pole_1236_275 :
    P1_7_1.groupedPoleMoment 1236 275 ≤ 65755659593 :=
  _root_.PoleAffine6970.certified 1236 275 65755659593 (by decide) (by decide +kernel)

private theorem pole_1236_277 :
    P1_7_1.groupedPoleMoment 1236 277 ≤ 66125876916 :=
  _root_.PoleAffine6970.certified 1236 277 66125876916 (by decide) (by decide +kernel)

private theorem pole_1257_281 :
    P1_7_1.groupedPoleMoment 1257 281 ≤ 70590385272 :=
  _root_.PoleAffine6970.certified 1257 281 70590385272 (by decide) (by decide +kernel)

theorem bank_665_922_207 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨665,922,207,u⟩,9102289797120,20550046594⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 665 922 207 u 9102289797120 20550046594
    (by decide) (by decide) (by decide) (by decide) pole_922_207

theorem bank_669_928_204 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨669,928,204,u⟩,9124056924160,20747512695⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 669 928 204 u 9124056924160 20747512695
    (by decide) (by decide) (by decide) (by decide) pole_928_204

theorem bank_671_931_204 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨671,931,204,u⟩,9185158758400,20963968915⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 671 931 204 u 9185158758400 20963968915
    (by decide) (by decide) (by decide) (by decide) pole_931_204

theorem bank_673_934_205 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨673,934,205,u⟩,9280779976704,21262440153⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 673 934 205 u 9280779976704 21262440153
    (by decide) (by decide) (by decide) (by decide) pole_934_205

theorem bank_782_1084_243 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨782,1084,243,u⟩,14766753447936,39166240361⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 782 1084 243 u 14766753447936 39166240361
    (by decide) (by decide) (by decide) (by decide) pole_1084_243

theorem bank_822_1140_256 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨822,1140,256,u⟩,17174554214400,47955479838⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 822 1140 256 u 17174554214400 47955479838
    (by decide) (by decide) (by decide) (by decide) pole_1140_256

theorem bank_867_1203_270 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨867,1203,270,u⟩,20145671503872,59420041004⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 867 1203 270 u 20145671503872 59420041004
    (by decide) (by decide) (by decide) (by decide) pole_1203_270

theorem bank_891_1236_275 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨891,1236,275,u⟩,21714760105984,65755659593⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 891 1236 275 u 21714760105984 65755659593
    (by decide) (by decide) (by decide) (by decide) pole_1236_275

theorem bank_891_1236_277 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨891,1236,277,u⟩,21834023567360,66125876916⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 891 1236 277 u 21834023567360 66125876916
    (by decide) (by decide) (by decide) (by decide) pole_1236_277

theorem bank_906_1257_281 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨906,1257,281,u⟩,22912574947328,70590385272⟩ :=
  pack_R6970Height2308MainRank06_bank_checked 906 1257 281 u 22912574947328 70590385272
    (by decide) (by decide) (by decide) (by decide) pole_1257_281

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank06

section Pack_R6970Height2308MainRank07

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank07_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_242_53 :
    P1_7_1.groupedPoleMoment 242 53 ≤ 98129954 :=
  _root_.PoleAffine6970.certified 242 53 98129954 (by decide) (by decide +kernel)

private theorem pole_242_54 :
    P1_7_1.groupedPoleMoment 242 54 ≤ 99540078 :=
  _root_.PoleAffine6970.certified 242 54 99540078 (by decide) (by decide +kernel)

private theorem pole_264_59 :
    P1_7_1.groupedPoleMoment 264 59 ≤ 140746391 :=
  _root_.PoleAffine6970.certified 264 59 140746391 (by decide) (by decide +kernel)

private theorem pole_1270_285 :
    P1_7_1.groupedPoleMoment 1270 285 ≤ 73770661510 :=
  _root_.PoleAffine6970.certified 1270 285 73770661510 (by decide) (by decide +kernel)

private theorem pole_1282_288 :
    P1_7_1.groupedPoleMoment 1282 288 ≤ 76657247691 :=
  _root_.PoleAffine6970.certified 1282 288 76657247691 (by decide) (by decide +kernel)

private theorem pole_1324_297 :
    P1_7_1.groupedPoleMoment 1324 297 ≤ 87090668127 :=
  _root_.PoleAffine6970.certified 1324 297 87090668127 (by decide) (by decide +kernel)

private theorem pole_1335_300 :
    P1_7_1.groupedPoleMoment 1335 300 ≤ 90140497767 :=
  _root_.PoleAffine6970.certified 1335 300 90140497767 (by decide) (by decide +kernel)

private theorem pole_1346_304 :
    P1_7_1.groupedPoleMoment 1346 304 ≤ 93507755861 :=
  _root_.PoleAffine6970.certified 1346 304 93507755861 (by decide) (by decide +kernel)

private theorem pole_1751_393 :
    P1_7_1.groupedPoleMoment 1751 393 ≤ 266125640712 :=
  _root_.PoleAffine6970.certified 1751 393 266125640712 (by decide) (by decide +kernel)

theorem bank_916_1270_285 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨916,1270,285,u⟩,23734898130944,73770661510⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 916 1270 285 u 23734898130944 73770661510
    (by decide) (by decide) (by decide) (by decide) pole_1270_285

theorem bank_924_1282_288 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨924,1282,288,u⟩,24393838755840,76657247691⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 924 1282 288 u 24393838755840 76657247691
    (by decide) (by decide) (by decide) (by decide) pole_1282_288

theorem bank_955_1324_297 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨955,1324,297,u⟩,26882670592000,87090668127⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 955 1324 297 u 26882670592000 87090668127
    (by decide) (by decide) (by decide) (by decide) pole_1324_297

theorem bank_963_1335_300 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨963,1335,300,u⟩,27598406549504,90140497767⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 963 1335 300 u 27598406549504 90140497767
    (by decide) (by decide) (by decide) (by decide) pole_1335_300

theorem bank_971_1346_304 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨971,1346,304,u⟩,28397233766400,93507755861⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 971 1346 304 u 28397233766400 93507755861
    (by decide) (by decide) (by decide) (by decide) pole_1346_304

theorem bank_1262_1751_393 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1262,1751,393,u⟩,62024394735616,266125640712⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 1262 1751 393 u 62024394735616 266125640712
    (by decide) (by decide) (by decide) (by decide) pole_1751_393

theorem bank_174_242_53 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨174,242,53,u⟩,163628974080,98129954⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 174 242 53 u 163628974080 98129954
    (by decide) (by decide) (by decide) (by decide) pole_242_53

theorem bank_175_242_54 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨175,242,54,u⟩,168055275520,99540078⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 175 242 54 u 168055275520 99540078
    (by decide) (by decide) (by decide) (by decide) pole_242_54

theorem bank_190_264_59 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨190,264,59,u⟩,215642275840,140746391⟩ :=
  pack_R6970Height2308MainRank07_bank_checked 190 264 59 u 215642275840 140746391
    (by decide) (by decide) (by decide) (by decide) pole_264_59

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank07

section Pack_R6970Height2308MainRank08

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank08_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_269_60 :
    P1_7_1.groupedPoleMoment 269 60 ≤ 151401819 :=
  _root_.PoleAffine6970.certified 269 60 151401819 (by decide) (by decide +kernel)

private theorem pole_284_63 :
    P1_7_1.groupedPoleMoment 284 63 ≤ 187015104 :=
  _root_.PoleAffine6970.certified 284 63 187015104 (by decide) (by decide +kernel)

private theorem pole_285_64 :
    P1_7_1.groupedPoleMoment 285 64 ≤ 191426557 :=
  _root_.PoleAffine6970.certified 285 64 191426557 (by decide) (by decide +kernel)

private theorem pole_299_67 :
    P1_7_1.groupedPoleMoment 299 67 ≤ 231211938 :=
  _root_.PoleAffine6970.certified 299 67 231211938 (by decide) (by decide +kernel)

private theorem pole_309_69 :
    P1_7_1.groupedPoleMoment 309 69 ≤ 262793893 :=
  _root_.PoleAffine6970.certified 309 69 262793893 (by decide) (by decide +kernel)

private theorem pole_313_70 :
    P1_7_1.groupedPoleMoment 313 70 ≤ 276897427 :=
  _root_.PoleAffine6970.certified 313 70 276897427 (by decide) (by decide +kernel)

private theorem pole_316_71 :
    P1_7_1.groupedPoleMoment 316 71 ≤ 288620195 :=
  _root_.PoleAffine6970.certified 316 71 288620195 (by decide) (by decide +kernel)

private theorem pole_329_74 :
    P1_7_1.groupedPoleMoment 329 74 ≤ 339056834 :=
  _root_.PoleAffine6970.certified 329 74 339056834 (by decide) (by decide +kernel)

private theorem pole_333_74 :
    P1_7_1.groupedPoleMoment 333 74 ≤ 352462234 :=
  _root_.PoleAffine6970.certified 333 74 352462234 (by decide) (by decide +kernel)

private theorem pole_351_78 :
    P1_7_1.groupedPoleMoment 351 78 ≤ 434522864 :=
  _root_.PoleAffine6970.certified 351 78 434522864 (by decide) (by decide +kernel)

theorem bank_194_269_60 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨194,269,60,u⟩,228748165120,151401819⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 194 269 60 u 228748165120 151401819
    (by decide) (by decide) (by decide) (by decide) pole_269_60

theorem bank_205_284_63 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨205,284,63,u⟩,268284461056,187015104⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 205 284 63 u 268284461056 187015104
    (by decide) (by decide) (by decide) (by decide) pole_284_63

theorem bank_206_285_64 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨206,285,64,u⟩,274418892800,191426557⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 206 285 64 u 274418892800 191426557
    (by decide) (by decide) (by decide) (by decide) pole_285_64

theorem bank_216_299_67 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨216,299,67,u⟩,315650211840,231211938⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 216 299 67 u 315650211840 231211938
    (by decide) (by decide) (by decide) (by decide) pole_299_67

theorem bank_223_309_69 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨223,309,69,u⟩,346467860480,262793893⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 223 309 69 u 346467860480 262793893
    (by decide) (by decide) (by decide) (by decide) pole_309_69

theorem bank_226_313_70 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨226,313,70,u⟩,360816574464,276897427⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 226 313 70 u 360816574464 276897427
    (by decide) (by decide) (by decide) (by decide) pole_313_70

theorem bank_228_316_71 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨228,316,71,u⟩,371903692800,288620195⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 228 316 71 u 371903692800 288620195
    (by decide) (by decide) (by decide) (by decide) pole_316_71

theorem bank_237_329_74 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨237,329,74,u⟩,418217984000,339056834⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 237 329 74 u 418217984000 339056834
    (by decide) (by decide) (by decide) (by decide) pole_329_74

theorem bank_240_333_74 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨240,333,74,u⟩,430132428800,352462234⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 240 333 74 u 430132428800 352462234
    (by decide) (by decide) (by decide) (by decide) pole_333_74

theorem bank_253_351_78 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨253,351,78,u⟩,503341383680,434522864⟩ :=
  pack_R6970Height2308MainRank08_bank_checked 253 351 78 u 503341383680 434522864
    (by decide) (by decide) (by decide) (by decide) pole_351_78

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank08

section Pack_R6970Height2308MainRank09

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank09_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_356_79 :
    P1_7_1.groupedPoleMoment 356 79 ≤ 459168566 :=
  _root_.PoleAffine6970.certified 356 79 459168566 (by decide) (by decide +kernel)

private theorem pole_356_80 :
    P1_7_1.groupedPoleMoment 356 80 ≤ 463622231 :=
  _root_.PoleAffine6970.certified 356 80 463622231 (by decide) (by decide +kernel)

private theorem pole_361_82 :
    P1_7_1.groupedPoleMoment 361 82 ≤ 494119366 :=
  _root_.PoleAffine6970.certified 361 82 494119366 (by decide) (by decide +kernel)

private theorem pole_364_82 :
    P1_7_1.groupedPoleMoment 364 82 ≤ 507425511 :=
  _root_.PoleAffine6970.certified 364 82 507425511 (by decide) (by decide +kernel)

private theorem pole_370_83 :
    P1_7_1.groupedPoleMoment 370 83 ≤ 539766907 :=
  _root_.PoleAffine6970.certified 370 83 539766907 (by decide) (by decide +kernel)

private theorem pole_374_84 :
    P1_7_1.groupedPoleMoment 374 84 ≤ 563884763 :=
  _root_.PoleAffine6970.certified 374 84 563884763 (by decide) (by decide +kernel)

private theorem pole_375_83 :
    P1_7_1.groupedPoleMoment 375 83 ≤ 563531627 :=
  _root_.PoleAffine6970.certified 375 83 563531627 (by decide) (by decide +kernel)

private theorem pole_379_84 :
    P1_7_1.groupedPoleMoment 379 84 ≤ 588443813 :=
  _root_.PoleAffine6970.certified 379 84 588443813 (by decide) (by decide +kernel)

theorem bank_257_356_79 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨257,356,79,u⟩,526280294400,459168566⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 257 356 79 u 526280294400 459168566
    (by decide) (by decide) (by decide) (by decide) pole_356_79

theorem bank_257_356_80 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨257,356,80,u⟩,531259195392,463622231⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 257 356 80 u 531259195392 463622231
    (by decide) (by decide) (by decide) (by decide) pole_356_80

theorem bank_261_361_82 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨261,361,82,u⟩,560158474240,494119366⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 261 361 82 u 560158474240 494119366
    (by decide) (by decide) (by decide) (by decide) pole_361_82

theorem bank_263_364_82 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨263,364,82,u⟩,569797246976,507425511⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 263 364 82 u 569797246976 507425511
    (by decide) (by decide) (by decide) (by decide) pole_364_82

theorem bank_267_370_83 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨267,370,83,u⟩,594711412736,539766907⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 267 370 83 u 594711412736 539766907
    (by decide) (by decide) (by decide) (by decide) pole_370_83

theorem bank_270_375_83 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨270,375,83,u⟩,609740128256,563531627⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 270 375 83 u 609740128256 563531627
    (by decide) (by decide) (by decide) (by decide) pole_375_83

theorem bank_270_374_84 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨270,374,84,u⟩,615234928640,563884763⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 270 374 84 u 615234928640 563884763
    (by decide) (by decide) (by decide) (by decide) pole_374_84

theorem bank_273_379_84 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨273,379,84,u⟩,630609674240,588443813⟩ :=
  pack_R6970Height2308MainRank09_bank_checked 273 379 84 u 630609674240 588443813
    (by decide) (by decide) (by decide) (by decide) pole_379_84

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank09

section Pack_R6970Height2308MainRank10

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank10_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_378_85 :
    P1_7_1.groupedPoleMoment 378 85 ≤ 588801451 :=
  _root_.PoleAffine6970.certified 378 85 588801451 (by decide) (by decide +kernel)

private theorem pole_385_86 :
    P1_7_1.groupedPoleMoment 385 86 ≤ 630165165 :=
  _root_.PoleAffine6970.certified 385 86 630165165 (by decide) (by decide +kernel)

private theorem pole_393_87 :
    P1_7_1.groupedPoleMoment 393 87 ≤ 679182041 :=
  _root_.PoleAffine6970.certified 393 87 679182041 (by decide) (by decide +kernel)

private theorem pole_396_89 :
    P1_7_1.groupedPoleMoment 396 89 ≤ 708231392 :=
  _root_.PoleAffine6970.certified 396 89 708231392 (by decide) (by decide +kernel)

private theorem pole_399_90 :
    P1_7_1.groupedPoleMoment 399 90 ≤ 731859035 :=
  _root_.PoleAffine6970.certified 399 90 731859035 (by decide) (by decide +kernel)

private theorem pole_400_89 :
    P1_7_1.groupedPoleMoment 400 89 ≤ 731459642 :=
  _root_.PoleAffine6970.certified 400 89 731459642 (by decide) (by decide +kernel)

private theorem pole_410_92 :
    P1_7_1.groupedPoleMoment 410 92 ≤ 812253080 :=
  _root_.PoleAffine6970.certified 410 92 812253080 (by decide) (by decide +kernel)

private theorem pack_R6970Height2308MainRank10_pole_412_92 :
    P1_7_1.groupedPoleMoment 412 92 ≤ 825046098 :=
  _root_.PoleAffine6970.certified 412 92 825046098 (by decide) (by decide +kernel)

theorem bank_273_378_85 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨273,378,85,u⟩,636225060864,588801451⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 273 378 85 u 636225060864 588801451
    (by decide) (by decide) (by decide) (by decide) pole_378_85

theorem bank_278_385_86 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨278,385,86,u⟩,668383313920,630165165⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 278 385 86 u 668383313920 630165165
    (by decide) (by decide) (by decide) (by decide) pole_385_86

theorem bank_283_393_87 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨283,393,87,u⟩,701587521536,679182041⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 283 393 87 u 701587521536 679182041
    (by decide) (by decide) (by decide) (by decide) pole_393_87

theorem bank_286_396_89 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨286,396,89,u⟩,730654310400,708231392⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 286 396 89 u 730654310400 708231392
    (by decide) (by decide) (by decide) (by decide) pole_396_89

theorem bank_288_400_89 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨288,400,89,u⟩,742120488960,731459642⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 288 400 89 u 742120488960 731459642
    (by decide) (by decide) (by decide) (by decide) pole_400_89

theorem bank_288_399_90 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨288,399,90,u⟩,748358467584,731859035⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 288 399 90 u 748358467584 731859035
    (by decide) (by decide) (by decide) (by decide) pole_399_90

theorem bank_296_410_92 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨296,410,92,u⟩,808826961920,812253080⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 296 410 92 u 808826961920 812253080
    (by decide) (by decide) (by decide) (by decide) pole_410_92

theorem bank_297_412_92 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨297,412,92,u⟩,814946189312,825046098⟩ :=
  pack_R6970Height2308MainRank10_bank_checked 297 412 92 u 814946189312 825046098
    (by decide) (by decide) (by decide) (by decide) pack_R6970Height2308MainRank10_pole_412_92

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank10

section Pack_R6970Height2308MainRank11

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2308.MainFreeRank

private theorem pack_R6970Height2308MainRank11_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_417_94 :
    P1_7_1.groupedPoleMoment 417 94 ≤ 871929152 :=
  _root_.PoleAffine6970.certified 417 94 871929152 (by decide) (by decide +kernel)

private theorem pole_420_95 :
    P1_7_1.groupedPoleMoment 420 95 ≤ 899521910 :=
  _root_.PoleAffine6970.certified 420 95 899521910 (by decide) (by decide +kernel)

private theorem pole_432_95 :
    P1_7_1.groupedPoleMoment 432 95 ≤ 984695894 :=
  _root_.PoleAffine6970.certified 432 95 984695894 (by decide) (by decide +kernel)

private theorem pole_436_97 :
    P1_7_1.groupedPoleMoment 436 97 ≤ 1030674998 :=
  _root_.PoleAffine6970.certified 436 97 1030674998 (by decide) (by decide +kernel)

private theorem pole_437_98 :
    P1_7_1.groupedPoleMoment 437 98 ≤ 1046511290 :=
  _root_.PoleAffine6970.certified 437 98 1046511290 (by decide) (by decide +kernel)

private theorem pole_439_99 :
    P1_7_1.groupedPoleMoment 439 99 ≤ 1070296326 :=
  _root_.PoleAffine6970.certified 439 99 1070296326 (by decide) (by decide +kernel)

private theorem pole_444_100 :
    P1_7_1.groupedPoleMoment 444 100 ≤ 1118563842 :=
  _root_.PoleAffine6970.certified 444 100 1118563842 (by decide) (by decide +kernel)

private theorem pole_448_101 :
    P1_7_1.groupedPoleMoment 448 101 ≤ 1160104080 :=
  _root_.PoleAffine6970.certified 448 101 1160104080 (by decide) (by decide +kernel)

theorem bank_301_417_94 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨301,417,94,u⟩,853324595200,871929152⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 301 417 94 u 853324595200 871929152
    (by decide) (by decide) (by decide) (by decide) pole_417_94

theorem bank_303_420_95 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨303,420,95,u⟩,872943714304,899521910⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 303 420 95 u 872943714304 899521910
    (by decide) (by decide) (by decide) (by decide) pole_420_95

theorem bank_311_432_95 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨311,432,95,u⟩,925288628224,984695894⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 311 432 95 u 925288628224 984695894
    (by decide) (by decide) (by decide) (by decide) pole_432_95

theorem bank_314_436_97 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨314,436,97,u⟩,960257851392,1030674998⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 314 436 97 u 960257851392 1030674998
    (by decide) (by decide) (by decide) (by decide) pole_436_97

theorem bank_315_437_98 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨315,437,98,u⟩,974576418816,1046511290⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 315 437 98 u 974576418816 1046511290
    (by decide) (by decide) (by decide) (by decide) pole_437_98

theorem bank_317_439_99 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨317,439,99,u⟩,996016128000,1070296326⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 317 439 99 u 996016128000 1070296326
    (by decide) (by decide) (by decide) (by decide) pole_439_99

theorem bank_320_444_100 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨320,444,100,u⟩,1024907018240,1118563842⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 320 444 100 u 1024907018240 1118563842
    (by decide) (by decide) (by decide) (by decide) pole_444_100

theorem bank_323_448_101 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨323,448,101,u⟩,1054351032320,1160104080⟩ :=
  pack_R6970Height2308MainRank11_bank_checked 323 448 101 u 1054351032320 1160104080
    (by decide) (by decide) (by decide) (by decide) pole_448_101

end Research6970.Height2308.MainFreeRank
end Pack_R6970Height2308MainRank11

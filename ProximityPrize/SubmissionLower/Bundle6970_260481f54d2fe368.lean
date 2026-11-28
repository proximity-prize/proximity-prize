import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri

section Pack_R6970Height2313CommonRanks00

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks00_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_314_69 :
    P1_7_1.groupedPoleMoment 314 69 ≤ 276676118 :=
  _root_.PoleAffine6970.certified 314 69 276676118 (by decide) (by decide +kernel)

private theorem pole_381_83 :
    P1_7_1.groupedPoleMoment 381 83 ≤ 592977449 :=
  _root_.PoleAffine6970.certified 381 83 592977449 (by decide) (by decide +kernel)

private theorem pole_383_87 :
    P1_7_1.groupedPoleMoment 383 87 ≤ 625236061 :=
  _root_.PoleAffine6970.certified 383 87 625236061 (by decide) (by decide +kernel)

private theorem pole_449_98 :
    P1_7_1.groupedPoleMoment 449 98 ≤ 1141622570 :=
  _root_.PoleAffine6970.certified 449 98 1141622570 (by decide) (by decide +kernel)

private theorem pole_451_98 :
    P1_7_1.groupedPoleMoment 451 98 ≤ 1158025616 :=
  _root_.PoleAffine6970.certified 451 98 1158025616 (by decide) (by decide +kernel)

private theorem pole_452_98 :
    P1_7_1.groupedPoleMoment 452 98 ≤ 1166286935 :=
  _root_.PoleAffine6970.certified 452 98 1166286935 (by decide) (by decide +kernel)

private theorem pole_452_100 :
    P1_7_1.groupedPoleMoment 452 100 ≤ 1184600066 :=
  _root_.PoleAffine6970.certified 452 100 1184600066 (by decide) (by decide +kernel)

private theorem pole_453_98 :
    P1_7_1.groupedPoleMoment 453 98 ≤ 1174588250 :=
  _root_.PoleAffine6970.certified 453 98 1174588250 (by decide) (by decide +kernel)

private theorem pole_453_100 :
    P1_7_1.groupedPoleMoment 453 100 ≤ 1193036697 :=
  _root_.PoleAffine6970.certified 453 100 1193036697 (by decide) (by decide +kernel)

private theorem pole_453_102 :
    P1_7_1.groupedPoleMoment 453 102 ≤ 1211360939 :=
  _root_.PoleAffine6970.certified 453 102 1211360939 (by decide) (by decide +kernel)

theorem bank_226_314_69 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨226,314,69,u⟩,356954931200,276676118⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 226 314 69 u 356954931200 276676118
    (by decide) (by decide) (by decide) (by decide) pole_314_69

theorem bank_274_381_83 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨274,381,83,u⟩,630086696960,592977449⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 274 381 83 u 630086696960 592977449
    (by decide) (by decide) (by decide) (by decide) pole_381_83

theorem bank_276_383_87 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨276,383,87,u⟩,663397335040,625236061⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 276 383 87 u 663397335040 625236061
    (by decide) (by decide) (by decide) (by decide) pole_383_87

theorem bank_322_449_98 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨322,449,98,u⟩,1023626182656,1141622570⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 322 449 98 u 1023626182656 1141622570
    (by decide) (by decide) (by decide) (by decide) pole_449_98

theorem bank_325_451_98 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨325,451,98,u⟩,1045036793856,1158025616⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 325 451 98 u 1045036793856 1158025616
    (by decide) (by decide) (by decide) (by decide) pole_451_98

theorem bank_325_452_98 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨325,452,98,u⟩,1045036793856,1166286935⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 325 452 98 u 1045036793856 1166286935
    (by decide) (by decide) (by decide) (by decide) pole_452_98

theorem bank_326_452_100 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨326,452,100,u⟩,1068355026944,1184600066⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 326 452 100 u 1068355026944 1184600066
    (by decide) (by decide) (by decide) (by decide) pole_452_100

theorem bank_326_453_98 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨326,453,98,u⟩,1052225568768,1174588250⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 326 453 98 u 1052225568768 1174588250
    (by decide) (by decide) (by decide) (by decide) pole_453_98

theorem bank_326_453_100 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨326,453,100,u⟩,1068355026944,1193036697⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 326 453 100 u 1068355026944 1193036697
    (by decide) (by decide) (by decide) (by decide) pole_453_100

theorem bank_326_453_102 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨326,453,102,u⟩,1084353413120,1211360939⟩ :=
  pack_R6970Height2313CommonRanks00_bank_checked 326 453 102 u 1084353413120 1211360939
    (by decide) (by decide) (by decide) (by decide) pole_453_102

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks00

section Pack_R6970Height2313CommonRanks01

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks01_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_550_120 :
    P1_7_1.groupedPoleMoment 550 120 ≤ 2560837984 :=
  _root_.PoleAffine6970.certified 550 120 2560837984 (by decide) (by decide +kernel)

private theorem pole_554_123 :
    P1_7_1.groupedPoleMoment 554 123 ≤ 2671618359 :=
  _root_.PoleAffine6970.certified 554 123 2671618359 (by decide) (by decide +kernel)

private theorem pole_557_120 :
    P1_7_1.groupedPoleMoment 557 120 ≤ 2666981483 :=
  _root_.PoleAffine6970.certified 557 120 2666981483 (by decide) (by decide +kernel)

private theorem pole_558_120 :
    P1_7_1.groupedPoleMoment 558 120 ≤ 2682384904 :=
  _root_.PoleAffine6970.certified 558 120 2682384904 (by decide) (by decide +kernel)

private theorem pole_558_123 :
    P1_7_1.groupedPoleMoment 558 123 ≤ 2734096379 :=
  _root_.PoleAffine6970.certified 558 123 2734096379 (by decide) (by decide +kernel)

private theorem pole_558_126 :
    P1_7_1.groupedPoleMoment 558 126 ≤ 2785382344 :=
  _root_.PoleAffine6970.certified 558 126 2785382344 (by decide) (by decide +kernel)

private theorem pole_647_141 :
    P1_7_1.groupedPoleMoment 647 141 ≤ 4888436051 :=
  _root_.PoleAffine6970.certified 647 141 4888436051 (by decide) (by decide +kernel)

private theorem pole_651_144 :
    P1_7_1.groupedPoleMoment 651 144 ≤ 5068091922 :=
  _root_.PoleAffine6970.certified 651 144 5068091922 (by decide) (by decide +kernel)

private theorem pole_653_141 :
    P1_7_1.groupedPoleMoment 653 141 ≤ 5035569706 :=
  _root_.PoleAffine6970.certified 653 141 5035569706 (by decide) (by decide +kernel)

private theorem pole_653_144 :
    P1_7_1.groupedPoleMoment 653 144 ≤ 5118308467 :=
  _root_.PoleAffine6970.certified 653 144 5118308467 (by decide) (by decide +kernel)

theorem bank_395_550_120 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨395,550,120,u⟩,1881913425920,2560837984⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 395 550 120 u 1881913425920 2560837984
    (by decide) (by decide) (by decide) (by decide) pole_550_120

theorem bank_399_554_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨399,554,123,u⟩,1960915763200,2671618359⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 399 554 123 u 1960915763200 2671618359
    (by decide) (by decide) (by decide) (by decide) pole_554_123

theorem bank_400_557_120 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨400,557,120,u⟩,1935519252480,2666981483⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 400 557 120 u 1935519252480 2666981483
    (by decide) (by decide) (by decide) (by decide) pole_557_120

theorem bank_401_558_120 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨401,558,120,u⟩,1946335576064,2682384904⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 401 558 120 u 1946335576064 2682384904
    (by decide) (by decide) (by decide) (by decide) pole_558_120

theorem bank_402_558_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨402,558,123,u⟩,1994022977536,2734096379⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 402 558 123 u 1994022977536 2734096379
    (by decide) (by decide) (by decide) (by decide) pole_558_123

theorem bank_401_558_123 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨401,558,123,u⟩,1982954733568,2734096379⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 401 558 123 u 1982954733568 2734096379
    (by decide) (by decide) (by decide) (by decide) pole_558_123

theorem bank_401_558_126 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨401,558,126,u⟩,2019210559488,2785382344⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 401 558 126 u 2019210559488 2785382344
    (by decide) (by decide) (by decide) (by decide) pole_558_126

theorem bank_464_647_141 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨464,647,141,u⟩,3045648498688,4888436051⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 464 647 141 u 3045648498688 4888436051
    (by decide) (by decide) (by decide) (by decide) pole_647_141

theorem bank_469_651_144 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨469,651,144,u⟩,3169461207040,5068091922⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 469 651 144 u 3169461207040 5068091922
    (by decide) (by decide) (by decide) (by decide) pole_651_144

theorem bank_470_653_141 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨470,653,141,u⟩,3134317133824,5035569706⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 470 653 141 u 3134317133824 5035569706
    (by decide) (by decide) (by decide) (by decide) pole_653_141

theorem bank_470_653_144 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨470,653,144,u⟩,3184589537280,5118308467⟩ :=
  pack_R6970Height2313CommonRanks01_bank_checked 470 653 144 u 3184589537280 5118308467
    (by decide) (by decide) (by decide) (by decide) pole_653_144

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks01

section Pack_R6970Height2313CommonRanks02

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks02_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_654_141 :
    P1_7_1.groupedPoleMoment 654 141 ≤ 5060381153 :=
  _root_.PoleAffine6970.certified 654 141 5060381153 (by decide) (by decide +kernel)

private theorem pole_654_144 :
    P1_7_1.groupedPoleMoment 654 144 ≤ 5143543252 :=
  _root_.PoleAffine6970.certified 654 144 5143543252 (by decide) (by decide +kernel)

private theorem pole_655_141 :
    P1_7_1.groupedPoleMoment 655 141 ≤ 5085275599 :=
  _root_.PoleAffine6970.certified 655 141 5085275599 (by decide) (by decide +kernel)

private theorem pole_655_144 :
    P1_7_1.groupedPoleMoment 655 144 ≤ 5168862572 :=
  _root_.PoleAffine6970.certified 655 144 5168862572 (by decide) (by decide +kernel)

private theorem pole_655_145 :
    P1_7_1.groupedPoleMoment 655 145 ≤ 5196592961 :=
  _root_.PoleAffine6970.certified 655 145 5196592961 (by decide) (by decide +kernel)

private theorem pole_655_148 :
    P1_7_1.groupedPoleMoment 655 148 ≤ 5279398867 :=
  _root_.PoleAffine6970.certified 655 148 5279398867 (by decide) (by decide +kernel)

private theorem pole_755_170 :
    P1_7_1.groupedPoleMoment 755 170 ≤ 9279237547 :=
  _root_.PoleAffine6970.certified 755 170 9279237547 (by decide) (by decide +kernel)

private theorem pole_756_170 :
    P1_7_1.groupedPoleMoment 756 170 ≤ 9318832198 :=
  _root_.PoleAffine6970.certified 756 170 9318832198 (by decide) (by decide +kernel)

private theorem pole_763_170 :
    P1_7_1.groupedPoleMoment 763 170 ≤ 9599221867 :=
  _root_.PoleAffine6970.certified 763 170 9599221867 (by decide) (by decide +kernel)

private theorem pole_764_170 :
    P1_7_1.groupedPoleMoment 764 170 ≤ 9639740602 :=
  _root_.PoleAffine6970.certified 764 170 9639740602 (by decide) (by decide +kernel)

theorem bank_470_654_141 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨470,654,141,u⟩,3134317133824,5060381153⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 470 654 141 u 3134317133824 5060381153
    (by decide) (by decide) (by decide) (by decide) pole_654_141

theorem bank_471_654_144 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨471,654,144,u⟩,3199755878400,5143543252⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 471 654 144 u 3199755878400 5143543252
    (by decide) (by decide) (by decide) (by decide) pole_654_144

theorem bank_471_655_141 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨471,655,141,u⟩,3149225525248,5085275599⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 471 655 141 u 3149225525248 5085275599
    (by decide) (by decide) (by decide) (by decide) pole_655_141

theorem bank_471_655_144 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨471,655,144,u⟩,3199755878400,5168862572⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 471 655 144 u 3199755878400 5168862572
    (by decide) (by decide) (by decide) (by decide) pole_655_144

theorem bank_472_655_144 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨472,655,144,u⟩,3214960230400,5168862572⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 472 655 144 u 3214960230400 5168862572
    (by decide) (by decide) (by decide) (by decide) pole_655_144

theorem bank_472_655_145 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨472,655,145,u⟩,3231793283072,5196592961⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 472 655 145 u 3231793283072 5196592961
    (by decide) (by decide) (by decide) (by decide) pole_655_145

theorem bank_471_655_148 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨471,655,148,u⟩,3266464186368,5279398867⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 471 655 148 u 3266464186368 5279398867
    (by decide) (by decide) (by decide) (by decide) pole_655_148

theorem bank_472_655_148 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨472,655,148,u⟩,3282009849856,5279398867⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 472 655 148 u 3282009849856 5279398867
    (by decide) (by decide) (by decide) (by decide) pole_655_148

theorem bank_544_755_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨544,755,170,u⟩,5005415546880,9279237547⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 544 755 170 u 5005415546880 9279237547
    (by decide) (by decide) (by decide) (by decide) pole_755_170

theorem bank_545_756_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨545,756,170,u⟩,5026035793920,9318832198⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 545 756 170 u 5026035793920 9318832198
    (by decide) (by decide) (by decide) (by decide) pole_756_170

theorem bank_550_763_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨550,763,170,u⟩,5129809428480,9599221867⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 550 763 170 u 5129809428480 9599221867
    (by decide) (by decide) (by decide) (by decide) pole_763_170

theorem bank_551_764_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨551,764,170,u⟩,5150698635264,9639740602⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 551 764 170 u 5150698635264 9639740602
    (by decide) (by decide) (by decide) (by decide) pole_764_170

theorem bank_550_764_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨550,764,170,u⟩,5129809428480,9639740602⟩ :=
  pack_R6970Height2313CommonRanks02_bank_checked 550 764 170 u 5129809428480 9639740602
    (by decide) (by decide) (by decide) (by decide) pole_764_170

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks02

section Pack_R6970Height2313CommonRanks03

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks03_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_767_170 :
    P1_7_1.groupedPoleMoment 767 170 ≤ 9761995171 :=
  _root_.PoleAffine6970.certified 767 170 9761995171 (by decide) (by decide +kernel)

private theorem pole_770_170 :
    P1_7_1.groupedPoleMoment 770 170 ≤ 9885300877 :=
  _root_.PoleAffine6970.certified 770 170 9885300877 (by decide) (by decide +kernel)

private theorem pole_771_170 :
    P1_7_1.groupedPoleMoment 771 170 ≤ 9926637163 :=
  _root_.PoleAffine6970.certified 771 170 9926637163 (by decide) (by decide +kernel)

private theorem pole_771_171 :
    P1_7_1.groupedPoleMoment 771 171 ≤ 9971791336 :=
  _root_.PoleAffine6970.certified 771 171 9971791336 (by decide) (by decide +kernel)

private theorem pole_772_170 :
    P1_7_1.groupedPoleMoment 772 170 ≤ 9968090926 :=
  _root_.PoleAffine6970.certified 772 170 9968090926 (by decide) (by decide +kernel)

private theorem pole_772_171 :
    P1_7_1.groupedPoleMoment 772 171 ≤ 10013440706 :=
  _root_.PoleAffine6970.certified 772 171 10013440706 (by decide) (by decide +kernel)

private theorem pole_773_169 :
    P1_7_1.groupedPoleMoment 773 169 ≤ 9964025195 :=
  _root_.PoleAffine6970.certified 773 169 9964025195 (by decide) (by decide +kernel)

private theorem pole_773_170 :
    P1_7_1.groupedPoleMoment 773 170 ≤ 10009662337 :=
  _root_.PoleAffine6970.certified 773 170 10009662337 (by decide) (by decide +kernel)

private theorem pole_773_172 :
    P1_7_1.groupedPoleMoment 773 172 ≤ 10100663999 :=
  _root_.PoleAffine6970.certified 773 172 10100663999 (by decide) (by decide +kernel)

private theorem pole_777_169 :
    P1_7_1.groupedPoleMoment 777 169 ≤ 10130698125 :=
  _root_.PoleAffine6970.certified 777 169 10130698125 (by decide) (by decide +kernel)

theorem bank_553_767_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨553,767,170,u⟩,5192611528704,9761995171⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 553 767 170 u 5192611528704 9761995171
    (by decide) (by decide) (by decide) (by decide) pole_767_170

theorem bank_554_770_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨554,770,170,u⟩,5213635215360,9885300877⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 554 770 170 u 5213635215360 9885300877
    (by decide) (by decide) (by decide) (by decide) pole_770_170

theorem bank_555_770_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨555,770,170,u⟩,5234703728640,9885300877⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 555 770 170 u 5234703728640 9885300877
    (by decide) (by decide) (by decide) (by decide) pole_770_170

theorem bank_555_771_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨555,771,170,u⟩,5234703728640,9926637163⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 555 771 170 u 5234703728640 9926637163
    (by decide) (by decide) (by decide) (by decide) pole_771_170

theorem bank_556_771_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨556,771,170,u⟩,5255817068544,9926637163⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 556 771 170 u 5255817068544 9926637163
    (by decide) (by decide) (by decide) (by decide) pole_771_170

theorem bank_555_771_171 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨555,771,171,u⟩,5257936502784,9971791336⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 555 771 171 u 5257936502784 9971791336
    (by decide) (by decide) (by decide) (by decide) pole_771_171

theorem bank_556_771_171 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨556,771,171,u⟩,5279150768128,9971791336⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 556 771 171 u 5279150768128 9971791336
    (by decide) (by decide) (by decide) (by decide) pole_771_171

theorem bank_555_772_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨555,772,170,u⟩,5234703728640,9968090926⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 555 772 170 u 5234703728640 9968090926
    (by decide) (by decide) (by decide) (by decide) pole_772_170

theorem bank_556_772_171 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨556,772,171,u⟩,5279150768128,10013440706⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 556 772 171 u 5279150768128 10013440706
    (by decide) (by decide) (by decide) (by decide) pole_772_171

theorem bank_556_773_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨556,773,169,u⟩,5232427008000,9964025195⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 556 773 169 u 5232427008000 9964025195
    (by decide) (by decide) (by decide) (by decide) pole_773_169

theorem bank_557_773_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨557,773,170,u⟩,5276975235072,10009662337⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 557 773 170 u 5276975235072 10009662337
    (by decide) (by decide) (by decide) (by decide) pole_773_170

theorem bank_557_773_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨557,773,172,u⟩,5323788910592,10100663999⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 557 773 172 u 5323788910592 10100663999
    (by decide) (by decide) (by decide) (by decide) pole_773_172

theorem bank_560_777_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨560,777,169,u⟩,5316921262080,10130698125⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 560 777 169 u 5316921262080 10130698125
    (by decide) (by decide) (by decide) (by decide) pole_777_169

theorem bank_559_777_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨559,777,169,u⟩,5295730851840,10130698125⟩ :=
  pack_R6970Height2313CommonRanks03_bank_checked 559 777 169 u 5295730851840 10130698125
    (by decide) (by decide) (by decide) (by decide) pole_777_169

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks03

section Pack_R6970Height2313CommonRanks04

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks04_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_777_172 :
    P1_7_1.groupedPoleMoment 777 172 ≤ 10269709565 :=
  _root_.PoleAffine6970.certified 777 172 10269709565 (by decide) (by decide +kernel)

private theorem pole_779_169 :
    P1_7_1.groupedPoleMoment 779 169 ≤ 10214741280 :=
  _root_.PoleAffine6970.certified 779 169 10214741280 (by decide) (by decide +kernel)

private theorem pole_779_172 :
    P1_7_1.groupedPoleMoment 779 172 ≤ 10354949952 :=
  _root_.PoleAffine6970.certified 779 172 10354949952 (by decide) (by decide +kernel)

private theorem pole_780_172 :
    P1_7_1.groupedPoleMoment 780 172 ≤ 10397750152 :=
  _root_.PoleAffine6970.certified 780 172 10397750152 (by decide) (by decide +kernel)

private theorem pole_781_169 :
    P1_7_1.groupedPoleMoment 781 169 ≤ 10299257375 :=
  _root_.PoleAffine6970.certified 781 169 10299257375 (by decide) (by decide +kernel)

private theorem pole_781_170 :
    P1_7_1.groupedPoleMoment 781 170 ≤ 10346489473 :=
  _root_.PoleAffine6970.certified 781 170 10346489473 (by decide) (by decide +kernel)

private theorem pole_781_172 :
    P1_7_1.groupedPoleMoment 781 172 ≤ 10440670587 :=
  _root_.PoleAffine6970.certified 781 172 10440670587 (by decide) (by decide +kernel)

private theorem pole_781_173 :
    P1_7_1.groupedPoleMoment 781 173 ≤ 10487621483 :=
  _root_.PoleAffine6970.certified 781 173 10487621483 (by decide) (by decide +kernel)

private theorem pole_781_176 :
    P1_7_1.groupedPoleMoment 781 176 ≤ 10627925923 :=
  _root_.PoleAffine6970.certified 781 176 10627925923 (by decide) (by decide +kernel)

private theorem pole_946_212 :
    P1_7_1.groupedPoleMoment 946 212 ≤ 22737372349 :=
  _root_.PoleAffine6970.certified 946 212 22737372349 (by decide) (by decide +kernel)

theorem bank_559_777_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨559,777,172,u⟩,5366645522432,10269709565⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 559 777 172 u 5366645522432 10269709565
    (by decide) (by decide) (by decide) (by decide) pole_777_172

theorem bank_560_779_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨560,779,169,u⟩,5316921262080,10214741280⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 560 779 169 u 5316921262080 10214741280
    (by decide) (by decide) (by decide) (by decide) pole_779_169

theorem bank_561_779_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨561,779,169,u⟩,5338156236800,10214741280⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 561 779 169 u 5338156236800 10214741280
    (by decide) (by decide) (by decide) (by decide) pole_779_169

theorem bank_561_779_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨561,779,172,u⟩,5409683537920,10354949952⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 561 779 172 u 5409683537920 10354949952
    (by decide) (by decide) (by decide) (by decide) pole_779_172

theorem bank_562_780_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨562,780,172,u⟩,5431270572032,10397750152⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 562 780 172 u 5431270572032 10397750152
    (by decide) (by decide) (by decide) (by decide) pole_780_172

theorem bank_562_781_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨562,781,169,u⟩,5359435776000,10299257375⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 562 781 169 u 5359435776000 10299257375
    (by decide) (by decide) (by decide) (by decide) pole_781_169

theorem bank_561_781_169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨561,781,169,u⟩,5338156236800,10299257375⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 561 781 169 u 5338156236800 10299257375
    (by decide) (by decide) (by decide) (by decide) pole_781_169

theorem bank_560_781_170 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨560,781,170,u⟩,5340718694400,10346489473⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 560 781 170 u 5340718694400 10346489473
    (by decide) (by decide) (by decide) (by decide) pole_781_170

theorem bank_561_781_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨561,781,172,u⟩,5409683537920,10440670587⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 561 781 172 u 5409683537920 10440670587
    (by decide) (by decide) (by decide) (by decide) pole_781_172

theorem bank_562_781_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨562,781,172,u⟩,5431270572032,10440670587⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 562 781 172 u 5431270572032 10440670587
    (by decide) (by decide) (by decide) (by decide) pole_781_172

theorem bank_562_781_173 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨562,781,173,u⟩,5455101034496,10487621483⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 562 781 173 u 5455101034496 10487621483
    (by decide) (by decide) (by decide) (by decide) pole_781_173

theorem bank_562_781_176 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨562,781,176,u⟩,5526256353280,10627925923⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 562 781 176 u 5526256353280 10627925923
    (by decide) (by decide) (by decide) (by decide) pole_781_176

theorem bank_561_781_176 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨561,781,176,u⟩,5504262995968,10627925923⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 561 781 176 u 5504262995968 10627925923
    (by decide) (by decide) (by decide) (by decide) pole_781_176

theorem bank_563_781_176 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨563,781,176,u⟩,5548296110080,10627925923⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 563 781 176 u 5548296110080 10627925923
    (by decide) (by decide) (by decide) (by decide) pole_781_176

theorem bank_682_946_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨682,946,212,u⟩,9806464417792,22737372349⟩ :=
  pack_R6970Height2313CommonRanks04_bank_checked 682 946 212 u 9806464417792 22737372349
    (by decide) (by decide) (by decide) (by decide) pole_946_212

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks04

section Pack_R6970Height2313CommonRanks05

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks05_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_954_208 :
    P1_7_1.groupedPoleMoment 954 208 ≤ 23019418180 :=
  _root_.PoleAffine6970.certified 954 208 23019418180 (by decide) (by decide +kernel)

private theorem pole_954_212 :
    P1_7_1.groupedPoleMoment 954 212 ≤ 23361831549 :=
  _root_.PoleAffine6970.certified 954 212 23361831549 (by decide) (by decide +kernel)

private theorem pole_955_208 :
    P1_7_1.groupedPoleMoment 955 208 ≤ 23097088014 :=
  _root_.PoleAffine6970.certified 955 208 23097088014 (by decide) (by decide +kernel)

private theorem pole_958_208 :
    P1_7_1.groupedPoleMoment 958 208 ≤ 23331166760 :=
  _root_.PoleAffine6970.certified 958 208 23331166760 (by decide) (by decide +kernel)

private theorem pole_958_212 :
    P1_7_1.groupedPoleMoment 958 212 ≤ 23678394421 :=
  _root_.PoleAffine6970.certified 958 212 23678394421 (by decide) (by decide +kernel)

private theorem pole_959_208 :
    P1_7_1.groupedPoleMoment 959 208 ≤ 23409550120 :=
  _root_.PoleAffine6970.certified 959 208 23409550120 (by decide) (by decide +kernel)

private theorem pole_960_208 :
    P1_7_1.groupedPoleMoment 960 208 ≤ 23488112384 :=
  _root_.PoleAffine6970.certified 960 208 23488112384 (by decide) (by decide +kernel)

private theorem pole_960_212 :
    P1_7_1.groupedPoleMoment 960 212 ≤ 23837765139 :=
  _root_.PoleAffine6970.certified 960 212 23837765139 (by decide) (by decide +kernel)

private theorem pole_961_208 :
    P1_7_1.groupedPoleMoment 961 208 ≤ 23566853761 :=
  _root_.PoleAffine6970.certified 961 208 23566853761 (by decide) (by decide +kernel)

private theorem pole_962_208 :
    P1_7_1.groupedPoleMoment 962 208 ≤ 23645774460 :=
  _root_.PoleAffine6970.certified 962 208 23645774460 (by decide) (by decide +kernel)

theorem bank_684_954_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨684,954,208,u⟩,9729817968640,23019418180⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 684 954 208 u 9729817968640 23019418180
    (by decide) (by decide) (by decide) (by decide) pole_954_208

theorem bank_686_954_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨686,954,208,u⟩,9793536524288,23019418180⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 686 954 208 u 9793536524288 23019418180
    (by decide) (by decide) (by decide) (by decide) pole_954_208

theorem bank_687_954_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨687,954,212,u⟩,9968111583232,23361831549⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 687 954 212 u 9968111583232 23361831549
    (by decide) (by decide) (by decide) (by decide) pole_954_212

theorem bank_687_955_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨687,955,208,u⟩,9825477984256,23097088014⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 687 955 208 u 9825477984256 23097088014
    (by decide) (by decide) (by decide) (by decide) pole_955_208

theorem bank_685_955_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨685,955,208,u⟩,9761649852416,23097088014⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 685 955 208 u 9761649852416 23097088014
    (by decide) (by decide) (by decide) (by decide) pole_955_208

theorem bank_690_958_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨690,958,208,u⟩,9921631092736,23331166760⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 690 958 208 u 9921631092736 23331166760
    (by decide) (by decide) (by decide) (by decide) pole_958_208

theorem bank_690_958_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨690,958,212,u⟩,10065769922560,23678394421⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 690 958 212 u 10065769922560 23678394421
    (by decide) (by decide) (by decide) (by decide) pole_958_212

theorem bank_690_959_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨690,959,208,u⟩,9921631092736,23409550120⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 690 959 208 u 9921631092736 23409550120
    (by decide) (by decide) (by decide) (by decide) pole_959_208

theorem bank_690_960_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨690,960,208,u⟩,9921631092736,23488112384⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 690 960 208 u 9921631092736 23488112384
    (by decide) (by decide) (by decide) (by decide) pole_960_208

theorem bank_691_960_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,960,212,u⟩,10098434375680,23837765139⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 691 960 212 u 10098434375680 23837765139
    (by decide) (by decide) (by decide) (by decide) pole_960_212

theorem bank_691_961_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,961,208,u⟩,9953791705088,23566853761⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 691 961 208 u 9953791705088 23566853761
    (by decide) (by decide) (by decide) (by decide) pole_961_208

theorem bank_690_961_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨690,961,208,u⟩,9921631092736,23566853761⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 690 961 208 u 9921631092736 23566853761
    (by decide) (by decide) (by decide) (by decide) pole_961_208

theorem bank_692_962_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,962,208,u⟩,9986007105536,23645774460⟩ :=
  pack_R6970Height2313CommonRanks05_bank_checked 692 962 208 u 9986007105536 23645774460
    (by decide) (by decide) (by decide) (by decide) pole_962_208

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks05

section Pack_R6970Height2313CommonRanks06

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks06_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_962_209 :
    P1_7_1.groupedPoleMoment 962 209 ≤ 23734012058 :=
  _root_.PoleAffine6970.certified 962 209 23734012058 (by decide) (by decide +kernel)

private theorem pole_962_212 :
    P1_7_1.groupedPoleMoment 962 212 ≤ 23997864317 :=
  _root_.PoleAffine6970.certified 962 212 23997864317 (by decide) (by decide +kernel)

private theorem pole_962_213 :
    P1_7_1.groupedPoleMoment 962 213 ≤ 24085532067 :=
  _root_.PoleAffine6970.certified 962 213 24085532067 (by decide) (by decide +kernel)

private theorem pole_962_214 :
    P1_7_1.groupedPoleMoment 962 214 ≤ 24173060093 :=
  _root_.PoleAffine6970.certified 962 214 24173060093 (by decide) (by decide +kernel)

private theorem pole_962_217 :
    P1_7_1.groupedPoleMoment 962 217 ≤ 24434817260 :=
  _root_.PoleAffine6970.certified 962 217 24434817260 (by decide) (by decide +kernel)

private theorem pole_963_208 :
    P1_7_1.groupedPoleMoment 963 208 ≤ 23724874690 :=
  _root_.PoleAffine6970.certified 963 208 23724874690 (by decide) (by decide +kernel)

private theorem pole_963_212 :
    P1_7_1.groupedPoleMoment 963 212 ≤ 24078187611 :=
  _root_.PoleAffine6970.certified 963 212 24078187611 (by decide) (by decide +kernel)

private theorem pole_963_217 :
    P1_7_1.groupedPoleMoment 963 217 ≤ 24516657294 :=
  _root_.PoleAffine6970.certified 963 217 24516657294 (by decide) (by decide +kernel)

private theorem pole_982_216 :
    P1_7_1.groupedPoleMoment 982 216 ≤ 26013996872 :=
  _root_.PoleAffine6970.certified 982 216 26013996872 (by decide) (by decide +kernel)

private theorem pole_1001_214 :
    P1_7_1.groupedPoleMoment 1001 214 ≤ 27467889943 :=
  _root_.PoleAffine6970.certified 1001 214 27467889943 (by decide) (by decide +kernel)

theorem bank_692_962_209 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,962,209,u⟩,10022400819200,23734012058⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 962 209 u 10022400819200 23734012058
    (by decide) (by decide) (by decide) (by decide) pole_962_209

theorem bank_691_962_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,962,212,u⟩,10098434375680,23997864317⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 691 962 212 u 10098434375680 23997864317
    (by decide) (by decide) (by decide) (by decide) pole_962_212

theorem bank_692_962_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,962,212,u⟩,10131154665472,23997864317⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 962 212 u 10131154665472 23997864317
    (by decide) (by decide) (by decide) (by decide) pole_962_212

theorem bank_693_962_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨693,962,212,u⟩,10163930791936,23997864317⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 693 962 212 u 10163930791936 23997864317
    (by decide) (by decide) (by decide) (by decide) pole_962_212

theorem bank_693_962_213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨693,962,213,u⟩,10200167219200,24085532067⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 693 962 213 u 10200167219200 24085532067
    (by decide) (by decide) (by decide) (by decide) pole_962_213

theorem bank_693_962_214 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨693,962,214,u⟩,10236333916160,24173060093⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 693 962 214 u 10236333916160 24173060093
    (by decide) (by decide) (by decide) (by decide) pole_962_214

theorem bank_692_962_214 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,962,214,u⟩,10203306393600,24173060093⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 962 214 u 10203306393600 24173060093
    (by decide) (by decide) (by decide) (by decide) pole_962_214

theorem bank_692_962_217 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,962,217,u⟩,10311018217472,24434817260⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 962 217 u 10311018217472 24434817260
    (by decide) (by decide) (by decide) (by decide) pole_962_217

theorem bank_691_962_217 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,962,217,u⟩,10277672714240,24434817260⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 691 962 217 u 10277672714240 24434817260
    (by decide) (by decide) (by decide) (by decide) pole_962_217

theorem bank_693_962_217 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨693,962,217,u⟩,10344420868096,24434817260⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 693 962 217 u 10344420868096 24434817260
    (by decide) (by decide) (by decide) (by decide) pole_962_217

theorem bank_691_963_208 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,963,208,u⟩,9953791705088,23724874690⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 691 963 208 u 9953791705088 23724874690
    (by decide) (by decide) (by decide) (by decide) pole_963_208

theorem bank_693_963_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨693,963,212,u⟩,10163930791936,24078187611⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 693 963 212 u 10163930791936 24078187611
    (by decide) (by decide) (by decide) (by decide) pole_963_212

theorem bank_692_963_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,963,212,u⟩,10131154665472,24078187611⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 963 212 u 10131154665472 24078187611
    (by decide) (by decide) (by decide) (by decide) pole_963_212

theorem bank_691_963_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨691,963,212,u⟩,10098434375680,24078187611⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 691 963 212 u 10098434375680 24078187611
    (by decide) (by decide) (by decide) (by decide) pole_963_212

theorem bank_694_963_212 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨694,963,212,u⟩,10196762755072,24078187611⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 694 963 212 u 10196762755072 24078187611
    (by decide) (by decide) (by decide) (by decide) pole_963_212

theorem bank_692_963_217 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨692,963,217,u⟩,10311018217472,24516657294⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 692 963 217 u 10311018217472 24516657294
    (by decide) (by decide) (by decide) (by decide) pole_963_217

theorem bank_705_982_216 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨705,982,216,u⟩,10712231706624,26013996872⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 705 982 216 u 10712231706624 26013996872
    (by decide) (by decide) (by decide) (by decide) pole_982_216

theorem bank_720_1001_214 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨720,1001,214,u⟩,11149381468160,27467889943⟩ :=
  pack_R6970Height2313CommonRanks06_bank_checked 720 1001 214 u 11149381468160 27467889943
    (by decide) (by decide) (by decide) (by decide) pole_1001_214

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks06

section Pack_R6970Height2313CommonRanks07

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks07_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1002_221 :
    P1_7_1.groupedPoleMoment 1002 221 ≤ 28253679740 :=
  _root_.PoleAffine6970.certified 1002 221 28253679740 (by decide) (by decide +kernel)

private theorem pole_1135_248 :
    P1_7_1.groupedPoleMoment 1135 248 ≤ 46132494262 :=
  _root_.PoleAffine6970.certified 1135 248 46132494262 (by decide) (by decide +kernel)

private theorem pole_1135_253 :
    P1_7_1.groupedPoleMoment 1135 253 ≤ 46852217617 :=
  _root_.PoleAffine6970.certified 1135 253 46852217617 (by decide) (by decide +kernel)

private theorem pole_1142_248 :
    P1_7_1.groupedPoleMoment 1142 248 ≤ 47053737158 :=
  _root_.PoleAffine6970.certified 1142 248 47053737158 (by decide) (by decide +kernel)

private theorem pole_1143_248 :
    P1_7_1.groupedPoleMoment 1143 248 ≤ 47186356218 :=
  _root_.PoleAffine6970.certified 1143 248 47186356218 (by decide) (by decide +kernel)

private theorem pole_1143_253 :
    P1_7_1.groupedPoleMoment 1143 253 ≤ 47923151213 :=
  _root_.PoleAffine6970.certified 1143 253 47923151213 (by decide) (by decide +kernel)

private theorem pole_1147_248 :
    P1_7_1.groupedPoleMoment 1147 248 ≤ 47719374748 :=
  _root_.PoleAffine6970.certified 1147 248 47719374748 (by decide) (by decide +kernel)

private theorem pole_1147_253 :
    P1_7_1.groupedPoleMoment 1147 253 ≤ 48464812563 :=
  _root_.PoleAffine6970.certified 1147 253 48464812563 (by decide) (by decide +kernel)

private theorem pole_1149_248 :
    P1_7_1.groupedPoleMoment 1149 248 ≤ 47987412873 :=
  _root_.PoleAffine6970.certified 1149 248 47987412873 (by decide) (by decide +kernel)

private theorem pole_1149_254 :
    P1_7_1.groupedPoleMoment 1149 254 ≤ 48886547370 :=
  _root_.PoleAffine6970.certified 1149 254 48886547370 (by decide) (by decide +kernel)

theorem bank_722_1002_221 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨722,1002,221,u⟩,11495983022080,28253679740⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 722 1002 221 u 11495983022080 28253679740
    (by decide) (by decide) (by decide) (by decide) pole_1002_221

theorem bank_814_1135_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨814,1135,248,u⟩,16404081541120,46132494262⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 814 1135 248 u 16404081541120 46132494262
    (by decide) (by decide) (by decide) (by decide) pole_1135_248

theorem bank_817_1135_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨817,1135,253,u⟩,16791364960256,46852217617⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 817 1135 253 u 16791364960256 46852217617
    (by decide) (by decide) (by decide) (by decide) pole_1135_253

theorem bank_819_1142_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨819,1142,248,u⟩,16630255452160,47053737158⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 819 1142 248 u 16630255452160 47053737158
    (by decide) (by decide) (by decide) (by decide) pole_1142_248

theorem bank_822_1143_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨822,1143,248,u⟩,16766743085056,47186356218⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 822 1143 248 u 16766743085056 47186356218
    (by decide) (by decide) (by decide) (by decide) pole_1143_248

theorem bank_825_1143_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨825,1143,248,u⟩,16903818182656,47186356218⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 825 1143 248 u 16903818182656 47186356218
    (by decide) (by decide) (by decide) (by decide) pole_1143_248

theorem bank_823_1143_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨823,1143,253,u⟩,17068623134720,47923151213⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 823 1143 253 u 17068623134720 47923151213
    (by decide) (by decide) (by decide) (by decide) pole_1143_253

theorem bank_825_1147_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨825,1147,248,u⟩,16903818182656,47719374748⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 825 1147 248 u 16903818182656 47719374748
    (by decide) (by decide) (by decide) (by decide) pole_1147_248

theorem bank_825_1147_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨825,1147,253,u⟩,17161575202816,48464812563⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 825 1147 253 u 17161575202816 48464812563
    (by decide) (by decide) (by decide) (by decide) pole_1147_253

theorem bank_825_1149_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨825,1149,248,u⟩,16903818182656,47987412873⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 825 1149 248 u 16903818182656 47987412873
    (by decide) (by decide) (by decide) (by decide) pole_1149_248

theorem bank_828_1149_254 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1149,254,u⟩,17353252536320,48886547370⟩ :=
  pack_R6970Height2313CommonRanks07_bank_checked 828 1149 254 u 17353252536320 48886547370
    (by decide) (by decide) (by decide) (by decide) pole_1149_254

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks07

section Pack_R6970Height2313CommonRanks08

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks08_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1149_255 :
    P1_7_1.groupedPoleMoment 1149 255 ≤ 49035695912 :=
  _root_.PoleAffine6970.certified 1149 255 49035695912 (by decide) (by decide +kernel)

private theorem pole_1150_253 :
    P1_7_1.groupedPoleMoment 1150 253 ≤ 48873782027 :=
  _root_.PoleAffine6970.certified 1150 253 48873782027 (by decide) (by decide +kernel)

private theorem pole_1150_260 :
    P1_7_1.groupedPoleMoment 1150 260 ≤ 49918096074 :=
  _root_.PoleAffine6970.certified 1150 260 49918096074 (by decide) (by decide +kernel)

private theorem pole_1151_248 :
    P1_7_1.groupedPoleMoment 1151 248 ≤ 48256472894 :=
  _root_.PoleAffine6970.certified 1151 248 48256472894 (by decide) (by decide +kernel)

private theorem pole_1151_250 :
    P1_7_1.groupedPoleMoment 1151 250 ≤ 48558751904 :=
  _root_.PoleAffine6970.certified 1151 250 48558751904 (by decide) (by decide +kernel)

private theorem pole_1151_253 :
    P1_7_1.groupedPoleMoment 1151 253 ≤ 49010625289 :=
  _root_.PoleAffine6970.certified 1151 253 49010625289 (by decide) (by decide +kernel)

private theorem pole_1151_255 :
    P1_7_1.groupedPoleMoment 1151 255 ≤ 49310859688 :=
  _root_.PoleAffine6970.certified 1151 255 49310859688 (by decide) (by decide +kernel)

private theorem pole_1151_260 :
    P1_7_1.groupedPoleMoment 1151 260 ≤ 50057971890 :=
  _root_.PoleAffine6970.certified 1151 260 50057971890 (by decide) (by decide +kernel)

private theorem pole_1152_254 :
    P1_7_1.groupedPoleMoment 1152 254 ≤ 49298382825 :=
  _root_.PoleAffine6970.certified 1152 254 49298382825 (by decide) (by decide +kernel)

private theorem pole_1363_296 :
    P1_7_1.groupedPoleMoment 1363 296 ≤ 95368174997 :=
  _root_.PoleAffine6970.certified 1363 296 95368174997 (by decide) (by decide +kernel)

theorem bank_826_1149_255 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨826,1149,255,u⟩,17310966349824,49035695912⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 826 1149 255 u 17310966349824 49035695912
    (by decide) (by decide) (by decide) (by decide) pole_1149_255

theorem bank_826_1150_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨826,1150,253,u⟩,17208151113728,48873782027⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 826 1150 253 u 17208151113728 48873782027
    (by decide) (by decide) (by decide) (by decide) pole_1150_253

theorem bank_828_1150_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1150,253,u⟩,17301502689280,48873782027⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1150 253 u 17301502689280 48873782027
    (by decide) (by decide) (by decide) (by decide) pole_1150_253

theorem bank_828_1150_260 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1150,260,u⟩,17662013865984,49918096074⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1150 260 u 17662013865984 49918096074
    (by decide) (by decide) (by decide) (by decide) pole_1150_260

theorem bank_829_1150_260 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨829,1150,260,u⟩,17709839155200,49918096074⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 829 1150 260 u 17709839155200 49918096074
    (by decide) (by decide) (by decide) (by decide) pole_1150_260

theorem bank_826_1151_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨826,1151,248,u⟩,16949640429568,48256472894⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 826 1151 248 u 16949640429568 48256472894
    (by decide) (by decide) (by decide) (by decide) pole_1151_248

theorem bank_827_1151_248 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨827,1151,248,u⟩,16995527950336,48256472894⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 827 1151 248 u 16995527950336 48256472894
    (by decide) (by decide) (by decide) (by decide) pole_1151_248

theorem bank_828_1151_250 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1151,250,u⟩,17145746161664,48558751904⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1151 250 u 17145746161664 48558751904
    (by decide) (by decide) (by decide) (by decide) pole_1151_250

theorem bank_828_1151_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1151,253,u⟩,17301502689280,49010625289⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1151 253 u 17301502689280 49010625289
    (by decide) (by decide) (by decide) (by decide) pole_1151_253

theorem bank_827_1151_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨827,1151,253,u⟩,17254793609216,49010625289⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 827 1151 253 u 17254793609216 49010625289
    (by decide) (by decide) (by decide) (by decide) pole_1151_253

theorem bank_826_1151_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨826,1151,253,u⟩,17208151113728,49010625289⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 826 1151 253 u 17208151113728 49010625289
    (by decide) (by decide) (by decide) (by decide) pole_1151_253

theorem bank_829_1151_253 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨829,1151,253,u⟩,17348278353920,49010625289⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 829 1151 253 u 17348278353920 49010625289
    (by decide) (by decide) (by decide) (by decide) pole_1151_253

theorem bank_829_1151_255 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨829,1151,255,u⟩,17451995627520,49310859688⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 829 1151 255 u 17451995627520 49310859688
    (by decide) (by decide) (by decide) (by decide) pole_1151_255

theorem bank_826_1151_260 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨826,1151,260,u⟩,17566568546304,50057971890⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 826 1151 260 u 17566568546304 50057971890
    (by decide) (by decide) (by decide) (by decide) pole_1151_260

theorem bank_827_1151_260 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨827,1151,260,u⟩,17614256996352,50057971890⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 827 1151 260 u 17614256996352 50057971890
    (by decide) (by decide) (by decide) (by decide) pole_1151_260

theorem bank_828_1151_260 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1151,260,u⟩,17662013865984,50057971890⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1151 260 u 17662013865984 50057971890
    (by decide) (by decide) (by decide) (by decide) pole_1151_260

theorem bank_828_1152_254 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1152,254,u⟩,17353252536320,49298382825⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 828 1152 254 u 17353252536320 49298382825
    (by decide) (by decide) (by decide) (by decide) pole_1152_254

theorem bank_981_1363_296 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨981,1363,296,u⟩,28475152662528,95368174997⟩ :=
  pack_R6970Height2313CommonRanks08_bank_checked 981 1363 296 u 28475152662528 95368174997
    (by decide) (by decide) (by decide) (by decide) pole_1363_296

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks08

section Pack_R6970Height2313CommonRanks09

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks09_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1363_301 :
    P1_7_1.groupedPoleMoment 1363 301 ≤ 96617256623 :=
  _root_.PoleAffine6970.certified 1363 301 96617256623 (by decide) (by decide +kernel)

private theorem pole_1377_296 :
    P1_7_1.groupedPoleMoment 1377 296 ≤ 98554239032 :=
  _root_.PoleAffine6970.certified 1377 296 98554239032 (by decide) (by decide +kernel)

private theorem pole_1379_296 :
    P1_7_1.groupedPoleMoment 1379 296 ≤ 99015216989 :=
  _root_.PoleAffine6970.certified 1379 296 99015216989 (by decide) (by decide +kernel)

private theorem pole_1379_301 :
    P1_7_1.groupedPoleMoment 1379 301 ≤ 100313940775 :=
  _root_.PoleAffine6970.certified 1379 301 100313940775 (by decide) (by decide +kernel)

private theorem pole_1379_307 :
    P1_7_1.groupedPoleMoment 1379 307 ≤ 101862721867 :=
  _root_.PoleAffine6970.certified 1379 307 101862721867 (by decide) (by decide +kernel)

private theorem pole_1386_307 :
    P1_7_1.groupedPoleMoment 1386 307 ≤ 103536241407 :=
  _root_.PoleAffine6970.certified 1386 307 103536241407 (by decide) (by decide +kernel)

private theorem pole_1387_296 :
    P1_7_1.groupedPoleMoment 1387 296 ≤ 100873788737 :=
  _root_.PoleAffine6970.certified 1387 296 100873788737 (by decide) (by decide +kernel)

private theorem pole_1387_301 :
    P1_7_1.groupedPoleMoment 1387 301 ≤ 102197851203 :=
  _root_.PoleAffine6970.certified 1387 301 102197851203 (by decide) (by decide +kernel)

private theorem pole_1387_307 :
    P1_7_1.groupedPoleMoment 1387 307 ≤ 103776832835 :=
  _root_.PoleAffine6970.certified 1387 307 103776832835 (by decide) (by decide +kernel)

private theorem pole_1391_297 :
    P1_7_1.groupedPoleMoment 1391 297 ≤ 102079893052 :=
  _root_.PoleAffine6970.certified 1391 297 102079893052 (by decide) (by decide +kernel)

theorem bank_981_1363_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨981,1363,301,u⟩,28839211696128,96617256623⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 981 1363 301 u 28839211696128 96617256623
    (by decide) (by decide) (by decide) (by decide) pole_1363_301

theorem bank_987_1377_296 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨987,1377,296,u⟩,28865915781120,98554239032⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 987 1377 296 u 28865915781120 98554239032
    (by decide) (by decide) (by decide) (by decide) pole_1377_296

theorem bank_989_1379_296 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨989,1379,296,u⟩,28996793008128,99015216989⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 989 1379 296 u 28996793008128 99015216989
    (by decide) (by decide) (by decide) (by decide) pole_1379_296

theorem bank_992_1379_296 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨992,1379,296,u⟩,29193692774400,99015216989⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 992 1379 296 u 29193692774400 99015216989
    (by decide) (by decide) (by decide) (by decide) pole_1379_296

theorem bank_989_1379_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨989,1379,301,u⟩,29368050515968,100313940775⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 989 1379 301 u 29368050515968 100313940775
    (by decide) (by decide) (by decide) (by decide) pole_1379_301

theorem bank_992_1379_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨992,1379,301,u⟩,29567671336960,100313940775⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 992 1379 301 u 29567671336960 100313940775
    (by decide) (by decide) (by decide) (by decide) pole_1379_301

theorem bank_993_1379_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨993,1379,307,u⟩,30080867762176,101862721867⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 993 1379 307 u 30080867762176 101862721867
    (by decide) (by decide) (by decide) (by decide) pole_1379_307

theorem bank_994_1379_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨994,1379,307,u⟩,30148730028032,101862721867⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 994 1379 307 u 30148730028032 101862721867
    (by decide) (by decide) (by decide) (by decide) pole_1379_307

theorem bank_1000_1386_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1386,307,u⟩,30557599170560,103536241407⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 1000 1386 307 u 30557599170560 103536241407
    (by decide) (by decide) (by decide) (by decide) pole_1386_307

theorem bank_994_1387_296 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨994,1387,296,u⟩,29325348569088,100873788737⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 994 1387 296 u 29325348569088 100873788737
    (by decide) (by decide) (by decide) (by decide) pole_1387_296

theorem bank_998_1387_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨998,1387,301,u⟩,29969050501120,102197851203⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 998 1387 301 u 29969050501120 102197851203
    (by decide) (by decide) (by decide) (by decide) pole_1387_301

theorem bank_1000_1387_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1387,301,u⟩,30103476895744,102197851203⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 1000 1387 301 u 30103476895744 102197851203
    (by decide) (by decide) (by decide) (by decide) pole_1387_301

theorem bank_999_1387_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨999,1387,307,u⟩,30489252462592,103776832835⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 999 1387 307 u 30489252462592 103776832835
    (by decide) (by decide) (by decide) (by decide) pole_1387_307

theorem bank_1000_1391_297 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1391,297,u⟩,29798654279680,102079893052⟩ :=
  pack_R6970Height2313CommonRanks09_bank_checked 1000 1391 297 u 29798654279680 102079893052
    (by decide) (by decide) (by decide) (by decide) pole_1391_297

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks09

section Pack_R6970Height2313CommonRanks10

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks10_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1391_301 :
    P1_7_1.groupedPoleMoment 1391 301 ≤ 103148766153 :=
  _root_.PoleAffine6970.certified 1391 301 103148766153 (by decide) (by decide +kernel)

private theorem pole_1391_304 :
    P1_7_1.groupedPoleMoment 1391 304 ≤ 103947228761 :=
  _root_.PoleAffine6970.certified 1391 304 103947228761 (by decide) (by decide +kernel)

private theorem pole_1391_307 :
    P1_7_1.groupedPoleMoment 1391 307 ≤ 104743003887 :=
  _root_.PoleAffine6970.certified 1391 307 104743003887 (by decide) (by decide +kernel)

private theorem pole_1393_301 :
    P1_7_1.groupedPoleMoment 1393 301 ≤ 103626472018 :=
  _root_.PoleAffine6970.certified 1393 301 103626472018 (by decide) (by decide +kernel)

private theorem pole_1393_309 :
    P1_7_1.groupedPoleMoment 1393 309 ≤ 105759965279 :=
  _root_.PoleAffine6970.certified 1393 309 105759965279 (by decide) (by decide +kernel)

private theorem pole_1393_311 :
    P1_7_1.groupedPoleMoment 1393 311 ≤ 106290385107 :=
  _root_.PoleAffine6970.certified 1393 311 106290385107 (by decide) (by decide +kernel)

private theorem pole_1394_305 :
    P1_7_1.groupedPoleMoment 1394 305 ≤ 104937588728 :=
  _root_.PoleAffine6970.certified 1394 305 104937588728 (by decide) (by decide +kernel)

private theorem pole_1394_307 :
    P1_7_1.groupedPoleMoment 1394 307 ≤ 105471636407 :=
  _root_.PoleAffine6970.certified 1394 307 105471636407 (by decide) (by decide +kernel)

private theorem pole_1394_308 :
    P1_7_1.groupedPoleMoment 1394 308 ≤ 105738215253 :=
  _root_.PoleAffine6970.certified 1394 308 105738215253 (by decide) (by decide +kernel)

private theorem pole_1394_315 :
    P1_7_1.groupedPoleMoment 1394 315 ≤ 107596110457 :=
  _root_.PoleAffine6970.certified 1394 315 107596110457 (by decide) (by decide +kernel)

theorem bank_1000_1391_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1391,301,u⟩,30103476895744,103148766153⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1000 1391 301 u 30103476895744 103148766153
    (by decide) (by decide) (by decide) (by decide) pole_1391_301

theorem bank_1000_1391_304 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1391,304,u⟩,30330999275520,103947228761⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1000 1391 304 u 30330999275520 103947228761
    (by decide) (by decide) (by decide) (by decide) pole_1391_304

theorem bank_1000_1391_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1000,1391,307,u⟩,30557599170560,104743003887⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1000 1391 307 u 30557599170560 104743003887
    (by decide) (by decide) (by decide) (by decide) pole_1391_307

theorem bank_1002_1391_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1391,307,u⟩,30694534807552,104743003887⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1002 1391 307 u 30694534807552 104743003887
    (by decide) (by decide) (by decide) (by decide) pole_1391_307

theorem bank_1002_1393_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1393,301,u⟩,30238219960320,103626472018⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1002 1393 301 u 30238219960320 103626472018
    (by decide) (by decide) (by decide) (by decide) pole_1393_301

theorem bank_1002_1393_309 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1393,309,u⟩,30845822566400,105759965279⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1002 1393 309 u 30845822566400 105759965279
    (by decide) (by decide) (by decide) (by decide) pole_1393_309

theorem bank_1002_1393_311 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1393,311,u⟩,30996708720640,106290385107⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1002 1393 311 u 30996708720640 106290385107
    (by decide) (by decide) (by decide) (by decide) pole_1393_311

theorem bank_1003_1394_305 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1003,1394,305,u⟩,30611065012224,104937588728⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1003 1394 305 u 30611065012224 104937588728
    (by decide) (by decide) (by decide) (by decide) pole_1394_305

theorem bank_1002_1394_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1394,307,u⟩,30694534807552,105471636407⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1002 1394 307 u 30694534807552 105471636407
    (by decide) (by decide) (by decide) (by decide) pole_1394_307

theorem bank_1004_1394_308 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1394,308,u⟩,30907852390400,105738215253⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1004 1394 308 u 30907852390400 105738215253
    (by decide) (by decide) (by decide) (by decide) pole_1394_308

theorem bank_1003_1394_315 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1003,1394,315,u⟩,31367332102144,107596110457⟩ :=
  pack_R6970Height2313CommonRanks10_bank_checked 1003 1394 315 u 31367332102144 107596110457
    (by decide) (by decide) (by decide) (by decide) pole_1394_315

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks10

section Pack_R6970Height2313CommonRanks11

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks11_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1395_301 :
    P1_7_1.groupedPoleMoment 1395 301 ≤ 104105680031 :=
  _root_.PoleAffine6970.certified 1395 301 104105680031 (by decide) (by decide +kernel)

private theorem pole_1395_302 :
    P1_7_1.groupedPoleMoment 1395 302 ≤ 104374703492 :=
  _root_.PoleAffine6970.certified 1395 302 104374703492 (by decide) (by decide +kernel)

private theorem pole_1395_303 :
    P1_7_1.groupedPoleMoment 1395 303 ≤ 104643421994 :=
  _root_.PoleAffine6970.certified 1395 303 104643421994 (by decide) (by decide +kernel)

private theorem pole_1395_305 :
    P1_7_1.groupedPoleMoment 1395 305 ≤ 105179950418 :=
  _root_.PoleAffine6970.certified 1395 305 105179950418 (by decide) (by decide +kernel)

private theorem pole_1395_307 :
    P1_7_1.groupedPoleMoment 1395 307 ≤ 105715278267 :=
  _root_.PoleAffine6970.certified 1395 307 105715278267 (by decide) (by decide +kernel)

private theorem pole_1395_308 :
    P1_7_1.groupedPoleMoment 1395 308 ≤ 105982496027 :=
  _root_.PoleAffine6970.certified 1395 308 105982496027 (by decide) (by decide +kernel)

private theorem pole_1395_309 :
    P1_7_1.groupedPoleMoment 1395 309 ≤ 106249418544 :=
  _root_.PoleAffine6970.certified 1395 309 106249418544 (by decide) (by decide +kernel)

private theorem pole_1395_315 :
    P1_7_1.groupedPoleMoment 1395 315 ≤ 107844841957 :=
  _root_.PoleAffine6970.certified 1395 315 107844841957 (by decide) (by decide +kernel)

private theorem pole_1396_314 :
    P1_7_1.groupedPoleMoment 1396 314 ≤ 107828145918 :=
  _root_.PoleAffine6970.certified 1396 314 107828145918 (by decide) (by decide +kernel)

private theorem pole_1422_313 :
    P1_7_1.groupedPoleMoment 1422 313 ≤ 114143855256 :=
  _root_.PoleAffine6970.certified 1422 313 114143855256 (by decide) (by decide +kernel)

theorem bank_1002_1395_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1395,301,u⟩,30238219960320,104105680031⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1002 1395 301 u 30238219960320 104105680031
    (by decide) (by decide) (by decide) (by decide) pole_1395_301

theorem bank_1003_1395_301 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1003,1395,301,u⟩,30305710243840,104105680031⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1003 1395 301 u 30305710243840 104105680031
    (by decide) (by decide) (by decide) (by decide) pole_1395_301

theorem bank_1004_1395_302 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,302,u⟩,30449958387712,104374703492⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 302 u 30449958387712 104374703492
    (by decide) (by decide) (by decide) (by decide) pole_1395_302

theorem bank_1004_1395_303 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,303,u⟩,30526532485120,104643421994⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 303 u 30526532485120 104643421994
    (by decide) (by decide) (by decide) (by decide) pole_1395_303

theorem bank_1004_1395_305 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,305,u⟩,30679368990720,105179950418⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 305 u 30679368990720 105179950418
    (by decide) (by decide) (by decide) (by decide) pole_1395_305

theorem bank_1001_1395_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1001,1395,307,u⟩,30626026618880,105715278267⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1001 1395 307 u 30626026618880 105715278267
    (by decide) (by decide) (by decide) (by decide) pole_1395_307

theorem bank_1005_1395_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1005,1395,307,u⟩,30900543815680,105715278267⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1005 1395 307 u 30900543815680 105715278267
    (by decide) (by decide) (by decide) (by decide) pole_1395_307

theorem bank_1004_1395_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,307,u⟩,30831793405952,105715278267⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 307 u 30831793405952 105715278267
    (by decide) (by decide) (by decide) (by decide) pole_1395_307

theorem bank_1003_1395_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1003,1395,307,u⟩,30763123736576,105715278267⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1003 1395 307 u 30763123736576 105715278267
    (by decide) (by decide) (by decide) (by decide) pole_1395_307

theorem bank_1002_1395_307 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1395,307,u⟩,30694534807552,105715278267⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1002 1395 307 u 30694534807552 105715278267
    (by decide) (by decide) (by decide) (by decide) pole_1395_307

theorem bank_1002_1395_308 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1002,1395,308,u⟩,30770229149696,105982496027⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1002 1395 308 u 30770229149696 105982496027
    (by decide) (by decide) (by decide) (by decide) pole_1395_308

theorem bank_1004_1395_309 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,309,u⟩,30983809925120,106249418544⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 309 u 30983809925120 106249418544
    (by decide) (by decide) (by decide) (by decide) pole_1395_309

theorem bank_1003_1395_315 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1003,1395,315,u⟩,31367332102144,107844841957⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1003 1395 315 u 31367332102144 107844841957
    (by decide) (by decide) (by decide) (by decide) pole_1395_315

theorem bank_1004_1395_315 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1004,1395,315,u⟩,31437454049280,107844841957⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1004 1395 315 u 31437454049280 107844841957
    (by decide) (by decide) (by decide) (by decide) pole_1395_315

theorem bank_1005_1396_314 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1005,1396,314,u⟩,31432118108160,107828145918⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1005 1396 314 u 31432118108160 107828145918
    (by decide) (by decide) (by decide) (by decide) pole_1396_314

theorem bank_1022_1422_313 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1022,1422,313,u⟩,32556399722496,114143855256⟩ :=
  pack_R6970Height2313CommonRanks11_bank_checked 1022 1422 313 u 32556399722496 114143855256
    (by decide) (by decide) (by decide) (by decide) pole_1422_313

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks11

section Pack_R6970Height2313CommonRanks12

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks12_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1641_368 :
    P1_7_1.groupedPoleMoment 1641 368 ≤ 205224620315 :=
  _root_.PoleAffine6970.certified 1641 368 205224620315 (by decide) (by decide +kernel)

private theorem pole_1642_355 :
    P1_7_1.groupedPoleMoment 1642 355 ≤ 199962033930 :=
  _root_.PoleAffine6970.certified 1642 355 199962033930 (by decide) (by decide +kernel)

private theorem pole_1642_361 :
    P1_7_1.groupedPoleMoment 1642 361 ≤ 202585533550 :=
  _root_.PoleAffine6970.certified 1642 361 202585533550 (by decide) (by decide +kernel)

private theorem pole_1657_368 :
    P1_7_1.groupedPoleMoment 1657 368 ≤ 211736467619 :=
  _root_.PoleAffine6970.certified 1657 368 211736467619 (by decide) (by decide +kernel)

private theorem pole_1658_355 :
    P1_7_1.groupedPoleMoment 1658 355 ≤ 206296069946 :=
  _root_.PoleAffine6970.certified 1658 355 206296069946 (by decide) (by decide +kernel)

private theorem pole_1658_361 :
    P1_7_1.groupedPoleMoment 1658 361 ≤ 209005943830 :=
  _root_.PoleAffine6970.certified 1658 361 209005943830 (by decide) (by decide +kernel)

private theorem pole_1658_368 :
    P1_7_1.groupedPoleMoment 1658 368 ≤ 212148065594 :=
  _root_.PoleAffine6970.certified 1658 368 212148065594 (by decide) (by decide +kernel)

private theorem pole_1665_368 :
    P1_7_1.groupedPoleMoment 1665 368 ≤ 215044511783 :=
  _root_.PoleAffine6970.certified 1665 368 215044511783 (by decide) (by decide +kernel)

private theorem pole_1666_361 :
    P1_7_1.groupedPoleMoment 1666 361 ≤ 212267437130 :=
  _root_.PoleAffine6970.certified 1666 361 212267437130 (by decide) (by decide +kernel)

private theorem pole_1669_368 :
    P1_7_1.groupedPoleMoment 1669 368 ≤ 216711646649 :=
  _root_.PoleAffine6970.certified 1669 368 216711646649 (by decide) (by decide +kernel)

theorem bank_1183_1641_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1183,1641,368,u⟩,51061142323200,205224620315⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1183 1641 368 u 51061142323200 205224620315
    (by decide) (by decide) (by decide) (by decide) pole_1641_368

theorem bank_1177_1642_355 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1177,1642,355,u⟩,49125646139392,199962033930⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1177 1642 355 u 49125646139392 199962033930
    (by decide) (by decide) (by decide) (by decide) pole_1642_355

theorem bank_1181_1642_355 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1181,1642,355,u⟩,49499685781504,199962033930⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1181 1642 355 u 49499685781504 199962033930
    (by decide) (by decide) (by decide) (by decide) pole_1642_355

theorem bank_1182_1642_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1182,1642,361,u⟩,50228757790720,202585533550⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1182 1642 361 u 50228757790720 202585533550
    (by decide) (by decide) (by decide) (by decide) pole_1642_361

theorem bank_1194_1657_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1194,1657,368,u⟩,52130505031680,211736467619⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1194 1657 368 u 52130505031680 211736467619
    (by decide) (by decide) (by decide) (by decide) pole_1657_368

theorem bank_1188_1658_355 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1188,1658,355,u⟩,50157848100864,206296069946⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1188 1658 355 u 50157848100864 206296069946
    (by decide) (by decide) (by decide) (by decide) pole_1658_355

theorem bank_1193_1658_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1193,1658,361,u⟩,51280444129280,209005943830⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1193 1658 361 u 51280444129280 209005943830
    (by decide) (by decide) (by decide) (by decide) pole_1658_361

theorem bank_1194_1658_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1194,1658,368,u⟩,52130505031680,212148065594⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1194 1658 368 u 52130505031680 212148065594
    (by decide) (by decide) (by decide) (by decide) pole_1658_368

theorem bank_1193_1658_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1193,1658,368,u⟩,52032806584320,212148065594⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1193 1658 368 u 52032806584320 212148065594
    (by decide) (by decide) (by decide) (by decide) pole_1658_368

theorem bank_1199_1665_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1199,1665,368,u⟩,52620448235520,215044511783⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1199 1665 368 u 52620448235520 215044511783
    (by decide) (by decide) (by decide) (by decide) pole_1665_368

theorem bank_1200_1666_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1200,1666,361,u⟩,51955677528064,212267437130⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1200 1666 361 u 51955677528064 212267437130
    (by decide) (by decide) (by decide) (by decide) pole_1666_361

theorem bank_1199_1666_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1199,1666,361,u⟩,51858930925568,212267437130⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1199 1666 361 u 51858930925568 212267437130
    (by decide) (by decide) (by decide) (by decide) pole_1666_361

theorem bank_1202_1669_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1669,368,u⟩,52915574931456,216711646649⟩ :=
  pack_R6970Height2313CommonRanks12_bank_checked 1202 1669 368 u 52915574931456 216711646649
    (by decide) (by decide) (by decide) (by decide) pole_1669_368

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks12

section Pack_R6970Height2313CommonRanks14

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks14_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1673_378 :
    P1_7_1.groupedPoleMoment 1673 378 ≤ 222977190790 :=
  _root_.PoleAffine6970.certified 1673 378 222977190790 (by decide) (by decide +kernel)

private theorem pole_1674_361 :
    P1_7_1.groupedPoleMoment 1674 361 ≤ 215563369662 :=
  _root_.PoleAffine6970.certified 1674 361 215563369662 (by decide) (by decide +kernel)

private theorem pole_1674_362 :
    P1_7_1.groupedPoleMoment 1674 362 ≤ 216028185312 :=
  _root_.PoleAffine6970.certified 1674 362 216028185312 (by decide) (by decide +kernel)

private theorem pole_1674_365 :
    P1_7_1.groupedPoleMoment 1674 365 ≤ 217419999532 :=
  _root_.PoleAffine6970.certified 1674 365 217419999532 (by decide) (by decide +kernel)

private theorem pole_1674_368 :
    P1_7_1.groupedPoleMoment 1674 368 ≤ 218807905514 :=
  _root_.PoleAffine6970.certified 1674 368 218807905514 (by decide) (by decide +kernel)

private theorem pole_1674_369 :
    P1_7_1.groupedPoleMoment 1674 369 ≤ 219269681483 :=
  _root_.PoleAffine6970.certified 1674 369 219269681483 (by decide) (by decide +kernel)

private theorem pole_1674_370 :
    P1_7_1.groupedPoleMoment 1674 370 ≤ 219731030846 :=
  _root_.PoleAffine6970.certified 1674 370 219731030846 (by decide) (by decide +kernel)

private theorem pole_1674_372 :
    P1_7_1.groupedPoleMoment 1674 372 ≤ 220652458042 :=
  _root_.PoleAffine6970.certified 1674 372 220652458042 (by decide) (by decide +kernel)

private theorem pole_1674_378 :
    P1_7_1.groupedPoleMoment 1674 378 ≤ 223406703910 :=
  _root_.PoleAffine6970.certified 1674 378 223406703910 (by decide) (by decide +kernel)

private theorem pole_1675_369 :
    P1_7_1.groupedPoleMoment 1675 369 ≤ 219691504053 :=
  _root_.PoleAffine6970.certified 1675 369 219691504053 (by decide) (by decide +kernel)

theorem bank_1206_1673_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1206,1673,378,u⟩,54403284860928,222977190790⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1206 1673 378 u 54403284860928 222977190790
    (by decide) (by decide) (by decide) (by decide) pole_1673_378

theorem bank_1205_1673_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1673,378,u⟩,54302243291136,222977190790⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1205 1673 378 u 54302243291136 222977190790
    (by decide) (by decide) (by decide) (by decide) pole_1673_378

theorem bank_1203_1673_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1673,378,u⟩,54100458209280,222977190790⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1673 378 u 54100458209280 222977190790
    (by decide) (by decide) (by decide) (by decide) pole_1673_378

theorem bank_1202_1674_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1674,361,u⟩,52149455421440,215563369662⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1202 1674 361 u 52149455421440 215563369662
    (by decide) (by decide) (by decide) (by decide) pole_1674_361

theorem bank_1203_1674_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1674,361,u⟩,52246486712320,215563369662⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1674 361 u 52246486712320 215563369662
    (by decide) (by decide) (by decide) (by decide) pole_1674_361

theorem bank_1201_1674_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1201,1674,361,u⟩,52052519026688,215563369662⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1201 1674 361 u 52052519026688 215563369662
    (by decide) (by decide) (by decide) (by decide) pole_1674_361

theorem bank_1203_1674_362 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1674,362,u⟩,52356525326336,216028185312⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1674 362 u 52356525326336 216028185312
    (by decide) (by decide) (by decide) (by decide) pole_1674_362

theorem bank_1204_1674_362 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1204,1674,362,u⟩,52453872238592,216028185312⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1204 1674 362 u 52453872238592 216028185312
    (by decide) (by decide) (by decide) (by decide) pole_1674_362

theorem bank_1205_1674_365 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1674,365,u⟩,52882002411520,217419999532⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1205 1674 365 u 52882002411520 217419999532
    (by decide) (by decide) (by decide) (by decide) pole_1674_365

theorem bank_1203_1674_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1674,368,u⟩,53014143959040,218807905514⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1674 368 u 53014143959040 218807905514
    (by decide) (by decide) (by decide) (by decide) pole_1674_368

theorem bank_1205_1674_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1674,368,u⟩,53211572207616,218807905514⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1205 1674 368 u 53211572207616 218807905514
    (by decide) (by decide) (by decide) (by decide) pole_1674_368

theorem bank_1201_1674_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1201,1674,368,u⟩,52817102635008,218807905514⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1201 1674 368 u 52817102635008 218807905514
    (by decide) (by decide) (by decide) (by decide) pole_1674_368

theorem bank_1202_1674_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1674,368,u⟩,52915574931456,218807905514⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1202 1674 368 u 52915574931456 218807905514
    (by decide) (by decide) (by decide) (by decide) pole_1674_368

theorem bank_1204_1674_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1204,1674,368,u⟩,53112809717760,218807905514⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1204 1674 368 u 53112809717760 218807905514
    (by decide) (by decide) (by decide) (by decide) pole_1674_368

theorem bank_1205_1674_369 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1674,369,u⟩,53321182740480,219269681483⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1205 1674 369 u 53321182740480 219269681483
    (by decide) (by decide) (by decide) (by decide) pole_1674_369

theorem bank_1204_1674_370 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1204,1674,370,u⟩,53331470581760,219731030846⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1204 1674 370 u 53331470581760 219731030846
    (by decide) (by decide) (by decide) (by decide) pole_1674_370

theorem bank_1202_1674_370 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1674,370,u⟩,53133361283072,219731030846⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1202 1674 370 u 53133361283072 219731030846
    (by decide) (by decide) (by decide) (by decide) pole_1674_370

theorem bank_1205_1674_372 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1674,372,u⟩,53649283481600,220652458042⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1205 1674 372 u 53649283481600 220652458042
    (by decide) (by decide) (by decide) (by decide) pole_1674_372

theorem bank_1203_1674_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1674,378,u⟩,54100458209280,223406703910⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1674 378 u 54100458209280 223406703910
    (by decide) (by decide) (by decide) (by decide) pole_1674_378

theorem bank_1204_1674_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1204,1674,378,u⟩,54201301073920,223406703910⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1204 1674 378 u 54201301073920 223406703910
    (by decide) (by decide) (by decide) (by decide) pole_1674_378

theorem bank_1203_1675_369 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1675,369,u⟩,53123316449280,219691504053⟩ :=
  pack_R6970Height2313CommonRanks14_bank_checked 1203 1675 369 u 53123316449280 219691504053
    (by decide) (by decide) (by decide) (by decide) pole_1675_369

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks14

section Pack_R6970Height2313CommonRanks15

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks15_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1676_370 :
    P1_7_1.groupedPoleMoment 1676 370 ≤ 220577070747 :=
  _root_.PoleAffine6970.certified 1676 370 220577070747 (by decide) (by decide +kernel)

private theorem pole_1677_378 :
    P1_7_1.groupedPoleMoment 1677 378 ≤ 224698623950 :=
  _root_.PoleAffine6970.certified 1677 378 224698623950 (by decide) (by decide +kernel)

private theorem pole_1990_445 :
    P1_7_1.groupedPoleMoment 1990 445 ≤ 442453109011 :=
  _root_.PoleAffine6970.certified 1990 445 442453109011 (by decide) (by decide +kernel)

private theorem pole_1991_436 :
    P1_7_1.groupedPoleMoment 1991 436 ≤ 436191362606 :=
  _root_.PoleAffine6970.certified 1991 436 436191362606 (by decide) (by decide +kernel)

private theorem pole_1991_445 :
    P1_7_1.groupedPoleMoment 1991 445 ≤ 443169438977 :=
  _root_.PoleAffine6970.certified 1991 445 443169438977 (by decide) (by decide +kernel)

private theorem pole_1996_432 :
    P1_7_1.groupedPoleMoment 1996 432 ≤ 436582815793 :=
  _root_.PoleAffine6970.certified 1996 432 436582815793 (by decide) (by decide +kernel)

private theorem pole_1996_442 :
    P1_7_1.groupedPoleMoment 1996 442 ≤ 444422784858 :=
  _root_.PoleAffine6970.certified 1996 442 444422784858 (by decide) (by decide +kernel)

private theorem pole_2006_436 :
    P1_7_1.groupedPoleMoment 2006 436 ≤ 446854153866 :=
  _root_.PoleAffine6970.certified 2006 436 446854153866 (by decide) (by decide +kernel)

private theorem pole_2006_445 :
    P1_7_1.groupedPoleMoment 2006 445 ≤ 454009341867 :=
  _root_.PoleAffine6970.certified 2006 445 454009341867 (by decide) (by decide +kernel)

private theorem pole_2007_436 :
    P1_7_1.groupedPoleMoment 2007 436 ≤ 447571244646 :=
  _root_.PoleAffine6970.certified 2007 436 447571244646 (by decide) (by decide +kernel)

theorem bank_1207_1676_370 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1207,1676,370,u⟩,53629363945472,220577070747⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1207 1676 370 u 53629363945472 220577070747
    (by decide) (by decide) (by decide) (by decide) pole_1676_370

theorem bank_1209_1677_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1209,1677,378,u⟩,54707005685760,224698623950⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1209 1677 378 u 54707005685760 224698623950
    (by decide) (by decide) (by decide) (by decide) pole_1677_378

theorem bank_1434_1990_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1434,1990,445,u⟩,90716759654400,442453109011⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1434 1990 445 u 90716759654400 442453109011
    (by decide) (by decide) (by decide) (by decide) pole_1990_445

theorem bank_1433_1991_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1433,1991,436,u⟩,89183141232640,436191362606⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1433 1991 436 u 89183141232640 436191362606
    (by decide) (by decide) (by decide) (by decide) pole_1991_436

theorem bank_1434_1991_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1434,1991,445,u⟩,90716759654400,443169438977⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1434 1991 445 u 90716759654400 443169438977
    (by decide) (by decide) (by decide) (by decide) pole_1991_445

theorem bank_1437_1996_432 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1437,1996,432,u⟩,89114385580032,436582815793⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1437 1996 432 u 89114385580032 436582815793
    (by decide) (by decide) (by decide) (by decide) pole_1996_432

theorem bank_1438_1996_442 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1438,1996,442,u⟩,90817910276096,444422784858⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1438 1996 442 u 90817910276096 444422784858
    (by decide) (by decide) (by decide) (by decide) pole_1996_442

theorem bank_1438_2006_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1438,2006,436,u⟩,89880792924160,446854153866⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1438 2006 436 u 89880792924160 446854153866
    (by decide) (by decide) (by decide) (by decide) pole_2006_436

theorem bank_1445_2006_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1445,2006,445,u⟩,92282560184320,454009341867⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1445 2006 445 u 92282560184320 454009341867
    (by decide) (by decide) (by decide) (by decide) pole_2006_445

theorem bank_1444_2007_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1444,2007,436,u⟩,90721755332608,447571244646⟩ :=
  pack_R6970Height2313CommonRanks15_bank_checked 1444 2007 436 u 90721755332608 447571244646
    (by decide) (by decide) (by decide) (by decide) pole_2007_436

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks15

section Pack_R6970Height2313CommonRanks17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks17_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2022_457 :
    P1_7_1.groupedPoleMoment 2022 457 ≤ 475487789910 :=
  _root_.PoleAffine6970.certified 2022 457 475487789910 (by decide) (by decide +kernel)

private theorem pole_2023_436 :
    P1_7_1.groupedPoleMoment 2023 436 ≤ 459151377566 :=
  _root_.PoleAffine6970.certified 2023 436 459151377566 (by decide) (by decide +kernel)

private theorem pole_2023_437 :
    P1_7_1.groupedPoleMoment 2023 437 ≤ 459971681523 :=
  _root_.PoleAffine6970.certified 2023 437 459971681523 (by decide) (by decide +kernel)

private theorem pole_2023_438 :
    P1_7_1.groupedPoleMoment 2023 438 ≤ 460791341260 :=
  _root_.PoleAffine6970.certified 2023 438 460791341260 (by decide) (by decide +kernel)

private theorem pole_2023_445 :
    P1_7_1.groupedPoleMoment 2023 445 ≤ 466511127281 :=
  _root_.PoleAffine6970.certified 2023 445 466511127281 (by decide) (by decide +kernel)

private theorem pole_2023_447 :
    P1_7_1.groupedPoleMoment 2023 447 ≤ 468139690480 :=
  _root_.PoleAffine6970.certified 2023 447 468139690480 (by decide) (by decide +kernel)

private theorem pole_2023_448 :
    P1_7_1.groupedPoleMoment 2023 448 ≤ 468953040013 :=
  _root_.PoleAffine6970.certified 2023 448 468953040013 (by decide) (by decide +kernel)

private theorem pole_2023_449 :
    P1_7_1.groupedPoleMoment 2023 449 ≤ 469765771732 :=
  _root_.PoleAffine6970.certified 2023 449 469765771732 (by decide) (by decide +kernel)

private theorem pole_2023_457 :
    P1_7_1.groupedPoleMoment 2023 457 ≤ 476245648464 :=
  _root_.PoleAffine6970.certified 2023 457 476245648464 (by decide) (by decide +kernel)

private theorem pole_2024_436 :
    P1_7_1.groupedPoleMoment 2024 436 ≤ 459881825688 :=
  _root_.PoleAffine6970.certified 2024 436 459881825688 (by decide) (by decide +kernel)

theorem bank_1455_2022_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1455,2022,457,u⟩,95625142599680,475487789910⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1455 2022 457 u 95625142599680 475487789910
    (by decide) (by decide) (by decide) (by decide) pole_2022_457

theorem bank_1452_2022_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1452,2022,457,u⟩,95183734833152,475487789910⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1452 2022 457 u 95183734833152 475487789910
    (by decide) (by decide) (by decide) (by decide) pole_2022_457

theorem bank_1451_2022_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2022,457,u⟩,95036839034880,475487789910⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1451 2022 457 u 95036839034880 475487789910
    (by decide) (by decide) (by decide) (by decide) pole_2022_457

theorem bank_1451_2023_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2023,436,u⟩,91708090482688,459151377566⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1451 2023 436 u 91708090482688 459151377566
    (by decide) (by decide) (by decide) (by decide) pole_2023_436

theorem bank_1453_2023_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1453,2023,436,u⟩,91990931537920,459151377566⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1453 2023 436 u 91990931537920 459151377566
    (by decide) (by decide) (by decide) (by decide) pole_2023_436

theorem bank_1455_2023_437 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1455,2023,437,u⟩,92435285278720,459971681523⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1455 2023 437 u 92435285278720 459971681523
    (by decide) (by decide) (by decide) (by decide) pole_2023_437

theorem bank_1456_2023_438 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1456,2023,438,u⟩,92738543157248,460791341260⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1456 2023 438 u 92738543157248 460791341260
    (by decide) (by decide) (by decide) (by decide) pole_2023_438

theorem bank_1455_2023_438 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1455,2023,438,u⟩,92596187693056,460791341260⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1455 2023 438 u 92596187693056 460791341260
    (by decide) (by decide) (by decide) (by decide) pole_2023_438

theorem bank_1452_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1452,2023,445,u⟩,93286344425472,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1452 2023 445 u 93286344425472 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1456_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1456,2023,445,u⟩,93862507577344,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1456 2023 445 u 93862507577344 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1454_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1454,2023,445,u⟩,93574192168960,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1454 2023 445 u 93574192168960 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1451_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2023,445,u⟩,93142595928064,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1451 2023 445 u 93142595928064 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1453_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1453,2023,445,u⟩,93430209839104,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1453 2023 445 u 93430209839104 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1457_2023_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1457,2023,445,u⟩,94006840655872,466511127281⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1457 2023 445 u 94006840655872 466511127281
    (by decide) (by decide) (by decide) (by decide) pole_2023_445

theorem bank_1454_2023_447 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1454,2023,447,u⟩,93892925980672,468139690480⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1454 2023 447 u 93892925980672 468139690480
    (by decide) (by decide) (by decide) (by decide) pole_2023_447

theorem bank_1457_2023_447 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1457,2023,447,u⟩,94327162273792,468139690480⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1457 2023 447 u 94327162273792 468139690480
    (by decide) (by decide) (by decide) (by decide) pole_2023_447

theorem bank_1454_2023_448 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1454,2023,448,u⟩,94052072816640,468953040013⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1454 2023 448 u 94052072816640 468953040013
    (by decide) (by decide) (by decide) (by decide) pole_2023_448

theorem bank_1457_2023_449 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1457,2023,449,u⟩,94646894592000,469765771732⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1457 2023 449 u 94646894592000 469765771732
    (by decide) (by decide) (by decide) (by decide) pole_2023_449

theorem bank_1454_2023_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1454,2023,457,u⟩,95477886615552,476245648464⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1454 2023 457 u 95477886615552 476245648464
    (by decide) (by decide) (by decide) (by decide) pole_2023_457

theorem bank_1459_2023_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1459,2023,457,u⟩,96215367155712,476245648464⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1459 2023 457 u 96215367155712 476245648464
    (by decide) (by decide) (by decide) (by decide) pole_2023_457

theorem bank_1451_2024_436 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2024,436,u⟩,91708090482688,459881825688⟩ :=
  pack_R6970Height2313CommonRanks17_bank_checked 1451 2024 436 u 91708090482688 459881825688
    (by decide) (by decide) (by decide) (by decide) pole_2024_436

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks17

section Pack_R6970Height2313CommonRanks18

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks18_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2025_449 :
    P1_7_1.groupedPoleMoment 2025 449 ≤ 471262550407 :=
  _root_.PoleAffine6970.certified 2025 449 471262550407 (by decide) (by decide +kernel)

private theorem pole_2029_449 :
    P1_7_1.groupedPoleMoment 2029 449 ≤ 474265839457 :=
  _root_.PoleAffine6970.certified 2029 449 474265839457 (by decide) (by decide +kernel)

private theorem pole_2031_445 :
    P1_7_1.groupedPoleMoment 2031 445 ≤ 472474533517 :=
  _root_.PoleAffine6970.certified 2031 445 472474533517 (by decide) (by decide +kernel)

private theorem pole_2063_444 :
    P1_7_1.groupedPoleMoment 2063 444 ≤ 495976619495 :=
  _root_.PoleAffine6970.certified 2063 444 495976619495 (by decide) (by decide +kernel)

private theorem pole_2063_453 :
    P1_7_1.groupedPoleMoment 2063 453 ≤ 503785592781 :=
  _root_.PoleAffine6970.certified 2063 453 503785592781 (by decide) (by decide +kernel)

private theorem pole_2409_537 :
    P1_7_1.groupedPoleMoment 2409 537 ≤ 947161992087 :=
  _root_.PoleAffine6970.certified 2409 537 947161992087 (by decide) (by decide +kernel)

private theorem pole_2410_527 :
    P1_7_1.groupedPoleMoment 2410 527 ≤ 934671348902 :=
  _root_.PoleAffine6970.certified 2410 527 934671348902 (by decide) (by decide +kernel)

private theorem pole_2424_537 :
    P1_7_1.groupedPoleMoment 2424 537 ≤ 966283133477 :=
  _root_.PoleAffine6970.certified 2424 537 966283133477 (by decide) (by decide +kernel)

private theorem pole_2425_537 :
    P1_7_1.groupedPoleMoment 2425 537 ≤ 967567137727 :=
  _root_.PoleAffine6970.certified 2425 537 967567137727 (by decide) (by decide +kernel)

private theorem pole_2426_518 :
    P1_7_1.groupedPoleMoment 2426 518 ≤ 942050892054 :=
  _root_.PoleAffine6970.certified 2426 518 942050892054 (by decide) (by decide +kernel)

theorem bank_1459_2025_449 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1459,2025,449,u⟩,94938031718400,471262550407⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1459 2025 449 u 94938031718400 471262550407
    (by decide) (by decide) (by decide) (by decide) pole_2025_449

theorem bank_1461_2029_449 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1461,2029,449,u⟩,95229640704000,474265839457⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1461 2029 449 u 95229640704000 474265839457
    (by decide) (by decide) (by decide) (by decide) pole_2029_449

theorem bank_1458_2031_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1458,2031,445,u⟩,94151290650624,472474533517⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1458 2031 445 u 94151290650624 472474533517
    (by decide) (by decide) (by decide) (by decide) pole_2031_445

theorem bank_1479_2063_444 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1479,2063,444,u⟩,97045462384640,495976619495⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1479 2063 444 u 97045462384640 495976619495
    (by decide) (by decide) (by decide) (by decide) pole_2063_444

theorem bank_1482_2063_453 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1482,2063,453,u⟩,98984436432896,503785592781⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1482 2063 453 u 98984436432896 503785592781
    (by decide) (by decide) (by decide) (by decide) pole_2063_453

theorem bank_1736_2409_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1736,2409,537,u⟩,160469647360000,947161992087⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1736 2409 537 u 160469647360000 947161992087
    (by decide) (by decide) (by decide) (by decide) pole_2409_537

theorem bank_1731_2410_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1731,2410,527,u⟩,157179550105600,934671348902⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1731 2410 527 u 157179550105600 934671348902
    (by decide) (by decide) (by decide) (by decide) pole_2410_527

theorem bank_1735_2410_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1735,2410,527,u⟩,157993412853760,934671348902⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1735 2410 527 u 157993412853760 934671348902
    (by decide) (by decide) (by decide) (by decide) pole_2410_527

theorem bank_1746_2424_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1746,2424,537,u⟩,162547070402560,966283133477⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1746 2424 537 u 162547070402560 966283133477
    (by decide) (by decide) (by decide) (by decide) pole_2424_537

theorem bank_1747_2425_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1747,2425,537,u⟩,162755588390912,967567137727⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1747 2425 537 u 162755588390912 967567137727
    (by decide) (by decide) (by decide) (by decide) pole_2425_537

theorem bank_1739_2426_518 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1739,2426,518,u⟩,156740461527040,942050892054⟩ :=
  pack_R6970Height2313CommonRanks18_bank_checked 1739 2426 518 u 156740461527040 942050892054
    (by decide) (by decide) (by decide) (by decide) pole_2426_518

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks18

section Pack_R6970Height2313CommonRanks20

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks20_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2439_527 :
    P1_7_1.groupedPoleMoment 2439 527 ≤ 971347212742 :=
  _root_.PoleAffine6970.certified 2439 527 971347212742 (by decide) (by decide +kernel)

private theorem pole_2439_538 :
    P1_7_1.groupedPoleMoment 2439 538 ≤ 987092092177 :=
  _root_.PoleAffine6970.certified 2439 538 987092092177 (by decide) (by decide +kernel)

private theorem pole_2439_539 :
    P1_7_1.groupedPoleMoment 2439 539 ≤ 988517960901 :=
  _root_.PoleAffine6970.certified 2439 539 988517960901 (by decide) (by decide +kernel)

private theorem pole_2440_520 :
    P1_7_1.groupedPoleMoment 2440 520 ≤ 962537056707 :=
  _root_.PoleAffine6970.certified 2440 520 962537056707 (by decide) (by decide +kernel)

private theorem pole_2440_527 :
    P1_7_1.groupedPoleMoment 2440 527 ≤ 972629061662 :=
  _root_.PoleAffine6970.certified 2440 527 972629061662 (by decide) (by decide +kernel)

private theorem pole_2440_529 :
    P1_7_1.groupedPoleMoment 2440 529 ≤ 975504013836 :=
  _root_.PoleAffine6970.certified 2440 529 975504013836 (by decide) (by decide +kernel)

private theorem pole_2440_537 :
    P1_7_1.groupedPoleMoment 2440 537 ≤ 986966790957 :=
  _root_.PoleAffine6970.certified 2440 537 986966790957 (by decide) (by decide +kernel)

private theorem pole_2441_528 :
    P1_7_1.groupedPoleMoment 2441 528 ≤ 975351973888 :=
  _root_.PoleAffine6970.certified 2441 528 975351973888 (by decide) (by decide +kernel)

private theorem pole_2441_537 :
    P1_7_1.groupedPoleMoment 2441 537 ≤ 988269431527 :=
  _root_.PoleAffine6970.certified 2441 537 988269431527 (by decide) (by decide +kernel)

private theorem pole_2441_541 :
    P1_7_1.groupedPoleMoment 2441 541 ≤ 993986736440 :=
  _root_.PoleAffine6970.certified 2441 541 993986736440 (by decide) (by decide +kernel)

theorem bank_1753_2439_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1753,2439,527,u⟩,161683200802816,971347212742⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1753 2439 527 u 161683200802816 971347212742
    (by decide) (by decide) (by decide) (by decide) pole_2439_527

theorem bank_1756_2439_538 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1756,2439,538,u⟩,164871213416448,987092092177⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1756 2439 538 u 164871213416448 987092092177
    (by decide) (by decide) (by decide) (by decide) pole_2439_538

theorem bank_1757_2439_539 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2439,539,u⟩,165314219212800,988517960901⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1757 2439 539 u 165314219212800 988517960901
    (by decide) (by decide) (by decide) (by decide) pole_2439_539

theorem bank_1749_2440_520 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1749,2440,520,u⟩,159229006315520,962537056707⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1749 2440 520 u 159229006315520 962537056707
    (by decide) (by decide) (by decide) (by decide) pole_2440_520

theorem bank_1753_2440_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1753,2440,527,u⟩,161683200802816,972629061662⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1753 2440 527 u 161683200802816 972629061662
    (by decide) (by decide) (by decide) (by decide) pole_2440_527

theorem bank_1755_2440_529 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1755,2440,529,u⟩,162563969515520,975504013836⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1755 2440 529 u 162563969515520 975504013836
    (by decide) (by decide) (by decide) (by decide) pole_2440_529

theorem bank_1754_2440_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2440,537,u⟩,164219163246592,986966790957⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1754 2440 537 u 164219163246592 986966790957
    (by decide) (by decide) (by decide) (by decide) pole_2440_537

theorem bank_1751_2441_528 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1751,2441,528,u⟩,161503828246528,975351973888⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1751 2441 528 u 161503828246528 975351973888
    (by decide) (by decide) (by decide) (by decide) pole_2441_528

theorem bank_1757_2441_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2441,537,u⟩,164848525115392,988269431527⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1757 2441 537 u 164848525115392 988269431527
    (by decide) (by decide) (by decide) (by decide) pole_2441_537

theorem bank_1756_2441_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1756,2441,537,u⟩,164638596792320,988269431527⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1756 2441 537 u 164638596792320 988269431527
    (by decide) (by decide) (by decide) (by decide) pole_2441_537

theorem bank_1752_2441_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1752,2441,537,u⟩,163800293834752,988269431527⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1752 2441 537 u 163800293834752 988269431527
    (by decide) (by decide) (by decide) (by decide) pole_2441_537

theorem bank_1751_2441_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1751,2441,537,u⟩,163591070679040,988269431527⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1751 2441 537 u 163591070679040 988269431527
    (by decide) (by decide) (by decide) (by decide) pole_2441_537

theorem bank_1754_2441_541 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2441,541,u⟩,165146013728768,993986736440⟩ :=
  pack_R6970Height2313CommonRanks20_bank_checked 1754 2441 541 u 165146013728768 993986736440
    (by decide) (by decide) (by decide) (by decide) pole_2441_541

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks20

section Pack_R6970Height2313CommonRanks21

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks21_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2441_551 :
    P1_7_1.groupedPoleMoment 2441 551 ≤ 1008217465165 :=
  _root_.PoleAffine6970.certified 2441 551 1008217465165 (by decide) (by decide +kernel)

private theorem pole_2442_526 :
    P1_7_1.groupedPoleMoment 2442 526 ≤ 973753382962 :=
  _root_.PoleAffine6970.certified 2442 526 973753382962 (by decide) (by decide +kernel)

private theorem pole_2442_527 :
    P1_7_1.groupedPoleMoment 2442 527 ≤ 975196209190 :=
  _root_.PoleAffine6970.certified 2442 527 975196209190 (by decide) (by decide +kernel)

private theorem pole_2442_528 :
    P1_7_1.groupedPoleMoment 2442 528 ≤ 976638095087 :=
  _root_.PoleAffine6970.certified 2442 528 976638095087 (by decide) (by decide +kernel)

private theorem pole_2442_529 :
    P1_7_1.groupedPoleMoment 2442 529 ≤ 978079044011 :=
  _root_.PoleAffine6970.certified 2442 529 978079044011 (by decide) (by decide +kernel)

private theorem pole_2442_535 :
    P1_7_1.groupedPoleMoment 2442 535 ≤ 986705217985 :=
  _root_.PoleAffine6970.certified 2442 535 986705217985 (by decide) (by decide +kernel)

private theorem pole_2442_537 :
    P1_7_1.groupedPoleMoment 2442 537 ≤ 989573241440 :=
  _root_.PoleAffine6970.certified 2442 537 989573241440 (by decide) (by decide +kernel)

private theorem pole_2442_538 :
    P1_7_1.groupedPoleMoment 2442 538 ≤ 991005884367 :=
  _root_.PoleAffine6970.certified 2442 538 991005884367 (by decide) (by decide +kernel)

private theorem pole_2444_525 :
    P1_7_1.groupedPoleMoment 2444 525 ≤ 974873455884 :=
  _root_.PoleAffine6970.certified 2444 525 974873455884 (by decide) (by decide +kernel)

private theorem pole_2445_527 :
    P1_7_1.groupedPoleMoment 2445 527 ≤ 979055562622 :=
  _root_.PoleAffine6970.certified 2445 527 979055562622 (by decide) (by decide +kernel)

theorem bank_1753_2441_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1753,2441,551,u⟩,167236956323840,1008217465165⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1753 2441 551 u 167236956323840 1008217465165
    (by decide) (by decide) (by decide) (by decide) pole_2441_551

theorem bank_1757_2441_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2441,551,u⟩,168093600972800,1008217465165⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1757 2441 551 u 168093600972800 1008217465165
    (by decide) (by decide) (by decide) (by decide) pole_2441_551

theorem bank_1752_2441_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1752,2441,551,u⟩,167023156920320,1008217465165⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1752 2441 551 u 167023156920320 1008217465165
    (by decide) (by decide) (by decide) (by decide) pole_2441_551

theorem bank_1758_2441_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1758,2441,551,u⟩,168308123893760,1008217465165⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1758 2441 551 u 168308123893760 1008217465165
    (by decide) (by decide) (by decide) (by decide) pole_2441_551

theorem bank_1751_2442_526 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1751,2442,526,u⟩,161038008844288,973753382962⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1751 2442 526 u 161038008844288 973753382962
    (by decide) (by decide) (by decide) (by decide) pole_2442_526

theorem bank_1752_2442_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1752,2442,527,u⟩,161477036081152,975196209190⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1752 2442 527 u 161477036081152 975196209190
    (by decide) (by decide) (by decide) (by decide) pole_2442_527

theorem bank_1751_2442_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1751,2442,527,u⟩,161271009771520,975196209190⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1751 2442 527 u 161271009771520 975196209190
    (by decide) (by decide) (by decide) (by decide) pole_2442_527

theorem bank_1754_2442_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2442,527,u⟩,161889503936512,975196209190⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1754 2442 527 u 161889503936512 975196209190
    (by decide) (by decide) (by decide) (by decide) pole_2442_527

theorem bank_1756_2442_528 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1756,2442,528,u⟩,162536950857728,976638095087⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1756 2442 528 u 162536950857728 976638095087
    (by decide) (by decide) (by decide) (by decide) pole_2442_528

theorem bank_1757_2442_528 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2442,528,u⟩,162743991402496,976638095087⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1757 2442 528 u 162743991402496 976638095087
    (by decide) (by decide) (by decide) (by decide) pole_2442_528

theorem bank_1757_2442_529 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2442,529,u⟩,162978555494400,978079044011⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1757 2442 529 u 162978555494400 978079044011
    (by decide) (by decide) (by decide) (by decide) pole_2442_529

theorem bank_1752_2442_535 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1752,2442,535,u⟩,163337078833152,986705217985⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1752 2442 535 u 163337078833152 986705217985
    (by decide) (by decide) (by decide) (by decide) pole_2442_535

theorem bank_1757_2442_535 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1757,2442,535,u⟩,164382115889152,986705217985⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1757 2442 535 u 164382115889152 986705217985
    (by decide) (by decide) (by decide) (by decide) pole_2442_535

theorem bank_1754_2442_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2442,537,u⟩,164219163246592,989573241440⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1754 2442 537 u 164219163246592 989573241440
    (by decide) (by decide) (by decide) (by decide) pole_2442_537

theorem bank_1753_2442_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1753,2442,537,u⟩,164009658023936,989573241440⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1753 2442 537 u 164009658023936 989573241440
    (by decide) (by decide) (by decide) (by decide) pole_2442_537

theorem bank_1758_2442_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1758,2442,537,u⟩,165058594471936,989573241440⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1758 2442 537 u 165058594471936 989573241440
    (by decide) (by decide) (by decide) (by decide) pole_2442_537

theorem bank_1754_2442_538 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2442,538,u⟩,164451141550080,991005884367⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1754 2442 538 u 164451141550080 991005884367
    (by decide) (by decide) (by decide) (by decide) pole_2442_538

theorem bank_1752_2444_525 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1752,2444,525,u⟩,161010208735232,974873455884⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1752 2444 525 u 161010208735232 974873455884
    (by decide) (by decide) (by decide) (by decide) pole_2444_525

theorem bank_1753_2445_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1753,2445,527,u⟩,161683200802816,979055562622⟩ :=
  pack_R6970Height2313CommonRanks21_bank_checked 1753 2445 527 u 161683200802816 979055562622
    (by decide) (by decide) (by decide) (by decide) pole_2445_527

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks21

section Pack_R6970Height2313CommonRanks22

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks22_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2447_551 :
    P1_7_1.groupedPoleMoment 2447 551 ≤ 1016222059945 :=
  _root_.PoleAffine6970.certified 2447 551 1016222059945 (by decide) (by decide +kernel)

private theorem pole_2448_527 :
    P1_7_1.groupedPoleMoment 2448 527 ≤ 982925287294 :=
  _root_.PoleAffine6970.certified 2448 527 982925287294 (by decide) (by decide +kernel)

private theorem pole_2451_551 :
    P1_7_1.groupedPoleMoment 2451 551 ≤ 1021582433505 :=
  _root_.PoleAffine6970.certified 2451 551 1021582433505 (by decide) (by decide +kernel)

private theorem pole_2454_527 :
    P1_7_1.groupedPoleMoment 2454 527 ≤ 990695907382 :=
  _root_.PoleAffine6970.certified 2454 527 990695907382 (by decide) (by decide +kernel)

private theorem pole_2456_529 :
    P1_7_1.groupedPoleMoment 2456 529 ≤ 996233808436 :=
  _root_.PoleAffine6970.certified 2456 529 996233808436 (by decide) (by decide +kernel)

private theorem pole_2480_534 :
    P1_7_1.groupedPoleMoment 2480 534 ≤ 1035458553608 :=
  _root_.PoleAffine6970.certified 2480 534 1035458553608 (by decide) (by decide +kernel)

private theorem pole_2488_544 :
    P1_7_1.groupedPoleMoment 2488 544 ≤ 1061475222728 :=
  _root_.PoleAffine6970.certified 2488 544 1061475222728 (by decide) (by decide +kernel)

private theorem pole_2490_537 :
    P1_7_1.groupedPoleMoment 2490 537 ≤ 1053541809432 :=
  _root_.PoleAffine6970.certified 2490 537 1053541809432 (by decide) (by decide +kernel)

private theorem pole_2494_537 :
    P1_7_1.groupedPoleMoment 2494 537 ≤ 1058996056122 :=
  _root_.PoleAffine6970.certified 2494 537 1058996056122 (by decide) (by decide +kernel)

private theorem pole_2504_539 :
    P1_7_1.groupedPoleMoment 2504 539 ≤ 1075830269751 :=
  _root_.PoleAffine6970.certified 2504 539 1075830269751 (by decide) (by decide +kernel)

theorem bank_1764_2447_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1764,2447,551,u⟩,169598300192768,1016222059945⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1764 2447 551 u 169598300192768 1016222059945
    (by decide) (by decide) (by decide) (by decide) pole_2447_551

theorem bank_1755_2448_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1755,2448,527,u⟩,162095945482240,982925287294⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1755 2448 527 u 162095945482240 982925287294
    (by decide) (by decide) (by decide) (by decide) pole_2448_527

theorem bank_1763_2451_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1763,2451,551,u⟩,169382909050880,1021582433505⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1763 2451 551 u 169382909050880 1021582433505
    (by decide) (by decide) (by decide) (by decide) pole_2451_551

theorem bank_1759_2454_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1759,2454,527,u⟩,162923095785472,990695907382⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1759 2454 527 u 162923095785472 990695907382
    (by decide) (by decide) (by decide) (by decide) pole_2454_527

theorem bank_1761_2456_529 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1761,2456,529,u⟩,163809394688000,996233808436⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1761 2456 529 u 163809394688000 996233808436
    (by decide) (by decide) (by decide) (by decide) pole_2456_529

theorem bank_1778_2480_534 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1778,2480,534,u⟩,168569368739840,1035458553608⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1778 2480 534 u 168569368739840 1035458553608
    (by decide) (by decide) (by decide) (by decide) pole_2480_534

theorem bank_1784_2488_544 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1784,2488,544,u⟩,172257669283840,1061475222728⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1784 2488 544 u 172257669283840 1061475222728
    (by decide) (by decide) (by decide) (by decide) pole_2488_544

theorem bank_1785_2490_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1785,2490,537,u⟩,170783777751040,1053541809432⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1785 2490 537 u 170783777751040 1053541809432
    (by decide) (by decide) (by decide) (by decide) pole_2490_537

theorem bank_1788_2494_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1788,2494,537,u⟩,171426255732736,1058996056122⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1788 2494 537 u 171426255732736 1058996056122
    (by decide) (by decide) (by decide) (by decide) pole_2494_537

theorem bank_1795_2504_539 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1795,2504,539,u⟩,173420665896960,1075830269751⟩ :=
  pack_R6970Height2313CommonRanks22_bank_checked 1795 2504 539 u 173420665896960 1075830269751
    (by decide) (by decide) (by decide) (by decide) pole_2504_539

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks22

section Pack_R6970Height2313CommonRanks25

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks25_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2915_632 :
    P1_7_1.groupedPoleMoment 2915 632 ≤ 1986048372698 :=
  _root_.PoleAffine6970.certified 2915 632 1986048372698 (by decide) (by decide +kernel)

private theorem pole_2918_622 :
    P1_7_1.groupedPoleMoment 2918 622 ≤ 1967992842119 :=
  _root_.PoleAffine6970.certified 2918 622 1967992842119 (by decide) (by decide +kernel)

private theorem pole_2918_626 :
    P1_7_1.groupedPoleMoment 2918 626 ≤ 1977865107915 :=
  _root_.PoleAffine6970.certified 2918 626 1977865107915 (by decide) (by decide +kernel)

private theorem pole_2918_636 :
    P1_7_1.groupedPoleMoment 2918 636 ≤ 2002451397973 :=
  _root_.PoleAffine6970.certified 2918 636 2002451397973 (by decide) (by decide +kernel)

private theorem pole_2922_632 :
    P1_7_1.groupedPoleMoment 2922 632 ≤ 2001435395356 :=
  _root_.PoleAffine6970.certified 2922 632 2001435395356 (by decide) (by decide +kernel)

private theorem pole_2922_634 :
    P1_7_1.groupedPoleMoment 2922 634 ≤ 2006369826343 :=
  _root_.PoleAffine6970.certified 2922 634 2006369826343 (by decide) (by decide +kernel)

private theorem pole_2922_645 :
    P1_7_1.groupedPoleMoment 2922 645 ≤ 2033414523647 :=
  _root_.PoleAffine6970.certified 2922 645 2033414523647 (by decide) (by decide +kernel)

private theorem pole_2924_626 :
    P1_7_1.groupedPoleMoment 2924 626 ≤ 1990976970162 :=
  _root_.PoleAffine6970.certified 2924 626 1990976970162 (by decide) (by decide +kernel)

private theorem pole_2924_634 :
    P1_7_1.groupedPoleMoment 2924 634 ≤ 2010792257808 :=
  _root_.PoleAffine6970.certified 2924 634 2010792257808 (by decide) (by decide +kernel)

private theorem pole_2926_636 :
    P1_7_1.groupedPoleMoment 2926 636 ≤ 2020172992773 :=
  _root_.PoleAffine6970.certified 2926 636 2020172992773 (by decide) (by decide +kernel)

theorem bank_2091_2915_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2091,2915,632,u⟩,275402019307520,1986048372698⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2091 2915 632 u 275402019307520 1986048372698
    (by decide) (by decide) (by decide) (by decide) pole_2915_632

theorem bank_2091_2918_622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2091,2918,622,u⟩,272075810406400,1967992842119⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2091 2918 622 u 272075810406400 1967992842119
    (by decide) (by decide) (by decide) (by decide) pole_2918_622

theorem bank_2091_2918_626 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2091,2918,626,u⟩,273408925892608,1977865107915⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2091 2918 626 u 273408925892608 1977865107915
    (by decide) (by decide) (by decide) (by decide) pole_2918_626

theorem bank_2095_2918_636 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2095,2918,636,u⟩,277912343281664,2002451397973⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2095 2918 636 u 277912343281664 2002451397973
    (by decide) (by decide) (by decide) (by decide) pole_2918_636

theorem bank_2100_2922_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2100,2922,632,u⟩,278060332482560,2001435395356⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2100 2922 632 u 278060332482560 2001435395356
    (by decide) (by decide) (by decide) (by decide) pole_2922_632

theorem bank_2096_2922_634 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2096,2922,634,u⟩,277543655833600,2006369826343⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2096 2922 634 u 277543655833600 2006369826343
    (by decide) (by decide) (by decide) (by decide) pole_2922_634

theorem bank_2100_2922_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2100,2922,645,u⟩,282396798484480,2033414523647⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2100 2922 645 u 282396798484480 2033414523647
    (by decide) (by decide) (by decide) (by decide) pole_2922_645

theorem bank_2095_2924_626 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2095,2924,626,u⟩,274579528351744,1990976970162⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2095 2924 626 u 274579528351744 1990976970162
    (by decide) (by decide) (by decide) (by decide) pole_2924_626

theorem bank_2104_2924_634 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2104,2924,634,u⟩,279918727659520,2010792257808⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2104 2924 634 u 279918727659520 2010792257808
    (by decide) (by decide) (by decide) (by decide) pole_2924_634

theorem bank_2106_2926_636 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2106,2926,636,u⟩,281187434364928,2020172992773⟩ :=
  pack_R6970Height2313CommonRanks25_bank_checked 2106 2926 636 u 281187434364928 2020172992773
    (by decide) (by decide) (by decide) (by decide) pole_2926_636

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks25

section Pack_R6970Height2313CommonRanks26

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks26_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2926_640 :
    P1_7_1.groupedPoleMoment 2926 640 ≤ 2030060368902 :=
  _root_.PoleAffine6970.certified 2926 640 2030060368902 (by decide) (by decide +kernel)

private theorem pole_2927_626 :
    P1_7_1.groupedPoleMoment 2927 626 ≤ 1997555002095 :=
  _root_.PoleAffine6970.certified 2927 626 1997555002095 (by decide) (by decide +kernel)

private theorem pole_2928_632 :
    P1_7_1.groupedPoleMoment 2928 632 ≤ 2014688622700 :=
  _root_.PoleAffine6970.certified 2928 632 2014688622700 (by decide) (by decide +kernel)

private theorem pole_2928_645 :
    P1_7_1.groupedPoleMoment 2928 645 ≤ 2046887686018 :=
  _root_.PoleAffine6970.certified 2928 645 2046887686018 (by decide) (by decide +kernel)

private theorem pole_2928_647 :
    P1_7_1.groupedPoleMoment 2928 647 ≤ 2051821599055 :=
  _root_.PoleAffine6970.certified 2928 647 2051821599055 (by decide) (by decide +kernel)

private theorem pole_2928_662 :
    P1_7_1.groupedPoleMoment 2928 662 ≤ 2088662039796 :=
  _root_.PoleAffine6970.certified 2928 662 2088662039796 (by decide) (by decide +kernel)

private theorem pole_2929_630 :
    P1_7_1.groupedPoleMoment 2929 630 ≤ 2011923818496 :=
  _root_.PoleAffine6970.certified 2929 630 2011923818496 (by decide) (by decide +kernel)

private theorem pole_2929_632 :
    P1_7_1.groupedPoleMoment 2929 632 ≤ 2016903279333 :=
  _root_.PoleAffine6970.certified 2929 632 2016903279333 (by decide) (by decide +kernel)

private theorem pole_2929_633 :
    P1_7_1.groupedPoleMoment 2929 633 ≤ 2019390978963 :=
  _root_.PoleAffine6970.certified 2929 633 2019390978963 (by decide) (by decide +kernel)

private theorem pole_2929_645 :
    P1_7_1.groupedPoleMoment 2929 645 ≤ 2049139102608 :=
  _root_.PoleAffine6970.certified 2929 645 2049139102608 (by decide) (by decide +kernel)

theorem bank_2106_2926_640 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2106,2926,640,u⟩,282531366436864,2030060368902⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2106 2926 640 u 282531366436864 2030060368902
    (by decide) (by decide) (by decide) (by decide) pole_2926_640

theorem bank_2098_2927_626 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2098,2927,626,u⟩,275459206021120,1997555002095⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2098 2927 626 u 275459206021120 1997555002095
    (by decide) (by decide) (by decide) (by decide) pole_2927_626

theorem bank_2104_2928_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2104,2928,632,u⟩,279246119370752,2014688622700⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2104 2928 632 u 279246119370752 2014688622700
    (by decide) (by decide) (by decide) (by decide) pole_2928_632

theorem bank_2105_2928_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2928,645,u⟩,283904392560640,2046887686018⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2105 2928 645 u 283904392560640 2046887686018
    (by decide) (by decide) (by decide) (by decide) pole_2928_645

theorem bank_2109_2928_647 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2109,2928,647,u⟩,285784336760832,2051821599055⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2109 2928 647 u 285784336760832 2051821599055
    (by decide) (by decide) (by decide) (by decide) pole_2928_647

theorem bank_2102_2928_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2102,2928,662,u⟩,288629091991552,2088662039796⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2102 2928 662 u 288629091991552 2088662039796
    (by decide) (by decide) (by decide) (by decide) pole_2928_662

theorem bank_2104_2928_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2104,2928,662,u⟩,289245218209792,2088662039796⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2104 2928 662 u 289245218209792 2088662039796
    (by decide) (by decide) (by decide) (by decide) pole_2928_662

theorem bank_2099_2929_630 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2099,2929,630,u⟩,277094667386880,2011923818496⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2099 2929 630 u 277094667386880 2011923818496
    (by decide) (by decide) (by decide) (by decide) pole_2929_630

theorem bank_2100_2929_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2100,2929,632,u⟩,278060332482560,2016903279333⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2100 2929 632 u 278060332482560 2016903279333
    (by decide) (by decide) (by decide) (by decide) pole_2929_632

theorem bank_2101_2929_633 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2929,633,u⟩,278691788095488,2019390978963⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2101 2929 633 u 278691788095488 2019390978963
    (by decide) (by decide) (by decide) (by decide) pole_2929_633

theorem bank_2108_2929_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2108,2929,645,u⟩,284810981146624,2049139102608⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2108 2929 645 u 284810981146624 2049139102608
    (by decide) (by decide) (by decide) (by decide) pole_2929_645

theorem bank_2107_2929_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2107,2929,645,u⟩,284508615606272,2049139102608⟩ :=
  pack_R6970Height2313CommonRanks26_bank_checked 2107 2929 645 u 284508615606272 2049139102608
    (by decide) (by decide) (by decide) (by decide) pole_2929_645

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks26

section Pack_R6970Height2313CommonRanks28

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks28_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2932_643 :
    P1_7_1.groupedPoleMoment 2932 643 ≤ 2050941744956 :=
  _root_.PoleAffine6970.certified 2932 643 2050941744956 (by decide) (by decide +kernel)

private theorem pole_2936_632 :
    P1_7_1.groupedPoleMoment 2936 632 ≤ 2032452241748 :=
  _root_.PoleAffine6970.certified 2936 632 2032452241748 (by decide) (by decide +kernel)

private theorem pole_2938_640 :
    P1_7_1.groupedPoleMoment 2938 640 ≤ 2056978448546 :=
  _root_.PoleAffine6970.certified 2938 640 2056978448546 (by decide) (by decide +kernel)

private theorem pole_2942_632 :
    P1_7_1.groupedPoleMoment 2942 632 ≤ 2045844620216 :=
  _root_.PoleAffine6970.certified 2942 632 2045844620216 (by decide) (by decide +kernel)

private theorem pole_2945_645 :
    P1_7_1.groupedPoleMoment 2945 645 ≤ 2085391291848 :=
  _root_.PoleAffine6970.certified 2945 645 2085391291848 (by decide) (by decide +kernel)

private theorem pole_2988_644 :
    P1_7_1.groupedPoleMoment 2988 644 ≤ 2182334193151 :=
  _root_.PoleAffine6970.certified 2988 644 2182334193151 (by decide) (by decide +kernel)

private theorem pole_3139_702 :
    P1_7_1.groupedPoleMoment 3139 702 ≤ 2735191490284 :=
  _root_.PoleAffine6970.certified 3139 702 2735191490284 (by decide) (by decide +kernel)

private theorem pole_3143_702 :
    P1_7_1.groupedPoleMoment 3143 702 ≤ 2746433306696 :=
  _root_.PoleAffine6970.certified 3143 702 2746433306696 (by decide) (by decide +kernel)

private theorem pole_3159_685 :
    P1_7_1.groupedPoleMoment 3159 685 ≤ 2738961313091 :=
  _root_.PoleAffine6970.certified 3159 685 2738961313091 (by decide) (by decide +kernel)

private theorem pole_3175_702 :
    P1_7_1.groupedPoleMoment 3175 702 ≤ 2837502581224 :=
  _root_.PoleAffine6970.certified 3175 702 2837502581224 (by decide) (by decide +kernel)

theorem bank_2105_2932_643 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2932,643,u⟩,283235782230016,2050941744956⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2105 2932 643 u 283235782230016 2050941744956
    (by decide) (by decide) (by decide) (by decide) pole_2932_643

theorem bank_2105_2936_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2936,632,u⟩,279542980935680,2032452241748⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2105 2936 632 u 279542980935680 2032452241748
    (by decide) (by decide) (by decide) (by decide) pole_2936_632

theorem bank_2114_2938_640 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2114,2938,640,u⟩,284938289807360,2056978448546⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2114 2938 640 u 284938289807360 2056978448546
    (by decide) (by decide) (by decide) (by decide) pole_2938_640

theorem bank_2109_2942_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2109,2942,632,u⟩,280732086566912,2045844620216⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2109 2942 632 u 280732086566912 2045844620216
    (by decide) (by decide) (by decide) (by decide) pole_2942_632

theorem bank_2119_2945_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2119,2945,645,u⟩,288148178862080,2085391291848⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2119 2945 645 u 288148178862080 2085391291848
    (by decide) (by decide) (by decide) (by decide) pole_2945_645

theorem bank_2142_2988_644 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2142,2988,644,u⟩,294843626291200,2182334193151⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2142 2988 644 u 294843626291200 2182334193151
    (by decide) (by decide) (by decide) (by decide) pole_2988_644

theorem bank_2262_3139_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2262,3139,702,u⟩,355651506143232,2735191490284⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2262 3139 702 u 355651506143232 2735191490284
    (by decide) (by decide) (by decide) (by decide) pole_3139_702

theorem bank_2265_3143_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2265,3143,702,u⟩,356709130567680,2746433306696⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2265 3143 702 u 356709130567680 2746433306696
    (by decide) (by decide) (by decide) (by decide) pole_3143_702

theorem bank_2269_3159_685 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2269,3159,685,u⟩,351516132638720,2738961313091⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2269 3159 685 u 351516132638720 2738961313091
    (by decide) (by decide) (by decide) (by decide) pole_3159_685

theorem bank_2287_3175_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2287,3175,702,u⟩,364515722002432,2837502581224⟩ :=
  pack_R6970Height2313CommonRanks28_bank_checked 2287 3175 702 u 364515722002432 2837502581224
    (by decide) (by decide) (by decide) (by decide) pole_3175_702

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks28

section Pack_R6970Height2313CommonRanks33

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks33_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3388_761 :
    P1_7_1.groupedPoleMoment 3388 761 ≤ 3723773825908 :=
  _root_.PoleAffine6970.certified 3388 761 3723773825908 (by decide) (by decide +kernel)

private theorem pole_3552_770 :
    P1_7_1.groupedPoleMoment 3552 770 ≤ 4375777081296 :=
  _root_.PoleAffine6970.certified 3552 770 4375777081296 (by decide) (by decide +kernel)

private theorem pole_3558_770 :
    P1_7_1.groupedPoleMoment 3558 770 ≤ 4399607751447 :=
  _root_.PoleAffine6970.certified 3558 770 4399607751447 (by decide) (by decide +kernel)

private theorem pole_3559_793 :
    P1_7_1.groupedPoleMoment 3559 793 ≤ 4505630874684 :=
  _root_.PoleAffine6970.certified 3559 793 4505630874684 (by decide) (by decide +kernel)

private theorem pole_3560_775 :
    P1_7_1.groupedPoleMoment 3560 775 ≤ 4429862775297 :=
  _root_.PoleAffine6970.certified 3560 775 4429862775297 (by decide) (by decide +kernel)

private theorem pole_3561_775 :
    P1_7_1.groupedPoleMoment 3561 775 ≤ 4433868945913 :=
  _root_.PoleAffine6970.certified 3561 775 4433868945913 (by decide) (by decide +kernel)

private theorem pole_3562_793 :
    P1_7_1.groupedPoleMoment 3562 793 ≤ 4517874243524 :=
  _root_.PoleAffine6970.certified 3562 793 4517874243524 (by decide) (by decide +kernel)

private theorem pole_3563_783 :
    P1_7_1.groupedPoleMoment 3563 783 ≤ 4477553723328 :=
  _root_.PoleAffine6970.certified 3563 783 4477553723328 (by decide) (by decide +kernel)

private theorem pole_3563_793 :
    P1_7_1.groupedPoleMoment 3563 793 ≤ 4521960393814 :=
  _root_.PoleAffine6970.certified 3563 793 4521960393814 (by decide) (by decide +kernel)

private theorem pole_3564_770 :
    P1_7_1.groupedPoleMoment 3564 770 ≤ 4423526519142 :=
  _root_.PoleAffine6970.certified 3564 770 4423526519142 (by decide) (by decide +kernel)

theorem bank_2434_3388_761 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2434,3388,761,u⟩,445535742066688,3723773825908⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2434 3388 761 u 445535742066688 3723773825908
    (by decide) (by decide) (by decide) (by decide) pole_3388_761

theorem bank_2555_3552_770 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2555,3552,770,u⟩,501114315735040,4375777081296⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2555 3552 770 u 501114315735040 4375777081296
    (by decide) (by decide) (by decide) (by decide) pole_3552_770

theorem bank_2550_3558_770 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2550,3558,770,u⟩,498923410554880,4399607751447⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2550 3558 770 u 498923410554880 4399607751447
    (by decide) (by decide) (by decide) (by decide) pole_3558_770

theorem bank_2564_3559_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2564,3559,793,u⟩,516495320023040,4505630874684⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2564 3559 793 u 516495320023040 4505630874684
    (by decide) (by decide) (by decide) (by decide) pole_3559_793

theorem bank_2554_3560_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2554,3560,775,u⟩,503147779850240,4429862775297⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2554 3560 775 u 503147779850240 4429862775297
    (by decide) (by decide) (by decide) (by decide) pole_3560_775

theorem bank_2562_3561_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2562,3561,775,u⟩,506680843436032,4433868945913⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2562 3561 775 u 506680843436032 4433868945913
    (by decide) (by decide) (by decide) (by decide) pole_3561_775

theorem bank_2567_3562_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2567,3562,793,u⟩,517850014416896,4517874243524⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2567 3562 793 u 517850014416896 4517874243524
    (by decide) (by decide) (by decide) (by decide) pole_3562_793

theorem bank_2566_3563_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2566,3563,783,u⟩,512438711615488,4477553723328⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2566 3563 783 u 512438711615488 4477553723328
    (by decide) (by decide) (by decide) (by decide) pole_3563_783

theorem bank_2567_3563_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2567,3563,793,u⟩,517850014416896,4521960393814⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2567 3563 793 u 517850014416896 4521960393814
    (by decide) (by decide) (by decide) (by decide) pole_3563_793

theorem bank_2554_3564_770 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2554,3564,770,u⟩,500675730472960,4423526519142⟩ :=
  pack_R6970Height2313CommonRanks33_bank_checked 2554 3564 770 u 500675730472960 4423526519142
    (by decide) (by decide) (by decide) (by decide) pole_3564_770

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks33

section Pack_R6970Height2313CommonRanks34

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks34_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3564_793 :
    P1_7_1.groupedPoleMoment 3564 793 ≤ 4526049059099 :=
  _root_.PoleAffine6970.certified 3564 793 4526049059099 (by decide) (by decide +kernel)

private theorem pole_3578_793 :
    P1_7_1.groupedPoleMoment 3578 793 ≤ 4583554892204 :=
  _root_.PoleAffine6970.certified 3578 793 4583554892204 (by decide) (by decide +kernel)

private theorem pole_3588_775 :
    P1_7_1.groupedPoleMoment 3588 775 ≤ 4542969264457 :=
  _root_.PoleAffine6970.certified 3588 775 4542969264457 (by decide) (by decide +kernel)

private theorem pole_3591_783 :
    P1_7_1.groupedPoleMoment 3591 783 ≤ 4591813372944 :=
  _root_.PoleAffine6970.certified 3591 783 4591813372944 (by decide) (by decide +kernel)

private theorem pole_3591_793 :
    P1_7_1.groupedPoleMoment 3591 793 ≤ 4637396591180 :=
  _root_.PoleAffine6970.certified 3591 793 4637396591180 (by decide) (by decide +kernel)

private theorem pole_3592_775 :
    P1_7_1.groupedPoleMoment 3592 775 ≤ 4559285936321 :=
  _root_.PoleAffine6970.certified 3592 775 4559285936321 (by decide) (by decide +kernel)

private theorem pole_3593_775 :
    P1_7_1.groupedPoleMoment 3593 775 ≤ 4563371321017 :=
  _root_.PoleAffine6970.certified 3593 775 4563371321017 (by decide) (by decide +kernel)

private theorem pole_3593_793 :
    P1_7_1.groupedPoleMoment 3593 793 ≤ 4645717944219 :=
  _root_.PoleAffine6970.certified 3593 793 4645717944219 (by decide) (by decide +kernel)

private theorem pole_3594_775 :
    P1_7_1.groupedPoleMoment 3594 775 ≤ 4567459193957 :=
  _root_.PoleAffine6970.certified 3594 775 4567459193957 (by decide) (by decide +kernel)

private theorem pole_3594_793 :
    P1_7_1.groupedPoleMoment 3594 793 ≤ 4649882428564 :=
  _root_.PoleAffine6970.certified 3594 793 4649882428564 (by decide) (by decide +kernel)

theorem bank_2567_3564_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2567,3564,793,u⟩,517850014416896,4526049059099⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2567 3564 793 u 517850014416896 4526049059099
    (by decide) (by decide) (by decide) (by decide) pole_3564_793

theorem bank_2576_3578_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2576,3578,793,u⟩,521925337284608,4583554892204⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2576 3578 793 u 521925337284608 4583554892204
    (by decide) (by decide) (by decide) (by decide) pole_3578_793

theorem bank_2581_3588_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2581,3588,775,u⟩,515124047642624,4542969264457⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2581 3588 775 u 515124047642624 4542969264457
    (by decide) (by decide) (by decide) (by decide) pole_3588_775

theorem bank_2585_3591_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2585,3591,783,u⟩,520968959164416,4591813372944⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2585 3591 783 u 520968959164416 4591813372944
    (by decide) (by decide) (by decide) (by decide) pole_3591_783

theorem bank_2586_3591_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2586,3591,793,u⟩,526473247326208,4637396591180⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2586 3591 793 u 526473247326208 4637396591180
    (by decide) (by decide) (by decide) (by decide) pole_3591_793

theorem bank_2577_3592_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2577,3592,775,u⟩,513340428255232,4559285936321⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2577 3592 775 u 513340428255232 4559285936321
    (by decide) (by decide) (by decide) (by decide) pole_3592_775

theorem bank_2577_3593_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2577,3593,775,u⟩,513340428255232,4563371321017⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2577 3593 775 u 513340428255232 4563371321017
    (by decide) (by decide) (by decide) (by decide) pole_3593_775

theorem bank_2588_3593_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2588,3593,793,u⟩,527385327042560,4645717944219⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2588 3593 793 u 527385327042560 4645717944219
    (by decide) (by decide) (by decide) (by decide) pole_3593_793

theorem bank_2585_3594_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2585,3594,775,u⟩,516910921809920,4567459193957⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2585 3594 775 u 516910921809920 4567459193957
    (by decide) (by decide) (by decide) (by decide) pole_3594_775

theorem bank_2588_3594_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2588,3594,793,u⟩,527385327042560,4649882428564⟩ :=
  pack_R6970Height2313CommonRanks34_bank_checked 2588 3594 793 u 527385327042560 4649882428564
    (by decide) (by decide) (by decide) (by decide) pole_3594_793

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks34

section Pack_R6970Height2313CommonRanks35

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks35_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3595_754 :
    P1_7_1.groupedPoleMoment 3595 754 ≤ 4474462064331 :=
  _root_.PoleAffine6970.certified 3595 754 4474462064331 (by decide) (by decide +kernel)

private theorem pole_3595_775 :
    P1_7_1.groupedPoleMoment 3595 775 ≤ 4571549555917 :=
  _root_.PoleAffine6970.certified 3595 775 4571549555917 (by decide) (by decide +kernel)

private theorem pole_3595_798 :
    P1_7_1.groupedPoleMoment 3595 798 ≤ 4676852015559 :=
  _root_.PoleAffine6970.certified 3595 798 4676852015559 (by decide) (by decide +kernel)

private theorem pole_3596_793 :
    P1_7_1.groupedPoleMoment 3596 793 ≤ 4658219016875 :=
  _root_.PoleAffine6970.certified 3596 793 4658219016875 (by decide) (by decide +kernel)

private theorem pole_3600_775 :
    P1_7_1.groupedPoleMoment 3600 775 ≤ 4592038728177 :=
  _root_.PoleAffine6970.certified 3600 775 4592038728177 (by decide) (by decide +kernel)

private theorem pole_3600_793 :
    P1_7_1.groupedPoleMoment 3600 793 ≤ 4674922694213 :=
  _root_.PoleAffine6970.certified 3600 793 4674922694213 (by decide) (by decide +kernel)

private theorem pole_3601_775 :
    P1_7_1.groupedPoleMoment 3601 775 ≤ 4596144040553 :=
  _root_.PoleAffine6970.certified 3601 775 4596144040553 (by decide) (by decide +kernel)

private theorem pole_3603_775 :
    P1_7_1.groupedPoleMoment 3603 775 ≤ 4604362149437 :=
  _root_.PoleAffine6970.certified 3603 775 4604362149437 (by decide) (by decide +kernel)

private theorem pole_3604_775 :
    P1_7_1.groupedPoleMoment 3604 775 ≤ 4608474947497 :=
  _root_.PoleAffine6970.certified 3604 775 4608474947497 (by decide) (by decide +kernel)

private theorem pole_3607_775 :
    P1_7_1.groupedPoleMoment 3607 775 ≤ 4620828325461 :=
  _root_.PoleAffine6970.certified 3607 775 4620828325461 (by decide) (by decide +kernel)

theorem bank_2579_3595_754 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2579,3595,754,u⟩,503556286709760,4474462064331⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2579 3595 754 u 503556286709760 4474462064331
    (by decide) (by decide) (by decide) (by decide) pole_3595_754

theorem bank_2586_3595_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2586,3595,775,u⟩,517358148911104,4571549555917⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2586 3595 775 u 517358148911104 4571549555917
    (by decide) (by decide) (by decide) (by decide) pole_3595_775

theorem bank_2590_3595_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2590,3595,798,u⟩,530824420130816,4676852015559⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2590 3595 798 u 530824420130816 4676852015559
    (by decide) (by decide) (by decide) (by decide) pole_3595_798

theorem bank_2590_3596_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2590,3596,793,u⟩,528298239328256,4658219016875⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2590 3596 793 u 528298239328256 4658219016875
    (by decide) (by decide) (by decide) (by decide) pole_3596_793

theorem bank_2590_3600_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2590,3600,775,u⟩,519149091553280,4592038728177⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2590 3600 775 u 519149091553280 4592038728177
    (by decide) (by decide) (by decide) (by decide) pole_3600_775

theorem bank_2593_3600_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2593,3600,793,u⟩,529669168824320,4674922694213⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2593 3600 793 u 529669168824320 4674922694213
    (by decide) (by decide) (by decide) (by decide) pole_3600_793

theorem bank_2590_3601_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2590,3601,775,u⟩,519149091553280,4596144040553⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2590 3601 775 u 519149091553280 4596144040553
    (by decide) (by decide) (by decide) (by decide) pole_3601_775

theorem bank_2592_3603_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2592,3603,775,u⟩,520045783416832,4604362149437⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2592 3603 775 u 520045783416832 4604362149437
    (by decide) (by decide) (by decide) (by decide) pole_3603_775

theorem bank_2593_3604_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2593,3604,775,u⟩,520494434484224,4608474947497⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2593 3604 775 u 520494434484224 4608474947497
    (by decide) (by decide) (by decide) (by decide) pole_3604_775

theorem bank_2592_3604_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2592,3604,775,u⟩,520045783416832,4608474947497⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2592 3604 775 u 520045783416832 4608474947497
    (by decide) (by decide) (by decide) (by decide) pole_3604_775

theorem bank_2595_3607_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2595,3607,775,u⟩,521392346890240,4620828325461⟩ :=
  pack_R6970Height2313CommonRanks35_bank_checked 2595 3607 775 u 521392346890240 4620828325461
    (by decide) (by decide) (by decide) (by decide) pole_3607_775

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks35

section Pack_R6970Height2313CommonRanks36

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks36_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3608_775 :
    P1_7_1.groupedPoleMoment 3608 775 ≤ 4624951115297 :=
  _root_.PoleAffine6970.certified 3608 775 4624951115297 (by decide) (by decide +kernel)

private theorem pole_3609_775 :
    P1_7_1.groupedPoleMoment 3609 775 ≤ 4629076405017 :=
  _root_.PoleAffine6970.certified 3609 775 4629076405017 (by decide) (by decide +kernel)

private theorem pole_3609_793 :
    P1_7_1.groupedPoleMoment 3609 793 ≤ 4712654891459 :=
  _root_.PoleAffine6970.certified 3609 793 4712654891459 (by decide) (by decide +kernel)

private theorem pole_3610_775 :
    P1_7_1.groupedPoleMoment 3610 775 ≤ 4633204195397 :=
  _root_.PoleAffine6970.certified 3610 775 4633204195397 (by decide) (by decide +kernel)

private theorem pole_3610_777 :
    P1_7_1.groupedPoleMoment 3610 777 ≤ 4642531995782 :=
  _root_.PoleAffine6970.certified 3610 777 4642531995782 (by decide) (by decide +kernel)

private theorem pole_3610_793 :
    P1_7_1.groupedPoleMoment 3610 793 ≤ 4716860104828 :=
  _root_.PoleAffine6970.certified 3610 793 4716860104828 (by decide) (by decide +kernel)

private theorem pole_3611_767 :
    P1_7_1.groupedPoleMoment 3611 767 ≤ 4599905423586 :=
  _root_.PoleAffine6970.certified 3611 767 4599905423586 (by decide) (by decide +kernel)

private theorem pole_3611_775 :
    P1_7_1.groupedPoleMoment 3611 775 ≤ 4637334487213 :=
  _root_.PoleAffine6970.certified 3611 775 4637334487213 (by decide) (by decide +kernel)

private theorem pole_3611_793 :
    P1_7_1.groupedPoleMoment 3611 793 ≤ 4721067870510 :=
  _root_.PoleAffine6970.certified 3611 793 4721067870510 (by decide) (by decide +kernel)

private theorem pole_3611_798 :
    P1_7_1.groupedPoleMoment 3611 798 ≤ 4744211205591 :=
  _root_.PoleAffine6970.certified 3611 798 4744211205591 (by decide) (by decide +kernel)

theorem bank_2588_3608_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2588,3608,775,u⟩,518253213384704,4624951115297⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2588 3608 775 u 518253213384704 4624951115297
    (by decide) (by decide) (by decide) (by decide) pole_3608_775

theorem bank_2596_3609_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2596,3609,775,u⟩,521841608228864,4629076405017⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2596 3609 775 u 521841608228864 4629076405017
    (by decide) (by decide) (by decide) (by decide) pole_3609_775

theorem bank_2599_3609_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2599,3609,793,u⟩,532416647659520,4712654891459⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2599 3609 793 u 532416647659520 4712654891459
    (by decide) (by decide) (by decide) (by decide) pole_3609_793

theorem bank_2600_3610_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3610,775,u⟩,523640687820800,4633204195397⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2600 3610 775 u 523640687820800 4633204195397
    (by decide) (by decide) (by decide) (by decide) pole_3610_775

theorem bank_2588_3610_777 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2588,3610,777,u⟩,519272186249216,4642531995782⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2588 3610 777 u 519272186249216 4642531995782
    (by decide) (by decide) (by decide) (by decide) pole_3610_777

theorem bank_2599_3610_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2599,3610,793,u⟩,532416647659520,4716860104828⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2599 3610 793 u 532416647659520 4716860104828
    (by decide) (by decide) (by decide) (by decide) pole_3610_793

theorem bank_2588_3611_767 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2588,3611,767,u⟩,514166406250496,4599905423586⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2588 3611 767 u 514166406250496 4599905423586
    (by decide) (by decide) (by decide) (by decide) pole_3611_767

theorem bank_2589_3611_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2589,3611,775,u⟩,518701050757120,4637334487213⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2589 3611 775 u 518701050757120 4637334487213
    (by decide) (by decide) (by decide) (by decide) pole_3611_775

theorem bank_2600_3611_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3611,775,u⟩,523640687820800,4637334487213⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2600 3611 775 u 523640687820800 4637334487213
    (by decide) (by decide) (by decide) (by decide) pole_3611_775

theorem bank_2600_3611_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3611,793,u⟩,532875289296896,4721067870510⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2600 3611 793 u 532875289296896 4721067870510
    (by decide) (by decide) (by decide) (by decide) pole_3611_793

theorem bank_2601_3611_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3611,798,u⟩,535886272135168,4744211205591⟩ :=
  pack_R6970Height2313CommonRanks36_bank_checked 2601 3611 798 u 535886272135168 4744211205591
    (by decide) (by decide) (by decide) (by decide) pole_3611_798

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks36

section Pack_R6970Height2313CommonRanks37

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks37_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3612_754 :
    P1_7_1.groupedPoleMoment 3612 754 ≤ 4542835970406 :=
  _root_.PoleAffine6970.certified 3612 754 4542835970406 (by decide) (by decide +kernel)

private theorem pole_3612_793 :
    P1_7_1.groupedPoleMoment 3612 793 ≤ 4725278189299 :=
  _root_.PoleAffine6970.certified 3612 793 4725278189299 (by decide) (by decide +kernel)

private theorem pole_3614_793 :
    P1_7_1.groupedPoleMoment 3614 793 ≤ 4733706489374 :=
  _root_.PoleAffine6970.certified 3614 793 4733706489374 (by decide) (by decide +kernel)

private theorem pole_3615_793 :
    P1_7_1.groupedPoleMoment 3615 793 ≤ 4737924472248 :=
  _root_.PoleAffine6970.certified 3615 793 4737924472248 (by decide) (by decide +kernel)

private theorem pole_3615_794 :
    P1_7_1.groupedPoleMoment 3615 794 ≤ 4742574286177 :=
  _root_.PoleAffine6970.certified 3615 794 4742574286177 (by decide) (by decide +kernel)

private theorem pole_3616_775 :
    P1_7_1.groupedPoleMoment 3616 775 ≤ 4658023494993 :=
  _root_.PoleAffine6970.certified 3616 775 4658023494993 (by decide) (by decide +kernel)

private theorem pole_3616_797 :
    P1_7_1.groupedPoleMoment 3616 797 ≤ 4760749454740 :=
  _root_.PoleAffine6970.certified 3616 797 4760749454740 (by decide) (by decide +kernel)

private theorem pole_3617_793 :
    P1_7_1.groupedPoleMoment 3617 793 ≤ 4746368107639 :=
  _root_.PoleAffine6970.certified 3617 793 4746368107639 (by decide) (by decide +kernel)

private theorem pole_3618_775 :
    P1_7_1.groupedPoleMoment 3618 775 ≤ 4666316635317 :=
  _root_.PoleAffine6970.certified 3618 775 4666316635317 (by decide) (by decide +kernel)

private theorem pole_3618_791 :
    P1_7_1.groupedPoleMoment 3618 791 ≤ 4741262283081 :=
  _root_.PoleAffine6970.certified 3618 791 4741262283081 (by decide) (by decide +kernel)

theorem bank_2591_3612_754 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2591,3612,754,u⟩,508801528627200,4542835970406⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2591 3612 754 u 508801528627200 4542835970406
    (by decide) (by decide) (by decide) (by decide) pole_3612_754

theorem bank_2601_3612_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3612,793,u⟩,533334139076608,4725278189299⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2601 3612 793 u 533334139076608 4725278189299
    (by decide) (by decide) (by decide) (by decide) pole_3612_793

theorem bank_2600_3614_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3614,793,u⟩,532875289296896,4733706489374⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2600 3614 793 u 532875289296896 4733706489374
    (by decide) (by decide) (by decide) (by decide) pole_3614_793

theorem bank_2603_3615_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3615,793,u⟩,534252463063040,4737924472248⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2603 3615 793 u 534252463063040 4737924472248
    (by decide) (by decide) (by decide) (by decide) pole_3615_793

theorem bank_2602_3615_794 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3615,794,u⟩,534304627097600,4742574286177⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2602 3615 794 u 534304627097600 4742574286177
    (by decide) (by decide) (by decide) (by decide) pole_3615_794

theorem bank_2600_3616_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3616,775,u⟩,523640687820800,4658023494993⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2600 3616 775 u 523640687820800 4658023494993
    (by decide) (by decide) (by decide) (by decide) pole_3616_775

theorem bank_2604_3616_797 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3616,797,u⟩,536759858102272,4760749454740⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2604 3616 797 u 536759858102272 4760749454740
    (by decide) (by decide) (by decide) (by decide) pole_3616_797

theorem bank_2604_3617_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3617,793,u⟩,534711937269760,4746368107639⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2604 3617 793 u 534711937269760 4746368107639
    (by decide) (by decide) (by decide) (by decide) pole_3617_793

theorem bank_2600_3618_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3618,775,u⟩,523640687820800,4666316635317⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2600 3618 775 u 523640687820800 4666316635317
    (by decide) (by decide) (by decide) (by decide) pole_3618_775

theorem bank_2605_3618_791 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3618,791,u⟩,534145111425024,4741262283081⟩ :=
  pack_R6970Height2313CommonRanks37_bank_checked 2605 3618 791 u 534145111425024 4741262283081
    (by decide) (by decide) (by decide) (by decide) pole_3618_791

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks37

section Pack_R6970Height2313CommonRanks43

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks43_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3633_819 :
    P1_7_1.groupedPoleMoment 3633 819 ≤ 4936552670529 :=
  _root_.PoleAffine6970.certified 3633 819 4936552670529 (by decide) (by decide +kernel)

private theorem pole_3634_782 :
    P1_7_1.groupedPoleMoment 3634 782 ≤ 4766365110730 :=
  _root_.PoleAffine6970.certified 3634 782 4766365110730 (by decide) (by decide +kernel)

private theorem pole_3634_783 :
    P1_7_1.groupedPoleMoment 3634 783 ≤ 4771119814608 :=
  _root_.PoleAffine6970.certified 3634 783 4771119814608 (by decide) (by decide +kernel)

private theorem pole_3636_783 :
    P1_7_1.groupedPoleMoment 3636 783 ≤ 4779573597624 :=
  _root_.PoleAffine6970.certified 3636 783 4779573597624 (by decide) (by decide +kernel)

private theorem pole_3640_783 :
    P1_7_1.groupedPoleMoment 3640 783 ≤ 4796511703592 :=
  _root_.PoleAffine6970.certified 3640 783 4796511703592 (by decide) (by decide +kernel)

private theorem pole_3644_793 :
    P1_7_1.groupedPoleMoment 3644 793 ≤ 4861361182339 :=
  _root_.PoleAffine6970.certified 3644 793 4861361182339 (by decide) (by decide +kernel)

private theorem pole_3699_813 :
    P1_7_1.groupedPoleMoment 3699 813 ≤ 5201448023684 :=
  _root_.PoleAffine6970.certified 3699 813 5201448023684 (by decide) (by decide +kernel)

private theorem pole_3700_797 :
    P1_7_1.groupedPoleMoment 3700 797 ≤ 5125966017010 :=
  _root_.PoleAffine6970.certified 3700 797 5125966017010 (by decide) (by decide +kernel)

private theorem pole_3700_798 :
    P1_7_1.groupedPoleMoment 3700 798 ≤ 5130982725704 :=
  _root_.PoleAffine6970.certified 3700 798 5130982725704 (by decide) (by decide +kernel)

private theorem pole_3739_821 :
    P1_7_1.groupedPoleMoment 3739 821 ≤ 5425909527495 :=
  _root_.PoleAffine6970.certified 3739 821 5425909527495 (by decide) (by decide +kernel)

theorem bank_2619_3633_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2619,3633,819,u⟩,555050351984640,4936552670529⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2619 3633 819 u 555050351984640 4936552670529
    (by decide) (by decide) (by decide) (by decide) pole_3633_819

theorem bank_2605_3634_782 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3634,782,u⟩,529512502394880,4766365110730⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2605 3634 782 u 529512502394880 4766365110730
    (by decide) (by decide) (by decide) (by decide) pole_3634_782

theorem bank_2605_3634_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3634,783,u⟩,530028320260096,4771119814608⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2605 3634 783 u 530028320260096 4771119814608
    (by decide) (by decide) (by decide) (by decide) pole_3634_783

theorem bank_2607_3636_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3636,783,u⟩,530938777829376,4779573597624⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2607 3636 783 u 530938777829376 4779573597624
    (by decide) (by decide) (by decide) (by decide) pole_3636_783

theorem bank_2610_3640_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2610,3640,783,u⟩,532306005590016,4796511703592⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2610 3640 783 u 532306005590016 4796511703592
    (by decide) (by decide) (by decide) (by decide) pole_3640_783

theorem bank_2623_3644_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2623,3644,793,u⟩,543481494241280,4861361182339⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2623 3644 793 u 543481494241280 4861361182339
    (by decide) (by decide) (by decide) (by decide) pole_3644_793

theorem bank_2652_3699_813 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2652,3699,813,u⟩,567668370046976,5201448023684⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2652 3699 813 u 567668370046976 5201448023684
    (by decide) (by decide) (by decide) (by decide) pole_3699_813

theorem bank_2653_3700_797 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2653,3700,797,u⟩,559623274233856,5125966017010⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2653 3700 797 u 559623274233856 5125966017010
    (by decide) (by decide) (by decide) (by decide) pole_3700_797

theorem bank_2653_3700_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2653,3700,798,u⟩,560158111170560,5130982725704⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2653 3700 798 u 560158111170560 5130982725704
    (by decide) (by decide) (by decide) (by decide) pole_3700_798

theorem bank_2685_3739_821 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2685,3739,821,u⟩,587960807849984,5425909527495⟩ :=
  pack_R6970Height2313CommonRanks43_bank_checked 2685 3739 821 u 587960807849984 5425909527495
    (by decide) (by decide) (by decide) (by decide) pole_3739_821

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks43

section Pack_R6970Height2313CommonRanks44

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks44_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3764_846 :
    P1_7_1.groupedPoleMoment 3764 846 ≤ 5674388321050 :=
  _root_.PoleAffine6970.certified 3764 846 5674388321050 (by decide) (by decide +kernel)

private theorem pole_3800_830 :
    P1_7_1.groupedPoleMoment 3800 830 ≤ 5764795702526 :=
  _root_.PoleAffine6970.certified 3800 830 5764795702526 (by decide) (by decide +kernel)

private theorem pole_3808_832 :
    P1_7_1.groupedPoleMoment 3808 832 ≤ 5814843148904 :=
  _root_.PoleAffine6970.certified 3808 832 5814843148904 (by decide) (by decide +kernel)

private theorem pole_3809_832 :
    P1_7_1.groupedPoleMoment 3809 832 ≤ 5819759915577 :=
  _root_.PoleAffine6970.certified 3809 832 5819759915577 (by decide) (by decide +kernel)

private theorem pole_3824_812 :
    P1_7_1.groupedPoleMoment 3824 812 ≤ 5782986158433 :=
  _root_.PoleAffine6970.certified 3824 812 5782986158433 (by decide) (by decide +kernel)

private theorem pole_3832_812 :
    P1_7_1.groupedPoleMoment 3832 812 ≤ 5821985239441 :=
  _root_.PoleAffine6970.certified 3832 812 5821985239441 (by decide) (by decide +kernel)

private theorem pole_3835_854 :
    P1_7_1.groupedPoleMoment 3835 854 ≤ 6070657981182 :=
  _root_.PoleAffine6970.certified 3835 854 6070657981182 (by decide) (by decide +kernel)

private theorem pole_3836_861 :
    P1_7_1.groupedPoleMoment 3836 861 ≤ 6114405280540 :=
  _root_.PoleAffine6970.certified 3836 861 6114405280540 (by decide) (by decide +kernel)

private theorem pole_3837_834 :
    P1_7_1.groupedPoleMoment 3837 834 ≤ 5969742006437 :=
  _root_.PoleAffine6970.certified 3837 834 5969742006437 (by decide) (by decide +kernel)

private theorem pole_3838_854 :
    P1_7_1.groupedPoleMoment 3838 854 ≤ 6085966034562 :=
  _root_.PoleAffine6970.certified 3838 854 6085966034562 (by decide) (by decide +kernel)

theorem bank_2713_3764_846 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2713,3764,846,u⟩,615629136855040,5674388321050⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2713 3764 846 u 615629136855040 5674388321050
    (by decide) (by decide) (by decide) (by decide) pole_3764_846

theorem bank_2736_3800_830 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2736,3800,830,u⟩,618353947049984,5764795702526⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2736 3800 830 u 618353947049984 5764795702526
    (by decide) (by decide) (by decide) (by decide) pole_3800_830

theorem bank_2729_3808_832 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2729,3808,832,u⟩,615945059172352,5814843148904⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2729 3808 832 u 615945059172352 5814843148904
    (by decide) (by decide) (by decide) (by decide) pole_3808_832

theorem bank_2730_3809_832 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2730,3809,832,u⟩,616450357985280,5819759915577⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2730 3809 832 u 616450357985280 5819759915577
    (by decide) (by decide) (by decide) (by decide) pole_3809_832

theorem bank_2748_3824_812 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2748,3824,812,u⟩,614083158081536,5782986158433⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2748 3824 812 u 614083158081536 5782986158433
    (by decide) (by decide) (by decide) (by decide) pole_3824_812

theorem bank_2754_3832_812 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2754,3832,812,u⟩,617082439073792,5821985239441⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2754 3832 812 u 617082439073792 5821985239441
    (by decide) (by decide) (by decide) (by decide) pole_3832_812

theorem bank_2763_3835_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2763,3835,854,u⟩,645932077547520,6070657981182⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2763 3835 854 u 645932077547520 6070657981182
    (by decide) (by decide) (by decide) (by decide) pole_3835_854

theorem bank_2762_3836_861 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2762,3836,861,u⟩,649412627660800,6114405280540⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2762 3836 861 u 649412627660800 6114405280540
    (by decide) (by decide) (by decide) (by decide) pole_3836_861

theorem bank_2754_3837_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2754,3837,834,u⟩,629792749649920,5969742006437⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2754 3837 834 u 629792749649920 5969742006437
    (by decide) (by decide) (by decide) (by decide) pole_3837_834

theorem bank_2765_3838_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2765,3838,854,u⟩,646979899883520,6085966034562⟩ :=
  pack_R6970Height2313CommonRanks44_bank_checked 2765 3838 854 u 646979899883520 6085966034562
    (by decide) (by decide) (by decide) (by decide) pole_3838_854

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks44

section Pack_R6970Height2313CommonRanks46

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks46_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3870_854 :
    P1_7_1.groupedPoleMoment 3870 854 ≤ 6250890231282 :=
  _root_.PoleAffine6970.certified 3870 854 6250890231282 (by decide) (by decide +kernel)

private theorem pole_3871_854 :
    P1_7_1.groupedPoleMoment 3871 854 ≤ 6256092552882 :=
  _root_.PoleAffine6970.certified 3871 854 6256092552882 (by decide) (by decide +kernel)

private theorem pole_3873_854 :
    P1_7_1.groupedPoleMoment 3873 854 ≤ 6266506033362 :=
  _root_.PoleAffine6970.certified 3873 854 6266506033362 (by decide) (by decide +kernel)

private theorem pole_3874_854 :
    P1_7_1.groupedPoleMoment 3874 854 ≤ 6271717193952 :=
  _root_.PoleAffine6970.certified 3874 854 6271717193952 (by decide) (by decide +kernel)

private theorem pole_3875_854 :
    P1_7_1.groupedPoleMoment 3875 854 ≤ 6276931302582 :=
  _root_.PoleAffine6970.certified 3875 854 6276931302582 (by decide) (by decide +kernel)

private theorem pole_3878_834 :
    P1_7_1.groupedPoleMoment 3878 834 ≤ 6177455542647 :=
  _root_.PoleAffine6970.certified 3878 834 6177455542647 (by decide) (by decide +kernel)

private theorem pole_3882_854 :
    P1_7_1.groupedPoleMoment 3882 854 ≤ 6313512679932 :=
  _root_.PoleAffine6970.certified 3882 854 6313512679932 (by decide) (by decide +kernel)

private theorem pole_3883_854 :
    P1_7_1.groupedPoleMoment 3883 854 ≤ 6318750403662 :=
  _root_.PoleAffine6970.certified 3883 854 6318750403662 (by decide) (by decide +kernel)

private theorem pole_3885_834 :
    P1_7_1.groupedPoleMoment 3885 834 ≤ 6213402888837 :=
  _root_.PoleAffine6970.certified 3885 834 6213402888837 (by decide) (by decide +kernel)

private theorem pole_3889_854 :
    P1_7_1.groupedPoleMoment 3889 854 ≤ 6350238846402 :=
  _root_.PoleAffine6970.certified 3889 854 6350238846402 (by decide) (by decide +kernel)

theorem bank_2787_3870_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2787,3870,854,u⟩,658565116723200,6250890231282⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2787 3870 854 u 658565116723200 6250890231282
    (by decide) (by decide) (by decide) (by decide) pole_3870_854

theorem bank_2788_3871_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2788,3871,854,u⟩,659094295019520,6256092552882⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2788 3871 854 u 659094295019520 6256092552882
    (by decide) (by decide) (by decide) (by decide) pole_3871_854

theorem bank_2789_3873_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2789,3873,854,u⟩,659623697448960,6266506033362⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2789 3873 854 u 659623697448960 6266506033362
    (by decide) (by decide) (by decide) (by decide) pole_3873_854

theorem bank_2790_3874_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2790,3874,854,u⟩,660153324011520,6271717193952⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2790 3874 854 u 660153324011520 6271717193952
    (by decide) (by decide) (by decide) (by decide) pole_3874_854

theorem bank_2791_3875_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2791,3875,854,u⟩,660683174707200,6276931302582⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2791 3875 854 u 660683174707200 6276931302582
    (by decide) (by decide) (by decide) (by decide) pole_3875_854

theorem bank_2790_3878_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2790,3878,834,u⟩,648354204221440,6177455542647⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2790 3878 834 u 648354204221440 6177455542647
    (by decide) (by decide) (by decide) (by decide) pole_3878_834

theorem bank_2793_3882_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2793,3882,854,u⟩,661743548497920,6313512679932⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2793 3882 854 u 661743548497920 6313512679932
    (by decide) (by decide) (by decide) (by decide) pole_3882_854

theorem bank_2796_3883_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2796,3883,854,u⟩,663335790182400,6318750403662⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2796 3883 854 u 663335790182400 6318750403662
    (by decide) (by decide) (by decide) (by decide) pole_3883_854

theorem bank_2794_3885_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2794,3885,834,u⟩,650434099281920,6213402888837⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2794 3885 834 u 650434099281920 6213402888837
    (by decide) (by decide) (by decide) (by decide) pole_3885_834

theorem bank_2800_3889_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2800,3889,854,u⟩,665461916958720,6350238846402⟩ :=
  pack_R6970Height2313CommonRanks46_bank_checked 2800 3889 854 u 665461916958720 6350238846402
    (by decide) (by decide) (by decide) (by decide) pole_3889_854

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks46

section Pack_R6970Height2313CommonRanks52

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks52_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4105_897 :
    P1_7_1.groupedPoleMoment 4105 897 ≤ 7851902147204 :=
  _root_.PoleAffine6970.certified 4105 897 7851902147204 (by decide) (by decide +kernel)

private theorem pole_4108_894 :
    P1_7_1.groupedPoleMoment 4108 894 ≤ 7849872303328 :=
  _root_.PoleAffine6970.certified 4108 894 7849872303328 (by decide) (by decide +kernel)

private theorem pole_4109_900 :
    P1_7_1.groupedPoleMoment 4109 900 ≤ 7897067162757 :=
  _root_.PoleAffine6970.certified 4109 900 7897067162757 (by decide) (by decide +kernel)

private theorem pole_4114_894 :
    P1_7_1.groupedPoleMoment 4114 894 ≤ 7886833980213 :=
  _root_.PoleAffine6970.certified 4114 894 7886833980213 (by decide) (by decide +kernel)

private theorem pole_4118_894 :
    P1_7_1.groupedPoleMoment 4118 894 ≤ 7911540743403 :=
  _root_.PoleAffine6970.certified 4118 894 7911540743403 (by decide) (by decide +kernel)

private theorem pole_4119_894 :
    P1_7_1.groupedPoleMoment 4119 894 ≤ 7917725648063 :=
  _root_.PoleAffine6970.certified 4119 894 7917725648063 (by decide) (by decide +kernel)

private theorem pole_4120_898 :
    P1_7_1.groupedPoleMoment 4120 898 ≤ 7951531802886 :=
  _root_.PoleAffine6970.certified 4120 898 7951531802886 (by decide) (by decide +kernel)

private theorem pole_4120_900 :
    P1_7_1.groupedPoleMoment 4120 900 ≤ 7965324963082 :=
  _root_.PoleAffine6970.certified 4120 900 7965324963082 (by decide) (by decide +kernel)

private theorem pole_4130_894 :
    P1_7_1.groupedPoleMoment 4130 894 ≤ 7985976760333 :=
  _root_.PoleAffine6970.certified 4130 894 7985976760333 (by decide) (by decide +kernel)

private theorem pole_4146_894 :
    P1_7_1.groupedPoleMoment 4146 894 ≤ 8085963618533 :=
  _root_.PoleAffine6970.certified 4146 894 8085963618533 (by decide) (by decide +kernel)

theorem bank_2953_4105_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2953,4105,897,u⟩,778135319085056,7851902147204⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2953 4105 897 u 778135319085056 7851902147204
    (by decide) (by decide) (by decide) (by decide) pole_4105_897

theorem bank_2957_4108_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2957,4108,894,u⟩,778508848332800,7849872303328⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2957 4108 894 u 778508848332800 7849872303328
    (by decide) (by decide) (by decide) (by decide) pole_4108_894

theorem bank_2950_4109_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2950,4109,900,u⟩,778340368384000,7897067162757⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2950 4109 900 u 778340368384000 7897067162757
    (by decide) (by decide) (by decide) (by decide) pole_4109_900

theorem bank_2953_4114_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2953,4114,894,u⟩,776154682490880,7886833980213⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2953 4114 894 u 776154682490880 7886833980213
    (by decide) (by decide) (by decide) (by decide) pole_4114_894

theorem bank_2954_4114_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2954,4114,894,u⟩,776742872023040,7886833980213⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2954 4114 894 u 776742872023040 7886833980213
    (by decide) (by decide) (by decide) (by decide) pole_4114_894

theorem bank_2954_4118_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2954,4118,894,u⟩,776742872023040,7911540743403⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2954 4118 894 u 776742872023040 7911540743403
    (by decide) (by decide) (by decide) (by decide) pole_4118_894

theorem bank_2954_4119_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2954,4119,894,u⟩,776742872023040,7917725648063⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2954 4119 894 u 776742872023040 7917725648063
    (by decide) (by decide) (by decide) (by decide) pole_4119_894

theorem bank_2965_4120_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2965,4120,898,u⟩,785894641238016,7951531802886⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2965 4120 898 u 785894641238016 7951531802886
    (by decide) (by decide) (by decide) (by decide) pole_4120_898

theorem bank_2958_4120_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2958,4120,900,u⟩,783072706166784,7965324963082⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2958 4120 900 u 783072706166784 7965324963082
    (by decide) (by decide) (by decide) (by decide) pole_4120_900

theorem bank_2965_4120_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2965,4120,900,u⟩,787225901793280,7965324963082⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2965 4120 900 u 787225901793280 7965324963082
    (by decide) (by decide) (by decide) (by decide) pole_4120_900

theorem bank_2972_4130_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2972,4130,894,u⟩,787370403430400,7985976760333⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2972 4130 894 u 787370403430400 7985976760333
    (by decide) (by decide) (by decide) (by decide) pole_4130_894

theorem bank_2983_4146_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2983,4146,894,u⟩,793902427668480,8085963618533⟩ :=
  pack_R6970Height2313CommonRanks52_bank_checked 2983 4146 894 u 793902427668480 8085963618533
    (by decide) (by decide) (by decide) (by decide) pole_4146_894

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks52

section Pack_R6970Height2313CommonRanks53

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks53_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4151_898 :
    P1_7_1.groupedPoleMoment 4151 898 ≤ 8145701898053 :=
  _root_.PoleAffine6970.certified 4151 898 8145701898053 (by decide) (by decide +kernel)

private theorem pole_4152_894 :
    P1_7_1.groupedPoleMoment 4152 894 ≤ 8123677052458 :=
  _root_.PoleAffine6970.certified 4152 894 8123677052458 (by decide) (by decide +kernel)

private theorem pole_4156_894 :
    P1_7_1.groupedPoleMoment 4156 894 ≤ 8148885667208 :=
  _root_.PoleAffine6970.certified 4156 894 8148885667208 (by decide) (by decide +kernel)

private theorem pole_4160_894 :
    P1_7_1.groupedPoleMoment 4160 894 ≤ 8174147409158 :=
  _root_.PoleAffine6970.certified 4160 894 8174147409158 (by decide) (by decide +kernel)

private theorem pole_4160_900 :
    P1_7_1.groupedPoleMoment 4160 900 ≤ 8216917752362 :=
  _root_.PoleAffine6970.certified 4160 900 8216917752362 (by decide) (by decide +kernel)

private theorem pole_4168_894 :
    P1_7_1.groupedPoleMoment 4168 894 ≤ 8224830503778 :=
  _root_.PoleAffine6970.certified 4168 894 8224830503778 (by decide) (by decide +kernel)

private theorem pole_4168_896 :
    P1_7_1.groupedPoleMoment 4168 896 ≤ 8239190160355 :=
  _root_.PoleAffine6970.certified 4168 896 8239190160355 (by decide) (by decide +kernel)

private theorem pole_4168_900 :
    P1_7_1.groupedPoleMoment 4168 900 ≤ 8267876438282 :=
  _root_.PoleAffine6970.certified 4168 900 8267876438282 (by decide) (by decide +kernel)

private theorem pole_4171_895 :
    P1_7_1.groupedPoleMoment 4171 895 ≤ 8251090109528 :=
  _root_.PoleAffine6970.certified 4171 895 8251090109528 (by decide) (by decide +kernel)

private theorem pole_4171_898 :
    P1_7_1.groupedPoleMoment 4171 898 ≤ 8272669034533 :=
  _root_.PoleAffine6970.certified 4171 898 8272669034533 (by decide) (by decide +kernel)

theorem bank_2987_4151_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2987,4151,898,u⟩,798998930128896,8145701898053⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2987 4151 898 u 798998930128896 8145701898053
    (by decide) (by decide) (by decide) (by decide) pole_4151_898

theorem bank_2976_4152_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2976,4152,894,u⟩,789742400307200,8123677052458⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2976 4152 894 u 789742400307200 8123677052458
    (by decide) (by decide) (by decide) (by decide) pole_4152_894

theorem bank_2990_4156_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2990,4156,894,u⟩,798073951354880,8148885667208⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2990 4156 894 u 798073951354880 8148885667208
    (by decide) (by decide) (by decide) (by decide) pole_4156_894

theorem bank_2983_4160_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2983,4160,894,u⟩,793902427668480,8174147409158⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2983 4160 894 u 793902427668480 8174147409158
    (by decide) (by decide) (by decide) (by decide) pole_4160_894

theorem bank_2992_4160_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2992,4160,900,u⟩,803353782648832,8216917752362⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2992 4160 900 u 803353782648832 8216917752362
    (by decide) (by decide) (by decide) (by decide) pole_4160_900

theorem bank_2987_4160_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2987,4160,900,u⟩,800354147500032,8216917752362⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2987 4160 900 u 800354147500032 8216917752362
    (by decide) (by decide) (by decide) (by decide) pole_4160_900

theorem bank_2998_4168_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2998,4168,894,u⟩,802855484129280,8224830503778⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2998 4168 894 u 802855484129280 8224830503778
    (by decide) (by decide) (by decide) (by decide) pole_4168_894

theorem bank_2998_4168_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2998,4168,896,u⟩,804225297940480,8239190160355⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2998 4168 896 u 804225297940480 8239190160355
    (by decide) (by decide) (by decide) (by decide) pole_4168_896

theorem bank_2989_4168_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2989,4168,900,u⟩,801553292984320,8267876438282⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 2989 4168 900 u 801553292984320 8267876438282
    (by decide) (by decide) (by decide) (by decide) pole_4168_900

theorem bank_3000_4171_895 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3000,4171,895,u⟩,804739381985280,8251090109528⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 3000 4171 895 u 804739381985280 8251090109528
    (by decide) (by decide) (by decide) (by decide) pole_4171_895

theorem bank_3001_4171_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4171,898,u⟩,807397411258368,8272669034533⟩ :=
  pack_R6970Height2313CommonRanks53_bank_checked 3001 4171 898 u 807397411258368 8272669034533
    (by decide) (by decide) (by decide) (by decide) pole_4171_898

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks53

section Pack_R6970Height2313CommonRanks55

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks55_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4401_963 :
    P1_7_1.groupedPoleMoment 4401 963 ≤ 10383217925868 :=
  _root_.PoleAffine6970.certified 4401 963 10383217925868 (by decide) (by decide +kernel)

private theorem pole_4417_963 :
    P1_7_1.groupedPoleMoment 4417 963 ≤ 10505224384092 :=
  _root_.PoleAffine6970.certified 4417 963 10505224384092 (by decide) (by decide +kernel)

private theorem pole_4431_982 :
    P1_7_1.groupedPoleMoment 4431 982 ≤ 10775449532456 :=
  _root_.PoleAffine6970.certified 4431 982 10775449532456 (by decide) (by decide +kernel)

private theorem pole_4432_947 :
    P1_7_1.groupedPoleMoment 4432 947 ≤ 10482540453677 :=
  _root_.PoleAffine6970.certified 4432 947 10482540453677 (by decide) (by decide +kernel)

private theorem pole_4433_963 :
    P1_7_1.groupedPoleMoment 4433 963 ≤ 10628202307532 :=
  _root_.PoleAffine6970.certified 4433 963 10628202307532 (by decide) (by decide +kernel)

private theorem pole_4440_947 :
    P1_7_1.groupedPoleMoment 4440 947 ≤ 10543530211269 :=
  _root_.PoleAffine6970.certified 4440 947 10543530211269 (by decide) (by decide +kernel)

private theorem pole_4441_963 :
    P1_7_1.groupedPoleMoment 4441 963 ≤ 10690056802628 :=
  _root_.PoleAffine6970.certified 4441 963 10690056802628 (by decide) (by decide +kernel)

private theorem pole_4446_982 :
    P1_7_1.groupedPoleMoment 4446 982 ≤ 10893360067896 :=
  _root_.PoleAffine6970.certified 4446 982 10893360067896 (by decide) (by decide +kernel)

private theorem pole_4447_982 :
    P1_7_1.groupedPoleMoment 4447 982 ≤ 10901251843544 :=
  _root_.PoleAffine6970.certified 4447 982 10901251843544 (by decide) (by decide +kernel)

private theorem pole_4449_963 :
    P1_7_1.groupedPoleMoment 4449 963 ≤ 10752155644732 :=
  _root_.PoleAffine6970.certified 4449 963 10752155644732 (by decide) (by decide +kernel)

theorem bank_3168_4401_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3168,4401,963,u⟩,961192486502400,10383217925868⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3168 4401 963 u 961192486502400 10383217925868
    (by decide) (by decide) (by decide) (by decide) pole_4401_963

theorem bank_3176_4417_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3176,4417,963,u⟩,966632758837248,10505224384092⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3176 4417 963 u 966632758837248 10505224384092
    (by decide) (by decide) (by decide) (by decide) pole_4417_963

theorem bank_3192_4431_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3192,4431,982,u⟩,992190100406272,10775449532456⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3192 4431 982 u 992190100406272 10775449532456
    (by decide) (by decide) (by decide) (by decide) pole_4431_982

theorem bank_3176_4432_947 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3176,4432,947,u⟩,954371090677760,10482540453677⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3176 4432 947 u 954371090677760 10482540453677
    (by decide) (by decide) (by decide) (by decide) pole_4432_947

theorem bank_3179_4433_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3179,4433,963,u⟩,968677030625280,10628202307532⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3179 4433 963 u 968677030625280 10628202307532
    (by decide) (by decide) (by decide) (by decide) pole_4433_963

theorem bank_3182_4440_947 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3182,4440,947,u⟩,958405939822592,10543530211269⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3182 4440 947 u 958405939822592 10543530211269
    (by decide) (by decide) (by decide) (by decide) pole_4440_947

theorem bank_3186_4441_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3186,4441,963,u⟩,973455842869248,10690056802628⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3186 4441 963 u 973455842869248 10690056802628
    (by decide) (by decide) (by decide) (by decide) pole_4441_963

theorem bank_3200_4446_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4446,982,u⟩,997767489781760,10893360067896⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3200 4446 982 u 997767489781760 10893360067896
    (by decide) (by decide) (by decide) (by decide) pole_4446_982

theorem bank_3200_4447_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4447,982,u⟩,997767489781760,10901251843544⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3200 4447 982 u 997767489781760 10901251843544
    (by decide) (by decide) (by decide) (by decide) pole_4447_982

theorem bank_3191_4449_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3191,4449,963,u⟩,976876861390848,10752155644732⟩ :=
  pack_R6970Height2313CommonRanks55_bank_checked 3191 4449 963 u 976876861390848 10752155644732
    (by decide) (by decide) (by decide) (by decide) pole_4449_963

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks55

section Pack_R6970Height2313CommonRanks59

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks59_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_4472_979 :
    P1_7_1.groupedPoleMoment 4472 979 ≤ 11073399396491 :=
  _root_.PoleAffine6970.certified 4472 979 11073399396491 (by decide) (by decide +kernel)

private theorem pole_4472_1000 :
    P1_7_1.groupedPoleMoment 4472 1000 ≤ 11257719822725 :=
  _root_.PoleAffine6970.certified 4472 1000 11257719822725 (by decide) (by decide +kernel)

private theorem pole_4473_963 :
    P1_7_1.groupedPoleMoment 4473 963 ≤ 10939923188772 :=
  _root_.PoleAffine6970.certified 4473 963 10939923188772 (by decide) (by decide +kernel)

private theorem pole_4475_1008 :
    P1_7_1.groupedPoleMoment 4475 1008 ≤ 11352091862286 :=
  _root_.PoleAffine6970.certified 4475 1008 11352091862286 (by decide) (by decide +kernel)

private theorem pole_4479_998 :
    P1_7_1.groupedPoleMoment 4479 998 ≤ 11296993100967 :=
  _root_.PoleAffine6970.certified 4479 998 11296993100967 (by decide) (by decide +kernel)

private theorem pole_4481_979 :
    P1_7_1.groupedPoleMoment 4481 979 ≤ 11145301432991 :=
  _root_.PoleAffine6970.certified 4481 979 11145301432991 (by decide) (by decide +kernel)

private theorem pole_5434_1189 :
    P1_7_1.groupedPoleMoment 5434 1189 ≤ 24123363874836 :=
  _root_.PoleAffine6970.certified 5434 1189 24123363874836 (by decide) (by decide +kernel)

private theorem pole_5447_1189 :
    P1_7_1.groupedPoleMoment 5447 1189 ≤ 24309649468876 :=
  _root_.PoleAffine6970.certified 5447 1189 24309649468876 (by decide) (by decide +kernel)

private theorem pole_5479_1169 :
    P1_7_1.groupedPoleMoment 5479 1169 ≤ 24446475358504 :=
  _root_.PoleAffine6970.certified 5479 1169 24446475358504 (by decide) (by decide +kernel)

private theorem pole_5480_1189 :
    P1_7_1.groupedPoleMoment 5480 1189 ≤ 24786918035651 :=
  _root_.PoleAffine6970.certified 5480 1189 24786918035651 (by decide) (by decide +kernel)

theorem bank_3220_4472_979 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3220,4472,979,u⟩,1009432193925120,11073399396491⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3220 4472 979 u 1009432193925120 11073399396491
    (by decide) (by decide) (by decide) (by decide) pole_4472_979

theorem bank_3219_4472_1000 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3219,4472,1000,u⟩,1025113218088960,11257719822725⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3219 4472 1000 u 1025113218088960 11257719822725
    (by decide) (by decide) (by decide) (by decide) pole_4472_1000

theorem bank_3207_4473_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3207,4473,963,u⟩,987866575405056,10939923188772⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3207 4473 963 u 987866575405056 10939923188772
    (by decide) (by decide) (by decide) (by decide) pole_4473_963

theorem bank_3226_4475_1008 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3226,4475,1008,u⟩,1036351157567488,11352091862286⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3226 4475 1008 u 1036351157567488 11352091862286
    (by decide) (by decide) (by decide) (by decide) pole_4475_1008

theorem bank_3227_4479_998 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3227,4479,998,u⟩,1029267100532736,11296993100967⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3227 4479 998 u 1029267100532736 11296993100967
    (by decide) (by decide) (by decide) (by decide) pole_4479_998

theorem bank_3226_4481_979 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3226,4481,979,u⟩,1013646399897600,11145301432991⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3226 4481 979 u 1013646399897600 11145301432991
    (by decide) (by decide) (by decide) (by decide) pole_4481_979

theorem bank_3896_5434_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3896,5434,1189,u⟩,1792666704281600,24123363874836⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3896 5434 1189 u 1792666704281600 24123363874836
    (by decide) (by decide) (by decide) (by decide) pole_5434_1189

theorem bank_3921_5447_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3921,5447,1189,u⟩,1818515773849600,24309649468876⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3921 5447 1189 u 1818515773849600 24309649468876
    (by decide) (by decide) (by decide) (by decide) pole_5447_1189

theorem bank_3926_5479_1169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3926,5479,1169,u⟩,1800277308211200,24446475358504⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3926 5479 1169 u 1800277308211200 24446475358504
    (by decide) (by decide) (by decide) (by decide) pole_5479_1169

theorem bank_3939_5480_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3939,5480,1189,u⟩,1837247829114880,24786918035651⟩ :=
  pack_R6970Height2313CommonRanks59_bank_checked 3939 5480 1189 u 1837247829114880 24786918035651
    (by decide) (by decide) (by decide) (by decide) pole_5480_1189

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks59

section Pack_R6970Height2313CommonRanks62

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks62_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_5514_1187 :
    P1_7_1.groupedPoleMoment 5514 1187 ≤ 25252070181474 :=
  _root_.PoleAffine6970.certified 5514 1187 25252070181474 (by decide) (by decide +kernel)

private theorem pole_5518_1189 :
    P1_7_1.groupedPoleMoment 5518 1189 ≤ 25344347044466 :=
  _root_.PoleAffine6970.certified 5518 1189 25344347044466 (by decide) (by decide +kernel)

private theorem pole_5520_1221 :
    P1_7_1.groupedPoleMoment 5520 1221 ≤ 25904511971665 :=
  _root_.PoleAffine6970.certified 5520 1221 25904511971665 (by decide) (by decide +kernel)

private theorem pole_5524_1189 :
    P1_7_1.groupedPoleMoment 5524 1189 ≤ 25433134016061 :=
  _root_.PoleAffine6970.certified 5524 1189 25433134016061 (by decide) (by decide +kernel)

private theorem pole_5528_1189 :
    P1_7_1.groupedPoleMoment 5528 1189 ≤ 25492442660491 :=
  _root_.PoleAffine6970.certified 5528 1189 25492442660491 (by decide) (by decide +kernel)

private theorem pole_5536_1244 :
    P1_7_1.groupedPoleMoment 5536 1244 ≤ 26529200910168 :=
  _root_.PoleAffine6970.certified 5536 1244 26529200910168 (by decide) (by decide +kernel)

private theorem pole_5539_1244 :
    P1_7_1.groupedPoleMoment 5539 1244 ≤ 26575548181548 :=
  _root_.PoleAffine6970.certified 5539 1244 26575548181548 (by decide) (by decide +kernel)

private theorem pole_6599_1420 :
    P1_7_1.groupedPoleMoment 6599 1420 ≤ 51772293031740 :=
  _root_.PoleAffine6970.certified 6599 1420 51772293031740 (by decide) (by decide +kernel)

private theorem pole_6618_1445 :
    P1_7_1.groupedPoleMoment 6618 1445 ≤ 52969844804533 :=
  _root_.PoleAffine6970.certified 6618 1445 52969844804533 (by decide) (by decide +kernel)

private theorem pole_6663_1474 :
    P1_7_1.groupedPoleMoment 6663 1474 ≤ 54982628702281 :=
  _root_.PoleAffine6970.certified 6663 1474 54982628702281 (by decide) (by decide +kernel)

theorem bank_3953_5514_1187 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3953,5514,1187,u⟩,1849512334196736,25252070181474⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3953 5514 1187 u 1849512334196736 25252070181474
    (by decide) (by decide) (by decide) (by decide) pole_5514_1187

theorem bank_3956_5518_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3956,5518,1189,u⟩,1855032020172800,25344347044466⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3956 5518 1189 u 1855032020172800 25344347044466
    (by decide) (by decide) (by decide) (by decide) pole_5518_1189

theorem bank_3969_5520_1221 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3969,5520,1221,u⟩,1906836793458688,25904511971665⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3969 5520 1221 u 1906836793458688 25904511971665
    (by decide) (by decide) (by decide) (by decide) pole_5520_1221

theorem bank_3960_5524_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3960,5524,1189,u⟩,1859229637672960,25433134016061⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3960 5524 1189 u 1859229637672960 25433134016061
    (by decide) (by decide) (by decide) (by decide) pole_5524_1189

theorem bank_3963_5528_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3963,5528,1189,u⟩,1862381126287360,25492442660491⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3963 5528 1189 u 1862381126287360 25492442660491
    (by decide) (by decide) (by decide) (by decide) pole_5528_1189

theorem bank_3991_5536_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3991,5536,1244,u⟩,1958113417625600,26529200910168⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3991 5536 1244 u 1958113417625600 26529200910168
    (by decide) (by decide) (by decide) (by decide) pole_5536_1244

theorem bank_3993_5539_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3993,5539,1244,u⟩,1960313472942080,26575548181548⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 3993 5539 1244 u 1960313472942080 26575548181548
    (by decide) (by decide) (by decide) (by decide) pole_5539_1244

theorem bank_4730_6599_1420 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4730,6599,1420,u⟩,3167380985610240,51772293031740⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 4730 6599 1420 u 3167380985610240 51772293031740
    (by decide) (by decide) (by decide) (by decide) pole_6599_1420

theorem bank_4746_6618_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4746,6618,1445,u⟩,3234102093021184,52969844804533⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 4746 6618 1445 u 3234102093021184 52969844804533
    (by decide) (by decide) (by decide) (by decide) pole_6618_1445

theorem bank_4800_6663_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4800,6663,1474,u⟩,3367547627110400,54982628702281⟩ :=
  pack_R6970Height2313CommonRanks62_bank_checked 4800 6663 1474 u 3367547627110400 54982628702281
    (by decide) (by decide) (by decide) (by decide) pole_6663_1474

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks62

section Pack_R6970Height2313CommonRanks66

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks66_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_6724_1506 :
    P1_7_1.groupedPoleMoment 6724 1506 ≤ 57574114957143 :=
  _root_.PoleAffine6970.certified 6724 1506 57574114957143 (by decide) (by decide +kernel)

private theorem pole_6729_1453 :
    P1_7_1.groupedPoleMoment 6729 1453 ≤ 56124300799930 :=
  _root_.PoleAffine6970.certified 6729 1453 56124300799930 (by decide) (by decide +kernel)

private theorem pole_6730_1506 :
    P1_7_1.groupedPoleMoment 6730 1506 ≤ 57739795581494 :=
  _root_.PoleAffine6970.certified 6730 1506 57739795581494 (by decide) (by decide +kernel)

private theorem pole_6829_1503 :
    P1_7_1.groupedPoleMoment 6829 1503 ≤ 60426714374650 :=
  _root_.PoleAffine6970.certified 6829 1503 60426714374650 (by decide) (by decide +kernel)

private theorem pole_7674_1657 :
    P1_7_1.groupedPoleMoment 7674 1657 ≤ 94920001073870 :=
  _root_.PoleAffine6970.certified 7674 1657 94920001073870 (by decide) (by decide +kernel)

private theorem pole_7775_1674 :
    P1_7_1.groupedPoleMoment 7775 1674 ≤ 99791494771586 :=
  _root_.PoleAffine6970.certified 7775 1674 99791494771586 (by decide) (by decide +kernel)

private theorem pole_7776_1675 :
    P1_7_1.groupedPoleMoment 7776 1675 ≤ 99879364782516 :=
  _root_.PoleAffine6970.certified 7776 1675 99879364782516 (by decide) (by decide +kernel)

private theorem pole_7884_1750 :
    P1_7_1.groupedPoleMoment 7884 1750 ≤ 108040693109459 :=
  _root_.PoleAffine6970.certified 7884 1750 108040693109459 (by decide) (by decide +kernel)

private theorem pole_7886_1750 :
    P1_7_1.groupedPoleMoment 7886 1750 ≤ 108128998877830 :=
  _root_.PoleAffine6970.certified 7886 1750 108128998877830 (by decide) (by decide +kernel)

private theorem pole_7888_1716 :
    P1_7_1.groupedPoleMoment 7888 1716 ≤ 106576249969594 :=
  _root_.PoleAffine6970.certified 7888 1716 106576249969594 (by decide) (by decide +kernel)

theorem bank_4846_6724_1506 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4846,6724,1506,u⟩,3496796367618048,57574114957143⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 4846 6724 1506 u 3496796367618048 57574114957143
    (by decide) (by decide) (by decide) (by decide) pole_6724_1506

theorem bank_4823_6729_1453 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4823,6729,1453,u⟩,3366818370027520,56124300799930⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 4823 6729 1453 u 3366818370027520 56124300799930
    (by decide) (by decide) (by decide) (by decide) pole_6729_1453

theorem bank_4851_6730_1506 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4851,6730,1506,u⟩,3504887012261888,57739795581494⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 4851 6730 1506 u 3504887012261888 57739795581494
    (by decide) (by decide) (by decide) (by decide) pole_6730_1506

theorem bank_4918_6829_1503 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4918,6829,1503,u⟩,3608781531381760,60426714374650⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 4918 6829 1503 u 3608781531381760 60426714374650
    (by decide) (by decide) (by decide) (by decide) pole_6829_1503

theorem bank_5502_7674_1657 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5502,7674,1657,u⟩,4996490915479552,94920001073870⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5502 7674 1657 u 4996490915479552 94920001073870
    (by decide) (by decide) (by decide) (by decide) pole_7674_1657

theorem bank_5574_7775_1674 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5574,7775,1674,u⟩,5184111810969600,99791494771586⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5574 7775 1674 u 5184111810969600 99791494771586
    (by decide) (by decide) (by decide) (by decide) pole_7775_1674

theorem bank_5575_7776_1675 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5575,7776,1675,u⟩,5188554299801600,99879364782516⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5575 7776 1675 u 5188554299801600 99879364782516
    (by decide) (by decide) (by decide) (by decide) pole_7776_1675

theorem bank_5680_7884_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5680,7884,1750,u⟩,5593163081973760,108040693109459⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5680 7884 1750 u 5593163081973760 108040693109459
    (by decide) (by decide) (by decide) (by decide) pole_7884_1750

theorem bank_5682_7886_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5682,7886,1750,u⟩,5597575584940032,108128998877830⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5682 7886 1750 u 5597575584940032 108128998877830
    (by decide) (by decide) (by decide) (by decide) pole_7886_1750

theorem bank_5678_7888_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5678,7888,1716,u⟩,5505996296028160,106576249969594⟩ :=
  pack_R6970Height2313CommonRanks66_bank_checked 5678 7888 1716 u 5505996296028160 106576249969594
    (by decide) (by decide) (by decide) (by decide) pole_7888_1716

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks66

section Pack_R6970Height2313CommonRanks69

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks69_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_7954_1747 :
    P1_7_1.groupedPoleMoment 7954 1747 ≤ 111012270743197 :=
  _root_.PoleAffine6970.certified 7954 1747 111012270743197 (by decide) (by decide +kernel)

private theorem pole_7956_1754 :
    P1_7_1.groupedPoleMoment 7956 1754 ≤ 111448689112361 :=
  _root_.PoleAffine6970.certified 7956 1754 111448689112361 (by decide) (by decide +kernel)

private theorem pole_7969_1766 :
    P1_7_1.groupedPoleMoment 7969 1766 ≤ 112632359565114 :=
  _root_.PoleAffine6970.certified 7969 1766 112632359565114 (by decide) (by decide +kernel)

private theorem pole_7984_1748 :
    P1_7_1.groupedPoleMoment 7984 1748 ≤ 112416216904324 :=
  _root_.PoleAffine6970.certified 7984 1748 112416216904324 (by decide) (by decide +kernel)

private theorem pole_7991_1754 :
    P1_7_1.groupedPoleMoment 7991 1754 ≤ 113035233942686 :=
  _root_.PoleAffine6970.certified 7991 1754 113035233942686 (by decide) (by decide +kernel)

private theorem pole_8110_1785 :
    P1_7_1.groupedPoleMoment 8110 1785 ≤ 120174411265203 :=
  _root_.PoleAffine6970.certified 8110 1785 120174411265203 (by decide) (by decide +kernel)

private theorem pole_8112_1785 :
    P1_7_1.groupedPoleMoment 8112 1785 ≤ 120269873432242 :=
  _root_.PoleAffine6970.certified 8112 1785 120269873432242 (by decide) (by decide +kernel)

private theorem pole_8954_1931 :
    P1_7_1.groupedPoleMoment 8954 1931 ≤ 175732707213154 :=
  _root_.PoleAffine6970.certified 8954 1931 175732707213154 (by decide) (by decide +kernel)

private theorem pole_9030_1946 :
    P1_7_1.groupedPoleMoment 9030 1946 ≤ 181672708620125 :=
  _root_.PoleAffine6970.certified 9030 1946 181672708620125 (by decide) (by decide +kernel)

private theorem pole_9557_2118 :
    P1_7_1.groupedPoleMoment 9557 2118 ≤ 232955158421260 :=
  _root_.PoleAffine6970.certified 9557 2118 232955158421260 (by decide) (by decide +kernel)

theorem bank_5711_7954_1747 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5711,7954,1747,u⟩,5654385624350720,111012270743197⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5711 7954 1747 u 5654385624350720 111012270743197
    (by decide) (by decide) (by decide) (by decide) pole_7954_1747

theorem bank_5730_7956_1754 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5730,7956,1754,u⟩,5713934202961920,111448689112361⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5730 7956 1754 u 5713934202961920 111448689112361
    (by decide) (by decide) (by decide) (by decide) pole_7956_1754

theorem bank_5727_7969_1766 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5727,7969,1766,u⟩,5736867509043200,112632359565114⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5727 7969 1766 u 5736867509043200 112632359565114
    (by decide) (by decide) (by decide) (by decide) pole_7969_1766

theorem bank_5748_7984_1748 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5748,7984,1748,u⟩,5739223187456000,112416216904324⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5748 7984 1748 u 5739223187456000 112416216904324
    (by decide) (by decide) (by decide) (by decide) pole_7984_1748

theorem bank_5732_7991_1754 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5732,7991,1754,u⟩,5718400951910400,113035233942686⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5732 7991 1754 u 5718400951910400 113035233942686
    (by decide) (by decide) (by decide) (by decide) pole_7991_1754

theorem bank_5841_8110_1785 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5841,8110,1785,u⟩,6044716112543744,120174411265203⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5841 8110 1785 u 6044716112543744 120174411265203
    (by decide) (by decide) (by decide) (by decide) pole_8110_1785

theorem bank_5819_8112_1785 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5819,8112,1785,u⟩,5993853912350720,120269873432242⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 5819 8112 1785 u 5993853912350720 120269873432242
    (by decide) (by decide) (by decide) (by decide) pole_8112_1785

theorem bank_6419_8954_1931 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6419,8954,1931,u⟩,7926481832378368,175732707213154⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 6419 8954 1931 u 7926481832378368 175732707213154
    (by decide) (by decide) (by decide) (by decide) pole_8954_1931

theorem bank_6473_9030_1946 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6473,9030,1946,u⟩,8124203203297280,181672708620125⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 6473 9030 1946 u 8124203203297280 181672708620125
    (by decide) (by decide) (by decide) (by decide) pole_9030_1946

theorem bank_6885_9557_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6885,9557,2118,u⟩,9948425779675136,232955158421260⟩ :=
  pack_R6970Height2313CommonRanks69_bank_checked 6885 9557 2118 u 9948425779675136 232955158421260
    (by decide) (by decide) (by decide) (by decide) pole_9557_2118

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks69

section Pack_R6970Height2313CommonRanks70

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks70_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_9561_2118 :
    P1_7_1.groupedPoleMoment 9561 2118 ≤ 233269354849936 :=
  _root_.PoleAffine6970.certified 9561 2118 233269354849936 (by decide) (by decide +kernel)

private theorem pole_9562_2077 :
    P1_7_1.groupedPoleMoment 9562 2077 ≤ 229821110674495 :=
  _root_.PoleAffine6970.certified 9562 2077 229821110674495 (by decide) (by decide +kernel)

private theorem pole_9581_2077 :
    P1_7_1.groupedPoleMoment 9581 2077 ≤ 231294349662262 :=
  _root_.PoleAffine6970.certified 9581 2077 231294349662262 (by decide) (by decide +kernel)

private theorem pole_9588_2058 :
    P1_7_1.groupedPoleMoment 9588 2058 ≤ 230181280555220 :=
  _root_.PoleAffine6970.certified 9588 2058 230181280555220 (by decide) (by decide +kernel)

private theorem pole_9596_2077 :
    P1_7_1.groupedPoleMoment 9596 2077 ≤ 232461959482352 :=
  _root_.PoleAffine6970.certified 9596 2077 232461959482352 (by decide) (by decide +kernel)

private theorem pole_9596_2150 :
    P1_7_1.groupedPoleMoment 9596 2150 ≤ 238800000867221 :=
  _root_.PoleAffine6970.certified 9596 2150 238800000867221 (by decide) (by decide +kernel)

private theorem pole_9609_2118 :
    P1_7_1.groupedPoleMoment 9609 2118 ≤ 237062237065760 :=
  _root_.PoleAffine6970.certified 9609 2118 237062237065760 (by decide) (by decide +kernel)

private theorem pole_9610_2118 :
    P1_7_1.groupedPoleMoment 9610 2118 ≤ 237141698561354 :=
  _root_.PoleAffine6970.certified 9610 2118 237141698561354 (by decide) (by decide +kernel)

private theorem pole_9612_2077 :
    P1_7_1.groupedPoleMoment 9612 2077 ≤ 233711820700520 :=
  _root_.PoleAffine6970.certified 9612 2077 233711820700520 (by decide) (by decide +kernel)

private theorem pole_9616_2077 :
    P1_7_1.groupedPoleMoment 9616 2077 ≤ 234024998385022 :=
  _root_.PoleAffine6970.certified 9616 2077 234024998385022 (by decide) (by decide +kernel)

theorem bank_6887_9561_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6887,9561,2118,u⟩,9954899935625216,233269354849936⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6887 9561 2118 u 9954899935625216 233269354849936
    (by decide) (by decide) (by decide) (by decide) pole_9561_2118

theorem bank_6874_9562_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6874,9562,2077,u⟩,9766584394186752,229821110674495⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6874 9562 2077 u 9766584394186752 229821110674495
    (by decide) (by decide) (by decide) (by decide) pole_9562_2077

theorem bank_6874_9581_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6874,9581,2077,u⟩,9766584394186752,231294349662262⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6874 9581 2077 u 9766584394186752 231294349662262
    (by decide) (by decide) (by decide) (by decide) pole_9581_2077

theorem bank_6871_9588_2058 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6871,9588,2058,u⟩,9688932169023488,230181280555220⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6871 9588 2058 u 9688932169023488 230181280555220
    (by decide) (by decide) (by decide) (by decide) pole_9588_2058

theorem bank_6896_9596_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6896,9596,2077,u⟩,9836655866019840,232461959482352⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6896 9596 2077 u 9836655866019840 232461959482352
    (by decide) (by decide) (by decide) (by decide) pole_9596_2077

theorem bank_6900_9596_2150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6900,9596,2150,u⟩,10111427995238400,238800000867221⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6900 9596 2150 u 10111427995238400 238800000867221
    (by decide) (by decide) (by decide) (by decide) pole_9596_2150

theorem bank_6921_9609_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6921,9609,2118,u⟩,10065300542455808,237062237065760⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6921 9609 2118 u 10065300542455808 237062237065760
    (by decide) (by decide) (by decide) (by decide) pole_9609_2118

theorem bank_6900_9610_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6900,9610,2118,u⟩,9997036108906496,237141698561354⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6900 9610 2118 u 9997036108906496 237141698561354
    (by decide) (by decide) (by decide) (by decide) pole_9610_2118

theorem bank_6907_9612_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6907,9612,2077,u⟩,9871790471380992,233711820700520⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6907 9612 2077 u 9871790471380992 233711820700520
    (by decide) (by decide) (by decide) (by decide) pole_9612_2077

theorem bank_6908_9616_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6908,9616,2077,u⟩,9874987794825216,234024998385022⟩ :=
  pack_R6970Height2313CommonRanks70_bank_checked 6908 9616 2077 u 9874987794825216 234024998385022
    (by decide) (by decide) (by decide) (by decide) pole_9616_2077

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks70

section Pack_R6970Height2313CommonRanks76

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks76_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_13889_3010 :
    P1_7_1.groupedPoleMoment 13889 3010 ≤ 1020905604721879 :=
  _root_.PoleAffine6970.certified 13889 3010 1020905604721879 (by decide) (by decide +kernel)

private theorem pole_13890_3010 :
    P1_7_1.groupedPoleMoment 13890 3010 ≤ 1021142236441759 :=
  _root_.PoleAffine6970.certified 13890 3010 1021142236441759 (by decide) (by decide +kernel)

private theorem pole_13920_3070 :
    P1_7_1.groupedPoleMoment 13920 3070 ≤ 1044203862130693 :=
  _root_.PoleAffine6970.certified 13920 3070 1044203862130693 (by decide) (by decide +kernel)

private theorem pole_13921_3070 :
    P1_7_1.groupedPoleMoment 13921 3070 ≤ 1044445480705554 :=
  _root_.PoleAffine6970.certified 13921 3070 1044445480705554 (by decide) (by decide +kernel)

private theorem pole_13922_3070 :
    P1_7_1.groupedPoleMoment 13922 3070 ≤ 1044687137320892 :=
  _root_.PoleAffine6970.certified 13922 3070 1044687137320892 (by decide) (by decide +kernel)

private theorem pole_13923_3042 :
    P1_7_1.groupedPoleMoment 13923 3042 ≤ 1037495757100745 :=
  _root_.PoleAffine6970.certified 13923 3042 1037495757100745 (by decide) (by decide +kernel)

private theorem pole_13932_3070 :
    P1_7_1.groupedPoleMoment 13932 3070 ≤ 1047105796376127 :=
  _root_.PoleAffine6970.certified 13932 3070 1047105796376127 (by decide) (by decide +kernel)

private theorem pole_13934_3070 :
    P1_7_1.groupedPoleMoment 13934 3070 ≤ 1047589984979998 :=
  _root_.PoleAffine6970.certified 13934 3070 1047589984979998 (by decide) (by decide +kernel)

private theorem pole_13935_3026 :
    P1_7_1.groupedPoleMoment 13935 3026 ≤ 1036107350026597 :=
  _root_.PoleAffine6970.certified 13935 3026 1036107350026597 (by decide) (by decide +kernel)

private theorem pole_13937_3026 :
    P1_7_1.groupedPoleMoment 13937 3026 ≤ 1036586141451239 :=
  _root_.PoleAffine6970.certified 13937 3026 1036586141451239 (by decide) (by decide +kernel)

theorem bank_9981_13889_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨9981,13889,3010,u⟩,29847417077366784,1020905604721879⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 9981 13889 3010 u 29847417077366784 1020905604721879
    (by decide) (by decide) (by decide) (by decide) pole_13889_3010

theorem bank_9988_13890_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨9988,13890,3010,u⟩,29894270850433024,1021142236441759⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 9988 13890 3010 u 29894270850433024 1021142236441759
    (by decide) (by decide) (by decide) (by decide) pole_13890_3010

theorem bank_10000_13920_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13920,3070,u⟩,30428373265940480,1044203862130693⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10000 13920 3070 u 30428373265940480 1044203862130693
    (by decide) (by decide) (by decide) (by decide) pole_13920_3070

theorem bank_10000_13921_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13921,3070,u⟩,30428373265940480,1044445480705554⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10000 13921 3070 u 30428373265940480 1044445480705554
    (by decide) (by decide) (by decide) (by decide) pole_13921_3070

theorem bank_10000_13922_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13922,3070,u⟩,30428373265940480,1044687137320892⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10000 13922 3070 u 30428373265940480 1044687137320892
    (by decide) (by decide) (by decide) (by decide) pole_13922_3070

theorem bank_10000_13923_3042 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13923,3042,u⟩,30217110574858240,1037495757100745⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10000 13923 3042 u 30217110574858240 1037495757100745
    (by decide) (by decide) (by decide) (by decide) pole_13923_3042

theorem bank_10034_13932_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10034,13932,3070,u⟩,30660552045363200,1047105796376127⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10034 13932 3070 u 30660552045363200 1047105796376127
    (by decide) (by decide) (by decide) (by decide) pole_13932_3070

theorem bank_10036_13934_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10036,13934,3070,u⟩,30674238602215424,1047589984979998⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10036 13934 3070 u 30674238602215424 1047589984979998
    (by decide) (by decide) (by decide) (by decide) pole_13934_3070

theorem bank_10029_13935_3026 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10029,13935,3026,u⟩,30291674730856448,1036107350026597⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10029 13935 3026 u 30291674730856448 1036107350026597
    (by decide) (by decide) (by decide) (by decide) pole_13935_3026

theorem bank_10004_13937_3026 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10004,13937,3026,u⟩,30122974528667648,1036586141451239⟩ :=
  pack_R6970Height2313CommonRanks76_bank_checked 10004 13937 3026 u 30122974528667648 1036586141451239
    (by decide) (by decide) (by decide) (by decide) pole_13937_3026

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks76

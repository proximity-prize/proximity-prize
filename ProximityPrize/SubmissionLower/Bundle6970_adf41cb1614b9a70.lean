import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0655
import ProximityPrize.SubmissionLower.Z6969Pack0594

section Pack_R6970Height2313CommonRanks13

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks13_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1670_361 :
    P1_7_1.groupedPoleMoment 1670 361 ≤ 213911086908 :=
  _root_.PoleAffine6970.certified 1670 361 213911086908 (by decide) (by decide +kernel)

private theorem pole_1670_365 :
    P1_7_1.groupedPoleMoment 1670 365 ≤ 215752938462 :=
  _root_.PoleAffine6970.certified 1670 365 215752938462 (by decide) (by decide +kernel)

private theorem pole_1670_368 :
    P1_7_1.groupedPoleMoment 1670 368 ≤ 217129800278 :=
  _root_.PoleAffine6970.certified 1670 368 217129800278 (by decide) (by decide +kernel)

private theorem pole_1670_378 :
    P1_7_1.groupedPoleMoment 1670 378 ≤ 221692026804 :=
  _root_.Research6969.PackedRanks.TerminalRanks4To7.moment1670_378

private theorem pole_1671_377 :
    P1_7_1.groupedPoleMoment 1671 377 ≤ 221664578344 :=
  _root_.PoleAffine6970.certified 1671 377 221664578344 (by decide) (by decide +kernel)

private theorem pole_1671_378 :
    P1_7_1.groupedPoleMoment 1671 378 ≤ 222119852616 :=
  _root_.PoleAffine6970.certified 1671 378 222119852616 (by decide) (by decide +kernel)

private theorem pole_1673_362 :
    P1_7_1.groupedPoleMoment 1673 362 ≤ 215613376984 :=
  _root_.PoleAffine6970.certified 1673 362 215613376984 (by decide) (by decide +kernel)

private theorem pole_1673_368 :
    P1_7_1.groupedPoleMoment 1673 368 ≤ 218387554859 :=
  _root_.PoleAffine6970.certified 1673 368 218387554859 (by decide) (by decide +kernel)

private theorem pole_1673_369 :
    P1_7_1.groupedPoleMoment 1673 369 ≤ 218848410398 :=
  _root_.PoleAffine6970.certified 1673 369 218848410398 (by decide) (by decide +kernel)

private theorem pole_1673_370 :
    P1_7_1.groupedPoleMoment 1673 370 ≤ 219308840266 :=
  _root_.PoleAffine6970.certified 1673 370 219308840266 (by decide) (by decide +kernel)

theorem bank_1200_1670_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1200,1670,361,u⟩,51955677528064,213911086908⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1200 1670 361 u 51955677528064 213911086908
    (by decide) (by decide) (by decide) (by decide) pole_1670_361

theorem bank_1201_1670_361 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1201,1670,361,u⟩,52052519026688,213911086908⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1201 1670 361 u 52052519026688 213911086908
    (by decide) (by decide) (by decide) (by decide) pole_1670_361

theorem bank_1202_1670_365 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1670,365,u⟩,52587979866112,215752938462⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1202 1670 365 u 52587979866112 215752938462
    (by decide) (by decide) (by decide) (by decide) pole_1670_365

theorem bank_1200_1670_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1200,1670,368,u⟩,52718727069696,217129800278⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1200 1670 368 u 52718727069696 217129800278
    (by decide) (by decide) (by decide) (by decide) pole_1670_368

theorem bank_1201_1670_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1201,1670,368,u⟩,52817102635008,217129800278⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1201 1670 368 u 52817102635008 217129800278
    (by decide) (by decide) (by decide) (by decide) pole_1670_368

theorem bank_1202_1670_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1202,1670,378,u⟩,53999714697216,221692026804⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1202 1670 378 u 53999714697216 221692026804
    (by decide) (by decide) (by decide) (by decide) pole_1670_378

theorem bank_1205_1671_377 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1671,377,u⟩,54193713315840,221664578344⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1205 1671 377 u 54193713315840 221664578344
    (by decide) (by decide) (by decide) (by decide) pole_1671_377

theorem bank_1205_1671_378 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1671,378,u⟩,54302243291136,222119852616⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1205 1671 378 u 54302243291136 222119852616
    (by decide) (by decide) (by decide) (by decide) pole_1671_378

theorem bank_1200_1673_362 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1200,1673,362,u⟩,52065055539200,215613376984⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1200 1673 362 u 52065055539200 215613376984
    (by decide) (by decide) (by decide) (by decide) pole_1673_362

theorem bank_1203_1673_362 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1673,362,u⟩,52356525326336,215613376984⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1203 1673 362 u 52356525326336 215613376984
    (by decide) (by decide) (by decide) (by decide) pole_1673_362

theorem bank_1204_1673_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1204,1673,368,u⟩,53112809717760,218387554859⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1204 1673 368 u 53112809717760 218387554859
    (by decide) (by decide) (by decide) (by decide) pole_1673_368

theorem bank_1201_1673_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1201,1673,368,u⟩,52817102635008,218387554859⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1201 1673 368 u 52817102635008 218387554859
    (by decide) (by decide) (by decide) (by decide) pole_1673_368

theorem bank_1205_1673_368 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1673,368,u⟩,53211572207616,218387554859⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1205 1673 368 u 53211572207616 218387554859
    (by decide) (by decide) (by decide) (by decide) pole_1673_368

theorem bank_1205_1673_369 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1673,369,u⟩,53321182740480,218848410398⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1205 1673 369 u 53321182740480 218848410398
    (by decide) (by decide) (by decide) (by decide) pole_1673_369

theorem bank_1203_1673_369 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1203,1673,369,u⟩,53123316449280,218848410398⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1203 1673 369 u 53123316449280 218848410398
    (by decide) (by decide) (by decide) (by decide) pole_1673_369

theorem bank_1205_1673_370 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1205,1673,370,u⟩,53430671114240,219308840266⟩ :=
  pack_R6970Height2313CommonRanks13_bank_checked 1205 1673 370 u 53430671114240 219308840266
    (by decide) (by decide) (by decide) (by decide) pole_1673_370

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks13

section Pack_R6970Height2313CommonRanks16

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks16_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2014_445 :
    P1_7_1.groupedPoleMoment 2014 445 ≤ 459863749271 :=
  _root_.PoleAffine6970.certified 2014 445 459863749271 (by decide) (by decide +kernel)

private theorem pole_2015_445 :
    P1_7_1.groupedPoleMoment 2015 445 ≤ 460599143061 :=
  _root_.PoleAffine6970.certified 2015 445 460599143061 (by decide) (by decide +kernel)

private theorem pole_2020_439 :
    P1_7_1.groupedPoleMoment 2020 439 ≤ 459411585633 :=
  _root_.PoleAffine6970.certified 2020 439 459411585633 (by decide) (by decide +kernel)

private theorem pole_2020_457 :
    P1_7_1.groupedPoleMoment 2020 457 ≤ 473974537987 :=
  _root_.Research6969.PackedRanks.TerminalRanks4To7.moment2020_457

private theorem pole_2021_438 :
    P1_7_1.groupedPoleMoment 2021 438 ≤ 459327400936 :=
  _root_.PoleAffine6970.certified 2021 438 459327400936 (by decide) (by decide +kernel)

private theorem pole_2021_445 :
    P1_7_1.groupedPoleMoment 2021 445 ≤ 465028319332 :=
  _root_.PoleAffine6970.certified 2021 445 465028319332 (by decide) (by decide +kernel)

private theorem pole_2021_447 :
    P1_7_1.groupedPoleMoment 2021 447 ≤ 466651512208 :=
  _root_.PoleAffine6970.certified 2021 447 466651512208 (by decide) (by decide +kernel)

private theorem pole_2021_449 :
    P1_7_1.groupedPoleMoment 2021 449 ≤ 468272232157 :=
  _root_.PoleAffine6970.certified 2021 449 468272232157 (by decide) (by decide +kernel)

private theorem pole_2022_445 :
    P1_7_1.groupedPoleMoment 2022 445 ≤ 465769321795 :=
  _root_.PoleAffine6970.certified 2022 445 465769321795 (by decide) (by decide +kernel)

private theorem pole_2022_447 :
    P1_7_1.groupedPoleMoment 2022 447 ≤ 467395198256 :=
  _root_.PoleAffine6970.certified 2022 447 467395198256 (by decide) (by decide +kernel)

theorem bank_1451_2014_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2014,445,u⟩,93142595928064,459863749271⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1451 2014 445 u 93142595928064 459863749271
    (by decide) (by decide) (by decide) (by decide) pole_2014_445

theorem bank_1450_2015_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1450,2015,445,u⟩,92998964346880,460599143061⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1450 2015 445 u 92998964346880 460599143061
    (by decide) (by decide) (by decide) (by decide) pole_2015_445

theorem bank_1451_2015_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1451,2015,445,u⟩,93142595928064,460599143061⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1451 2015 445 u 93142595928064 460599143061
    (by decide) (by decide) (by decide) (by decide) pole_2015_445

theorem bank_1449_2020_439 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1449,2020,439,u⟩,91903628410880,459411585633⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1449 2020 439 u 91903628410880 459411585633
    (by decide) (by decide) (by decide) (by decide) pole_2020_439

theorem bank_1455_2020_457 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1455,2020,457,u⟩,95625142599680,473974537987⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1455 2020 457 u 95625142599680 473974537987
    (by decide) (by decide) (by decide) (by decide) pole_2020_457

theorem bank_1450_2021_438 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1450,2021,438,u⟩,91886136590336,459327400936⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1450 2021 438 u 91886136590336 459327400936
    (by decide) (by decide) (by decide) (by decide) pole_2021_438

theorem bank_1455_2021_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1455,2021,445,u⟩,93718291415040,465028319332⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1455 2021 445 u 93718291415040 465028319332
    (by decide) (by decide) (by decide) (by decide) pole_2021_445

theorem bank_1453_2021_447 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1453,2021,447,u⟩,93748415430656,466651512208⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1453 2021 447 u 93748415430656 466651512208
    (by decide) (by decide) (by decide) (by decide) pole_2021_447

theorem bank_1456_2021_449 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1456,2021,449,u⟩,94501502976000,468272232157⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1456 2021 449 u 94501502976000 468272232157
    (by decide) (by decide) (by decide) (by decide) pole_2021_449

theorem bank_1454_2022_445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1454,2022,445,u⟩,93574192168960,465769321795⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1454 2022 445 u 93574192168960 465769321795
    (by decide) (by decide) (by decide) (by decide) pole_2022_445

theorem bank_1456_2022_447 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1456,2022,447,u⟩,94182299402240,467395198256⟩ :=
  pack_R6970Height2313CommonRanks16_bank_checked 1456 2022 447 u 94182299402240 467395198256
    (by decide) (by decide) (by decide) (by decide) pole_2022_447

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks16

section Pack_R6970Height2313CommonRanks19

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks19_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2426_527 :
    P1_7_1.groupedPoleMoment 2426 527 ≤ 954787561062 :=
  _root_.PoleAffine6970.certified 2426 527 954787561062 (by decide) (by decide +kernel)

private theorem pole_2434_537 :
    P1_7_1.groupedPoleMoment 2434 537 ≤ 979175473612 :=
  _root_.PoleAffine6970.certified 2434 537 979175473612 (by decide) (by decide +kernel)

private theorem pole_2436_522 :
    P1_7_1.groupedPoleMoment 2436 522 ≤ 960344122766 :=
  _root_.PoleAffine6970.certified 2436 522 960344122766 (by decide) (by decide +kernel)

private theorem pole_2437_551 :
    P1_7_1.groupedPoleMoment 2437 551 ≤ 1002904994165 :=
  _root_.Research6969.PackedRanks.TerminalRanks8To11.moment2437_551

private theorem pole_2438_522 :
    P1_7_1.groupedPoleMoment 2438 522 ≤ 962882398143 :=
  _root_.PoleAffine6970.certified 2438 522 962882398143 (by decide) (by decide +kernel)

private theorem pole_2438_528 :
    P1_7_1.groupedPoleMoment 2438 528 ≤ 971500521147 :=
  _root_.PoleAffine6970.certified 2438 528 971500521147 (by decide) (by decide +kernel)

private theorem pole_2438_536 :
    P1_7_1.groupedPoleMoment 2438 536 ≤ 982939289346 :=
  _root_.PoleAffine6970.certified 2438 536 982939289346 (by decide) (by decide +kernel)

private theorem pole_2438_551 :
    P1_7_1.groupedPoleMoment 2438 551 ≤ 1004231319985 :=
  _root_.Research6969.PackedRanks.TerminalRanks8To11.moment2438_551

private theorem pole_2439_519 :
    P1_7_1.groupedPoleMoment 2439 519 ≤ 959825484853 :=
  _root_.PoleAffine6970.certified 2439 519 959825484853 (by decide) (by decide +kernel)

private theorem pole_2439_526 :
    P1_7_1.groupedPoleMoment 2439 526 ≤ 969910301864 :=
  _root_.PoleAffine6970.certified 2439 526 969910301864 (by decide) (by decide +kernel)

theorem bank_1741_2426_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1741,2426,527,u⟩,159218359336960,954787561062⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1741 2426 527 u 159218359336960 954787561062
    (by decide) (by decide) (by decide) (by decide) pole_2426_527

theorem bank_1744_2426_527 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1744,2426,527,u⟩,159832701140992,954787561062⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1744 2426 527 u 159832701140992 954787561062
    (by decide) (by decide) (by decide) (by decide) pole_2426_527

theorem bank_1750_2434_537 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1750,2434,537,u⟩,163381988556800,979175473612⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1750 2434 537 u 163381988556800 979175473612
    (by decide) (by decide) (by decide) (by decide) pole_2434_537

theorem bank_1749_2436_522 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1749,2436,522,u⟩,159695745318912,960344122766⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1749 2436 522 u 159695745318912 960344122766
    (by decide) (by decide) (by decide) (by decide) pole_2436_522

theorem bank_1756_2437_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1756,2437,551,u⟩,167879222755328,1002904994165⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1756 2437 551 u 167879222755328 1002904994165
    (by decide) (by decide) (by decide) (by decide) pole_2437_551

theorem bank_1747_2438_522 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1747,2438,522,u⟩,159287868915712,962882398143⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1747 2438 522 u 159287868915712 962882398143
    (by decide) (by decide) (by decide) (by decide) pole_2438_522

theorem bank_1749_2438_528 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1749,2438,528,u⟩,161091549921280,971500521147⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1749 2438 528 u 161091549921280 971500521147
    (by decide) (by decide) (by decide) (by decide) pole_2438_528

theorem bank_1755_2438_536 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1755,2438,536,u⟩,164196333912064,982939289346⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1755 2438 536 u 164196333912064 982939289346
    (by decide) (by decide) (by decide) (by decide) pole_2438_536

theorem bank_1754_2438_551 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1754,2438,551,u⟩,167450900430848,1004231319985⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1754 2438 551 u 167450900430848 1004231319985
    (by decide) (by decide) (by decide) (by decide) pole_2438_551

theorem bank_1748_2439_519 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1748,2439,519,u⟩,158792317665280,959825484853⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1748 2439 519 u 158792317665280 959825484853
    (by decide) (by decide) (by decide) (by decide) pole_2439_519

theorem bank_1748_2439_526 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1748,2439,526,u⟩,160421722193920,969910301864⟩ :=
  pack_R6970Height2313CommonRanks19_bank_checked 1748 2439 526 u 160421722193920 969910301864
    (by decide) (by decide) (by decide) (by decide) pole_2439_526

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks19

section Pack_R6970Height2313CommonRanks42

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks42_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3628_793 :
    P1_7_1.groupedPoleMoment 3628 793 ≤ 4792991160379 :=
  _root_.Research6969.PackedRanks.TerminalRanks52To55.moment3628_793

private theorem pole_3628_796 :
    P1_7_1.groupedPoleMoment 3628 796 ≤ 4807102837758 :=
  _root_.PoleAffine6970.certified 3628 796 4807102837758 (by decide) (by decide +kernel)

private theorem pole_3628_797 :
    P1_7_1.groupedPoleMoment 3628 797 ≤ 4811802684982 :=
  _root_.PoleAffine6970.certified 3628 797 4811802684982 (by decide) (by decide +kernel)

private theorem pole_3628_798 :
    P1_7_1.groupedPoleMoment 3628 798 ≤ 4816500515660 :=
  _root_.Research6969.PackedRanks.PackedRanks270To272.moment3628_798

private theorem pole_3628_801 :
    P1_7_1.groupedPoleMoment 3628 801 ≤ 4830581955242 :=
  _root_.PoleAffine6970.certified 3628 801 4830581955242 (by decide) (by decide +kernel)

private theorem pole_3628_819 :
    P1_7_1.groupedPoleMoment 3628 819 ≤ 4914696693929 :=
  _root_.Research6969.PackedRanks.TerminalRanks52To55.moment3628_819

private theorem pole_3630_783 :
    P1_7_1.groupedPoleMoment 3630 783 ≤ 4754242757152 :=
  _root_.PoleAffine6970.certified 3630 783 4754242757152 (by decide) (by decide +kernel)

private theorem pole_3630_800 :
    P1_7_1.groupedPoleMoment 3630 800 ≤ 4834461033641 :=
  _root_.PoleAffine6970.certified 3630 800 4834461033641 (by decide) (by decide +kernel)

private theorem pole_3630_815 :
    P1_7_1.groupedPoleMoment 3630 815 ≤ 4904759411010 :=
  _root_.PoleAffine6970.certified 3630 815 4904759411010 (by decide) (by decide +kernel)

private theorem pole_3632_783 :
    P1_7_1.groupedPoleMoment 3632 783 ≤ 4762676203208 :=
  _root_.PoleAffine6970.certified 3632 783 4762676203208 (by decide) (by decide +kernel)

theorem bank_2605_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3628,793,u⟩,535171619618816,4792991160379⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2605 3628 793 u 535171619618816 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2610_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2610,3628,793,u⟩,537473153499136,4792991160379⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2610 3628 793 u 537473153499136 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2608_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3628,793,u⟩,536551915520000,4792991160379⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2608 3628 793 u 536551915520000 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2612_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3628,793,u⟩,538395224047616,4792991160379⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2612 3628 793 u 538395224047616 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2611_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2611,3628,793,u⟩,537934084702208,4792991160379⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2611 3628 793 u 537934084702208 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2604_3628_796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3628,796,u⟩,536248275959808,4807102837758⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2604 3628 796 u 536248275959808 4807102837758
    (by decide) (by decide) (by decide) (by decide) pole_3628_796

theorem bank_2612_3628_797 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3628,797,u⟩,540458353426432,4811802684982⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2612 3628 797 u 540458353426432 4811802684982
    (by decide) (by decide) (by decide) (by decide) pole_3628_797

theorem bank_2607_3628_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3628,798,u⟩,538657964425216,4816500515660⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2607 3628 798 u 538657964425216 4816500515660
    (by decide) (by decide) (by decide) (by decide) pole_3628_798

theorem bank_2606_3628_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3628,798,u⟩,538195492077568,4816500515660⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2606 3628 798 u 538195492077568 4816500515660
    (by decide) (by decide) (by decide) (by decide) pole_3628_798

theorem bank_2605_3628_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3628,798,u⟩,537733229182976,4816500515660⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2605 3628 798 u 537733229182976 4816500515660
    (by decide) (by decide) (by decide) (by decide) pole_3628_798

theorem bank_2612_3628_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3628,798,u⟩,540973467959296,4816500515660⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2612 3628 798 u 540973467959296 4816500515660
    (by decide) (by decide) (by decide) (by decide) pole_3628_798

theorem bank_2612_3628_801 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3628,801,u⟩,542517217198080,4830581955242⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2612 3628 801 u 542517217198080 4830581955242
    (by decide) (by decide) (by decide) (by decide) pole_3628_801

theorem bank_2613_3628_801 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2613,3628,801,u⟩,542982372065280,4830581955242⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2613 3628 801 u 542982372065280 4830581955242
    (by decide) (by decide) (by decide) (by decide) pole_3628_801

theorem bank_2603_3628_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3628,819,u⟩,547476948910080,4914696693929⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2603 3628 819 u 547476948910080 4914696693929
    (by decide) (by decide) (by decide) (by decide) pole_3628_819

theorem bank_2603_3630_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3630,783,u⟩,529118684774400,4754242757152⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2603 3630 783 u 529118684774400 4754242757152
    (by decide) (by decide) (by decide) (by decide) pole_3630_783

theorem bank_2606_3630_800 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3630,800,u⟩,539219229671424,4834461033641⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2606 3630 800 u 539219229671424 4834461033641
    (by decide) (by decide) (by decide) (by decide) pole_3630_800

theorem bank_2614_3630_815 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2614,3630,815,u⟩,550633901916160,4904759411010⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2614 3630 815 u 550633901916160 4904759411010
    (by decide) (by decide) (by decide) (by decide) pole_3630_815

theorem bank_2604_3632_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3632,783,u⟩,529573399756800,4762676203208⟩ :=
  pack_R6970Height2313CommonRanks42_bank_checked 2604 3632 783 u 529573399756800 4762676203208
    (by decide) (by decide) (by decide) (by decide) pole_3632_783

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks42

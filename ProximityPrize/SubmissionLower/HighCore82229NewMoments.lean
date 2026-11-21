import ProximityPrize.SubmissionLower.HighCore82219Moments5
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart0
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart1
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart2
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart3
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart4
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart5
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart6
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart7
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart8
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart9
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart10
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart11
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart12
import ProximityPrize.SubmissionLower.HighCore82229NewMomentsPart13

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nextMoment108_23 : momentEstimate 108 23 = 0x3ca9b9 := nb108_23_0

theorem nextMoment112_24 : momentEstimate 112 24 = 0x464bcb := nb112_24_0

theorem nextMoment136_30 : momentEstimate 136 30 = 0x9a30e6 := nb136_30_0

theorem nextMoment151_33 : momentEstimate 151 33 = 0xe74c1b := nb151_33_0

theorem nextMoment173_38 : momentEstimate 173 38 = 0x18d4b08 := nb173_38_0

theorem nextMoment188_41 : momentEstimate 188 41 = 0x224f886 := nb188_41_0

theorem nextMoment213_47 : momentEstimate 213 47 = 0x38bfb68 := nb213_47_0

theorem nextMoment233_51 : momentEstimate 233 51 = 0x507dc25 := nb233_51_0

theorem nextMoment244_54 : momentEstimate 244 54 = 0x6176fe9 := nb244_54_0

theorem nextMoment268_58 : momentEstimate 268 58 = 0x8b05777 := nb268_58_0

theorem nextMoment300_67 : momentEstimate 300 67 = 0xdedff80 := nb300_67_0

theorem nextMoment307_67 : momentEstimate 307 67 = 0xeffb6fa := nb307_67_0

theorem nextMoment371_84 : momentEstimate 371 84 = 0x20c08c09 := nb371_84_0

theorem nextMoment380_84 : momentEstimate 380 84 = 0x235f32c1 := nb380_84_0

theorem nextMoment392_88 : momentEstimate 392 88 = 0x2881bf10 := nb392_88_0

theorem nextMoment407_89 : momentEstimate 407 89 = 0x2e1859e9 := nb407_89_0

theorem nextMoment414_87 : momentEstimate 414 87 = 0x2fd6e865 := nb414_87_0

theorem nextMoment415_91 : momentEstimate 415 91 = 0x31e9f423 := nb415_91_0

theorem nextMoment552_121 : momentEstimate 552 121 = 0x9b6be4a3 := nb552_121_0

theorem nextMoment562_118 : momentEstimate 562 118 = 0xa178c6a5 := nb562_118_0

theorem nextMoment595_125 : momentEstimate 595 125 = 0xcaca5052 := nb595_125_0

theorem nextMoment615_129 : momentEstimate 615 129 = 0xe712e33d := nb615_129_0

theorem na683_143_1 : blockEstimate 683 143 143 826 = 0x15e85234c :=
  block_append nb683_143_0 nb683_143_1 rfl rfl rfl
theorem nextMoment683_143 : momentEstimate 683 143 = 0x15e85234c := na683_143_1

theorem na692_155_1 : blockEstimate 692 155 155 847 = 0x185234383 :=
  block_append nb692_155_0 nb692_155_1 rfl rfl rfl
theorem nextMoment692_155 : momentEstimate 692 155 = 0x185234383 := na692_155_1

theorem na738_155_1 : blockEstimate 738 155 155 893 = 0x1de880865 :=
  block_append nb738_155_0 nb738_155_1 rfl rfl rfl
theorem nextMoment738_155 : momentEstimate 738 155 = 0x1de880865 := na738_155_1

theorem na844_187_1 : blockEstimate 844 187 187 1031 = 0x3540983af :=
  block_append nb844_187_0 nb844_187_1 rfl rfl rfl
theorem nextMoment844_187 : momentEstimate 844 187 = 0x3540983af := na844_187_1

theorem na882_186_1 : blockEstimate 882 186 186 1068 = 0x3d18186c7 :=
  block_append nb882_186_0 nb882_186_1 rfl rfl rfl
theorem nextMoment882_186 : momentEstimate 882 186 = 0x3d18186c7 := na882_186_1

theorem na911_204_1 : blockEstimate 911 204 204 1115 = 0x48d3f0165 :=
  block_append nb911_204_0 nb911_204_1 rfl rfl rfl
theorem nextMoment911_204 : momentEstimate 911 204 = 0x48d3f0165 := na911_204_1

theorem na975_205_1 : blockEstimate 975 205 205 1180 = 0x5aef90203 :=
  block_append nb975_205_0 nb975_205_1 rfl rfl rfl
theorem nextMoment975_205 : momentEstimate 975 205 = 0x5aef90203 := na975_205_1

theorem na1106_244_1 : blockEstimate 1106 244 244 1350 = 0x9c255acf1 :=
  block_append nb1106_244_0 nb1106_244_1 rfl rfl rfl
theorem nextMoment1106_244 : momentEstimate 1106 244 = 0x9c255acf1 := na1106_244_1

theorem na1154_244_1 : blockEstimate 1154 244 244 1398 = 0xb2ffabfb1 :=
  block_append nb1154_244_0 nb1154_244_1 rfl rfl rfl
theorem nextMoment1154_244 : momentEstimate 1154 244 = 0xb2ffabfb1 := na1154_244_1

theorem na1235_261_1 : blockEstimate 1235 261 261 1496 = 0xea98932cb :=
  block_append nb1235_261_0 nb1235_261_1 rfl rfl rfl
theorem nextMoment1235_261 : momentEstimate 1235 261 = 0xea98932cb := na1235_261_1

theorem na1298_273_1 : blockEstimate 1298 273 273 1571 = 0x11d168cd1f :=
  block_append nb1298_273_0 nb1298_273_1 rfl rfl rfl
theorem nextMoment1298_273 : momentEstimate 1298 273 = 0x11d168cd1f := na1298_273_1

theorem na1307_276_1 : blockEstimate 1307 276 276 1583 = 0x125fc26c02 :=
  block_append nb1307_276_0 nb1307_276_1 rfl rfl rfl
theorem nextMoment1307_276 : momentEstimate 1307 276 = 0x125fc26c02 := na1307_276_1

theorem na1687_355_1 : blockEstimate 1687 355 355 1600 = 0x3048ff9b2b :=
  block_append nb1687_355_0 nb1687_355_1 rfl rfl rfl
theorem na1687_355_2 : blockEstimate 1687 355 355 2042 = 0x32c91050b2 :=
  block_append na1687_355_1 nb1687_355_2 rfl rfl rfl
theorem nextMoment1687_355 : momentEstimate 1687 355 = 0x32c91050b2 := na1687_355_2

theorem na1721_365_1 : blockEstimate 1721 365 365 1600 = 0x33fddce612 :=
  block_append nb1721_365_0 nb1721_365_1 rfl rfl rfl
theorem na1721_365_2 : blockEstimate 1721 365 365 2086 = 0x37562c3cfd :=
  block_append na1721_365_1 nb1721_365_2 rfl rfl rfl
theorem nextMoment1721_365 : momentEstimate 1721 365 = 0x37562c3cfd := na1721_365_2

theorem na1835_388_1 : blockEstimate 1835 388 388 1600 = 0x401f3b7d12 :=
  block_append nb1835_388_0 nb1835_388_1 rfl rfl rfl
theorem na1835_388_2 : blockEstimate 1835 388 388 2223 = 0x47547d44aa :=
  block_append na1835_388_1 nb1835_388_2 rfl rfl rfl
theorem nextMoment1835_388 : momentEstimate 1835 388 = 0x47547d44aa := na1835_388_2

theorem na1977_416_1 : blockEstimate 1977 416 416 1600 = 0x507962b0c8 :=
  block_append nb1977_416_0 nb1977_416_1 rfl rfl rfl
theorem na1977_416_2 : blockEstimate 1977 416 416 2393 = 0x5fb60cd0a4 :=
  block_append na1977_416_1 nb1977_416_2 rfl rfl rfl
theorem nextMoment1977_416 : momentEstimate 1977 416 = 0x5fb60cd0a4 := na1977_416_2

theorem na2096_439_1 : blockEstimate 2096 439 439 1600 = 0x5f064bf3a6 :=
  block_append nb2096_439_0 nb2096_439_1 rfl rfl rfl
theorem na2096_439_2 : blockEstimate 2096 439 439 2400 = 0x785a78777f :=
  block_append na2096_439_1 nb2096_439_2 rfl rfl rfl
theorem na2096_439_3 : blockEstimate 2096 439 439 2535 = 0x787427c579 :=
  block_append na2096_439_2 nb2096_439_3 rfl rfl rfl
theorem nextMoment2096_439 : momentEstimate 2096 439 = 0x787427c579 := na2096_439_3

theorem na2096_448_1 : blockEstimate 2096 448 448 1600 = 0x6042b613f0 :=
  block_append nb2096_448_0 nb2096_448_1 rfl rfl rfl
theorem na2096_448_2 : blockEstimate 2096 448 448 2400 = 0x7a41cfc921 :=
  block_append na2096_448_1 nb2096_448_2 rfl rfl rfl
theorem na2096_448_3 : blockEstimate 2096 448 448 2544 = 0x7a60dae739 :=
  block_append na2096_448_2 nb2096_448_3 rfl rfl rfl
theorem nextMoment2096_448 : momentEstimate 2096 448 = 0x7a60dae739 := na2096_448_3

theorem na2179_461_1 : blockEstimate 2179 461 461 1600 = 0x6a767d67cb :=
  block_append nb2179_461_0 nb2179_461_1 rfl rfl rfl
theorem na2179_461_2 : blockEstimate 2179 461 461 2400 = 0x8d3890911d :=
  block_append na2179_461_1 nb2179_461_2 rfl rfl rfl
theorem na2179_461_3 : blockEstimate 2179 461 461 2640 = 0x8dc92dfed1 :=
  block_append na2179_461_2 nb2179_461_3 rfl rfl rfl
theorem nextMoment2179_461 : momentEstimate 2179 461 = 0x8dc92dfed1 := na2179_461_3

theorem na2395_500_1 : blockEstimate 2395 500 500 1600 = 0x87200053cd :=
  block_append nb2395_500_0 nb2395_500_1 rfl rfl rfl
theorem na2395_500_2 : blockEstimate 2395 500 500 2400 = 0xc7942efe44 :=
  block_append na2395_500_1 nb2395_500_2 rfl rfl rfl
theorem na2395_500_3 : blockEstimate 2395 500 500 2895 = 0xccb7865054 :=
  block_append na2395_500_2 nb2395_500_3 rfl rfl rfl
theorem nextMoment2395_500 : momentEstimate 2395 500 = 0xccb7865054 := na2395_500_3

theorem na2479_526_1 : blockEstimate 2479 526 526 1600 = 0x949ac1afb4 :=
  block_append nb2479_526_0 nb2479_526_1 rfl rfl rfl
theorem na2479_526_2 : blockEstimate 2479 526 526 2400 = 0xe474e9064a :=
  block_append na2479_526_1 nb2479_526_2 rfl rfl rfl
theorem na2479_526_3 : blockEstimate 2479 526 526 3005 = 0xedf44d5ab0 :=
  block_append na2479_526_2 nb2479_526_3 rfl rfl rfl
theorem nextMoment2479_526 : momentEstimate 2479 526 = 0xedf44d5ab0 := na2479_526_3

theorem na3244_683_1 : blockEstimate 3244 683 683 1600 = 0x10d8bfb71e9 :=
  block_append nb3244_683_0 nb3244_683_1 rfl rfl rfl
theorem na3244_683_2 : blockEstimate 3244 683 683 2400 = 0x20dcb9c1249 :=
  block_append na3244_683_1 nb3244_683_2 rfl rfl rfl
theorem na3244_683_3 : blockEstimate 3244 683 683 3200 = 0x29f351a696b :=
  block_append na3244_683_2 nb3244_683_3 rfl rfl rfl
theorem na3244_683_4 : blockEstimate 3244 683 683 3927 = 0x2b4fcb8af08 :=
  block_append na3244_683_3 nb3244_683_4 rfl rfl rfl
theorem nextMoment3244_683 : momentEstimate 3244 683 = 0x2b4fcb8af08 := na3244_683_4

theorem na3787_799_1 : blockEstimate 3787 799 799 1600 = 0x16c77061668 :=
  block_append nb3787_799_0 nb3787_799_1 rfl rfl rfl
theorem na3787_799_2 : blockEstimate 3787 799 799 2400 = 0x30ef50d1f68 :=
  block_append na3787_799_1 nb3787_799_2 rfl rfl rfl
theorem na3787_799_3 : blockEstimate 3787 799 799 3200 = 0x468c40a7dc7 :=
  block_append na3787_799_2 nb3787_799_3 rfl rfl rfl
theorem na3787_799_4 : blockEstimate 3787 799 799 4000 = 0x4fad228a3f9 :=
  block_append na3787_799_3 nb3787_799_4 rfl rfl rfl
theorem na3787_799_5 : blockEstimate 3787 799 799 4586 = 0x508a478f764 :=
  block_append na3787_799_4 nb3787_799_5 rfl rfl rfl
theorem nextMoment3787_799 : momentEstimate 3787 799 = 0x508a478f764 := na3787_799_5

theorem na4935_1017_1 : blockEstimate 4935 1017 1017 1600 = 0x23820625eda :=
  block_append nb4935_1017_0 nb4935_1017_1 rfl rfl rfl
theorem na4935_1017_2 : blockEstimate 4935 1017 1017 2400 = 0x56c7e2e58ca :=
  block_append na4935_1017_1 nb4935_1017_2 rfl rfl rfl
theorem na4935_1017_3 : blockEstimate 4935 1017 1017 3200 = 0x90279693eba :=
  block_append na4935_1017_2 nb4935_1017_3 rfl rfl rfl
theorem na4935_1017_4 : blockEstimate 4935 1017 1017 4000 = 0xc0764a14ed6 :=
  block_append na4935_1017_3 nb4935_1017_4 rfl rfl rfl
theorem na4935_1017_5 : blockEstimate 4935 1017 1017 4800 = 0xdbb983ec4f9 :=
  block_append na4935_1017_4 nb4935_1017_5 rfl rfl rfl
theorem na4935_1017_6 : blockEstimate 4935 1017 1017 5600 = 0xe3a5104706e :=
  block_append na4935_1017_5 nb4935_1017_6 rfl rfl rfl
theorem na4935_1017_7 : blockEstimate 4935 1017 1017 5952 = 0xe3e67c2d9d6 :=
  block_append na4935_1017_6 nb4935_1017_7 rfl rfl rfl
theorem nextMoment4935_1017 : momentEstimate 4935 1017 = 0xe3e67c2d9d6 := na4935_1017_7

theorem na5036_1070_1 : blockEstimate 5036 1070 1070 1600 = 0x24e5c35c657 :=
  block_append nb5036_1070_0 nb5036_1070_1 rfl rfl rfl
theorem na5036_1070_2 : blockEstimate 5036 1070 1070 2400 = 0x5bb7240e4a7 :=
  block_append na5036_1070_1 nb5036_1070_2 rfl rfl rfl
theorem na5036_1070_3 : blockEstimate 5036 1070 1070 3200 = 0x9a393d0f6f7 :=
  block_append na5036_1070_2 nb5036_1070_3 rfl rfl rfl
theorem na5036_1070_4 : blockEstimate 5036 1070 1070 4000 = 0xd0768d7f4e9 :=
  block_append na5036_1070_3 nb5036_1070_4 rfl rfl rfl
theorem na5036_1070_5 : blockEstimate 5036 1070 1070 4800 = 0xf1245ff1479 :=
  block_append na5036_1070_4 nb5036_1070_5 rfl rfl rfl
theorem na5036_1070_6 : blockEstimate 5036 1070 1070 5600 = 0xfc5a2fcc962 :=
  block_append na5036_1070_5 nb5036_1070_6 rfl rfl rfl
theorem na5036_1070_7 : blockEstimate 5036 1070 1070 6106 = 0xfd1cefeba54 :=
  block_append na5036_1070_6 nb5036_1070_7 rfl rfl rfl
theorem nextMoment5036_1070 : momentEstimate 5036 1070 = 0xfd1cefeba54 := na5036_1070_7

theorem na6482_1369_1 : blockEstimate 6482 1369 1369 1600 = 0x346e1ed4aba :=
  block_append nb6482_1369_0 nb6482_1369_1 rfl rfl rfl
theorem na6482_1369_2 : blockEstimate 6482 1369 1369 2400 = 0x91a9607daaa :=
  block_append na6482_1369_1 nb6482_1369_2 rfl rfl rfl
theorem na6482_1369_3 : blockEstimate 6482 1369 1369 3200 = 0x10d166a00e9a :=
  block_append na6482_1369_2 nb6482_1369_3 rfl rfl rfl
theorem na6482_1369_4 : blockEstimate 6482 1369 1369 4000 = 0x1924b18be68a :=
  block_append na6482_1369_3 nb6482_1369_4 rfl rfl rfl
theorem na6482_1369_5 : blockEstimate 6482 1369 1369 4800 = 0x20cdd4a1627a :=
  block_append na6482_1369_4 nb6482_1369_5 rfl rfl rfl
theorem na6482_1369_6 : blockEstimate 6482 1369 1369 5600 = 0x268fcc1616a6 :=
  block_append na6482_1369_5 nb6482_1369_6 rfl rfl rfl
theorem na6482_1369_7 : blockEstimate 6482 1369 1369 6400 = 0x29da57804a2d :=
  block_append na6482_1369_6 nb6482_1369_7 rfl rfl rfl
theorem na6482_1369_8 : blockEstimate 6482 1369 1369 7200 = 0x2b11ff13c364 :=
  block_append na6482_1369_7 nb6482_1369_8 rfl rfl rfl
theorem na6482_1369_9 : blockEstimate 6482 1369 1369 7851 = 0x2b334b40c95c :=
  block_append na6482_1369_8 nb6482_1369_9 rfl rfl rfl
theorem nextMoment6482_1369 : momentEstimate 6482 1369 = 0x2b334b40c95c := na6482_1369_9

theorem na7120_1510_1 : blockEstimate 7120 1510 1510 1600 = 0x3aeafb3dc95 :=
  block_append nb7120_1510_0 nb7120_1510_1 rfl rfl rfl
theorem na7120_1510_2 : blockEstimate 7120 1510 1510 2400 = 0xaa29e7a3465 :=
  block_append na7120_1510_1 nb7120_1510_2 rfl rfl rfl
theorem na7120_1510_3 : blockEstimate 7120 1510 1510 3200 = 0x144ae87c2035 :=
  block_append na7120_1510_2 nb7120_1510_3 rfl rfl rfl
theorem na7120_1510_4 : blockEstimate 7120 1510 1510 4000 = 0x1f3f4d9aa005 :=
  block_append na7120_1510_3 nb7120_1510_4 rfl rfl rfl
theorem na7120_1510_5 : blockEstimate 7120 1510 1510 4800 = 0x2a178db6b3d5 :=
  block_append na7120_1510_4 nb7120_1510_5 rfl rfl rfl
theorem na7120_1510_6 : blockEstimate 7120 1510 1510 5600 = 0x336b68b15ba5 :=
  block_append na7120_1510_5 nb7120_1510_6 rfl rfl rfl
theorem na7120_1510_7 : blockEstimate 7120 1510 1510 6400 = 0x3a0222d93062 :=
  block_append na7120_1510_6 nb7120_1510_7 rfl rfl rfl
theorem na7120_1510_8 : blockEstimate 7120 1510 1510 7200 = 0x3da6cbadd7fe :=
  block_append na7120_1510_7 nb7120_1510_8 rfl rfl rfl
theorem na7120_1510_9 : blockEstimate 7120 1510 1510 8000 = 0x3ef4927d217a :=
  block_append na7120_1510_8 nb7120_1510_9 rfl rfl rfl
theorem na7120_1510_10 : blockEstimate 7120 1510 1510 8630 = 0x3f15ec384879 :=
  block_append na7120_1510_9 nb7120_1510_10 rfl rfl rfl
theorem nextMoment7120_1510 : momentEstimate 7120 1510 = 0x3f15ec384879 := na7120_1510_10

end HighCore82219BankProof

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

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (momentEstimate blockEstimate block_append)

theorem nextMoment148_33 : momentEstimate 148 33 = 0xd8f2fa := w148_33_0

theorem m175_39_39_214 : blockEstimate 175 39 39 214 = 0x1a458a5 :=
  block_append (B := 175) (J := 39) (start := 39) (next := 239)
    (a := 200) (b := 14) (n := 214) (x := 0x1a38d3b) (y := 0xcb6a) (z := 0x1a458a5)
    w175_39_0 w175_39_1 rfl rfl rfl

theorem nextMoment175_39 : momentEstimate 175 39 = 0x1a458a5 := m175_39_39_214

theorem m247_55_55_302 : blockEstimate 247 55 55 302 = 0x66c8fdf :=
  block_append (B := 247) (J := 55) (start := 55) (next := 255)
    (a := 200) (b := 102) (n := 302) (x := 0x5597b9e) (y := 0x1131441) (z := 0x66c8fdf)
    w247_55_0 w247_55_1 rfl rfl rfl

theorem nextMoment247_55 : momentEstimate 247 55 = 0x66c8fdf := m247_55_55_302

theorem m347_78_278_225 : blockEstimate 347 78 278 225 = 0xc38fe2c :=
  block_append (B := 347) (J := 78) (start := 278) (next := 478)
    (a := 200) (b := 25) (n := 225) (x := 0xc31102c) (y := 0x7ee00) (z := 0xc38fe2c)
    w347_78_1 w347_78_2 rfl rfl rfl

theorem m347_78_78_425 : blockEstimate 347 78 78 425 = 0x18f6d6a4 :=
  block_append (B := 347) (J := 78) (start := 78) (next := 278)
    (a := 200) (b := 225) (n := 425) (x := 0xcbdd878) (y := 0xc38fe2c) (z := 0x18f6d6a4)
    w347_78_0 m347_78_278_225 rfl rfl rfl

theorem nextMoment347_78 : momentEstimate 347 78 = 0x18f6d6a4 := m347_78_78_425

theorem m478_108_308_386 : blockEstimate 478 108 308 386 = 0x41796b40 :=
  block_append (B := 478) (J := 108) (start := 308) (next := 508)
    (a := 200) (b := 186) (n := 386) (x := 0x34e22986) (y := 0xc9741ba) (z := 0x41796b40)
    w478_108_1 w478_108_2 rfl rfl rfl

theorem m478_108_108_586 : blockEstimate 478 108 108 586 = 0x59a98629 :=
  block_append (B := 478) (J := 108) (start := 108) (next := 308)
    (a := 200) (b := 386) (n := 586) (x := 0x18301ae9) (y := 0x41796b40) (z := 0x59a98629)
    w478_108_0 m478_108_308_386 rfl rfl rfl

theorem nextMoment478_108 : momentEstimate 478 108 = 0x59a98629 := m478_108_108_586

theorem m522_118_118_400 : blockEstimate 522 118 118 400 = 0x63b045b7 :=
  block_append (B := 522) (J := 118) (start := 118) (next := 318)
    (a := 200) (b := 200) (n := 400) (x := 0x1c30de3b) (y := 0x477f677c) (z := 0x63b045b7)
    w522_118_0 w522_118_1 rfl rfl rfl

theorem m522_118_518_240 : blockEstimate 522 118 518 240 = 0x1bb23022 :=
  block_append (B := 522) (J := 118) (start := 518) (next := 718)
    (a := 200) (b := 40) (n := 240) (x := 0x1b847042) (y := 0x2dbfe0) (z := 0x1bb23022)
    w522_118_2 w522_118_3 rfl rfl rfl

theorem m522_118_118_640 : blockEstimate 522 118 118 640 = 0x7f6275d9 :=
  block_append (B := 522) (J := 118) (start := 118) (next := 518)
    (a := 400) (b := 240) (n := 640) (x := 0x63b045b7) (y := 0x1bb23022) (z := 0x7f6275d9)
    m522_118_118_400 m522_118_518_240 rfl rfl rfl

theorem nextMoment522_118 : momentEstimate 522 118 = 0x7f6275d9 := m522_118_118_640

theorem m606_128_128_400 : blockEstimate 606 128 128 400 = 0x8d9de9c0 :=
  block_append (B := 606) (J := 128) (start := 128) (next := 328)
    (a := 200) (b := 200) (n := 400) (x := 0x23459730) (y := 0x6a585290) (z := 0x8d9de9c0)
    w606_128_0 w606_128_1 rfl rfl rfl

theorem m606_128_528_334 : blockEstimate 606 128 528 334 = 0x4d7369b2 :=
  block_append (B := 606) (J := 128) (start := 528) (next := 728)
    (a := 200) (b := 134) (n := 334) (x := 0x46bb458e) (y := 0x6b82424) (z := 0x4d7369b2)
    w606_128_2 w606_128_3 rfl rfl rfl

theorem m606_128_128_734 : blockEstimate 606 128 128 734 = 0xdb115372 :=
  block_append (B := 606) (J := 128) (start := 128) (next := 528)
    (a := 400) (b := 334) (n := 734) (x := 0x8d9de9c0) (y := 0x4d7369b2) (z := 0xdb115372)
    m606_128_128_400 m606_128_528_334 rfl rfl rfl

theorem nextMoment606_128 : momentEstimate 606 128 = 0xdb115372 := m606_128_128_734

theorem m608_128_128_400 : blockEstimate 608 128 128 400 = 0x8e7f86d0 :=
  block_append (B := 608) (J := 128) (start := 128) (next := 328)
    (a := 200) (b := 200) (n := 400) (x := 0x236cfeb8) (y := 0x6b128818) (z := 0x8e7f86d0)
    w608_128_0 w608_128_1 rfl rfl rfl

theorem m608_128_528_336 : blockEstimate 608 128 528 336 = 0x4ee5f662 :=
  block_append (B := 608) (J := 128) (start := 528) (next := 728)
    (a := 200) (b := 136) (n := 336) (x := 0x47dd1f80) (y := 0x708d6e2) (z := 0x4ee5f662)
    w608_128_2 w608_128_3 rfl rfl rfl

theorem m608_128_128_736 : blockEstimate 608 128 128 736 = 0xdd657d32 :=
  block_append (B := 608) (J := 128) (start := 128) (next := 528)
    (a := 400) (b := 336) (n := 736) (x := 0x8e7f86d0) (y := 0x4ee5f662) (z := 0xdd657d32)
    m608_128_128_400 m608_128_528_336 rfl rfl rfl

theorem nextMoment608_128 : momentEstimate 608 128 = 0xdd657d32 := m608_128_128_736

theorem m686_144_144_400 : blockEstimate 686 144 144 400 = 0xbd520be4 :=
  block_append (B := 686) (J := 144) (start := 144) (next := 344)
    (a := 200) (b := 200) (n := 400) (x := 0x2a6d18b4) (y := 0x92e4f330) (z := 0xbd520be4)
    w686_144_0 w686_144_1 rfl rfl rfl

theorem m686_144_744_230 : blockEstimate 686 144 744 230 = 0x2343abf7 :=
  block_append (B := 686) (J := 144) (start := 744) (next := 944)
    (a := 200) (b := 30) (n := 230) (x := 0x2328fcfb) (y := 0x1aaefc) (z := 0x2343abf7)
    w686_144_3 w686_144_4 rfl rfl rfl

theorem m686_144_544_430 : blockEstimate 686 144 544 430 = 0xa81901d0 :=
  block_append (B := 686) (J := 144) (start := 544) (next := 744)
    (a := 200) (b := 230) (n := 430) (x := 0x84d555d9) (y := 0x2343abf7) (z := 0xa81901d0)
    w686_144_2 m686_144_744_230 rfl rfl rfl

theorem m686_144_144_830 : blockEstimate 686 144 144 830 = 0x1656b0db4 :=
  block_append (B := 686) (J := 144) (start := 144) (next := 544)
    (a := 400) (b := 430) (n := 830) (x := 0xbd520be4) (y := 0xa81901d0) (z := 0x1656b0db4)
    m686_144_144_400 m686_144_544_430 rfl rfl rfl

theorem nextMoment686_144 : momentEstimate 686 144 = 0x1656b0db4 := m686_144_144_830

theorem m692_155_155_400 : blockEstimate 692 155 155 400 = 0xc7e67e05 :=
  block_append (B := 692) (J := 155) (start := 155) (next := 355)
    (a := 200) (b := 200) (n := 400) (x := 0x2b53c7cd) (y := 0x9c92b638) (z := 0xc7e67e05)
    w692_155_0 w692_155_1 rfl rfl rfl

theorem m692_155_755_247 : blockEstimate 692 155 755 247 = 0x2b6f597b :=
  block_append (B := 692) (J := 155) (start := 755) (next := 955)
    (a := 200) (b := 47) (n := 247) (x := 0x2b0e22ef) (y := 0x61368c) (z := 0x2b6f597b)
    w692_155_3 w692_155_4 rfl rfl rfl

theorem m692_155_555_447 : blockEstimate 692 155 555 447 = 0xbd3cc57e :=
  block_append (B := 692) (J := 155) (start := 555) (next := 755)
    (a := 200) (b := 247) (n := 447) (x := 0x91cd6c03) (y := 0x2b6f597b) (z := 0xbd3cc57e)
    w692_155_2 m692_155_755_247 rfl rfl rfl

theorem m692_155_155_847 : blockEstimate 692 155 155 847 = 0x185234383 :=
  block_append (B := 692) (J := 155) (start := 155) (next := 555)
    (a := 400) (b := 447) (n := 847) (x := 0xc7e67e05) (y := 0xbd3cc57e) (z := 0x185234383)
    m692_155_155_400 m692_155_555_447 rfl rfl rfl

theorem nextMoment692_155 : momentEstimate 692 155 = 0x185234383 := m692_155_155_847

theorem m706_149_149_400 : blockEstimate 706 149 149 400 = 0xca8aedfd :=
  block_append (B := 706) (J := 149) (start := 149) (next := 349)
    (a := 200) (b := 200) (n := 400) (x := 0x2c3a7ac9) (y := 0x9e507334) (z := 0xca8aedfd)
    w706_149_0 w706_149_1 rfl rfl rfl

theorem m706_149_749_255 : blockEstimate 706 149 749 255 = 0x306f03ee :=
  block_append (B := 706) (J := 149) (start := 749) (next := 949)
    (a := 200) (b := 55) (n := 255) (x := 0x2fd2f22c) (y := 0x9c11c2) (z := 0x306f03ee)
    w706_149_3 w706_149_4 rfl rfl rfl

theorem m706_149_549_455 : blockEstimate 706 149 549 455 = 0xc7f5cf80 :=
  block_append (B := 706) (J := 149) (start := 549) (next := 749)
    (a := 200) (b := 255) (n := 455) (x := 0x9786cb92) (y := 0x306f03ee) (z := 0xc7f5cf80)
    w706_149_2 m706_149_749_255 rfl rfl rfl

theorem m706_149_149_855 : blockEstimate 706 149 149 855 = 0x19280bd7d :=
  block_append (B := 706) (J := 149) (start := 149) (next := 549)
    (a := 400) (b := 455) (n := 855) (x := 0xca8aedfd) (y := 0xc7f5cf80) (z := 0x19280bd7d)
    m706_149_149_400 m706_149_549_455 rfl rfl rfl

theorem nextMoment706_149 : momentEstimate 706 149 = 0x19280bd7d := m706_149_149_855

theorem m731_154_154_400 : blockEstimate 731 154 154 400 = 0xda7136e1 :=
  block_append (B := 731) (J := 154) (start := 154) (next := 354)
    (a := 200) (b := 200) (n := 400) (x := 0x2e678319) (y := 0xac09b3c8) (z := 0xda7136e1)
    w731_154_0 w731_154_1 rfl rfl rfl

theorem m731_154_754_285 : blockEstimate 731 154 754 285 = 0x4450b92b :=
  block_append (B := 731) (J := 154) (start := 754) (next := 954)
    (a := 200) (b := 85) (n := 285) (x := 0x4217811e) (y := 0x239380d) (z := 0x4450b92b)
    w731_154_3 w731_154_4 rfl rfl rfl

theorem m731_154_554_485 : blockEstimate 731 154 554 485 = 0xf356a357 :=
  block_append (B := 731) (J := 154) (start := 554) (next := 754)
    (a := 200) (b := 285) (n := 485) (x := 0xaf05ea2c) (y := 0x4450b92b) (z := 0xf356a357)
    w731_154_2 m731_154_754_285 rfl rfl rfl

theorem m731_154_154_885 : blockEstimate 731 154 154 885 = 0x1cdc7da38 :=
  block_append (B := 731) (J := 154) (start := 154) (next := 554)
    (a := 400) (b := 485) (n := 885) (x := 0xda7136e1) (y := 0xf356a357) (z := 0x1cdc7da38)
    m731_154_154_400 m731_154_554_485 rfl rfl rfl

theorem nextMoment731_154 : momentEstimate 731 154 = 0x1cdc7da38 := m731_154_154_885

theorem m831_188_388_400 : blockEstimate 831 188 388 400 = 0x217df9d78 :=
  block_append (B := 831) (J := 188) (start := 388) (next := 588)
    (a := 200) (b := 200) (n := 400) (x := 0xefc6079c) (y := 0x1281995dc) (z := 0x217df9d78)
    w831_188_1 w831_188_2 rfl rfl rfl

theorem m831_188_188_600 : blockEstimate 831 188 188 600 = 0x24edbd51f :=
  block_append (B := 831) (J := 188) (start := 188) (next := 388)
    (a := 200) (b := 400) (n := 600) (x := 0x36fc37a7) (y := 0x217df9d78) (z := 0x24edbd51f)
    w831_188_0 m831_188_388_400 rfl rfl rfl

theorem m831_188_988_219 : blockEstimate 831 188 988 219 = 0x26c6a696 :=
  block_append (B := 831) (J := 188) (start := 988) (next := 1188)
    (a := 200) (b := 19) (n := 219) (x := 0x26bdacb7) (y := 0x8f9df) (z := 0x26c6a696)
    w831_188_4 w831_188_5 rfl rfl rfl

theorem m831_188_788_419 : blockEstimate 831 188 788 419 = 0xdf0647f4 :=
  block_append (B := 831) (J := 188) (start := 788) (next := 988)
    (a := 200) (b := 219) (n := 419) (x := 0xb83fa15e) (y := 0x26c6a696) (z := 0xdf0647f4)
    w831_188_3 m831_188_988_219 rfl rfl rfl

theorem m831_188_188_1019 : blockEstimate 831 188 188 1019 = 0x32de21d13 :=
  block_append (B := 831) (J := 188) (start := 188) (next := 788)
    (a := 600) (b := 419) (n := 1019) (x := 0x24edbd51f) (y := 0xdf0647f4) (z := 0x32de21d13)
    m831_188_188_600 m831_188_788_419 rfl rfl rfl

theorem nextMoment831_188 : momentEstimate 831 188 = 0x32de21d13 := m831_188_188_1019

theorem m892_188_388_400 : blockEstimate 892 188 388 400 = 0x26c1f3ba0 :=
  block_append (B := 892) (J := 188) (start := 388) (next := 588)
    (a := 200) (b := 200) (n := 400) (x := 0x10c277790) (y := 0x15ff7c410) (z := 0x26c1f3ba0)
    w892_188_1 w892_188_2 rfl rfl rfl

theorem m892_188_188_600 : blockEstimate 892 188 188 600 = 0x2a806e8f9 :=
  block_append (B := 892) (J := 188) (start := 188) (next := 388)
    (a := 200) (b := 400) (n := 600) (x := 0x3be7ad59) (y := 0x26c1f3ba0) (z := 0x2a806e8f9)
    w892_188_0 m892_188_388_400 rfl rfl rfl

theorem m892_188_988_280 : blockEstimate 892 188 988 280 = 0x53b170ba :=
  block_append (B := 892) (J := 188) (start := 988) (next := 1188)
    (a := 200) (b := 80) (n := 280) (x := 0x5164f0f2) (y := 0x24c7fc8) (z := 0x53b170ba)
    w892_188_4 w892_188_5 rfl rfl rfl

theorem m892_188_788_480 : blockEstimate 892 188 788 480 = 0x155ffa6ac :=
  block_append (B := 892) (J := 188) (start := 788) (next := 988)
    (a := 200) (b := 280) (n := 480) (x := 0x1024e35f2) (y := 0x53b170ba) (z := 0x155ffa6ac)
    w892_188_3 m892_188_988_280 rfl rfl rfl

theorem m892_188_188_1080 : blockEstimate 892 188 188 1080 = 0x3fe068fa5 :=
  block_append (B := 892) (J := 188) (start := 188) (next := 788)
    (a := 600) (b := 480) (n := 1080) (x := 0x2a806e8f9) (y := 0x155ffa6ac) (z := 0x3fe068fa5)
    m892_188_188_600 m892_188_788_480 rfl rfl rfl

theorem nextMoment892_188 : momentEstimate 892 188 = 0x3fe068fa5 := m892_188_188_1080

theorem m952_201_401_400 : blockEstimate 952 201 401 400 = 0x2de0c28b8 :=
  block_append (B := 952) (J := 201) (start := 401) (next := 601)
    (a := 200) (b := 200) (n := 400) (x := 0x1323896bc) (y := 0x1abd391fc) (z := 0x2de0c28b8)
    w952_201_1 w952_201_2 rfl rfl rfl

theorem m952_201_201_600 : blockEstimate 952 201 201 600 = 0x31ecdf232 :=
  block_append (B := 952) (J := 201) (start := 201) (next := 401)
    (a := 200) (b := 400) (n := 600) (x := 0x40c1c97a) (y := 0x2de0c28b8) (z := 0x31ecdf232)
    w952_201_0 m952_201_401_400 rfl rfl rfl

theorem m952_201_1001_353 : blockEstimate 952 201 1001 353 = 0xab16a628 :=
  block_append (B := 952) (J := 201) (start := 1001) (next := 1201)
    (a := 200) (b := 153) (n := 353) (x := 0x9af3c379) (y := 0x1022e2af) (z := 0xab16a628)
    w952_201_4 w952_201_5 rfl rfl rfl

theorem m952_201_801_553 : blockEstimate 952 201 801 553 = 0x2103de969 :=
  block_append (B := 952) (J := 201) (start := 801) (next := 1001)
    (a := 200) (b := 353) (n := 553) (x := 0x165274341) (y := 0xab16a628) (z := 0x2103de969)
    w952_201_3 m952_201_1001_353 rfl rfl rfl

theorem m952_201_201_1153 : blockEstimate 952 201 201 1153 = 0x52f0bdb9b :=
  block_append (B := 952) (J := 201) (start := 201) (next := 801)
    (a := 600) (b := 553) (n := 1153) (x := 0x31ecdf232) (y := 0x2103de969) (z := 0x52f0bdb9b)
    m952_201_201_600 m952_201_801_553 rfl rfl rfl

theorem nextMoment952_201 : momentEstimate 952 201 = 0x52f0bdb9b := m952_201_201_1153

theorem m1101_233_433_400 : blockEstimate 1101 233 433 400 = 0x40d69cc70 :=
  block_append (B := 1101) (J := 233) (start := 433) (next := 633)
    (a := 200) (b := 200) (n := 400) (x := 0x192678834) (y := 0x27b02443c) (z := 0x40d69cc70)
    w1101_233_1 w1101_233_2 rfl rfl rfl

theorem m1101_233_233_600 : blockEstimate 1101 233 233 600 = 0x45a309f02 :=
  block_append (B := 1101) (J := 233) (start := 233) (next := 433)
    (a := 200) (b := 400) (n := 600) (x := 0x4cc6d292) (y := 0x40d69cc70) (z := 0x45a309f02)
    w1101_233_0 m1101_233_433_400 rfl rfl rfl

theorem m1101_233_833_400 : blockEstimate 1101 233 833 400 = 0x43d229b8d :=
  block_append (B := 1101) (J := 233) (start := 833) (next := 1033)
    (a := 200) (b := 200) (n := 400) (x := 0x284c5a7fc) (y := 0x1b85cf391) (z := 0x43d229b8d)
    w1101_233_3 w1101_233_4 rfl rfl rfl

theorem m1101_233_1233_334 : blockEstimate 1101 233 1233 334 = 0xb0253605 :=
  block_append (B := 1101) (J := 233) (start := 1233) (next := 1433)
    (a := 200) (b := 134) (n := 334) (x := 0xa34f3186) (y := 0xcd6047f) (z := 0xb0253605)
    w1101_233_5 w1101_233_6 rfl rfl rfl

theorem m1101_233_833_734 : blockEstimate 1101 233 833 734 = 0x4ed47d192 :=
  block_append (B := 1101) (J := 233) (start := 833) (next := 1233)
    (a := 400) (b := 334) (n := 734) (x := 0x43d229b8d) (y := 0xb0253605) (z := 0x4ed47d192)
    m1101_233_833_400 m1101_233_1233_334 rfl rfl rfl

theorem m1101_233_233_1334 : blockEstimate 1101 233 233 1334 = 0x947787094 :=
  block_append (B := 1101) (J := 233) (start := 233) (next := 833)
    (a := 600) (b := 734) (n := 1334) (x := 0x45a309f02) (y := 0x4ed47d192) (z := 0x947787094)
    m1101_233_233_600 m1101_233_833_734 rfl rfl rfl

theorem nextMoment1101_233 : momentEstimate 1101 233 = 0x947787094 := m1101_233_233_1334

theorem m1202_254_254_400 : blockEstimate 1202 254 254 400 = 0x22853c765 :=
  block_append (B := 1202) (J := 254) (start := 254) (next := 454)
    (a := 200) (b := 200) (n := 400) (x := 0x54ec992a) (y := 0x1d3672e3b) (z := 0x22853c765)
    w1202_254_0 w1202_254_1 rfl rfl rfl

theorem m1202_254_654_400 : blockEstimate 1202 254 654 400 = 0x6755ecd58 :=
  block_append (B := 1202) (J := 254) (start := 654) (next := 854)
    (a := 200) (b := 200) (n := 400) (x := 0x31378a4cc) (y := 0x361e6288c) (z := 0x6755ecd58)
    w1202_254_2 w1202_254_3 rfl rfl rfl

theorem m1202_254_254_800 : blockEstimate 1202 254 254 800 = 0x89db294bd :=
  block_append (B := 1202) (J := 254) (start := 254) (next := 654)
    (a := 400) (b := 400) (n := 800) (x := 0x22853c765) (y := 0x6755ecd58) (z := 0x89db294bd)
    m1202_254_254_400 m1202_254_654_400 rfl rfl rfl

theorem m1202_254_1054_400 : blockEstimate 1202 254 1054 400 = 0x42effeb4b :=
  block_append (B := 1202) (J := 254) (start := 1054) (next := 1254)
    (a := 200) (b := 200) (n := 400) (x := 0x2bdae08d1) (y := 0x17151e27a) (z := 0x42effeb4b)
    w1202_254_4 w1202_254_5 rfl rfl rfl

theorem m1202_254_1454_256 : blockEstimate 1202 254 1454 256 = 0x5bd0ace0 :=
  block_append (B := 1202) (J := 254) (start := 1454) (next := 1654)
    (a := 200) (b := 56) (n := 256) (x := 0x5ab47210) (y := 0x11c3ad0) (z := 0x5bd0ace0)
    w1202_254_6 w1202_254_7 rfl rfl rfl

theorem m1202_254_1054_656 : blockEstimate 1202 254 1054 656 = 0x48ad0982b :=
  block_append (B := 1202) (J := 254) (start := 1054) (next := 1454)
    (a := 400) (b := 256) (n := 656) (x := 0x42effeb4b) (y := 0x5bd0ace0) (z := 0x48ad0982b)
    m1202_254_1054_400 m1202_254_1454_256 rfl rfl rfl

theorem m1202_254_254_1456 : blockEstimate 1202 254 254 1456 = 0xd28832ce8 :=
  block_append (B := 1202) (J := 254) (start := 254) (next := 1054)
    (a := 800) (b := 656) (n := 1456) (x := 0x89db294bd) (y := 0x48ad0982b) (z := 0xd28832ce8)
    m1202_254_254_800 m1202_254_1054_656 rfl rfl rfl

theorem nextMoment1202_254 : momentEstimate 1202 254 = 0xd28832ce8 := m1202_254_254_1456

theorem m1412_298_298_400 : blockEstimate 1412 298 298 400 = 0x2bdd72dba :=
  block_append (B := 1412) (J := 298) (start := 298) (next := 498)
    (a := 200) (b := 200) (n := 400) (x := 0x65dd5c1a) (y := 0x257f9d1a0) (z := 0x2bdd72dba)
    w1412_298_0 w1412_298_1 rfl rfl rfl

theorem m1412_298_698_400 : blockEstimate 1412 298 698 400 = 0x9d81366b8 :=
  block_append (B := 1412) (J := 298) (start := 698) (next := 898)
    (a := 200) (b := 200) (n := 400) (x := 0x46b5d54fc) (y := 0x56cb611bc) (z := 0x9d81366b8)
    w1412_298_2 w1412_298_3 rfl rfl rfl

theorem m1412_298_298_800 : blockEstimate 1412 298 298 800 = 0xc95ea9472 :=
  block_append (B := 1412) (J := 298) (start := 298) (next := 698)
    (a := 400) (b := 400) (n := 800) (x := 0x2bdd72dba) (y := 0x9d81366b8) (z := 0xc95ea9472)
    m1412_298_298_400 m1412_298_698_400 rfl rfl rfl

theorem m1412_298_1098_400 : blockEstimate 1412 298 1098 400 = 0x96bcba3bb :=
  block_append (B := 1412) (J := 298) (start := 1098) (next := 1298)
    (a := 200) (b := 200) (n := 400) (x := 0x550e8c27c) (y := 0x41ae2e13f) (z := 0x96bcba3bb)
    w1412_298_4 w1412_298_5 rfl rfl rfl

theorem m1412_298_1698_310 : blockEstimate 1412 298 1698 310 = 0xbe415b9f :=
  block_append (B := 1412) (J := 298) (start := 1698) (next := 1898)
    (a := 200) (b := 110) (n := 310) (x := 0xb4e2900d) (y := 0x95ecb92) (z := 0xbe415b9f)
    w1412_298_7 w1412_298_8 rfl rfl rfl

theorem m1412_298_1498_510 : blockEstimate 1412 298 1498 510 = 0x2ffaf44c6 :=
  block_append (B := 1412) (J := 298) (start := 1498) (next := 1698)
    (a := 200) (b := 310) (n := 510) (x := 0x2416de927) (y := 0xbe415b9f) (z := 0x2ffaf44c6)
    w1412_298_6 m1412_298_1698_310 rfl rfl rfl

theorem m1412_298_1098_910 : blockEstimate 1412 298 1098 910 = 0xc6b7ae881 :=
  block_append (B := 1412) (J := 298) (start := 1098) (next := 1498)
    (a := 400) (b := 510) (n := 910) (x := 0x96bcba3bb) (y := 0x2ffaf44c6) (z := 0xc6b7ae881)
    m1412_298_1098_400 m1412_298_1498_510 rfl rfl rfl

theorem m1412_298_298_1710 : blockEstimate 1412 298 298 1710 = 0x1901657cf3 :=
  block_append (B := 1412) (J := 298) (start := 298) (next := 1098)
    (a := 800) (b := 910) (n := 1710) (x := 0xc95ea9472) (y := 0xc6b7ae881) (z := 0x1901657cf3)
    m1412_298_298_800 m1412_298_1098_910 rfl rfl rfl

theorem nextMoment1412_298 : momentEstimate 1412 298 = 0x1901657cf3 := m1412_298_298_1710

theorem m1815_383_383_400 : blockEstimate 1815 383 383 400 = 0x3cadbc9e0 :=
  block_append (B := 1815) (J := 383) (start := 383) (next := 583)
    (a := 200) (b := 200) (n := 400) (x := 0x865fcfc2) (y := 0x3447bfa1e) (z := 0x3cadbc9e0)
    w1815_383_0 w1815_383_1 rfl rfl rfl

theorem m1815_383_983_400 : blockEstimate 1815 383 983 400 = 0x15a3e9c600 :=
  block_append (B := 1815) (J := 383) (start := 983) (next := 1183)
    (a := 200) (b := 200) (n := 400) (x := 0xa17e02b00) (y := 0xb8c099b00) (z := 0x15a3e9c600)
    w1815_383_3 w1815_383_4 rfl rfl rfl

theorem m1815_383_783_600 : blockEstimate 1815 383 783 600 = 0x1cd96a8100 :=
  block_append (B := 1815) (J := 383) (start := 783) (next := 983)
    (a := 200) (b := 400) (n := 600) (x := 0x73580bb00) (y := 0x15a3e9c600) (z := 0x1cd96a8100)
    w1815_383_2 m1815_383_983_400 rfl rfl rfl

theorem m1815_383_383_1000 : blockEstimate 1815 383 383 1000 = 0x20a4464ae0 :=
  block_append (B := 1815) (J := 383) (start := 383) (next := 783)
    (a := 400) (b := 600) (n := 1000) (x := 0x3cadbc9e0) (y := 0x1cd96a8100) (z := 0x20a4464ae0)
    m1815_383_383_400 m1815_383_783_600 rfl rfl rfl

theorem m1815_383_1583_400 : blockEstimate 1815 383 1583 400 = 0x119a45a134 :=
  block_append (B := 1815) (J := 383) (start := 1583) (next := 1783)
    (a := 200) (b := 200) (n := 400) (x := 0xa29ba7b00) (y := 0x7708b2634) (z := 0x119a45a134)
    w1815_383_6 w1815_383_7 rfl rfl rfl

theorem m1815_383_1383_600 : blockEstimate 1815 383 1383 600 = 0x1d2c42ac34 :=
  block_append (B := 1815) (J := 383) (start := 1383) (next := 1583)
    (a := 200) (b := 400) (n := 600) (x := 0xb91fd0b00) (y := 0x119a45a134) (z := 0x1d2c42ac34)
    w1815_383_5 m1815_383_1583_400 rfl rfl rfl

theorem m1815_383_2183_398 : blockEstimate 1815 383 2183 398 = 0x203e717b4 :=
  block_append (B := 1815) (J := 383) (start := 2183) (next := 2383)
    (a := 200) (b := 198) (n := 398) (x := 0x1bff52d39) (y := 0x43f1ea7b) (z := 0x203e717b4)
    w1815_383_9 w1815_383_10 rfl rfl rfl

theorem m1815_383_1983_598 : blockEstimate 1815 383 1983 598 = 0x65a3cc37e :=
  block_append (B := 1815) (J := 383) (start := 1983) (next := 2183)
    (a := 200) (b := 398) (n := 598) (x := 0x45655abca) (y := 0x203e717b4) (z := 0x65a3cc37e)
    w1815_383_8 m1815_383_2183_398 rfl rfl rfl

theorem m1815_383_1383_1198 : blockEstimate 1815 383 1383 1198 = 0x23867f6fb2 :=
  block_append (B := 1815) (J := 383) (start := 1383) (next := 1983)
    (a := 600) (b := 598) (n := 1198) (x := 0x1d2c42ac34) (y := 0x65a3cc37e) (z := 0x23867f6fb2)
    m1815_383_1383_600 m1815_383_1983_598 rfl rfl rfl

theorem m1815_383_383_2198 : blockEstimate 1815 383 383 2198 = 0x442ac5ba92 :=
  block_append (B := 1815) (J := 383) (start := 383) (next := 1383)
    (a := 1000) (b := 1198) (n := 2198) (x := 0x20a4464ae0) (y := 0x23867f6fb2) (z := 0x442ac5ba92)
    m1815_383_383_1000 m1815_383_1383_1198 rfl rfl rfl

theorem nextMoment1815_383 : momentEstimate 1815 383 = 0x442ac5ba92 := m1815_383_383_2198

theorem m2035_429_629_400 : blockEstimate 2035 429 629 400 = 0xc7a2290fd :=
  block_append (B := 2035) (J := 429) (start := 629) (next := 829)
    (a := 200) (b := 200) (n := 400) (x := 0x3bfbaacb2) (y := 0x8ba67e44b) (z := 0xc7a2290fd)
    w2035_429_1 w2035_429_2 rfl rfl rfl

theorem m2035_429_429_600 : blockEstimate 2035 429 429 600 = 0xd1241a6df :=
  block_append (B := 2035) (J := 429) (start := 429) (next := 629)
    (a := 200) (b := 400) (n := 600) (x := 0x981f15e2) (y := 0xc7a2290fd) (z := 0xd1241a6df)
    w2035_429_0 m2035_429_629_400 rfl rfl rfl

theorem m2035_429_1229_400 : blockEstimate 2035 429 1229 400 = 0x200f70b0c8 :=
  block_append (B := 2035) (J := 429) (start := 1229) (next := 1429)
    (a := 200) (b := 200) (n := 400) (x := 0xf87d38fc4) (y := 0x10879d2104) (z := 0x200f70b0c8)
    w2035_429_4 w2035_429_5 rfl rfl rfl

theorem m2035_429_1029_600 : blockEstimate 2035 429 1029 600 = 0x2cfd66374c :=
  block_append (B := 2035) (J := 429) (start := 1029) (next := 1229)
    (a := 200) (b := 400) (n := 600) (x := 0xcedf58684) (y := 0x200f70b0c8) (z := 0x2cfd66374c)
    w2035_429_3 m2035_429_1229_400 rfl rfl rfl

theorem m2035_429_429_1200 : blockEstimate 2035 429 429 1200 = 0x3a0fa7de2b :=
  block_append (B := 2035) (J := 429) (start := 429) (next := 1029)
    (a := 600) (b := 600) (n := 1200) (x := 0xd1241a6df) (y := 0x2cfd66374c) (z := 0x3a0fa7de2b)
    m2035_429_429_600 m2035_429_1029_600 rfl rfl rfl

theorem m2035_429_1829_400 : blockEstimate 2035 429 1829 400 = 0x17d63238c3 :=
  block_append (B := 2035) (J := 429) (start := 1829) (next := 2029)
    (a := 200) (b := 200) (n := 400) (x := 0xdb8f2db84) (y := 0xa1d3f5d3f) (z := 0x17d63238c3)
    w2035_429_7 w2035_429_8 rfl rfl rfl

theorem m2035_429_1629_600 : blockEstimate 2035 429 1629 600 = 0x27c3847307 :=
  block_append (B := 2035) (J := 429) (start := 1629) (next := 1829)
    (a := 200) (b := 400) (n := 600) (x := 0xfed523a44) (y := 0x17d63238c3) (z := 0x27c3847307)
    w2035_429_6 m2035_429_1829_400 rfl rfl rfl

theorem m2035_429_2229_400 : blockEstimate 2035 429 2229 400 = 0x912069600 :=
  block_append (B := 2035) (J := 429) (start := 2229) (next := 2429)
    (a := 200) (b := 200) (n := 400) (x := 0x6350e2efb) (y := 0x2dcf86705) (z := 0x912069600)
    w2035_429_9 w2035_429_10 rfl rfl rfl

theorem m2035_429_2629_264 : blockEstimate 2035 429 2629 264 = 0xb1b9e156 :=
  block_append (B := 2035) (J := 429) (start := 2629) (next := 2829)
    (a := 200) (b := 64) (n := 264) (x := 0xaeed80a6) (y := 0x2cc60b0) (z := 0xb1b9e156)
    w2035_429_11 w2035_429_12 rfl rfl rfl

theorem m2035_429_2229_664 : blockEstimate 2035 429 2229 664 = 0x9c3c07756 :=
  block_append (B := 2035) (J := 429) (start := 2229) (next := 2629)
    (a := 400) (b := 264) (n := 664) (x := 0x912069600) (y := 0xb1b9e156) (z := 0x9c3c07756)
    m2035_429_2229_400 m2035_429_2629_264 rfl rfl rfl

theorem m2035_429_1629_1264 : blockEstimate 2035 429 1629 1264 = 0x318744ea5d :=
  block_append (B := 2035) (J := 429) (start := 1629) (next := 2229)
    (a := 600) (b := 664) (n := 1264) (x := 0x27c3847307) (y := 0x9c3c07756) (z := 0x318744ea5d)
    m2035_429_1629_600 m2035_429_2229_664 rfl rfl rfl

theorem m2035_429_429_2464 : blockEstimate 2035 429 429 2464 = 0x6b96ecc888 :=
  block_append (B := 2035) (J := 429) (start := 429) (next := 1629)
    (a := 1200) (b := 1264) (n := 2464) (x := 0x3a0fa7de2b) (y := 0x318744ea5d) (z := 0x6b96ecc888)
    m2035_429_429_1200 m2035_429_1629_1264 rfl rfl rfl

theorem nextMoment2035_429 : momentEstimate 2035 429 = 0x6b96ecc888 := m2035_429_429_2464

theorem m2235_472_672_400 : blockEstimate 2235 472 672 400 = 0xe3ffdce54 :=
  block_append (B := 2235) (J := 472) (start := 672) (next := 872)
    (a := 200) (b := 200) (n := 400) (x := 0x42fb50e72) (y := 0xa1048bfe2) (z := 0xe3ffdce54)
    w2235_472_1 w2235_472_2 rfl rfl rfl

theorem m2235_472_472_600 : blockEstimate 2235 472 472 600 = 0xee83f23f6 :=
  block_append (B := 2235) (J := 472) (start := 472) (next := 672)
    (a := 200) (b := 400) (n := 600) (x := 0xa84155a2) (y := 0xe3ffdce54) (z := 0xee83f23f6)
    w2235_472_0 m2235_472_672_400 rfl rfl rfl

theorem m2235_472_1072_400 : blockEstimate 2235 472 1072 400 = 0x231c003068 :=
  block_append (B := 2235) (J := 472) (start := 1072) (next := 1272)
    (a := 200) (b := 200) (n := 400) (x := 0xfa2e0dc54) (y := 0x13791f5414) (z := 0x231c003068)
    w2235_472_3 w2235_472_4 rfl rfl rfl

theorem m2235_472_1472_400 : blockEstimate 2235 472 1472 400 = 0x2b689fff68 :=
  block_append (B := 2235) (J := 472) (start := 1472) (next := 1672)
    (a := 200) (b := 200) (n := 400) (x := 0x158c4747d4) (y := 0x15dc58b794) (z := 0x2b689fff68)
    w2235_472_5 w2235_472_6 rfl rfl rfl

theorem m2235_472_1072_800 : blockEstimate 2235 472 1072 800 = 0x4e84a02fd0 :=
  block_append (B := 2235) (J := 472) (start := 1072) (next := 1472)
    (a := 400) (b := 400) (n := 800) (x := 0x231c003068) (y := 0x2b689fff68) (z := 0x4e84a02fd0)
    m2235_472_1072_400 m2235_472_1472_400 rfl rfl rfl

theorem m2235_472_472_1400 : blockEstimate 2235 472 472 1400 = 0x5d6cdf53c6 :=
  block_append (B := 2235) (J := 472) (start := 472) (next := 1072)
    (a := 600) (b := 800) (n := 1400) (x := 0xee83f23f6) (y := 0x4e84a02fd0) (z := 0x5d6cdf53c6)
    m2235_472_472_600 m2235_472_1072_800 rfl rfl rfl

theorem m2235_472_2072_400 : blockEstimate 2235 472 2072 400 = 0x1dd44b2143 :=
  block_append (B := 2235) (J := 472) (start := 2072) (next := 2272)
    (a := 200) (b := 200) (n := 400) (x := 0x11339142ef) (y := 0xca0b9de54) (z := 0x1dd44b2143)
    w2235_472_8 w2235_472_9 rfl rfl rfl

theorem m2235_472_1872_600 : blockEstimate 2235 472 1872 600 = 0x323d9ec497 :=
  block_append (B := 2235) (J := 472) (start := 1872) (next := 2072)
    (a := 200) (b := 400) (n := 600) (x := 0x146953a354) (y := 0x1dd44b2143) (z := 0x323d9ec497)
    w2235_472_7 m2235_472_2072_400 rfl rfl rfl

theorem m2235_472_2472_400 : blockEstimate 2235 472 2472 400 = 0xbd715dd50 :=
  block_append (B := 2235) (J := 472) (start := 2472) (next := 2672)
    (a := 200) (b := 200) (n := 400) (x := 0x7ef8d4fda) (y := 0x3e7888d76) (z := 0xbd715dd50)
    w2235_472_10 w2235_472_11 rfl rfl rfl

theorem m2235_472_2872_307 : blockEstimate 2235 472 2872 307 = 0x1310c6d4b :=
  block_append (B := 2235) (J := 472) (start := 2872) (next := 3072)
    (a := 200) (b := 107) (n := 307) (x := 0x1232f5782) (y := 0xddd15c9) (z := 0x1310c6d4b)
    w2235_472_12 w2235_472_13 rfl rfl rfl

theorem m2235_472_2472_707 : blockEstimate 2235 472 2472 707 = 0xd08224a9b :=
  block_append (B := 2235) (J := 472) (start := 2472) (next := 2872)
    (a := 400) (b := 307) (n := 707) (x := 0xbd715dd50) (y := 0x1310c6d4b) (z := 0xd08224a9b)
    m2235_472_2472_400 m2235_472_2872_307 rfl rfl rfl

theorem m2235_472_1872_1307 : blockEstimate 2235 472 1872 1307 = 0x3f45c10f32 :=
  block_append (B := 2235) (J := 472) (start := 1872) (next := 2472)
    (a := 600) (b := 707) (n := 1307) (x := 0x323d9ec497) (y := 0xd08224a9b) (z := 0x3f45c10f32)
    m2235_472_1872_600 m2235_472_2472_707 rfl rfl rfl

theorem m2235_472_472_2707 : blockEstimate 2235 472 472 2707 = 0x9cb2a062f8 :=
  block_append (B := 2235) (J := 472) (start := 472) (next := 1872)
    (a := 1400) (b := 1307) (n := 2707) (x := 0x5d6cdf53c6) (y := 0x3f45c10f32) (z := 0x9cb2a062f8)
    m2235_472_472_1400 m2235_472_1872_1307 rfl rfl rfl

theorem nextMoment2235_472 : momentEstimate 2235 472 = 0x9cb2a062f8 := m2235_472_472_2707

theorem m3142_664_664_400 : blockEstimate 3142 664 664 400 = 0x71cf31ca4 :=
  block_append (B := 3142) (J := 664) (start := 664) (next := 864)
    (a := 200) (b := 200) (n := 400) (x := 0xf16c038a) (y := 0x62b87191a) (z := 0x71cf31ca4)
    w3142_664_0 w3142_664_1 rfl rfl rfl

theorem m3142_664_1264_400 : blockEstimate 3142 664 1264 400 = 0x432b3fba10 :=
  block_append (B := 3142) (J := 664) (start := 1264) (next := 1464)
    (a := 200) (b := 200) (n := 400) (x := 0x1bcb50b6d0) (y := 0x275fef0340) (z := 0x432b3fba10)
    w3142_664_3 w3142_664_4 rfl rfl rfl

theorem m3142_664_1064_600 : blockEstimate 3142 664 1064 600 = 0x52bd3c71ba :=
  block_append (B := 3142) (J := 664) (start := 1064) (next := 1264)
    (a := 200) (b := 400) (n := 600) (x := 0xf91fcb7aa) (y := 0x432b3fba10) (z := 0x52bd3c71ba)
    w3142_664_2 m3142_664_1264_400 rfl rfl rfl

theorem m3142_664_664_1000 : blockEstimate 3142 664 664 1000 = 0x59da2f8e5e :=
  block_append (B := 3142) (J := 664) (start := 664) (next := 1064)
    (a := 400) (b := 600) (n := 1000) (x := 0x71cf31ca4) (y := 0x52bd3c71ba) (z := 0x59da2f8e5e)
    m3142_664_664_400 m3142_664_1064_600 rfl rfl rfl

theorem m3142_664_1664_400 : blockEstimate 3142 664 1664 400 = 0x67a8aea000 :=
  block_append (B := 3142) (J := 664) (start := 1664) (next := 1864)
    (a := 200) (b := 200) (n := 400) (x := 0x3080efb7c0) (y := 0x3727bee840) (z := 0x67a8aea000)
    w3142_664_5 w3142_664_6 rfl rfl rfl

theorem m3142_664_2264_400 : blockEstimate 3142 664 2264 400 = 0x7945cc1f00 :=
  block_append (B := 3142) (J := 664) (start := 2264) (next := 2464)
    (a := 200) (b := 200) (n := 400) (x := 0x3d06c8bd40) (y := 0x3c3f0361c0) (z := 0x7945cc1f00)
    w3142_664_8 w3142_664_9 rfl rfl rfl

theorem m3142_664_2064_600 : blockEstimate 3142 664 2064 600 = 0xb49a28b3c0 :=
  block_append (B := 3142) (J := 664) (start := 2064) (next := 2264)
    (a := 200) (b := 400) (n := 600) (x := 0x3b545c94c0) (y := 0x7945cc1f00) (z := 0xb49a28b3c0)
    w3142_664_7 m3142_664_2264_400 rfl rfl rfl

theorem m3142_664_1664_1000 : blockEstimate 3142 664 1664 1000 = 0x11c42d753c0 :=
  block_append (B := 3142) (J := 664) (start := 1664) (next := 2064)
    (a := 400) (b := 600) (n := 1000) (x := 0x67a8aea000) (y := 0xb49a28b3c0) (z := 0x11c42d753c0)
    m3142_664_1664_400 m3142_664_2064_600 rfl rfl rfl

theorem m3142_664_664_2000 : blockEstimate 3142 664 664 2000 = 0x1761d06e21e :=
  block_append (B := 3142) (J := 664) (start := 664) (next := 1664)
    (a := 1000) (b := 1000) (n := 2000) (x := 0x59da2f8e5e) (y := 0x11c42d753c0) (z := 0x1761d06e21e)
    m3142_664_664_1000 m3142_664_1664_1000 rfl rfl rfl

theorem m3142_664_2664_400 : blockEstimate 3142 664 2664 400 = 0x6c3df0a100 :=
  block_append (B := 3142) (J := 664) (start := 2664) (next := 2864)
    (a := 200) (b := 200) (n := 400) (x := 0x38fd0c8240) (y := 0x3340e41ec0) (z := 0x6c3df0a100)
    w3142_664_10 w3142_664_11 rfl rfl rfl

theorem m3142_664_3264_400 : blockEstimate 3142 664 3264 400 = 0x3a07069402 :=
  block_append (B := 3142) (J := 664) (start := 3264) (next := 3464)
    (a := 200) (b := 200) (n := 400) (x := 0x21b0d1cbd2) (y := 0x185634c830) (z := 0x3a07069402)
    w3142_664_13 w3142_664_14 rfl rfl rfl

theorem m3142_664_3064_600 : blockEstimate 3142 664 3064 600 = 0x65235d5d34 :=
  block_append (B := 3142) (J := 664) (start := 3064) (next := 3264)
    (a := 200) (b := 400) (n := 600) (x := 0x2b1c56c932) (y := 0x3a07069402) (z := 0x65235d5d34)
    w3142_664_12 m3142_664_3264_400 rfl rfl rfl

theorem m3142_664_2664_1000 : blockEstimate 3142 664 2664 1000 = 0xd1614dfe34 :=
  block_append (B := 3142) (J := 664) (start := 2664) (next := 3064)
    (a := 400) (b := 600) (n := 1000) (x := 0x6c3df0a100) (y := 0x65235d5d34) (z := 0xd1614dfe34)
    m3142_664_2664_400 m3142_664_3064_600 rfl rfl rfl

theorem m3142_664_3664_400 : blockEstimate 3142 664 3664 400 = 0x18524733fa :=
  block_append (B := 3142) (J := 664) (start := 3664) (next := 3864)
    (a := 200) (b := 200) (n := 400) (x := 0xfc3312665) (y := 0x88f160d95) (z := 0x18524733fa)
    w3142_664_15 w3142_664_16 rfl rfl rfl

theorem m3142_664_4264_206 : blockEstimate 3142 664 4264 206 = 0x872b88fe :=
  block_append (B := 3142) (J := 664) (start := 4264) (next := 4464)
    (a := 200) (b := 6) (n := 206) (x := 0x8729e7fd) (y := 0x1a101) (z := 0x872b88fe)
    w3142_664_18 w3142_664_19 rfl rfl rfl

theorem m3142_664_4064_406 : blockEstimate 3142 664 4064 406 = 0x3e04e9d1f :=
  block_append (B := 3142) (J := 664) (start := 4064) (next := 4264)
    (a := 200) (b := 206) (n := 406) (x := 0x359231421) (y := 0x872b88fe) (z := 0x3e04e9d1f)
    w3142_664_17 m3142_664_4264_206 rfl rfl rfl

theorem m3142_664_3664_806 : blockEstimate 3142 664 3664 806 = 0x1c3295d119 :=
  block_append (B := 3142) (J := 664) (start := 3664) (next := 4064)
    (a := 400) (b := 406) (n := 806) (x := 0x18524733fa) (y := 0x3e04e9d1f) (z := 0x1c3295d119)
    m3142_664_3664_400 m3142_664_4064_406 rfl rfl rfl

theorem m3142_664_2664_1806 : blockEstimate 3142 664 2664 1806 = 0xed93e3cf4d :=
  block_append (B := 3142) (J := 664) (start := 2664) (next := 3664)
    (a := 1000) (b := 806) (n := 1806) (x := 0xd1614dfe34) (y := 0x1c3295d119) (z := 0xed93e3cf4d)
    m3142_664_2664_1000 m3142_664_3664_806 rfl rfl rfl

theorem m3142_664_664_3806 : blockEstimate 3142 664 664 3806 = 0x263b0eab16b :=
  block_append (B := 3142) (J := 664) (start := 664) (next := 2664)
    (a := 2000) (b := 1806) (n := 3806) (x := 0x1761d06e21e) (y := 0xed93e3cf4d) (z := 0x263b0eab16b)
    m3142_664_664_2000 m3142_664_2664_1806 rfl rfl rfl

theorem nextMoment3142_664 : momentEstimate 3142 664 = 0x263b0eab16b := m3142_664_664_3806

theorem m3850_812_1012_400 : blockEstimate 3850 812 1012 400 = 0x1b7b357d84 :=
  block_append (B := 3850) (J := 812) (start := 1012) (next := 1212)
    (a := 200) (b := 200) (n := 400) (x := 0x7b7ee16fa) (y := 0x13c347668a) (z := 0x1b7b357d84)
    w3850_812_1 w3850_812_2 rfl rfl rfl

theorem m3850_812_812_600 : blockEstimate 3850 812 812 600 = 0x1ca5be95ee :=
  block_append (B := 3850) (J := 812) (start := 812) (next := 1012)
    (a := 200) (b := 400) (n := 600) (x := 0x12a89186a) (y := 0x1b7b357d84) (z := 0x1ca5be95ee)
    w3850_812_0 m3850_812_1012_400 rfl rfl rfl

theorem m3850_812_1612_400 : blockEstimate 3850 812 1612 400 = 0x7f4d334d71 :=
  block_append (B := 3850) (J := 812) (start := 1612) (next := 1812)
    (a := 200) (b := 200) (n := 400) (x := 0x371c2cdb09) (y := 0x4831067268) (z := 0x7f4d334d71)
    w3850_812_4 w3850_812_5 rfl rfl rfl

theorem m3850_812_1412_600 : blockEstimate 3850 812 1412 600 = 0xa37bae248b :=
  block_append (B := 3850) (J := 812) (start := 1412) (next := 1612)
    (a := 200) (b := 400) (n := 600) (x := 0x242e7ad71a) (y := 0x7f4d334d71) (z := 0xa37bae248b)
    w3850_812_3 m3850_812_1612_400 rfl rfl rfl

theorem m3850_812_812_1200 : blockEstimate 3850 812 812 1200 = 0xc0216cba79 :=
  block_append (B := 3850) (J := 812) (start := 812) (next := 1412)
    (a := 600) (b := 600) (n := 1200) (x := 0x1ca5be95ee) (y := 0xa37bae248b) (z := 0xc0216cba79)
    m3850_812_812_600 m3850_812_1412_600 rfl rfl rfl

theorem m3850_812_2212_400 : blockEstimate 3850 812 2212 400 = 0xca888664d0 :=
  block_append (B := 3850) (J := 812) (start := 2212) (next := 2412)
    (a := 200) (b := 200) (n := 400) (x := 0x6144d13e68) (y := 0x6943b52668) (z := 0xca888664d0)
    w3850_812_7 w3850_812_8 rfl rfl rfl

theorem m3850_812_2012_600 : blockEstimate 3850 812 2012 600 = 0x120c71d6738 :=
  block_append (B := 3850) (J := 812) (start := 2012) (next := 2212)
    (a := 200) (b := 400) (n := 600) (x := 0x563e970268) (y := 0xca888664d0) (z := 0x120c71d6738)
    w3850_812_6 m3850_812_2212_400 rfl rfl rfl

theorem m3850_812_2812_400 : blockEstimate 3850 812 2812 400 = 0xdf3fd4e0d0 :=
  block_append (B := 3850) (J := 812) (start := 2812) (next := 3012)
    (a := 200) (b := 200) (n := 400) (x := 0x702b79fa68) (y := 0x6f145ae668) (z := 0xdf3fd4e0d0)
    w3850_812_10 w3850_812_11 rfl rfl rfl

theorem m3850_812_2612_600 : blockEstimate 3850 812 2612 600 = 0x14d7b179b38 :=
  block_append (B := 3850) (J := 812) (start := 2612) (next := 2812)
    (a := 200) (b := 400) (n := 600) (x := 0x6e3b42ba68) (y := 0xdf3fd4e0d0) (z := 0x14d7b179b38)
    w3850_812_9 m3850_812_2812_400 rfl rfl rfl

theorem m3850_812_2012_1200 : blockEstimate 3850 812 2012 1200 = 0x26e42350270 :=
  block_append (B := 3850) (J := 812) (start := 2012) (next := 2612)
    (a := 600) (b := 600) (n := 1200) (x := 0x120c71d6738) (y := 0x14d7b179b38) (z := 0x26e42350270)
    m3850_812_2012_600 m3850_812_2612_600 rfl rfl rfl

theorem m3850_812_812_2400 : blockEstimate 3850 812 812 2400 = 0x32e63a1bce9 :=
  block_append (B := 3850) (J := 812) (start := 812) (next := 2012)
    (a := 1200) (b := 1200) (n := 2400) (x := 0xc0216cba79) (y := 0x26e42350270) (z := 0x32e63a1bce9)
    m3850_812_812_1200 m3850_812_2012_1200 rfl rfl rfl

theorem m3850_812_3412_400 : blockEstimate 3850 812 3412 400 = 0xbd731174d0 :=
  block_append (B := 3850) (J := 812) (start := 3412) (next := 3612)
    (a := 200) (b := 200) (n := 400) (x := 0x63d019c268) (y := 0x59a2f7b268) (z := 0xbd731174d0)
    w3850_812_13 w3850_812_14 rfl rfl rfl

theorem m3850_812_3212_600 : blockEstimate 3850 812 3212 600 = 0x12868f6f338 :=
  block_append (B := 3850) (J := 812) (start := 3212) (next := 3412)
    (a := 200) (b := 400) (n := 600) (x := 0x6af5e57e68) (y := 0xbd731174d0) (z := 0x12868f6f338)
    w3850_812_12 m3850_812_3412_400 rfl rfl rfl

theorem m3850_812_4012_400 : blockEstimate 3850 812 4012 400 = 0x6eb3f8df01 :=
  block_append (B := 3850) (J := 812) (start := 4012) (next := 4212)
    (a := 200) (b := 200) (n := 400) (x := 0x3e6b976415) (y := 0x3048617aec) (z := 0x6eb3f8df01)
    w3850_812_16 w3850_812_17 rfl rfl rfl

theorem m3850_812_3812_600 : blockEstimate 3850 812 3812 600 = 0xbb55be5e72 :=
  block_append (B := 3850) (J := 812) (start := 3812) (next := 4012)
    (a := 200) (b := 400) (n := 600) (x := 0x4ca1c57f71) (y := 0x6eb3f8df01) (z := 0xbb55be5e72)
    w3850_812_15 m3850_812_4012_400 rfl rfl rfl

theorem m3850_812_3212_1200 : blockEstimate 3850 812 3212 1200 = 0x1e3beb551aa :=
  block_append (B := 3850) (J := 812) (start := 3212) (next := 3812)
    (a := 600) (b := 600) (n := 1200) (x := 0x12868f6f338) (y := 0xbb55be5e72) (z := 0x1e3beb551aa)
    m3850_812_3212_600 m3850_812_3812_600 rfl rfl rfl

theorem m3850_812_4612_400 : blockEstimate 3850 812 4612 400 = 0x2407517bca :=
  block_append (B := 3850) (J := 812) (start := 4612) (next := 4812)
    (a := 200) (b := 200) (n := 400) (x := 0x16fc35d4e1) (y := 0xd0b1ba6e9) (z := 0x2407517bca)
    w3850_812_19 w3850_812_20 rfl rfl rfl

theorem m3850_812_4412_600 : blockEstimate 3850 812 4412 600 = 0x46f6b6bd3e :=
  block_append (B := 3850) (J := 812) (start := 4412) (next := 4612)
    (a := 200) (b := 400) (n := 600) (x := 0x22ef654174) (y := 0x2407517bca) (z := 0x46f6b6bd3e)
    w3850_812_18 m3850_812_4612_400 rfl rfl rfl

theorem m3850_812_5212_262 : blockEstimate 3850 812 5212 262 = 0x152c1ee69 :=
  block_append (B := 3850) (J := 812) (start := 5212) (next := 5412)
    (a := 200) (b := 62) (n := 262) (x := 0x14de63b71) (y := 0x4dbb2f8) (z := 0x152c1ee69)
    w3850_812_22 w3850_812_23 rfl rfl rfl

theorem m3850_812_5012_462 : blockEstimate 3850 812 5012 462 = 0x70563df6e :=
  block_append (B := 3850) (J := 812) (start := 5012) (next := 5212)
    (a := 200) (b := 262) (n := 462) (x := 0x5b2a1f105) (y := 0x152c1ee69) (z := 0x70563df6e)
    w3850_812_21 m3850_812_5212_262 rfl rfl rfl

theorem m3850_812_4412_1062 : blockEstimate 3850 812 4412 1062 = 0x4dfc1a9cac :=
  block_append (B := 3850) (J := 812) (start := 4412) (next := 5012)
    (a := 600) (b := 462) (n := 1062) (x := 0x46f6b6bd3e) (y := 0x70563df6e) (z := 0x4dfc1a9cac)
    m3850_812_4412_600 m3850_812_5012_462 rfl rfl rfl

theorem m3850_812_3212_2262 : blockEstimate 3850 812 3212 2262 = 0x231bacfee56 :=
  block_append (B := 3850) (J := 812) (start := 3212) (next := 4412)
    (a := 1200) (b := 1062) (n := 2262) (x := 0x1e3beb551aa) (y := 0x4dfc1a9cac) (z := 0x231bacfee56)
    m3850_812_3212_1200 m3850_812_4412_1062 rfl rfl rfl

theorem m3850_812_812_4662 : blockEstimate 3850 812 812 4662 = 0x5601e71ab3f :=
  block_append (B := 3850) (J := 812) (start := 812) (next := 3212)
    (a := 2400) (b := 2262) (n := 4662) (x := 0x32e63a1bce9) (y := 0x231bacfee56) (z := 0x5601e71ab3f)
    m3850_812_812_2400 m3850_812_3212_2262 rfl rfl rfl

theorem nextMoment3850_812 : momentEstimate 3850 812 = 0x5601e71ab3f := m3850_812_812_4662

theorem m4863_1027_1227_400 : blockEstimate 4863 1027 1227 400 = 0x23b208ad74 :=
  block_append (B := 4863) (J := 1027) (start := 1227) (next := 1427)
    (a := 200) (b := 200) (n := 400) (x := 0x9ef195052) (y := 0x19c2ef5d22) (z := 0x23b208ad74)
    w4863_1027_1 w4863_1027_2 rfl rfl rfl

theorem m4863_1027_1027_600 : blockEstimate 4863 1027 1027 600 = 0x252e497bf6 :=
  block_append (B := 4863) (J := 1027) (start := 1027) (next := 1227)
    (a := 200) (b := 400) (n := 600) (x := 0x17c40ce82) (y := 0x23b208ad74) (z := 0x252e497bf6)
    w4863_1027_0 m4863_1027_1227_400 rfl rfl rfl

theorem m4863_1027_1627_400 : blockEstimate 4863 1027 1627 400 = 0x7aeed41cb4 :=
  block_append (B := 4863) (J := 1027) (start := 1627) (next := 1827)
    (a := 200) (b := 200) (n := 400) (x := 0x2fd9a8c4f2) (y := 0x4b152b57c2) (z := 0x7aeed41cb4)
    w4863_1027_3 w4863_1027_4 rfl rfl rfl

theorem m4863_1027_2027_400 : blockEstimate 4863 1027 2027 400 = 0xefafe57ea9 :=
  block_append (B := 4863) (J := 1027) (start := 2027) (next := 2227)
    (a := 200) (b := 200) (n := 400) (x := 0x6998b57841) (y := 0x8617300668) (z := 0xefafe57ea9)
    w4863_1027_5 w4863_1027_6 rfl rfl rfl

theorem m4863_1027_1627_800 : blockEstimate 4863 1027 1627 800 = 0x16a9eb99b5d :=
  block_append (B := 4863) (J := 1027) (start := 1627) (next := 2027)
    (a := 400) (b := 400) (n := 800) (x := 0x7aeed41cb4) (y := 0xefafe57ea9) (z := 0x16a9eb99b5d)
    m4863_1027_1627_400 m4863_1027_2027_400 rfl rfl rfl

theorem m4863_1027_1027_1400 : blockEstimate 4863 1027 1027 1400 = 0x18fcd031753 :=
  block_append (B := 4863) (J := 1027) (start := 1027) (next := 1627)
    (a := 600) (b := 800) (n := 1400) (x := 0x252e497bf6) (y := 0x16a9eb99b5d) (z := 0x18fcd031753)
    m4863_1027_1027_600 m4863_1027_1627_800 rfl rfl rfl

theorem m4863_1027_2427_400 : blockEstimate 4863 1027 2427 400 = 0x1525a8fd650 :=
  block_append (B := 4863) (J := 1027) (start := 2427) (next := 2627)
    (a := 200) (b := 200) (n := 400) (x := 0x9ec20acee8) (y := 0xb398850768) (z := 0x1525a8fd650)
    w4863_1027_7 w4863_1027_8 rfl rfl rfl

theorem m4863_1027_2827_400 : blockEstimate 4863 1027 2827 400 = 0x19662f67850 :=
  block_append (B := 4863) (J := 1027) (start := 2827) (next := 3027)
    (a := 200) (b := 200) (n := 400) (x := 0xc49a9eafe8) (y := 0xd1c857c868) (z := 0x19662f67850)
    w4863_1027_9 w4863_1027_10 rfl rfl rfl

theorem m4863_1027_2427_800 : blockEstimate 4863 1027 2427 800 = 0x2e8bd864ea0 :=
  block_append (B := 4863) (J := 1027) (start := 2427) (next := 2827)
    (a := 400) (b := 400) (n := 800) (x := 0x1525a8fd650) (y := 0x19662f67850) (z := 0x2e8bd864ea0)
    m4863_1027_2427_400 m4863_1027_2827_400 rfl rfl rfl

theorem m4863_1027_3227_400 : blockEstimate 4863 1027 3227 400 = 0x1bbc8589a50 :=
  block_append (B := 4863) (J := 1027) (start := 3227) (next := 3427)
    (a := 200) (b := 200) (n := 400) (x := 0xdb21b050e8) (y := 0xe0a6a84968) (z := 0x1bbc8589a50)
    w4863_1027_11 w4863_1027_12 rfl rfl rfl

theorem m4863_1027_3627_400 : blockEstimate 4863 1027 3627 400 = 0x1c28ab63c50 :=
  block_append (B := 4863) (J := 1027) (start := 3627) (next := 3827)
    (a := 200) (b := 200) (n := 400) (x := 0xe2573fb1e8) (y := 0xe033768a68) (z := 0x1c28ab63c50)
    w4863_1027_13 w4863_1027_14 rfl rfl rfl

theorem m4863_1027_3227_800 : blockEstimate 4863 1027 3227 800 = 0x37e530ed6a0 :=
  block_append (B := 4863) (J := 1027) (start := 3227) (next := 3627)
    (a := 400) (b := 400) (n := 800) (x := 0x1bbc8589a50) (y := 0x1c28ab63c50) (z := 0x37e530ed6a0)
    m4863_1027_3227_400 m4863_1027_3627_400 rfl rfl rfl

theorem m4863_1027_2427_1600 : blockEstimate 4863 1027 2427 1600 = 0x66710952540 :=
  block_append (B := 4863) (J := 1027) (start := 2427) (next := 3227)
    (a := 800) (b := 800) (n := 1600) (x := 0x2e8bd864ea0) (y := 0x37e530ed6a0) (z := 0x66710952540)
    m4863_1027_2427_800 m4863_1027_3227_800 rfl rfl rfl

theorem m4863_1027_1027_3000 : blockEstimate 4863 1027 1027 3000 = 0x7f6dd983c93 :=
  block_append (B := 4863) (J := 1027) (start := 1027) (next := 2427)
    (a := 1400) (b := 1600) (n := 3000) (x := 0x18fcd031753) (y := 0x66710952540) (z := 0x7f6dd983c93)
    m4863_1027_1027_1400 m4863_1027_2427_1600 rfl rfl rfl

theorem m4863_1027_4227_400 : blockEstimate 4863 1027 4227 400 = 0x1933c9a3f50 :=
  block_append (B := 4863) (J := 1027) (start := 4227) (next := 4427)
    (a := 200) (b := 200) (n := 400) (x := 0xd06ec28b68) (y := 0xc2cdd7b3e8) (z := 0x1933c9a3f50)
    w4863_1027_16 w4863_1027_17 rfl rfl rfl

theorem m4863_1027_4027_600 : blockEstimate 4863 1027 4027 600 = 0x26d77e71238 :=
  block_append (B := 4863) (J := 1027) (start := 4027) (next := 4227)
    (a := 200) (b := 400) (n := 600) (x := 0xda3b4cd2e8) (y := 0x1933c9a3f50) (z := 0x26d77e71238)
    w4863_1027_15 m4863_1027_4227_400 rfl rfl rfl

theorem m4863_1027_4627_400 : blockEstimate 4863 1027 4627 400 = 0x14da99085cc :=
  block_append (B := 4863) (J := 1027) (start := 4627) (next := 4827)
    (a := 200) (b := 200) (n := 400) (x := 0xb1588c4c68) (y := 0x9c51043964) (z := 0x14da99085cc)
    w4863_1027_18 w4863_1027_19 rfl rfl rfl

theorem m4863_1027_5027_400 : blockEstimate 4863 1027 5027 400 = 0xf49d17b5a2 :=
  block_append (B := 4863) (J := 1027) (start := 5027) (next := 5227)
    (a := 200) (b := 200) (n := 400) (x := 0x85b28b51d1) (y := 0x6eea8c63d1) (z := 0xf49d17b5a2)
    w4863_1027_20 w4863_1027_21 rfl rfl rfl

theorem m4863_1027_4627_800 : blockEstimate 4863 1027 4627 800 = 0x24246a83b6e :=
  block_append (B := 4863) (J := 1027) (start := 4627) (next := 5027)
    (a := 400) (b := 400) (n := 800) (x := 0x14da99085cc) (y := 0xf49d17b5a2) (z := 0x24246a83b6e)
    m4863_1027_4627_400 m4863_1027_5027_400 rfl rfl rfl

theorem m4863_1027_4027_1400 : blockEstimate 4863 1027 4027 1400 = 0x4afbe8f4da6 :=
  block_append (B := 4863) (J := 1027) (start := 4027) (next := 4627)
    (a := 600) (b := 800) (n := 1400) (x := 0x26d77e71238) (y := 0x24246a83b6e) (z := 0x4afbe8f4da6)
    m4863_1027_4027_600 m4863_1027_4627_800 rfl rfl rfl

theorem m4863_1027_5427_400 : blockEstimate 4863 1027 5427 400 = 0x9c7da28b58 :=
  block_append (B := 4863) (J := 1027) (start := 5427) (next := 5627)
    (a := 200) (b := 200) (n := 400) (x := 0x58b6dbe157) (y := 0x43c6c6aa01) (z := 0x9c7da28b58)
    w4863_1027_22 w4863_1027_23 rfl rfl rfl

theorem m4863_1027_5827_400 : blockEstimate 4863 1027 5827 400 = 0x50ad6f67db :=
  block_append (B := 4863) (J := 1027) (start := 5827) (next := 6027)
    (a := 200) (b := 200) (n := 400) (x := 0x30ad835e00) (y := 0x1fffec09db) (z := 0x50ad6f67db)
    w4863_1027_24 w4863_1027_25 rfl rfl rfl

theorem m4863_1027_5427_800 : blockEstimate 4863 1027 5427 800 = 0xed2b11f333 :=
  block_append (B := 4863) (J := 1027) (start := 5427) (next := 5827)
    (a := 400) (b := 400) (n := 800) (x := 0x9c7da28b58) (y := 0x50ad6f67db) (z := 0xed2b11f333)
    m4863_1027_5427_400 m4863_1027_5827_400 rfl rfl rfl

theorem m4863_1027_6227_400 : blockEstimate 4863 1027 6227 400 = 0x1adb255ab2 :=
  block_append (B := 4863) (J := 1027) (start := 6227) (next := 6427)
    (a := 200) (b := 200) (n := 400) (x := 0x1273e91a3f) (y := 0x8673c4073) (z := 0x1adb255ab2)
    w4863_1027_26 w4863_1027_27 rfl rfl rfl

theorem m4863_1027_6627_290 : blockEstimate 4863 1027 6627 290 = 0x245a544d0 :=
  block_append (B := 4863) (J := 1027) (start := 6627) (next := 6827)
    (a := 200) (b := 90) (n := 290) (x := 0x2334dab77) (y := 0x12579959) (z := 0x245a544d0)
    w4863_1027_28 w4863_1027_29 rfl rfl rfl

theorem m4863_1027_6227_690 : blockEstimate 4863 1027 6227 690 = 0x1d20ca9f82 :=
  block_append (B := 4863) (J := 1027) (start := 6227) (next := 6627)
    (a := 400) (b := 290) (n := 690) (x := 0x1adb255ab2) (y := 0x245a544d0) (z := 0x1d20ca9f82)
    m4863_1027_6227_400 m4863_1027_6627_290 rfl rfl rfl

theorem m4863_1027_5427_1490 : blockEstimate 4863 1027 5427 1490 = 0x10a4bdc92b5 :=
  block_append (B := 4863) (J := 1027) (start := 5427) (next := 6227)
    (a := 800) (b := 690) (n := 1490) (x := 0xed2b11f333) (y := 0x1d20ca9f82) (z := 0x10a4bdc92b5)
    m4863_1027_5427_800 m4863_1027_6227_690 rfl rfl rfl

theorem m4863_1027_4027_2890 : blockEstimate 4863 1027 4027 2890 = 0x5ba0a6be05b :=
  block_append (B := 4863) (J := 1027) (start := 4027) (next := 5427)
    (a := 1400) (b := 1490) (n := 2890) (x := 0x4afbe8f4da6) (y := 0x10a4bdc92b5) (z := 0x5ba0a6be05b)
    m4863_1027_4027_1400 m4863_1027_5427_1490 rfl rfl rfl

theorem m4863_1027_1027_5890 : blockEstimate 4863 1027 1027 5890 = 0xdb0e8041cee :=
  block_append (B := 4863) (J := 1027) (start := 1027) (next := 4027)
    (a := 3000) (b := 2890) (n := 5890) (x := 0x7f6dd983c93) (y := 0x5ba0a6be05b) (z := 0xdb0e8041cee)
    m4863_1027_1027_3000 m4863_1027_4027_2890 rfl rfl rfl

theorem nextMoment4863_1027 : momentEstimate 4863 1027 = 0xdb0e8041cee := m4863_1027_1027_5890

theorem m6010_1275_1275_400 : blockEstimate 6010 1275 1275 400 = 0xe4a12cc64 :=
  block_append (B := 6010) (J := 1275) (start := 1275) (next := 1475)
    (a := 200) (b := 200) (n := 400) (x := 0x1d8c7c8ea) (y := 0xc714b037a) (z := 0xe4a12cc64)
    w6010_1275_0 w6010_1275_1 rfl rfl rfl

theorem m6010_1275_1675_400 : blockEstimate 6010 1275 1675 400 = 0x5d9db64aa4 :=
  block_append (B := 6010) (J := 1275) (start := 1675) (next := 1875)
    (a := 200) (b := 200) (n := 400) (x := 0x208dba6f0a) (y := 0x3d0ffbdb9a) (z := 0x5d9db64aa4)
    w6010_1275_2 w6010_1275_3 rfl rfl rfl

theorem m6010_1275_1275_800 : blockEstimate 6010 1275 1275 800 = 0x6be7c91708 :=
  block_append (B := 6010) (J := 1275) (start := 1275) (next := 1675)
    (a := 400) (b := 400) (n := 800) (x := 0xe4a12cc64) (y := 0x5d9db64aa4) (z := 0x6be7c91708)
    m6010_1275_1275_400 m6010_1275_1675_400 rfl rfl rfl

theorem m6010_1275_2075_400 : blockEstimate 6010 1275 2075 400 = 0xeba78110e4 :=
  block_append (B := 6010) (J := 1275) (start := 2075) (next := 2275)
    (a := 200) (b := 200) (n := 400) (x := 0x60d9f5192a) (y := 0x8acd8bf7ba) (z := 0xeba78110e4)
    w6010_1275_4 w6010_1275_5 rfl rfl rfl

theorem m6010_1275_2675_400 : blockEstimate 6010 1275 2675 400 = 0x1f726fa77f0 :=
  block_append (B := 6010) (J := 1275) (start := 2675) (next := 2875)
    (a := 200) (b := 200) (n := 400) (x := 0xe71775ebb8) (y := 0x1100f848c38) (z := 0x1f726fa77f0)
    w6010_1275_7 w6010_1275_8 rfl rfl rfl

theorem m6010_1275_2475_600 : blockEstimate 6010 1275 2475 600 = 0x2b0999266a1 :=
  block_append (B := 6010) (J := 1275) (start := 2475) (next := 2675)
    (a := 200) (b := 400) (n := 600) (x := 0xb97297eeb1) (y := 0x1f726fa77f0) (z := 0x2b0999266a1)
    w6010_1275_6 m6010_1275_2675_400 rfl rfl rfl

theorem m6010_1275_2075_1000 : blockEstimate 6010 1275 2075 1000 = 0x39c41137785 :=
  block_append (B := 6010) (J := 1275) (start := 2075) (next := 2475)
    (a := 400) (b := 600) (n := 1000) (x := 0xeba78110e4) (y := 0x2b0999266a1) (z := 0x39c41137785)
    m6010_1275_2075_400 m6010_1275_2475_600 rfl rfl rfl

theorem m6010_1275_1275_1800 : blockEstimate 6010 1275 1275 1800 = 0x40828dc8e8d :=
  block_append (B := 6010) (J := 1275) (start := 1275) (next := 2075)
    (a := 800) (b := 1000) (n := 1800) (x := 0x6be7c91708) (y := 0x39c41137785) (z := 0x40828dc8e8d)
    m6010_1275_1275_800 m6010_1275_2075_1000 rfl rfl rfl

theorem m6010_1275_3075_400 : blockEstimate 6010 1275 3075 400 = 0x28803a739f0 :=
  block_append (B := 6010) (J := 1275) (start := 3075) (next := 3275)
    (a := 200) (b := 200) (n := 400) (x := 0x13446afbcb8) (y := 0x153bcf77d38) (z := 0x28803a739f0)
    w6010_1275_9 w6010_1275_10 rfl rfl rfl

theorem m6010_1275_3475_400 : blockEstimate 6010 1275 3475 400 = 0x2f2d9387bf0 :=
  block_append (B := 6010) (J := 1275) (start := 3475) (next := 3675)
    (a := 200) (b := 200) (n := 400) (x := 0x16e725bcdb8) (y := 0x18466dcae38) (z := 0x2f2d9387bf0)
    w6010_1275_11 w6010_1275_12 rfl rfl rfl

theorem m6010_1275_3075_800 : blockEstimate 6010 1275 3075 800 = 0x57adcdfb5e0 :=
  block_append (B := 6010) (J := 1275) (start := 3075) (next := 3475)
    (a := 400) (b := 400) (n := 800) (x := 0x28803a739f0) (y := 0x2f2d9387bf0) (z := 0x57adcdfb5e0)
    m6010_1275_3075_400 m6010_1275_3475_400 rfl rfl rfl

theorem m6010_1275_3875_400 : blockEstimate 6010 1275 3875 400 = 0x337a7ae3df0 :=
  block_append (B := 6010) (J := 1275) (start := 3875) (next := 4075)
    (a := 200) (b := 200) (n := 400) (x := 0x1959a7a1eb8) (y := 0x1a20d341f38) (z := 0x337a7ae3df0)
    w6010_1275_13 w6010_1275_14 rfl rfl rfl

theorem m6010_1275_4475_400 : blockEstimate 6010 1275 4475 400 = 0x357900b50f0 :=
  block_append (B := 6010) (J := 1275) (start := 4475) (next := 4675)
    (a := 200) (b := 200) (n := 400) (x := 0x1acaffdd038) (y := 0x1aae00d80b8) (z := 0x357900b50f0)
    w6010_1275_16 w6010_1275_17 rfl rfl rfl

theorem m6010_1275_4275_600 : blockEstimate 6010 1275 4275 600 = 0x5014f1600a8 :=
  block_append (B := 6010) (J := 1275) (start := 4275) (next := 4475)
    (a := 200) (b := 400) (n := 600) (x := 0x1a9bf0aafb8) (y := 0x357900b50f0) (z := 0x5014f1600a8)
    w6010_1275_15 m6010_1275_4475_400 rfl rfl rfl

theorem m6010_1275_3875_1000 : blockEstimate 6010 1275 3875 1000 = 0x838f6c43e98 :=
  block_append (B := 6010) (J := 1275) (start := 3875) (next := 4275)
    (a := 400) (b := 600) (n := 1000) (x := 0x337a7ae3df0) (y := 0x5014f1600a8) (z := 0x838f6c43e98)
    m6010_1275_3875_400 m6010_1275_4275_600 rfl rfl rfl

theorem m6010_1275_3075_1800 : blockEstimate 6010 1275 3075 1800 = 0xdb3d3a3f478 :=
  block_append (B := 6010) (J := 1275) (start := 3075) (next := 3875)
    (a := 800) (b := 1000) (n := 1800) (x := 0x57adcdfb5e0) (y := 0x838f6c43e98) (z := 0xdb3d3a3f478)
    m6010_1275_3075_800 m6010_1275_3875_1000 rfl rfl rfl

theorem m6010_1275_1275_3600 : blockEstimate 6010 1275 1275 3600 = 0x11bbfc808305 :=
  block_append (B := 6010) (J := 1275) (start := 1275) (next := 3075)
    (a := 1800) (b := 1800) (n := 3600) (x := 0x40828dc8e8d) (y := 0xdb3d3a3f478) (z := 0x11bbfc808305)
    m6010_1275_1275_1800 m6010_1275_3075_1800 rfl rfl rfl

theorem m6010_1275_4875_400 : blockEstimate 6010 1275 4875 400 = 0x33d4cbc52f0 :=
  block_append (B := 6010) (J := 1275) (start := 4875) (next := 5075)
    (a := 200) (b := 200) (n := 400) (x := 0x1a44f39c138) (y := 0x198fd8291b8) (z := 0x33d4cbc52f0)
    w6010_1275_18 w6010_1275_19 rfl rfl rfl

theorem m6010_1275_5275_400 : blockEstimate 6010 1275 5275 400 = 0x2fd0251d4f0 :=
  block_append (B := 6010) (J := 1275) (start := 5275) (next := 5475)
    (a := 200) (b := 200) (n := 400) (x := 0x188eae7f238) (y := 0x1741769e2b8) (z := 0x2fd0251d4f0)
    w6010_1275_20 w6010_1275_21 rfl rfl rfl

theorem m6010_1275_4875_800 : blockEstimate 6010 1275 4875 800 = 0x63a4f0e27e0 :=
  block_append (B := 6010) (J := 1275) (start := 4875) (next := 5275)
    (a := 400) (b := 400) (n := 800) (x := 0x33d4cbc52f0) (y := 0x2fd0251d4f0) (z := 0x63a4f0e27e0)
    m6010_1275_4875_400 m6010_1275_5275_400 rfl rfl rfl

theorem m6010_1275_5675_400 : blockEstimate 6010 1275 5675 400 = 0x296b5b9a370 :=
  block_append (B := 6010) (J := 1275) (start := 5675) (next := 5875)
    (a := 200) (b := 200) (n := 400) (x := 0x15a83086338) (y := 0x13c32b14038) (z := 0x296b5b9a370)
    w6010_1275_22 w6010_1275_23 rfl rfl rfl

theorem m6010_1275_6275_400 : blockEstimate 6010 1275 6275 400 = 0x1cc76e5ca3a :=
  block_append (B := 6010) (J := 1275) (start := 6275) (next := 6475)
    (a := 200) (b := 200) (n := 400) (x := 0xf7a8dddb16) (y := 0xd4ce07ef24) (z := 0x1cc76e5ca3a)
    w6010_1275_25 w6010_1275_26 rfl rfl rfl

theorem m6010_1275_6075_600 : blockEstimate 6010 1275 6075 600 = 0x2e6e6898dc3 :=
  block_append (B := 6010) (J := 1275) (start := 6075) (next := 6275)
    (a := 200) (b := 400) (n := 600) (x := 0x11a6fa3c389) (y := 0x1cc76e5ca3a) (z := 0x2e6e6898dc3)
    w6010_1275_24 m6010_1275_6275_400 rfl rfl rfl

theorem m6010_1275_5675_1000 : blockEstimate 6010 1275 5675 1000 = 0x57d9c433133 :=
  block_append (B := 6010) (J := 1275) (start := 5675) (next := 6075)
    (a := 400) (b := 600) (n := 1000) (x := 0x296b5b9a370) (y := 0x2e6e6898dc3) (z := 0x57d9c433133)
    m6010_1275_5675_400 m6010_1275_6075_600 rfl rfl rfl

theorem m6010_1275_4875_1800 : blockEstimate 6010 1275 4875 1800 = 0xbb7eb515913 :=
  block_append (B := 6010) (J := 1275) (start := 4875) (next := 5675)
    (a := 800) (b := 1000) (n := 1800) (x := 0x63a4f0e27e0) (y := 0x57d9c433133) (z := 0xbb7eb515913)
    m6010_1275_4875_800 m6010_1275_5675_1000 rfl rfl rfl

theorem m6010_1275_6675_400 : blockEstimate 6010 1275 6675 400 = 0x1445e82b6a6 :=
  block_append (B := 6010) (J := 1275) (start := 6675) (next := 6875)
    (a := 200) (b := 200) (n := 400) (x := 0xb29b9dba73) (y := 0x91c2e4fc33) (z := 0x1445e82b6a6)
    w6010_1275_27 w6010_1275_28 rfl rfl rfl

theorem m6010_1275_7275_400 : blockEstimate 6010 1275 7275 400 = 0x93cb04a244 :=
  block_append (B := 6010) (J := 1275) (start := 7275) (next := 7475)
    (a := 200) (b := 200) (n := 400) (x := 0x56830fcf23) (y := 0x3d47f4d321) (z := 0x93cb04a244)
    w6010_1275_30 w6010_1275_31 rfl rfl rfl

theorem m6010_1275_7075_600 : blockEstimate 6010 1275 7075 600 = 0x106b4f2161a :=
  block_append (B := 6010) (J := 1275) (start := 7075) (next := 7275)
    (a := 200) (b := 400) (n := 600) (x := 0x72e9ed73d6) (y := 0x93cb04a244) (z := 0x106b4f2161a)
    w6010_1275_29 m6010_1275_7275_400 rfl rfl rfl

theorem m6010_1275_6675_1000 : blockEstimate 6010 1275 6675 1000 = 0x24b1374ccc0 :=
  block_append (B := 6010) (J := 1275) (start := 6675) (next := 7075)
    (a := 400) (b := 600) (n := 1000) (x := 0x1445e82b6a6) (y := 0x106b4f2161a) (z := 0x24b1374ccc0)
    m6010_1275_6675_400 m6010_1275_7075_600 rfl rfl rfl

theorem m6010_1275_7675_400 : blockEstimate 6010 1275 7675 400 = 0x3eb87b2aae :=
  block_append (B := 6010) (J := 1275) (start := 7675) (next := 7875)
    (a := 200) (b := 200) (n := 400) (x := 0x27ecef8535) (y := 0x16cb8ba579) (z := 0x3eb87b2aae)
    w6010_1275_32 w6010_1275_33 rfl rfl rfl

theorem m6010_1275_8275_285 : blockEstimate 6010 1275 8275 285 = 0x2ae799f3c :=
  block_append (B := 6010) (J := 1275) (start := 8275) (next := 8475)
    (a := 200) (b := 85) (n := 285) (x := 0x29b48ec91) (y := 0x1330b2ab) (z := 0x2ae799f3c)
    w6010_1275_35 w6010_1275_36 rfl rfl rfl

theorem m6010_1275_8075_485 : blockEstimate 6010 1275 8075 485 = 0xcebab0229 :=
  block_append (B := 6010) (J := 1275) (start := 8075) (next := 8275)
    (a := 200) (b := 285) (n := 485) (x := 0xa3d3162ed) (y := 0x2ae799f3c) (z := 0xcebab0229)
    w6010_1275_34 m6010_1275_8275_285 rfl rfl rfl

theorem m6010_1275_7675_885 : blockEstimate 6010 1275 7675 885 = 0x4ba4262cd7 :=
  block_append (B := 6010) (J := 1275) (start := 7675) (next := 8075)
    (a := 400) (b := 485) (n := 885) (x := 0x3eb87b2aae) (y := 0xcebab0229) (z := 0x4ba4262cd7)
    m6010_1275_7675_400 m6010_1275_8075_485 rfl rfl rfl

theorem m6010_1275_6675_1885 : blockEstimate 6010 1275 6675 1885 = 0x296b79af997 :=
  block_append (B := 6010) (J := 1275) (start := 6675) (next := 7675)
    (a := 1000) (b := 885) (n := 1885) (x := 0x24b1374ccc0) (y := 0x4ba4262cd7) (z := 0x296b79af997)
    m6010_1275_6675_1000 m6010_1275_7675_885 rfl rfl rfl

theorem m6010_1275_4875_3685 : blockEstimate 6010 1275 4875 3685 = 0xe4ea2ec52aa :=
  block_append (B := 6010) (J := 1275) (start := 4875) (next := 6675)
    (a := 1800) (b := 1885) (n := 3685) (x := 0xbb7eb515913) (y := 0x296b79af997) (z := 0xe4ea2ec52aa)
    m6010_1275_4875_1800 m6010_1275_6675_1885 rfl rfl rfl

theorem m6010_1275_1275_7285 : blockEstimate 6010 1275 1275 7285 = 0x200a9f6cd5af :=
  block_append (B := 6010) (J := 1275) (start := 1275) (next := 4875)
    (a := 3600) (b := 3685) (n := 7285) (x := 0x11bbfc808305) (y := 0xe4ea2ec52aa) (z := 0x200a9f6cd5af)
    m6010_1275_1275_3600 m6010_1275_4875_3685 rfl rfl rfl

theorem nextMoment6010_1275 : momentEstimate 6010 1275 = 0x200a9f6cd5af := m6010_1275_1275_7285

end HighCore82219BankProof

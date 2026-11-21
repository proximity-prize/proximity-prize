import ProximityPrize.SubmissionLower.HighCore82219Moments3

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219BankProof

open P1_7_1_3 (momentEstimate blockEstimate block_append)

set_option maxHeartbeats 14000000

private theorem p1566_343_343 : blockEstimate 1566 343 343 215 = 0x8cb4a7da := by decide +kernel
private theorem p1566_343_558 : blockEstimate 1566 343 558 215 = 0x3495531d0 := by decide +kernel
private theorem p1566_343_773 : blockEstimate 1566 343 773 215 = 0x66d8979d4 := by decide +kernel
private theorem p1566_343_988 : blockEstimate 1566 343 988 215 = 0x815ad2268 := by decide +kernel
private theorem p1566_343_1203 : blockEstimate 1566 343 1203 215 = 0x82643442c := by decide +kernel
private theorem p1566_343_1418 : blockEstimate 1566 343 1418 215 = 0x6a0c0f430 := by decide +kernel
private theorem p1566_343_1633 : blockEstimate 1566 343 1633 215 = 0x403728846 := by decide +kernel
private theorem p1566_343_1848 : blockEstimate 1566 343 1848 215 = 0x194cfe1e9 := by decide +kernel
private theorem p1566_343_2063 : blockEstimate 1566 343 2063 189 = 0x32c0b1a8 := by decide +kernel

private theorem s1566_343_343_430 : blockEstimate 1566 343 343 430 = 0x3d609d9aa :=
  block_append (B := 1566) (J := 343) (start := 343) (next := 558)
    (a := 215) (b := 215) (n := 430) (x := 0x8cb4a7da) (y := 0x3495531d0) (z := 0x3d609d9aa)
    p1566_343_343 p1566_343_558 rfl rfl rfl

private theorem s1566_343_773_430 : blockEstimate 1566 343 773 430 = 0xe83369c3c :=
  block_append (B := 1566) (J := 343) (start := 773) (next := 988)
    (a := 215) (b := 215) (n := 430) (x := 0x66d8979d4) (y := 0x815ad2268) (z := 0xe83369c3c)
    p1566_343_773 p1566_343_988 rfl rfl rfl

private theorem s1566_343_343_860 : blockEstimate 1566 343 343 860 = 0x12594075e6 :=
  block_append (B := 1566) (J := 343) (start := 343) (next := 773)
    (a := 430) (b := 430) (n := 860) (x := 0x3d609d9aa) (y := 0xe83369c3c) (z := 0x12594075e6)
    s1566_343_343_430 s1566_343_773_430 rfl rfl rfl

private theorem s1566_343_1203_430 : blockEstimate 1566 343 1203 430 = 0xec704385c :=
  block_append (B := 1566) (J := 343) (start := 1203) (next := 1418)
    (a := 215) (b := 215) (n := 430) (x := 0x82643442c) (y := 0x6a0c0f430) (z := 0xec704385c)
    p1566_343_1203 p1566_343_1418 rfl rfl rfl

private theorem s1566_343_1848_404 : blockEstimate 1566 343 1848 404 = 0x1c7909391 :=
  block_append (B := 1566) (J := 343) (start := 1848) (next := 2063)
    (a := 215) (b := 189) (n := 404) (x := 0x194cfe1e9) (y := 0x32c0b1a8) (z := 0x1c7909391)
    p1566_343_1848 p1566_343_2063 rfl rfl rfl

private theorem s1566_343_1633_619 : blockEstimate 1566 343 1633 619 = 0x5cb031bd7 :=
  block_append (B := 1566) (J := 343) (start := 1633) (next := 1848)
    (a := 215) (b := 404) (n := 619) (x := 0x403728846) (y := 0x1c7909391) (z := 0x5cb031bd7)
    p1566_343_1633 s1566_343_1848_404 rfl rfl rfl

private theorem s1566_343_1203_1049 : blockEstimate 1566 343 1203 1049 = 0x1492075433 :=
  block_append (B := 1566) (J := 343) (start := 1203) (next := 1633)
    (a := 430) (b := 619) (n := 1049) (x := 0xec704385c) (y := 0x5cb031bd7) (z := 0x1492075433)
    s1566_343_1203_430 s1566_343_1633_619 rfl rfl rfl

private theorem s1566_343_343_1909 : blockEstimate 1566 343 343 1909 = 0x26eb47ca19 :=
  block_append (B := 1566) (J := 343) (start := 343) (next := 1203)
    (a := 860) (b := 1049) (n := 1909) (x := 0x12594075e6) (y := 0x1492075433) (z := 0x26eb47ca19)
    s1566_343_343_860 s1566_343_1203_1049 rfl rfl rfl

theorem moment1566_343 : momentEstimate 1566 343 = 0x26eb47ca19 := s1566_343_343_1909

private theorem p1572_307_307 : blockEstimate 1572 307 307 215 = 0x8d4e6d02 := by decide +kernel
private theorem p1572_307_522 : blockEstimate 1572 307 522 215 = 0x33f648b6b := by decide +kernel
private theorem p1572_307_737 : blockEstimate 1572 307 737 215 = 0x6138ac8a2 := by decide +kernel
private theorem p1572_307_952 : blockEstimate 1572 307 952 215 = 0x7851c86f8 := by decide +kernel
private theorem p1572_307_1167 : blockEstimate 1572 307 1167 215 = 0x789c75e76 := by decide +kernel
private theorem p1572_307_1382 : blockEstimate 1572 307 1382 215 = 0x621a008f0 := by decide +kernel
private theorem p1572_307_1597 : blockEstimate 1572 307 1597 215 = 0x3a0340332 := by decide +kernel
private theorem p1572_307_1812 : blockEstimate 1572 307 1812 215 = 0x1501e502a := by decide +kernel
private theorem p1572_307_2027 : blockEstimate 1572 307 2027 159 = 0x1ec3a3e8 := by decide +kernel

private theorem s1572_307_307_430 : blockEstimate 1572 307 307 430 = 0x3ccb2f86d :=
  block_append (B := 1572) (J := 307) (start := 307) (next := 522)
    (a := 215) (b := 215) (n := 430) (x := 0x8d4e6d02) (y := 0x33f648b6b) (z := 0x3ccb2f86d)
    p1572_307_307 p1572_307_522 rfl rfl rfl

private theorem s1572_307_737_430 : blockEstimate 1572 307 737 430 = 0xd98a74f9a :=
  block_append (B := 1572) (J := 307) (start := 737) (next := 952)
    (a := 215) (b := 215) (n := 430) (x := 0x6138ac8a2) (y := 0x7851c86f8) (z := 0xd98a74f9a)
    p1572_307_737 p1572_307_952 rfl rfl rfl

private theorem s1572_307_307_860 : blockEstimate 1572 307 307 860 = 0x11655a4807 :=
  block_append (B := 1572) (J := 307) (start := 307) (next := 737)
    (a := 430) (b := 430) (n := 860) (x := 0x3ccb2f86d) (y := 0xd98a74f9a) (z := 0x11655a4807)
    s1572_307_307_430 s1572_307_737_430 rfl rfl rfl

private theorem s1572_307_1167_430 : blockEstimate 1572 307 1167 430 = 0xdab676766 :=
  block_append (B := 1572) (J := 307) (start := 1167) (next := 1382)
    (a := 215) (b := 215) (n := 430) (x := 0x789c75e76) (y := 0x621a008f0) (z := 0xdab676766)
    p1572_307_1167 p1572_307_1382 rfl rfl rfl

private theorem s1572_307_1812_374 : blockEstimate 1572 307 1812 374 = 0x16ee1f412 :=
  block_append (B := 1572) (J := 307) (start := 1812) (next := 2027)
    (a := 215) (b := 159) (n := 374) (x := 0x1501e502a) (y := 0x1ec3a3e8) (z := 0x16ee1f412)
    p1572_307_1812 p1572_307_2027 rfl rfl rfl

private theorem s1572_307_1597_589 : blockEstimate 1572 307 1597 589 = 0x50f15f744 :=
  block_append (B := 1572) (J := 307) (start := 1597) (next := 1812)
    (a := 215) (b := 374) (n := 589) (x := 0x3a0340332) (y := 0x16ee1f412) (z := 0x50f15f744)
    p1572_307_1597 s1572_307_1812_374 rfl rfl rfl

private theorem s1572_307_1167_1019 : blockEstimate 1572 307 1167 1019 = 0x12ba7d5eaa :=
  block_append (B := 1572) (J := 307) (start := 1167) (next := 1597)
    (a := 430) (b := 589) (n := 1019) (x := 0xdab676766) (y := 0x50f15f744) (z := 0x12ba7d5eaa)
    s1572_307_1167_430 s1572_307_1597_589 rfl rfl rfl

private theorem s1572_307_307_1879 : blockEstimate 1572 307 307 1879 = 0x241fd7a6b1 :=
  block_append (B := 1572) (J := 307) (start := 307) (next := 1167)
    (a := 860) (b := 1019) (n := 1879) (x := 0x11655a4807) (y := 0x12ba7d5eaa) (z := 0x241fd7a6b1)
    s1572_307_307_860 s1572_307_1167_1019 rfl rfl rfl

theorem moment1572_307 : momentEstimate 1572 307 = 0x241fd7a6b1 := s1572_307_307_1879

private theorem p1703_357_357 : blockEstimate 1703 357 357 215 = 0x9a6bbd96 := by decide +kernel
private theorem p1703_357_572 : blockEstimate 1703 357 572 215 = 0x3ab2a546c := by decide +kernel
private theorem p1703_357_787 : blockEstimate 1703 357 787 215 = 0x7716a55c2 := by decide +kernel
private theorem p1703_357_1002 : blockEstimate 1703 357 1002 215 = 0x9b8da7e3f := by decide +kernel
private theorem p1703_357_1217 : blockEstimate 1703 357 1217 215 = 0xa5826fe28 := by decide +kernel
private theorem p1703_357_1432 : blockEstimate 1703 357 1432 215 = 0x94f4fd57d := by decide +kernel
private theorem p1703_357_1647 : blockEstimate 1703 357 1647 215 = 0x6b5c333a0 := by decide +kernel
private theorem p1703_357_1862 : blockEstimate 1703 357 1862 215 = 0x395e1d7c9 := by decide +kernel
private theorem p1703_357_2077 : blockEstimate 1703 357 2077 215 = 0x120f30cfa := by decide +kernel
private theorem p1703_357_2292 : blockEstimate 1703 357 2292 125 = 0x1089f950 := by decide +kernel

private theorem s1703_357_357_430 : blockEstimate 1703 357 357 430 = 0x445961202 :=
  block_append (B := 1703) (J := 357) (start := 357) (next := 572)
    (a := 215) (b := 215) (n := 430) (x := 0x9a6bbd96) (y := 0x3ab2a546c) (z := 0x445961202)
    p1703_357_357 p1703_357_572 rfl rfl rfl

private theorem s1703_357_1002_430 : blockEstimate 1703 357 1002 430 = 0x1411017c67 :=
  block_append (B := 1703) (J := 357) (start := 1002) (next := 1217)
    (a := 215) (b := 215) (n := 430) (x := 0x9b8da7e3f) (y := 0xa5826fe28) (z := 0x1411017c67)
    p1703_357_1002 p1703_357_1217 rfl rfl rfl

private theorem s1703_357_787_645 : blockEstimate 1703 357 787 645 = 0x1b826bd229 :=
  block_append (B := 1703) (J := 357) (start := 787) (next := 1002)
    (a := 215) (b := 430) (n := 645) (x := 0x7716a55c2) (y := 0x1411017c67) (z := 0x1b826bd229)
    p1703_357_787 s1703_357_1002_430 rfl rfl rfl

private theorem s1703_357_357_1075 : blockEstimate 1703 357 357 1075 = 0x1fc801e42b :=
  block_append (B := 1703) (J := 357) (start := 357) (next := 787)
    (a := 430) (b := 645) (n := 1075) (x := 0x445961202) (y := 0x1b826bd229) (z := 0x1fc801e42b)
    s1703_357_357_430 s1703_357_787_645 rfl rfl rfl

private theorem s1703_357_1432_430 : blockEstimate 1703 357 1432 430 = 0x100513091d :=
  block_append (B := 1703) (J := 357) (start := 1432) (next := 1647)
    (a := 215) (b := 215) (n := 430) (x := 0x94f4fd57d) (y := 0x6b5c333a0) (z := 0x100513091d)
    p1703_357_1432 p1703_357_1647 rfl rfl rfl

private theorem s1703_357_2077_340 : blockEstimate 1703 357 2077 340 = 0x1317d064a :=
  block_append (B := 1703) (J := 357) (start := 2077) (next := 2292)
    (a := 215) (b := 125) (n := 340) (x := 0x120f30cfa) (y := 0x1089f950) (z := 0x1317d064a)
    p1703_357_2077 p1703_357_2292 rfl rfl rfl

private theorem s1703_357_1862_555 : blockEstimate 1703 357 1862 555 = 0x4c75ede13 :=
  block_append (B := 1703) (J := 357) (start := 1862) (next := 2077)
    (a := 215) (b := 340) (n := 555) (x := 0x395e1d7c9) (y := 0x1317d064a) (z := 0x4c75ede13)
    p1703_357_1862 s1703_357_2077_340 rfl rfl rfl

private theorem s1703_357_1432_985 : blockEstimate 1703 357 1432 985 = 0x14cc71e730 :=
  block_append (B := 1703) (J := 357) (start := 1432) (next := 1862)
    (a := 430) (b := 555) (n := 985) (x := 0x100513091d) (y := 0x4c75ede13) (z := 0x14cc71e730)
    s1703_357_1432_430 s1703_357_1862_555 rfl rfl rfl

private theorem s1703_357_357_2060 : blockEstimate 1703 357 357 2060 = 0x349473cb5b :=
  block_append (B := 1703) (J := 357) (start := 357) (next := 1432)
    (a := 1075) (b := 985) (n := 2060) (x := 0x1fc801e42b) (y := 0x14cc71e730) (z := 0x349473cb5b)
    s1703_357_357_1075 s1703_357_1432_985 rfl rfl rfl

theorem moment1703_357 : momentEstimate 1703 357 = 0x349473cb5b := s1703_357_357_2060

private theorem p1839_385_385 : blockEstimate 1839 385 385 215 = 0xa8093276 := by decide +kernel
private theorem p1839_385_600 : blockEstimate 1839 385 600 215 = 0x40d6c6955 := by decide +kernel
private theorem p1839_385_815 : blockEstimate 1839 385 815 215 = 0x89e1fdea6 := by decide +kernel
private theorem p1839_385_1030 : blockEstimate 1839 385 1030 215 = 0xbb2b8dee1 := by decide +kernel
private theorem p1839_385_1245 : blockEstimate 1839 385 1245 215 = 0xcfe01f300 := by decide +kernel
private theorem p1839_385_1460 : blockEstimate 1839 385 1460 215 = 0xc7ffb1b03 := by decide +kernel
private theorem p1839_385_1675 : blockEstimate 1839 385 1675 215 = 0xa3967be4d := by decide +kernel
private theorem p1839_385_1890 : blockEstimate 1839 385 1890 215 = 0x6a6910bc7 := by decide +kernel
private theorem p1839_385_2105 : blockEstimate 1839 385 2105 215 = 0x331c1724d := by decide +kernel
private theorem p1839_385_2320 : blockEstimate 1839 385 2320 215 = 0xcba85474 := by decide +kernel
private theorem p1839_385_2535 : blockEstimate 1839 385 2535 74 = 0x3db743f := by decide +kernel

private theorem s1839_385_385_430 : blockEstimate 1839 385 385 430 = 0x4b5759bcb :=
  block_append (B := 1839) (J := 385) (start := 385) (next := 600)
    (a := 215) (b := 215) (n := 430) (x := 0xa8093276) (y := 0x40d6c6955) (z := 0x4b5759bcb)
    p1839_385_385 p1839_385_600 rfl rfl rfl

private theorem s1839_385_1030_430 : blockEstimate 1839 385 1030 430 = 0x18b0bad1e1 :=
  block_append (B := 1839) (J := 385) (start := 1030) (next := 1245)
    (a := 215) (b := 215) (n := 430) (x := 0xbb2b8dee1) (y := 0xcfe01f300) (z := 0x18b0bad1e1)
    p1839_385_1030 p1839_385_1245 rfl rfl rfl

private theorem s1839_385_815_645 : blockEstimate 1839 385 815 645 = 0x214edab087 :=
  block_append (B := 1839) (J := 385) (start := 815) (next := 1030)
    (a := 215) (b := 430) (n := 645) (x := 0x89e1fdea6) (y := 0x18b0bad1e1) (z := 0x214edab087)
    p1839_385_815 s1839_385_1030_430 rfl rfl rfl

private theorem s1839_385_385_1075 : blockEstimate 1839 385 385 1075 = 0x2604504c52 :=
  block_append (B := 1839) (J := 385) (start := 385) (next := 815)
    (a := 430) (b := 645) (n := 1075) (x := 0x4b5759bcb) (y := 0x214edab087) (z := 0x2604504c52)
    s1839_385_385_430 s1839_385_815_645 rfl rfl rfl

private theorem s1839_385_1675_430 : blockEstimate 1839 385 1675 430 = 0x10dff8ca14 :=
  block_append (B := 1839) (J := 385) (start := 1675) (next := 1890)
    (a := 215) (b := 215) (n := 430) (x := 0xa3967be4d) (y := 0x6a6910bc7) (z := 0x10dff8ca14)
    p1839_385_1675 p1839_385_1890 rfl rfl rfl

private theorem s1839_385_1460_645 : blockEstimate 1839 385 1460 645 = 0x1d5ff3e517 :=
  block_append (B := 1839) (J := 385) (start := 1460) (next := 1675)
    (a := 215) (b := 430) (n := 645) (x := 0xc7ffb1b03) (y := 0x10dff8ca14) (z := 0x1d5ff3e517)
    p1839_385_1460 s1839_385_1675_430 rfl rfl rfl

private theorem s1839_385_2320_289 : blockEstimate 1839 385 2320 289 = 0xcf83c8b3 :=
  block_append (B := 1839) (J := 385) (start := 2320) (next := 2535)
    (a := 215) (b := 74) (n := 289) (x := 0xcba85474) (y := 0x3db743f) (z := 0xcf83c8b3)
    p1839_385_2320 p1839_385_2535 rfl rfl rfl

private theorem s1839_385_2105_504 : blockEstimate 1839 385 2105 504 = 0x401453b00 :=
  block_append (B := 1839) (J := 385) (start := 2105) (next := 2320)
    (a := 215) (b := 289) (n := 504) (x := 0x331c1724d) (y := 0xcf83c8b3) (z := 0x401453b00)
    p1839_385_2105 s1839_385_2320_289 rfl rfl rfl

private theorem s1839_385_1460_1149 : blockEstimate 1839 385 1460 1149 = 0x2161392017 :=
  block_append (B := 1839) (J := 385) (start := 1460) (next := 2105)
    (a := 645) (b := 504) (n := 1149) (x := 0x1d5ff3e517) (y := 0x401453b00) (z := 0x2161392017)
    s1839_385_1460_645 s1839_385_2105_504 rfl rfl rfl

private theorem s1839_385_385_2224 : blockEstimate 1839 385 385 2224 = 0x4765896c69 :=
  block_append (B := 1839) (J := 385) (start := 385) (next := 1460)
    (a := 1075) (b := 1149) (n := 2224) (x := 0x2604504c52) (y := 0x2161392017) (z := 0x4765896c69)
    s1839_385_385_1075 s1839_385_1460_1149 rfl rfl rfl

theorem moment1839_385 : momentEstimate 1839 385 = 0x4765896c69 := s1839_385_385_2224

end HighCore82219BankProof

import ProximityPrize.SubmissionLower.KoalaTaperExtraWindows
import ProximityPrize.SubmissionLower.KoalaTaperExtraRawClip

set_option Elab.async false
set_option autoImplicit false

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace KoalaTaperExtra
open K1_13_2_3 Low48PrimaryPivot

private theorem feeA_0_32 : binChunk extraA 0 32 = 0 := by decide +kernel
private theorem feeA_32_64 : binChunk extraA 32 32 = 0 := by decide +kernel
private theorem feeA_64_96 : binChunk extraA 64 32 = 0 := by decide +kernel
private theorem feeA_96_128 : binChunk extraA 96 32 = 0 := by decide +kernel
private theorem feeA_128_160 : binChunk extraA 128 32 = 0 := by decide +kernel
private theorem feeA_160_192 : binChunk extraA 160 32 = 0 := by decide +kernel
private theorem feeA_192_224 : binChunk extraA 192 32 = 0 := by decide +kernel
private theorem feeA_224_256 : binChunk extraA 224 32 = 183064 := by decide +kernel
private theorem feeA_256_288 : binChunk extraA 256 32 = 3584940 := by decide +kernel
private theorem feeA_288_320 : binChunk extraA 288 32 = 20336160 := by decide +kernel
private theorem feeA_320_352 : binChunk extraA 320 32 = 68630628 := by decide +kernel
private theorem feeA_352_384 : binChunk extraA 352 32 = 174737644 := by decide +kernel
private theorem feeA_384_416 : binChunk extraA 384 32 = 373016816 := by decide +kernel
private theorem feeA_416_448 : binChunk extraA 416 32 = 705888852 := by decide +kernel
private theorem feeA_448_480 : binChunk extraA 448 32 = 1223853612 := by decide +kernel
private theorem feeA_480_512 : binChunk extraA 480 32 = 1985271847 := by decide +kernel
private theorem feeA_512_544 : binChunk extraA 512 32 = 3037975746 := by decide +kernel
private theorem feeA_544_576 : binChunk extraA 544 32 = 4337988607 := by decide +kernel
private theorem feeA_576_608 : binChunk extraA 576 32 = 5716253542 := by decide +kernel
private theorem feeA_608_640 : binChunk extraA 608 32 = 7176088878 := by decide +kernel
private theorem feeA_640_672 : binChunk extraA 640 32 = 8815385556 := by decide +kernel
private theorem feeA_672_704 : binChunk extraA 672 32 = 10636534062 := by decide +kernel
private theorem feeA_704_736 : binChunk extraA 704 32 = 12639501102 := by decide +kernel
private theorem feeA_736_768 : binChunk extraA 736 32 = 14824286676 := by decide +kernel
private theorem feeA_768_800 : binChunk extraA 768 32 = 17190924078 := by decide +kernel
private theorem feeA_800_832 : binChunk extraA 800 32 = 19739380014 := by decide +kernel
private theorem feeA_832_864 : binChunk extraA 832 32 = 22469654484 := by decide +kernel
private theorem feeA_864_896 : binChunk extraA 864 32 = 25381780782 := by decide +kernel
private theorem feeA_896_928 : binChunk extraA 896 32 = 28540182798 := by decide +kernel
private theorem feeA_928_960 : binChunk extraA 928 32 = 32677286646 := by decide +kernel
private theorem feeA_960_992 : binChunk extraA 960 32 = 38806216216 := by decide +kernel
private theorem feeA_992_1024 : binChunk extraA 992 32 = 47398517294 := by decide +kernel
private theorem feeA_1024_1056 : binChunk extraA 1024 32 = 58102738058 := by decide +kernel
private theorem feeA_1056_1088 : binChunk extraA 1056 32 = 69961867896 := by decide +kernel
private theorem feeA_1088_1120 : binChunk extraA 1088 32 = 82190755886 := by decide +kernel
private theorem feeA_1120_1152 : binChunk extraA 1120 32 = 94732970846 := by decide +kernel
private theorem feeA_1152_1184 : binChunk extraA 1152 32 = 109054770512 := by decide +kernel
private theorem feeA_1184_1216 : binChunk extraA 1184 32 = 123659209388 := by decide +kernel
private theorem feeA_1216_1248 : binChunk extraA 1216 32 = 134590488788 := by decide +kernel
private theorem feeA_1248_1280 : binChunk extraA 1248 32 = 142409449006 := by decide +kernel
private theorem feeA_1280_1312 : binChunk extraA 1280 32 = 149706371118 := by decide +kernel
private theorem feeA_1312_1344 : binChunk extraA 1312 32 = 157175580372 := by decide +kernel
private theorem feeA_1344_1376 : binChunk extraA 1344 32 = 164826641454 := by decide +kernel
private theorem feeA_1376_1408 : binChunk extraA 1376 32 = 172659521070 := by decide +kernel
private theorem feeA_1408_1440 : binChunk extraA 1408 32 = 180674219220 := by decide +kernel
private theorem feeA_1440_1472 : binChunk extraA 1440 32 = 188870769198 := by decide +kernel
private theorem feeA_1472_1504 : binChunk extraA 1472 32 = 197249137710 := by decide +kernel
private theorem feeA_1504_1536 : binChunk extraA 1504 32 = 205809324756 := by decide +kernel
private theorem feeA_1536_1568 : binChunk extraA 1536 32 = 214551363630 := by decide +kernel
private theorem feeA_1568_1600 : binChunk extraA 1568 32 = 223475221038 := by decide +kernel
private theorem feeA_1600_1632 : binChunk extraA 1600 32 = 232580896980 := by decide +kernel
private theorem feeA_1632_1651 : binChunk extraA 1632 19 = 142477611132 := by decide +kernel
private theorem feeA_32_96 : binChunk extraA 32 64 = 0 := binChunk_join (w := extraA) (start := 32) (left := 32) (right := 32) feeA_32_64 feeA_64_96
private theorem feeA_0_96 : binChunk extraA 0 96 = 0 := binChunk_join (w := extraA) (start := 0) (left := 32) (right := 64) feeA_0_32 feeA_32_96
private theorem feeA_128_192 : binChunk extraA 128 64 = 0 := binChunk_join (w := extraA) (start := 128) (left := 32) (right := 32) feeA_128_160 feeA_160_192
private theorem feeA_96_192 : binChunk extraA 96 96 = 0 := binChunk_join (w := extraA) (start := 96) (left := 32) (right := 64) feeA_96_128 feeA_128_192
private theorem feeA_0_192 : binChunk extraA 0 192 = 0 := binChunk_join (w := extraA) (start := 0) (left := 96) (right := 96) feeA_0_96 feeA_96_192
private theorem feeA_224_288 : binChunk extraA 224 64 = 3768004 := binChunk_join (w := extraA) (start := 224) (left := 32) (right := 32) feeA_224_256 feeA_256_288
private theorem feeA_192_288 : binChunk extraA 192 96 = 3768004 := binChunk_join (w := extraA) (start := 192) (left := 32) (right := 64) feeA_192_224 feeA_224_288
private theorem feeA_288_352 : binChunk extraA 288 64 = 88966788 := binChunk_join (w := extraA) (start := 288) (left := 32) (right := 32) feeA_288_320 feeA_320_352
private theorem feeA_352_416 : binChunk extraA 352 64 = 547754460 := binChunk_join (w := extraA) (start := 352) (left := 32) (right := 32) feeA_352_384 feeA_384_416
private theorem feeA_288_416 : binChunk extraA 288 128 = 636721248 := binChunk_join (w := extraA) (start := 288) (left := 64) (right := 64) feeA_288_352 feeA_352_416
private theorem feeA_192_416 : binChunk extraA 192 224 = 640489252 := binChunk_join (w := extraA) (start := 192) (left := 96) (right := 128) feeA_192_288 feeA_288_416
private theorem feeA_0_416 : binChunk extraA 0 416 = 640489252 := binChunk_join (w := extraA) (start := 0) (left := 192) (right := 224) feeA_0_192 feeA_192_416
private theorem feeA_448_512 : binChunk extraA 448 64 = 3209125459 := binChunk_join (w := extraA) (start := 448) (left := 32) (right := 32) feeA_448_480 feeA_480_512
private theorem feeA_416_512 : binChunk extraA 416 96 = 3915014311 := binChunk_join (w := extraA) (start := 416) (left := 32) (right := 64) feeA_416_448 feeA_448_512
private theorem feeA_544_608 : binChunk extraA 544 64 = 10054242149 := binChunk_join (w := extraA) (start := 544) (left := 32) (right := 32) feeA_544_576 feeA_576_608
private theorem feeA_512_608 : binChunk extraA 512 96 = 13092217895 := binChunk_join (w := extraA) (start := 512) (left := 32) (right := 64) feeA_512_544 feeA_544_608
private theorem feeA_416_608 : binChunk extraA 416 192 = 17007232206 := binChunk_join (w := extraA) (start := 416) (left := 96) (right := 96) feeA_416_512 feeA_512_608
private theorem feeA_640_704 : binChunk extraA 640 64 = 19451919618 := binChunk_join (w := extraA) (start := 640) (left := 32) (right := 32) feeA_640_672 feeA_672_704
private theorem feeA_608_704 : binChunk extraA 608 96 = 26628008496 := binChunk_join (w := extraA) (start := 608) (left := 32) (right := 64) feeA_608_640 feeA_640_704
private theorem feeA_704_768 : binChunk extraA 704 64 = 27463787778 := binChunk_join (w := extraA) (start := 704) (left := 32) (right := 32) feeA_704_736 feeA_736_768
private theorem feeA_768_832 : binChunk extraA 768 64 = 36930304092 := binChunk_join (w := extraA) (start := 768) (left := 32) (right := 32) feeA_768_800 feeA_800_832
private theorem feeA_704_832 : binChunk extraA 704 128 = 64394091870 := binChunk_join (w := extraA) (start := 704) (left := 64) (right := 64) feeA_704_768 feeA_768_832
private theorem feeA_608_832 : binChunk extraA 608 224 = 91022100366 := binChunk_join (w := extraA) (start := 608) (left := 96) (right := 128) feeA_608_704 feeA_704_832
private theorem feeA_416_832 : binChunk extraA 416 416 = 108029332572 := binChunk_join (w := extraA) (start := 416) (left := 192) (right := 224) feeA_416_608 feeA_608_832
private theorem feeA_0_832 : binChunk extraA 0 832 = 108669821824 := binChunk_join (w := extraA) (start := 0) (left := 416) (right := 416) feeA_0_416 feeA_416_832
private theorem feeA_864_928 : binChunk extraA 864 64 = 53921963580 := binChunk_join (w := extraA) (start := 864) (left := 32) (right := 32) feeA_864_896 feeA_896_928
private theorem feeA_832_928 : binChunk extraA 832 96 = 76391618064 := binChunk_join (w := extraA) (start := 832) (left := 32) (right := 64) feeA_832_864 feeA_864_928
private theorem feeA_960_1024 : binChunk extraA 960 64 = 86204733510 := binChunk_join (w := extraA) (start := 960) (left := 32) (right := 32) feeA_960_992 feeA_992_1024
private theorem feeA_928_1024 : binChunk extraA 928 96 = 118882020156 := binChunk_join (w := extraA) (start := 928) (left := 32) (right := 64) feeA_928_960 feeA_960_1024
private theorem feeA_832_1024 : binChunk extraA 832 192 = 195273638220 := binChunk_join (w := extraA) (start := 832) (left := 96) (right := 96) feeA_832_928 feeA_928_1024
private theorem feeA_1056_1120 : binChunk extraA 1056 64 = 152152623782 := binChunk_join (w := extraA) (start := 1056) (left := 32) (right := 32) feeA_1056_1088 feeA_1088_1120
private theorem feeA_1024_1120 : binChunk extraA 1024 96 = 210255361840 := binChunk_join (w := extraA) (start := 1024) (left := 32) (right := 64) feeA_1024_1056 feeA_1056_1120
private theorem feeA_1120_1184 : binChunk extraA 1120 64 = 203787741358 := binChunk_join (w := extraA) (start := 1120) (left := 32) (right := 32) feeA_1120_1152 feeA_1152_1184
private theorem feeA_1184_1248 : binChunk extraA 1184 64 = 258249698176 := binChunk_join (w := extraA) (start := 1184) (left := 32) (right := 32) feeA_1184_1216 feeA_1216_1248
private theorem feeA_1120_1248 : binChunk extraA 1120 128 = 462037439534 := binChunk_join (w := extraA) (start := 1120) (left := 64) (right := 64) feeA_1120_1184 feeA_1184_1248
private theorem feeA_1024_1248 : binChunk extraA 1024 224 = 672292801374 := binChunk_join (w := extraA) (start := 1024) (left := 96) (right := 128) feeA_1024_1120 feeA_1120_1248
private theorem feeA_832_1248 : binChunk extraA 832 416 = 867566439594 := binChunk_join (w := extraA) (start := 832) (left := 192) (right := 224) feeA_832_1024 feeA_1024_1248
private theorem feeA_1280_1344 : binChunk extraA 1280 64 = 306881951490 := binChunk_join (w := extraA) (start := 1280) (left := 32) (right := 32) feeA_1280_1312 feeA_1312_1344
private theorem feeA_1248_1344 : binChunk extraA 1248 96 = 449291400496 := binChunk_join (w := extraA) (start := 1248) (left := 32) (right := 64) feeA_1248_1280 feeA_1280_1344
private theorem feeA_1376_1440 : binChunk extraA 1376 64 = 353333740290 := binChunk_join (w := extraA) (start := 1376) (left := 32) (right := 32) feeA_1376_1408 feeA_1408_1440
private theorem feeA_1344_1440 : binChunk extraA 1344 96 = 518160381744 := binChunk_join (w := extraA) (start := 1344) (left := 32) (right := 64) feeA_1344_1376 feeA_1376_1440
private theorem feeA_1248_1440 : binChunk extraA 1248 192 = 967451782240 := binChunk_join (w := extraA) (start := 1248) (left := 96) (right := 96) feeA_1248_1344 feeA_1344_1440
private theorem feeA_1472_1536 : binChunk extraA 1472 64 = 403058462466 := binChunk_join (w := extraA) (start := 1472) (left := 32) (right := 32) feeA_1472_1504 feeA_1504_1536
private theorem feeA_1440_1536 : binChunk extraA 1440 96 = 591929231664 := binChunk_join (w := extraA) (start := 1440) (left := 32) (right := 64) feeA_1440_1472 feeA_1472_1536
private theorem feeA_1536_1600 : binChunk extraA 1536 64 = 438026584668 := binChunk_join (w := extraA) (start := 1536) (left := 32) (right := 32) feeA_1536_1568 feeA_1568_1600
private theorem feeA_1600_1651 : binChunk extraA 1600 51 = 375058508112 := binChunk_join (w := extraA) (start := 1600) (left := 32) (right := 19) feeA_1600_1632 feeA_1632_1651
private theorem feeA_1536_1651 : binChunk extraA 1536 115 = 813085092780 := binChunk_join (w := extraA) (start := 1536) (left := 64) (right := 51) feeA_1536_1600 feeA_1600_1651
private theorem feeA_1440_1651 : binChunk extraA 1440 211 = 1405014324444 := binChunk_join (w := extraA) (start := 1440) (left := 96) (right := 115) feeA_1440_1536 feeA_1536_1651
private theorem feeA_1248_1651 : binChunk extraA 1248 403 = 2372466106684 := binChunk_join (w := extraA) (start := 1248) (left := 192) (right := 211) feeA_1248_1440 feeA_1440_1651
private theorem feeA_832_1651 : binChunk extraA 832 819 = 3240032546278 := binChunk_join (w := extraA) (start := 832) (left := 416) (right := 403) feeA_832_1248 feeA_1248_1651
private theorem feeA_0_1651 : binChunk extraA 0 1651 = 3348702368102 := binChunk_join (w := extraA) (start := 0) (left := 832) (right := 819) feeA_0_832 feeA_832_1651

private theorem rawA_1064 : RawReceipt.rawChunk extraA 1064 64 = 219621489142 :=
  (RawClosed.rawChunk_closed extraA 1064 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1128 : RawReceipt.rawChunk extraA 1128 64 = 561160289650 :=
  (RawClosed.rawChunk_closed extraA 1128 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1192 : RawReceipt.rawChunk extraA 1192 64 = 599110936320 :=
  (RawClosed.rawChunk_closed extraA 1192 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1256 : RawReceipt.rawChunk extraA 1256 64 = 599110936320 :=
  (RawClosed.rawChunk_closed extraA 1256 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1320 : RawReceipt.rawChunk extraA 1320 64 = 599110936320 :=
  (RawClosed.rawChunk_closed extraA 1320 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1384 : RawReceipt.rawChunk extraA 1384 64 = 561148976777 :=
  (RawClosed.rawChunk_closed extraA 1384 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1448 : RawReceipt.rawChunk extraA 1448 64 = 211737665971 :=
  (RawClosed.rawChunk_closed extraA 1448 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawA_1512 : RawReceipt.rawChunk extraA 1512 2 = 275569540 :=
  (RawClosed.rawChunk_closed extraA 1512 2 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

theorem rawA : rawWindow extraA = 3351276800040 := by
  rw [raw_eq_compute extraA (by decide) (by decide), RawReceipt.rawCompute_eq]
  have part1064_128 := RawReceipt.joinRaw (start := 1064) (a := 64) (b := 64) rawA_1064 rawA_1128
  have part1192_128 := RawReceipt.joinRaw (start := 1192) (a := 64) (b := 64) rawA_1192 rawA_1256
  have part1064_256 := RawReceipt.joinRaw (start := 1064) (a := 128) (b := 128) part1064_128 part1192_128
  have part1320_128 := RawReceipt.joinRaw (start := 1320) (a := 64) (b := 64) rawA_1320 rawA_1384
  have part1448_66 := RawReceipt.joinRaw (start := 1448) (a := 64) (b := 2) rawA_1448 rawA_1512
  have part1320_194 := RawReceipt.joinRaw (start := 1320) (a := 128) (b := 66) part1320_128 part1448_66
  have part1064_450 := RawReceipt.joinRaw (start := 1064) (a := 256) (b := 194) part1064_256 part1320_194
  have active := part1064_450
  have beforeRange := RawReceipt.rawChunk_zero extraA 0 1064 (Or.inl (by decide))
  have afterRange := RawReceipt.rawChunk_zero extraA 1514 137 (Or.inr (by decide))
  have rest := RawReceipt.joinRaw (start := 1064) (a := 450) (b := 137) active afterRange
  exact RawReceipt.joinRaw (start := 0) (a := 1064) (b := 587) beforeRange rest

theorem binA : binCompute extraA = 3348702368102 :=
  (binCompute_eq_chunk extraA 0 (by decide) (by decide)).trans feeA_0_1651

#print axioms rawA
#print axioms binA
end KoalaTaperExtra

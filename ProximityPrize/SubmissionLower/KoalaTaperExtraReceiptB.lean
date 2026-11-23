import ProximityPrize.SubmissionLower.KoalaTaperExtraWindows
import ProximityPrize.SubmissionLower.KoalaTaperExtraRawClip

set_option Elab.async false
set_option autoImplicit false

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace KoalaTaperExtra
open K1_13_2_3 Low48PrimaryPivot

private theorem feeB_0_32 : binChunk extraB 0 32 = 0 := by decide +kernel
private theorem feeB_32_64 : binChunk extraB 32 32 = 0 := by decide +kernel
private theorem feeB_64_96 : binChunk extraB 64 32 = 0 := by decide +kernel
private theorem feeB_96_128 : binChunk extraB 96 32 = 0 := by decide +kernel
private theorem feeB_128_160 : binChunk extraB 128 32 = 0 := by decide +kernel
private theorem feeB_160_192 : binChunk extraB 160 32 = 0 := by decide +kernel
private theorem feeB_192_224 : binChunk extraB 192 32 = 0 := by decide +kernel
private theorem feeB_224_256 : binChunk extraB 224 32 = 0 := by decide +kernel
private theorem feeB_256_288 : binChunk extraB 256 32 = 0 := by decide +kernel
private theorem feeB_288_320 : binChunk extraB 288 32 = 0 := by decide +kernel
private theorem feeB_320_352 : binChunk extraB 320 32 = 0 := by decide +kernel
private theorem feeB_352_384 : binChunk extraB 352 32 = 0 := by decide +kernel
private theorem feeB_384_416 : binChunk extraB 384 32 = 0 := by decide +kernel
private theorem feeB_416_448 : binChunk extraB 416 32 = 0 := by decide +kernel
private theorem feeB_448_480 : binChunk extraB 448 32 = 0 := by decide +kernel
private theorem feeB_480_512 : binChunk extraB 480 32 = 90901 := by decide +kernel
private theorem feeB_512_544 : binChunk extraB 512 32 = 13196248 := by decide +kernel
private theorem feeB_544_576 : binChunk extraB 544 32 = 139943089 := by decide +kernel
private theorem feeB_576_608 : binChunk extraB 576 32 = 496652212 := by decide +kernel
private theorem feeB_608_640 : binChunk extraB 608 32 = 721129750 := by decide +kernel
private theorem feeB_640_672 : binChunk extraB 640 32 = 959868500 := by decide +kernel
private theorem feeB_672_704 : binChunk extraB 672 32 = 1240937750 := by decide +kernel
private theorem feeB_704_736 : binChunk extraB 704 32 = 1564329750 := by decide +kernel
private theorem feeB_736_768 : binChunk extraB 736 32 = 1930044500 := by decide +kernel
private theorem feeB_768_800 : binChunk extraB 768 32 = 2338089750 := by decide +kernel
private theorem feeB_800_832 : binChunk extraB 800 32 = 2788457750 := by decide +kernel
private theorem feeB_832_864 : binChunk extraB 832 32 = 3281148500 := by decide +kernel
private theorem feeB_864_896 : binChunk extraB 864 32 = 3816169750 := by decide +kernel
private theorem feeB_896_928 : binChunk extraB 896 32 = 4394765902 := by decide +kernel
private theorem feeB_928_960 : binChunk extraB 928 32 = 5049522956 := by decide +kernel
private theorem feeB_960_992 : binChunk extraB 960 32 = 5907310110 := by decide +kernel
private theorem feeB_992_1024 : binChunk extraB 992 32 = 7184421122 := by decide +kernel
private theorem feeB_1024_1056 : binChunk extraB 1024 32 = 9134623731 := by decide +kernel
private theorem feeB_1056_1088 : binChunk extraB 1056 32 = 11776140166 := by decide +kernel
private theorem feeB_1088_1120 : binChunk extraB 1088 32 = 14887215006 := by decide +kernel
private theorem feeB_1120_1152 : binChunk extraB 1120 32 = 18201333547 := by decide +kernel
private theorem feeB_1152_1184 : binChunk extraB 1152 32 = 21795295000 := by decide +kernel
private theorem feeB_1184_1216 : binChunk extraB 1184 32 = 26029553290 := by decide +kernel
private theorem feeB_1216_1248 : binChunk extraB 1216 32 = 30104604155 := by decide +kernel
private theorem feeB_1248_1280 : binChunk extraB 1248 32 = 32937582670 := by decide +kernel
private theorem feeB_1280_1312 : binChunk extraB 1280 32 = 34845341818 := by decide +kernel
private theorem feeB_1312_1344 : binChunk extraB 1312 32 = 36586494500 := by decide +kernel
private theorem feeB_1344_1376 : binChunk extraB 1344 32 = 38367467750 := by decide +kernel
private theorem feeB_1376_1408 : binChunk extraB 1376 32 = 40190763750 := by decide +kernel
private theorem feeB_1408_1440 : binChunk extraB 1408 32 = 42056382500 := by decide +kernel
private theorem feeB_1440_1472 : binChunk extraB 1440 32 = 43964331750 := by decide +kernel
private theorem feeB_1472_1504 : binChunk extraB 1472 32 = 45914603750 := by decide +kernel
private theorem feeB_1504_1536 : binChunk extraB 1504 32 = 47907198500 := by decide +kernel
private theorem feeB_1536_1568 : binChunk extraB 1536 32 = 49942123750 := by decide +kernel
private theorem feeB_1568_1600 : binChunk extraB 1568 32 = 52019371750 := by decide +kernel
private theorem feeB_1600_1632 : binChunk extraB 1600 32 = 54138942500 := by decide +kernel
private theorem feeB_1632_1651 : binChunk extraB 1632 19 = 33165179500 := by decide +kernel
private theorem feeB_32_96 : binChunk extraB 32 64 = 0 := binChunk_join (w := extraB) (start := 32) (left := 32) (right := 32) feeB_32_64 feeB_64_96
private theorem feeB_0_96 : binChunk extraB 0 96 = 0 := binChunk_join (w := extraB) (start := 0) (left := 32) (right := 64) feeB_0_32 feeB_32_96
private theorem feeB_128_192 : binChunk extraB 128 64 = 0 := binChunk_join (w := extraB) (start := 128) (left := 32) (right := 32) feeB_128_160 feeB_160_192
private theorem feeB_96_192 : binChunk extraB 96 96 = 0 := binChunk_join (w := extraB) (start := 96) (left := 32) (right := 64) feeB_96_128 feeB_128_192
private theorem feeB_0_192 : binChunk extraB 0 192 = 0 := binChunk_join (w := extraB) (start := 0) (left := 96) (right := 96) feeB_0_96 feeB_96_192
private theorem feeB_224_288 : binChunk extraB 224 64 = 0 := binChunk_join (w := extraB) (start := 224) (left := 32) (right := 32) feeB_224_256 feeB_256_288
private theorem feeB_192_288 : binChunk extraB 192 96 = 0 := binChunk_join (w := extraB) (start := 192) (left := 32) (right := 64) feeB_192_224 feeB_224_288
private theorem feeB_288_352 : binChunk extraB 288 64 = 0 := binChunk_join (w := extraB) (start := 288) (left := 32) (right := 32) feeB_288_320 feeB_320_352
private theorem feeB_352_416 : binChunk extraB 352 64 = 0 := binChunk_join (w := extraB) (start := 352) (left := 32) (right := 32) feeB_352_384 feeB_384_416
private theorem feeB_288_416 : binChunk extraB 288 128 = 0 := binChunk_join (w := extraB) (start := 288) (left := 64) (right := 64) feeB_288_352 feeB_352_416
private theorem feeB_192_416 : binChunk extraB 192 224 = 0 := binChunk_join (w := extraB) (start := 192) (left := 96) (right := 128) feeB_192_288 feeB_288_416
private theorem feeB_0_416 : binChunk extraB 0 416 = 0 := binChunk_join (w := extraB) (start := 0) (left := 192) (right := 224) feeB_0_192 feeB_192_416
private theorem feeB_448_512 : binChunk extraB 448 64 = 90901 := binChunk_join (w := extraB) (start := 448) (left := 32) (right := 32) feeB_448_480 feeB_480_512
private theorem feeB_416_512 : binChunk extraB 416 96 = 90901 := binChunk_join (w := extraB) (start := 416) (left := 32) (right := 64) feeB_416_448 feeB_448_512
private theorem feeB_544_608 : binChunk extraB 544 64 = 636595301 := binChunk_join (w := extraB) (start := 544) (left := 32) (right := 32) feeB_544_576 feeB_576_608
private theorem feeB_512_608 : binChunk extraB 512 96 = 649791549 := binChunk_join (w := extraB) (start := 512) (left := 32) (right := 64) feeB_512_544 feeB_544_608
private theorem feeB_416_608 : binChunk extraB 416 192 = 649882450 := binChunk_join (w := extraB) (start := 416) (left := 96) (right := 96) feeB_416_512 feeB_512_608
private theorem feeB_640_704 : binChunk extraB 640 64 = 2200806250 := binChunk_join (w := extraB) (start := 640) (left := 32) (right := 32) feeB_640_672 feeB_672_704
private theorem feeB_608_704 : binChunk extraB 608 96 = 2921936000 := binChunk_join (w := extraB) (start := 608) (left := 32) (right := 64) feeB_608_640 feeB_640_704
private theorem feeB_704_768 : binChunk extraB 704 64 = 3494374250 := binChunk_join (w := extraB) (start := 704) (left := 32) (right := 32) feeB_704_736 feeB_736_768
private theorem feeB_768_832 : binChunk extraB 768 64 = 5126547500 := binChunk_join (w := extraB) (start := 768) (left := 32) (right := 32) feeB_768_800 feeB_800_832
private theorem feeB_704_832 : binChunk extraB 704 128 = 8620921750 := binChunk_join (w := extraB) (start := 704) (left := 64) (right := 64) feeB_704_768 feeB_768_832
private theorem feeB_608_832 : binChunk extraB 608 224 = 11542857750 := binChunk_join (w := extraB) (start := 608) (left := 96) (right := 128) feeB_608_704 feeB_704_832
private theorem feeB_416_832 : binChunk extraB 416 416 = 12192740200 := binChunk_join (w := extraB) (start := 416) (left := 192) (right := 224) feeB_416_608 feeB_608_832
private theorem feeB_0_832 : binChunk extraB 0 832 = 12192740200 := binChunk_join (w := extraB) (start := 0) (left := 416) (right := 416) feeB_0_416 feeB_416_832
private theorem feeB_864_928 : binChunk extraB 864 64 = 8210935652 := binChunk_join (w := extraB) (start := 864) (left := 32) (right := 32) feeB_864_896 feeB_896_928
private theorem feeB_832_928 : binChunk extraB 832 96 = 11492084152 := binChunk_join (w := extraB) (start := 832) (left := 32) (right := 64) feeB_832_864 feeB_864_928
private theorem feeB_960_1024 : binChunk extraB 960 64 = 13091731232 := binChunk_join (w := extraB) (start := 960) (left := 32) (right := 32) feeB_960_992 feeB_992_1024
private theorem feeB_928_1024 : binChunk extraB 928 96 = 18141254188 := binChunk_join (w := extraB) (start := 928) (left := 32) (right := 64) feeB_928_960 feeB_960_1024
private theorem feeB_832_1024 : binChunk extraB 832 192 = 29633338340 := binChunk_join (w := extraB) (start := 832) (left := 96) (right := 96) feeB_832_928 feeB_928_1024
private theorem feeB_1056_1120 : binChunk extraB 1056 64 = 26663355172 := binChunk_join (w := extraB) (start := 1056) (left := 32) (right := 32) feeB_1056_1088 feeB_1088_1120
private theorem feeB_1024_1120 : binChunk extraB 1024 96 = 35797978903 := binChunk_join (w := extraB) (start := 1024) (left := 32) (right := 64) feeB_1024_1056 feeB_1056_1120
private theorem feeB_1120_1184 : binChunk extraB 1120 64 = 39996628547 := binChunk_join (w := extraB) (start := 1120) (left := 32) (right := 32) feeB_1120_1152 feeB_1152_1184
private theorem feeB_1184_1248 : binChunk extraB 1184 64 = 56134157445 := binChunk_join (w := extraB) (start := 1184) (left := 32) (right := 32) feeB_1184_1216 feeB_1216_1248
private theorem feeB_1120_1248 : binChunk extraB 1120 128 = 96130785992 := binChunk_join (w := extraB) (start := 1120) (left := 64) (right := 64) feeB_1120_1184 feeB_1184_1248
private theorem feeB_1024_1248 : binChunk extraB 1024 224 = 131928764895 := binChunk_join (w := extraB) (start := 1024) (left := 96) (right := 128) feeB_1024_1120 feeB_1120_1248
private theorem feeB_832_1248 : binChunk extraB 832 416 = 161562103235 := binChunk_join (w := extraB) (start := 832) (left := 192) (right := 224) feeB_832_1024 feeB_1024_1248
private theorem feeB_1280_1344 : binChunk extraB 1280 64 = 71431836318 := binChunk_join (w := extraB) (start := 1280) (left := 32) (right := 32) feeB_1280_1312 feeB_1312_1344
private theorem feeB_1248_1344 : binChunk extraB 1248 96 = 104369418988 := binChunk_join (w := extraB) (start := 1248) (left := 32) (right := 64) feeB_1248_1280 feeB_1280_1344
private theorem feeB_1376_1440 : binChunk extraB 1376 64 = 82247146250 := binChunk_join (w := extraB) (start := 1376) (left := 32) (right := 32) feeB_1376_1408 feeB_1408_1440
private theorem feeB_1344_1440 : binChunk extraB 1344 96 = 120614614000 := binChunk_join (w := extraB) (start := 1344) (left := 32) (right := 64) feeB_1344_1376 feeB_1376_1440
private theorem feeB_1248_1440 : binChunk extraB 1248 192 = 224984032988 := binChunk_join (w := extraB) (start := 1248) (left := 96) (right := 96) feeB_1248_1344 feeB_1344_1440
private theorem feeB_1472_1536 : binChunk extraB 1472 64 = 93821802250 := binChunk_join (w := extraB) (start := 1472) (left := 32) (right := 32) feeB_1472_1504 feeB_1504_1536
private theorem feeB_1440_1536 : binChunk extraB 1440 96 = 137786134000 := binChunk_join (w := extraB) (start := 1440) (left := 32) (right := 64) feeB_1440_1472 feeB_1472_1536
private theorem feeB_1536_1600 : binChunk extraB 1536 64 = 101961495500 := binChunk_join (w := extraB) (start := 1536) (left := 32) (right := 32) feeB_1536_1568 feeB_1568_1600
private theorem feeB_1600_1651 : binChunk extraB 1600 51 = 87304122000 := binChunk_join (w := extraB) (start := 1600) (left := 32) (right := 19) feeB_1600_1632 feeB_1632_1651
private theorem feeB_1536_1651 : binChunk extraB 1536 115 = 189265617500 := binChunk_join (w := extraB) (start := 1536) (left := 64) (right := 51) feeB_1536_1600 feeB_1600_1651
private theorem feeB_1440_1651 : binChunk extraB 1440 211 = 327051751500 := binChunk_join (w := extraB) (start := 1440) (left := 96) (right := 115) feeB_1440_1536 feeB_1536_1651
private theorem feeB_1248_1651 : binChunk extraB 1248 403 = 552035784488 := binChunk_join (w := extraB) (start := 1248) (left := 192) (right := 211) feeB_1248_1440 feeB_1440_1651
private theorem feeB_832_1651 : binChunk extraB 832 819 = 713597887723 := binChunk_join (w := extraB) (start := 832) (left := 416) (right := 403) feeB_832_1248 feeB_1248_1651
private theorem feeB_0_1651 : binChunk extraB 0 1651 = 725790627923 := binChunk_join (w := extraB) (start := 0) (left := 832) (right := 819) feeB_0_832 feeB_832_1651

private theorem rawB_1063 : RawReceipt.rawChunk extraB 1063 64 = 562446797443 :=
  (RawClosed.rawChunk_closed extraB 1063 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawB_1127 : RawReceipt.rawChunk extraB 1127 60 = 164225064287 :=
  (RawClosed.rawChunk_closed extraB 1127 60 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

theorem rawB : rawWindow extraB = 726671861730 := by
  rw [raw_eq_compute extraB (by decide) (by decide), RawReceipt.rawCompute_eq]
  have part1063_124 := RawReceipt.joinRaw (start := 1063) (a := 64) (b := 60) rawB_1063 rawB_1127
  have active := part1063_124
  have afterRange := RawReceipt.rawChunk_zero extraB 1187 464 (Or.inr (by decide))
  exact RawReceipt.joinRaw (start := 1063) (a := 124) (b := 464) active afterRange

theorem binB : binCompute extraB = 725790627923 :=
  (binCompute_eq_chunk extraB 0 (by decide) (by decide)).trans feeB_0_1651

#print axioms rawB
#print axioms binB
end KoalaTaperExtra

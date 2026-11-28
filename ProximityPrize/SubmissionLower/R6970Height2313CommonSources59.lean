import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_adf41cb1614b9a70
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_adf41cb1614b9a70
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_fa0707633ba569a9
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks41
import ProximityPrize.SubmissionLower.Bundle6970_6ed322075960e0ab
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks64
import ProximityPrize.SubmissionLower.Bundle6970_ceea66e6500ee0de
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks77
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks78
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0591

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src94 : Request := ⟨⟨⟨1205,1671,377,35029⟩,54193713315840,221664578344⟩,115,2,1,257319,513⟩

theorem rank94 : P3_7_1.BankOK src94.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1671_377 35029

theorem width94 : Lower6960.HelperSource.WidthGuard src94.bank 179730 2308 src94.reserve := requestWidth (by decide)

def ends94 : List ℕ := [2308, 2309, 2313]

theorem inside94 : Research6966.TerminalBanks.inside src94.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover94 : Cover (Triangular src94) 2313 2308 ends94 := triangleCover (by decide +kernel)

def src940 : Request := ⟨⟨⟨2987,4160,900,195527⟩,800354147500032,8216917752362⟩,44,3,1,386273,26⟩

theorem rank940 : P3_7_1.BankOK src940.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2987_4160_900 195527

theorem width940 : Lower6960.HelperSource.WidthGuard src940.bank 179730 2308 src940.reserve := requestWidth (by decide)

def ends940 : List ℕ := [2308, 2309, 2313]

theorem inside940 : Research6966.TerminalBanks.inside src940.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover940 : Cover (Triangular src940) 2313 2308 ends940 := triangleCover (by decide +kernel)

def src941 : Request := ⟨⟨⟨4824,6697,1478,81858⟩,3412388399022080,56009326793616⟩,65,3,1,385979,26⟩

theorem rank941 : P3_7_1.BankOK src941.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4824_6697_1478 81858

theorem width941 : Lower6960.HelperSource.WidthGuard src941.bank 179730 2308 src941.reserve := requestWidth (by decide)

def ends941 : List ℕ := [2308, 2309, 2313]




theorem cover941 : Cover (Triangular src941) 2313 2308 ends941 := triangleCover (by decide +kernel)

def src942 : Request := ⟨⟨⟨8505,11810,2598,496657⟩,18650290068914176,540020413005418⟩,145,3,1,386273,26⟩

theorem rank942 : P3_7_1.BankOK src942.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8505_11810_2598 496657

theorem width942 : Lower6960.HelperSource.WidthGuard src942.bank 179730 2308 src942.reserve := requestWidth (by decide)

def ends942 : List ℕ := [2308, 2309, 2313]




theorem cover942 : Cover (Triangular src942) 2313 2308 ends942 := triangleCover (by decide +kernel)

def src943 : Request := ⟨⟨⟨10049,13952,3078,166043⟩,30824208543252480,1054088797470548⟩,145,3,1,385979,26⟩

theorem rank943 : P3_7_1.BankOK src943.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10049_13952_3078 166043

theorem width943 : Lower6960.HelperSource.WidthGuard src943.bank 179730 2308 src943.reserve := requestWidth (by decide)

def ends943 : List ℕ := [2308, 2309, 2313]




theorem cover943 : Cover (Triangular src943) 2313 2308 ends943 := triangleCover (by decide +kernel)

def src944 : Request := ⟨⟨⟨692,963,212,9763⟩,10131154665472,24078187611⟩,0,3,1,385979,27⟩

theorem rank944 : P3_7_1.BankOK src944.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_963_212 9763

theorem width944 : Lower6960.HelperSource.WidthGuard src944.bank 179730 2308 src944.reserve := requestWidth (by decide)

def ends944 : List ℕ := [2308, 2313]

theorem inside944 : Research6966.TerminalBanks.inside src944.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover944 : Cover (Triangular src944) 2313 2308 ends944 := triangleCover (by decide +kernel)

def src945 : Request := ⟨⟨⟨825,1147,248,10915⟩,16903818182656,47719374748⟩,1,3,1,385979,27⟩

theorem rank945 : P3_7_1.BankOK src945.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_825_1147_248 10915

theorem width945 : Lower6960.HelperSource.WidthGuard src945.bank 179730 2308 src945.reserve := requestWidth (by decide)

def ends945 : List ℕ := [2308, 2309, 2313]

theorem inside945 : Research6966.TerminalBanks.inside src945.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover945 : Cover (Triangular src945) 2313 2308 ends945 := triangleCover (by decide +kernel)

def src946 : Request := ⟨⟨⟨822,1143,248,12199⟩,16766743085056,47186356218⟩,2,3,1,385979,27⟩

theorem rank946 : P3_7_1.BankOK src946.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_822_1143_248 12199

theorem width946 : Lower6960.HelperSource.WidthGuard src946.bank 179730 2308 src946.reserve := requestWidth (by decide)

def ends946 : List ℕ := [2308, 2309, 2313]

theorem inside946 : Research6966.TerminalBanks.inside src946.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover946 : Cover (Triangular src946) 2313 2308 ends946 := triangleCover (by decide +kernel)

def src947 : Request := ⟨⟨⟨1000,1387,301,13822⟩,30103476895744,102197851203⟩,4,3,1,385979,27⟩

theorem rank947 : P3_7_1.BankOK src947.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1387_301 13822

theorem width947 : Lower6960.HelperSource.WidthGuard src947.bank 179730 2308 src947.reserve := requestWidth (by decide)

def ends947 : List ℕ := [2308, 2309, 2313]

theorem inside947 : Research6966.TerminalBanks.inside src947.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover947 : Cover (Triangular src947) 2313 2308 ends947 := triangleCover (by decide +kernel)

def src948 : Request := ⟨⟨⟨1000,1395,307,17590⟩,30557599170560,105715278267⟩,6,3,1,385979,27⟩

theorem rank948 : P3_7_1.BankOK src948.bank := by
  simpa only [src948, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 17590

theorem width948 : Lower6960.HelperSource.WidthGuard src948.bank 179730 2308 src948.reserve := requestWidth (by decide)

def ends948 : List ℕ := [2308, 2309, 2313]

theorem inside948 : Research6966.TerminalBanks.inside src948.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover948 : Cover (Triangular src948) 2313 2308 ends948 := triangleCover (by decide +kernel)

def src949 : Request := ⟨⟨⟨1201,1674,368,17590⟩,52817102635008,218807905514⟩,8,3,1,385979,27⟩

theorem rank949 : P3_7_1.BankOK src949.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_368 17590

theorem width949 : Lower6960.HelperSource.WidthGuard src949.bank 179730 2308 src949.reserve := requestWidth (by decide)

def ends949 : List ℕ := [2308, 2309, 2313]

theorem inside949 : Research6966.TerminalBanks.inside src949.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover949 : Cover (Triangular src949) 2313 2308 ends949 := triangleCover (by decide +kernel)

def src95 : Request := ⟨⟨⟨2590,3600,775,61216⟩,519149091553280,4592038728177⟩,249,2,1,257319,513⟩

theorem rank95 : P3_7_1.BankOK src95.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2590_3600_775 61216

theorem width95 : Lower6960.HelperSource.WidthGuard src95.bank 179730 2308 src95.reserve := requestWidth (by decide)

def ends95 : List ℕ := [2308, 2309, 2313]

theorem inside95 : Research6966.TerminalBanks.inside src95.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover95 : Cover (Triangular src95) 2313 2308 ends95 := triangleCover (by decide +kernel)

def src950 : Request := ⟨⟨⟨1457,2023,449,22355⟩,94646894592000,469765771732⟩,13,3,1,385979,27⟩

theorem rank950 : P3_7_1.BankOK src950.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1457_2023_449 22355

theorem width950 : Lower6960.HelperSource.WidthGuard src950.bank 179730 2308 src950.reserve := requestWidth (by decide)

def ends950 : List ℕ := [2308, 2309, 2313]

theorem inside950 : Research6966.TerminalBanks.inside src950.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover950 : Cover (Triangular src950) 2313 2308 ends950 := triangleCover (by decide +kernel)

def src951 : Request := ⟨⟨⟨2566,3563,783,43594⟩,512438711615488,4477553723328⟩,32,3,1,385979,27⟩

theorem rank951 : P3_7_1.BankOK src951.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2566_3563_783 43594

theorem width951 : Lower6960.HelperSource.WidthGuard src951.bank 179730 2308 src951.reserve := requestWidth (by decide)

def ends951 : List ℕ := [2308, 2309, 2313]

theorem inside951 : Research6966.TerminalBanks.inside src951.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover951 : Cover (Triangular src951) 2313 2308 ends951 := triangleCover (by decide +kernel)

def src952 : Request := ⟨⟨⟨2768,3842,854,38252⟩,648553314385920,6106417618032⟩,32,3,1,385979,27⟩

theorem rank952 : P3_7_1.BankOK src952.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2768_3842_854 38252

theorem width952 : Lower6960.HelperSource.WidthGuard src952.bank 179730 2308 src952.reserve := requestWidth (by decide)

def ends952 : List ℕ := [2308, 2309, 2313]

theorem inside952 : Research6966.TerminalBanks.inside src952.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover952 : Cover (Triangular src952) 2313 2308 ends952 := triangleCover (by decide +kernel)

def src953 : Request := ⟨⟨⟨2998,4168,896,145596⟩,804225297940480,8239190160355⟩,44,3,1,385979,27⟩

theorem rank953 : P3_7_1.BankOK src953.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4168_896 145596

theorem width953 : Lower6960.HelperSource.WidthGuard src953.bank 179730 2308 src953.reserve := requestWidth (by decide)

def ends953 : List ℕ := [2308, 2309, 2313]

theorem inside953 : Research6966.TerminalBanks.inside src953.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover953 : Cover (Triangular src953) 2313 2308 ends953 := triangleCover (by decide +kernel)

def src954 : Request := ⟨⟨⟨4815,6697,1474,72277⟩,3391159166566400,55891290082931⟩,65,3,1,385979,27⟩

theorem rank954 : P3_7_1.BankOK src954.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4815_6697_1474 72277

theorem width954 : Lower6960.HelperSource.WidthGuard src954.bank 179730 2308 src954.reserve := requestWidth (by decide)

def ends954 : List ℕ := [2309, 2313]



theorem cover954 : Cover (Triangular src954) 2313 2308 ends954 := triangleCover (by decide +kernel)

def src955 : Request := ⟨⟨⟨8505,11810,2598,264035⟩,18650290068914176,540020413005418⟩,145,3,1,386273,27⟩

theorem rank955 : P3_7_1.BankOK src955.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8505_11810_2598 264035

theorem width955 : Lower6960.HelperSource.WidthGuard src955.bank 179730 2308 src955.reserve := requestWidth (by decide)

def ends955 : List ℕ := [2308, 2309, 2313]




theorem cover955 : Cover (Triangular src955) 2313 2308 ends955 := triangleCover (by decide +kernel)

def src956 : Request := ⟨⟨⟨10040,13952,3070,146522⟩,30701621376450560,1051954539834997⟩,145,3,1,385979,27⟩

theorem rank956 : P3_7_1.BankOK src956.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10040_13952_3070 146522

theorem width956 : Lower6960.HelperSource.WidthGuard src956.bank 179730 2308 src956.reserve := requestWidth (by decide)

def ends956 : List ℕ := [2309, 2313]



theorem cover956 : Cover (Triangular src956) 2313 2308 ends956 := triangleCover (by decide +kernel)

def src957 : Request := ⟨⟨⟨691,963,212,8679⟩,10098434375680,24078187611⟩,0,3,1,385979,28⟩

theorem rank957 : P3_7_1.BankOK src957.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_963_212 8679

theorem width957 : Lower6960.HelperSource.WidthGuard src957.bank 179730 2308 src957.reserve := requestWidth (by decide)

def ends957 : List ℕ := [2308, 2309, 2313]

theorem inside957 : Research6966.TerminalBanks.inside src957.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover957 : Cover (Triangular src957) 2313 2308 ends957 := triangleCover (by decide +kernel)

def src958 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,1,3,1,385979,28⟩

theorem rank958 : P3_7_1.BankOK src958.bank := by
  simpa only [src958, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 9763

theorem width958 : Lower6960.HelperSource.WidthGuard src958.bank 179730 2308 src958.reserve := requestWidth (by decide)

def ends958 : List ℕ := [2313]

theorem inside958 : Research6966.TerminalBanks.inside src958.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover958 : Cover (Triangular src958) 2313 2308 ends958 := triangleCover (by decide +kernel)

def src959 : Request := ⟨⟨⟨825,1143,248,10958⟩,16903818182656,47186356218⟩,2,3,1,385979,28⟩

theorem rank959 : P3_7_1.BankOK src959.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_825_1143_248 10958

theorem width959 : Lower6960.HelperSource.WidthGuard src959.bank 179730 2308 src959.reserve := requestWidth (by decide)

def ends959 : List ℕ := [2308, 2309, 2313]

theorem inside959 : Research6966.TerminalBanks.inside src959.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover959 : Cover (Triangular src959) 2313 2308 ends959 := triangleCover (by decide +kernel)

def src96 : Request := ⟨⟨⟨2305,3201,702,81694⟩,370969276579840,2912992731804⟩,250,2,1,257319,1025⟩

theorem rank96 : P3_7_1.BankOK src96.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3201_702 81694

theorem width96 : Lower6960.HelperSource.WidthGuard src96.bank 179730 2308 src96.reserve := requestWidth (by decide)

def ends96 : List ℕ := [2308, 2309, 2313]

theorem inside96 : Research6966.TerminalBanks.inside src96.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover96 : Cover (Triangular src96) 2313 2308 ends96 := triangleCover (by decide +kernel)

def src960 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,3,3,1,385979,28⟩

theorem rank960 : P3_7_1.BankOK src960.bank := by
  simpa only [src960, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 12355

theorem width960 : Lower6960.HelperSource.WidthGuard src960.bank 179730 2308 src960.reserve := requestWidth (by decide)

def ends960 : List ℕ := [2308, 2313]

theorem inside960 : Research6966.TerminalBanks.inside src960.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover960 : Cover (Triangular src960) 2313 2308 ends960 := triangleCover (by decide +kernel)

def src961 : Request := ⟨⟨⟨828,1151,253,13899⟩,17301502689280,49010625289⟩,4,3,1,385979,28⟩

theorem rank961 : P3_7_1.BankOK src961.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_253 13899

theorem width961 : Lower6960.HelperSource.WidthGuard src961.bank 179730 2308 src961.reserve := requestWidth (by decide)

def ends961 : List ℕ := [2308, 2309, 2313]

theorem inside961 : Research6966.TerminalBanks.inside src961.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover961 : Cover (Triangular src961) 2313 2308 ends961 := triangleCover (by decide +kernel)

def src962 : Request := ⟨⟨⟨994,1379,307,13892⟩,30148730028032,101862721867⟩,6,3,1,385979,28⟩

theorem rank962 : P3_7_1.BankOK src962.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_994_1379_307 13892

theorem width962 : Lower6960.HelperSource.WidthGuard src962.bank 179730 2308 src962.reserve := requestWidth (by decide)

def ends962 : List ℕ := [2308, 2309, 2313]

theorem inside962 : Research6966.TerminalBanks.inside src962.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover962 : Cover (Triangular src962) 2313 2308 ends962 := triangleCover (by decide +kernel)

def src963 : Request := ⟨⟨⟨1201,1674,368,15636⟩,52817102635008,218807905514⟩,8,3,1,385979,28⟩

theorem rank963 : P3_7_1.BankOK src963.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_368 15636

theorem width963 : Lower6960.HelperSource.WidthGuard src963.bank 179730 2308 src963.reserve := requestWidth (by decide)

def ends963 : List ℕ := [2309, 2313]

theorem inside963 : Research6966.TerminalBanks.inside src963.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover963 : Cover (Triangular src963) 2313 2308 ends963 := triangleCover (by decide +kernel)

def src964 : Request := ⟨⟨⟨1455,2021,445,19768⟩,93718291415040,465028319332⟩,13,3,1,385979,28⟩

theorem rank964 : P3_7_1.BankOK src964.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2021_445 19768

theorem width964 : Lower6960.HelperSource.WidthGuard src964.bank 179730 2308 src964.reserve := requestWidth (by decide)

def ends964 : List ℕ := [2308, 2309, 2313]

theorem inside964 : Research6966.TerminalBanks.inside src964.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover964 : Cover (Triangular src964) 2313 2308 ends964 := triangleCover (by decide +kernel)

def src965 : Request := ⟨⟨⟨2590,3595,798,35505⟩,530824420130816,4676852015559⟩,32,3,1,385979,28⟩

theorem rank965 : P3_7_1.BankOK src965.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2590_3595_798 35505

theorem width965 : Lower6960.HelperSource.WidthGuard src965.bank 179730 2308 src965.reserve := requestWidth (by decide)

def ends965 : List ℕ := [2308, 2309, 2313]

theorem inside965 : Research6966.TerminalBanks.inside src965.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover965 : Cover (Triangular src965) 2313 2308 ends965 := triangleCover (by decide +kernel)

def src966 : Request := ⟨⟨⟨2615,3627,819,35562⟩,553151842222080,4910333421859⟩,32,3,1,385979,28⟩

theorem rank966 : P3_7_1.BankOK src966.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 35562

theorem width966 : Lower6960.HelperSource.WidthGuard src966.bank 179730 2308 src966.reserve := requestWidth (by decide)

def ends966 : List ℕ := [2309, 2313]

theorem inside966 : Research6966.TerminalBanks.inside src966.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover966 : Cover (Triangular src966) 2313 2308 ends966 := triangleCover (by decide +kernel)

def src967 : Request := ⟨⟨⟨3000,4171,895,91609⟩,804739381985280,8251090109528⟩,44,3,1,385979,28⟩

theorem rank967 : P3_7_1.BankOK src967.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4171_895 91609

theorem width967 : Lower6960.HelperSource.WidthGuard src967.bank 179730 2308 src967.reserve := requestWidth (by decide)

def ends967 : List ℕ := [2308, 2309, 2313]

theorem inside967 : Research6966.TerminalBanks.inside src967.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover967 : Cover (Triangular src967) 2313 2308 ends967 := triangleCover (by decide +kernel)

def src968 : Request := ⟨⟨⟨8366,11611,2580,189362⟩,17879833989873664,508497594730893⟩,145,3,1,385979,28⟩

theorem rank968 : P3_7_1.BankOK src968.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8366_11611_2580 189362

theorem width968 : Lower6960.HelperSource.WidthGuard src968.bank 179730 2308 src968.reserve := requestWidth (by decide)

def ends968 : List ℕ := [2308, 2309, 2313]




theorem cover968 : Cover (Triangular src968) 2313 2308 ends968 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical

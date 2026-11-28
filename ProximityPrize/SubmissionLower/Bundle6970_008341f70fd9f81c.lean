import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks27
import ProximityPrize.SubmissionLower.Bundle6970_c51a423b59d0dd6b
import ProximityPrize.SubmissionLower.Bundle6970_ec9790ff7fc8ae2f
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks41
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks50
import ProximityPrize.SubmissionLower.Bundle6970_fa78e5af1890b063
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks61
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks68
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks71
import ProximityPrize.SubmissionLower.Bundle6970_ceea66e6500ee0de
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks77
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Bundle6970_fa0707633ba569a9
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks31
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Bundle6970_6ed322075960e0ab
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks60
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks67
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks64
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks72
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks38
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks73
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks54
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks56
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks47
import ProximityPrize.SubmissionLower.Z6969Pack0632

section Pack_R6970Height2313CommonSources04

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1030 : Request := ⟨⟨⟨3965,5510,1244,40111⟩,1929631496929280,26129827888718⟩,65,3,1,385979,33⟩

theorem rank1030 : P3_7_1.BankOK src1030.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3965_5510_1244 40111

theorem width1030 : Lower6960.HelperSource.WidthGuard src1030.bank 179730 2308 src1030.reserve := requestWidth (by decide)

def ends1030 : List ℕ := [2308, 2313]



theorem cover1030 : Cover (Triangular src1030) 2313 2308 ends1030 := triangleCover (by decide +kernel)

def src1031 : Request := ⟨⟨⟨6934,9625,2134,112563⟩,10165649691115520,239736170913945⟩,145,3,1,385979,33⟩

theorem rank1031 : P3_7_1.BankOK src1031.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6934_9625_2134 112563

theorem width1031 : Lower6960.HelperSource.WidthGuard src1031.bank 179730 2308 src1031.reserve := requestWidth (by decide)

def ends1031 : List ℕ := [2308, 2309, 2313]




theorem cover1031 : Cover (Triangular src1031) 2313 2308 ends1031 := triangleCover (by decide +kernel)

def src1032 : Request := ⟨⟨⟨10006,13950,3070,115771⟩,30469278368006144,1051468979452278⟩,190,3,1,385979,33⟩

theorem rank1032 : P3_7_1.BankOK src1032.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10006_13950_3070 115771

theorem width1032 : Lower6960.HelperSource.WidthGuard src1032.bank 179730 2308 src1032.reserve := requestWidth (by decide)

def ends1032 : List ℕ := [2308, 2309, 2313]




theorem cover1032 : Cover (Triangular src1032) 2313 2308 ends1032 := triangleCover (by decide +kernel)

def src1033 : Request := ⟨⟨⟨471,655,144,6096⟩,3199755878400,5168862572⟩,0,3,1,385979,34⟩

theorem rank1033 : P3_7_1.BankOK src1033.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 6096

theorem width1033 : Lower6960.HelperSource.WidthGuard src1033.bank 179730 2308 src1033.reserve := requestWidth (by decide)

def ends1033 : List ℕ := [2308, 2313]

theorem inside1033 : Research6966.TerminalBanks.inside src1033.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1033 : Cover (Triangular src1033) 2313 2308 ends1033 := triangleCover (by decide +kernel)

def src1034 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,1,3,1,385979,34⟩

theorem rank1034 : P3_7_1.BankOK src1034.bank := by
  simpa only [src1034, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 6096

theorem width1034 : Lower6960.HelperSource.WidthGuard src1034.bank 179730 2308 src1034.reserve := requestWidth (by decide)

def ends1034 : List ℕ := [2308, 2309, 2313]

theorem inside1034 : Research6966.TerminalBanks.inside src1034.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1034 : Cover (Triangular src1034) 2313 2308 ends1034 := triangleCover (by decide +kernel)

def src1035 : Request := ⟨⟨⟨690,962,208,6858⟩,9921631092736,23645774460⟩,2,3,1,385979,34⟩

theorem rank1035 : P3_7_1.BankOK src1035.bank := by
  simpa only [src1035, _root_.Research6969.TransitionBanks.bank192] using _root_.Research6969.TransitionBanks.rank192 6858

theorem width1035 : Lower6960.HelperSource.WidthGuard src1035.bank 179730 2308 src1035.reserve := requestWidth (by decide)

def ends1035 : List ℕ := [2309, 2313]

theorem inside1035 : Research6966.TerminalBanks.inside src1035.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1035 : Cover (Triangular src1035) 2313 2308 ends1035 := triangleCover (by decide +kernel)

def src1036 : Request := ⟨⟨⟨692,962,212,6858⟩,10131154665472,23997864317⟩,3,3,1,385979,34⟩

theorem rank1036 : P3_7_1.BankOK src1036.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_212 6858

theorem width1036 : Lower6960.HelperSource.WidthGuard src1036.bank 179730 2308 src1036.reserve := requestWidth (by decide)

def ends1036 : List ℕ := [2308, 2309, 2313]

theorem inside1036 : Research6966.TerminalBanks.inside src1036.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1036 : Cover (Triangular src1036) 2313 2308 ends1036 := triangleCover (by decide +kernel)

def src1037 : Request := ⟨⟨⟨691,962,212,7715⟩,10098434375680,23997864317⟩,4,3,1,385979,34⟩

theorem rank1037 : P3_7_1.BankOK src1037.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 7715

theorem width1037 : Lower6960.HelperSource.WidthGuard src1037.bank 179730 2308 src1037.reserve := requestWidth (by decide)

def ends1037 : List ℕ := [2309, 2313]

theorem inside1037 : Research6966.TerminalBanks.inside src1037.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1037 : Cover (Triangular src1037) 2313 2308 ends1037 := triangleCover (by decide +kernel)

def src1038 : Request := ⟨⟨⟨827,1151,253,10983⟩,17254793609216,49010625289⟩,8,3,1,385979,34⟩

theorem rank1038 : P3_7_1.BankOK src1038.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_253 10983

theorem width1038 : Lower6960.HelperSource.WidthGuard src1038.bank 179730 2308 src1038.reserve := requestWidth (by decide)

def ends1038 : List ℕ := [2309, 2313]

theorem inside1038 : Research6966.TerminalBanks.inside src1038.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1038 : Cover (Triangular src1038) 2313 2308 ends1038 := triangleCover (by decide +kernel)

def src1039 : Request := ⟨⟨⟨1454,2023,457,15636⟩,95477886615552,476245648464⟩,20,3,1,385979,34⟩

theorem rank1039 : P3_7_1.BankOK src1039.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2023_457 15636

theorem width1039 : Lower6960.HelperSource.WidthGuard src1039.bank 179730 2308 src1039.reserve := requestWidth (by decide)

def ends1039 : List ℕ := [2308, 2309, 2313]

theorem inside1039 : Research6966.TerminalBanks.inside src1039.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1039 : Cover (Triangular src1039) 2313 2308 ends1039 := triangleCover (by decide +kernel)

def src104 : Request := ⟨⟨⟨2821,3913,882,32757⟩,693453055590400,6641779624741⟩,85,2,1,278103,49⟩

theorem rank104 : P3_7_1.BankOK src104.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2821_3913_882 32757

theorem width104 : Lower6960.HelperSource.WidthGuard src104.bank 179730 2308 src104.reserve := requestWidth (by decide)

def ends104 : List ℕ := [2308, 2309, 2313]

theorem inside104 : Research6966.TerminalBanks.inside src104.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover104 : Cover (Triangular src104) 2313 2308 ends104 := triangleCover (by decide +kernel)

def src1040 : Request := ⟨⟨⟨2607,3627,819,25043⟩,549365140684800,4910333421859⟩,40,3,1,385979,34⟩

theorem rank1040 : P3_7_1.BankOK src1040.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3627_819 25043

theorem width1040 : Lower6960.HelperSource.WidthGuard src1040.bank 179730 2308 src1040.reserve := requestWidth (by decide)

def ends1040 : List ℕ := [2308, 2309, 2313]

theorem inside1040 : Research6966.TerminalBanks.inside src1040.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1040 : Cover (Triangular src1040) 2313 2308 ends1040 := triangleCover (by decide +kernel)

def src1041 : Request := ⟨⟨⟨2605,3623,775,39876⟩,525894114344960,4687093383477⟩,45,3,1,385979,34⟩

theorem rank1041 : P3_7_1.BankOK src1041.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3623_775 39876

theorem width1041 : Lower6960.HelperSource.WidthGuard src1041.bank 179730 2308 src1041.reserve := requestWidth (by decide)

def ends1041 : List ℕ := [2308, 2309, 2313]

theorem inside1041 : Research6966.TerminalBanks.inside src1041.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1041 : Cover (Triangular src1041) 2313 2308 ends1041 := triangleCover (by decide +kernel)

def src1042 : Request := ⟨⟨⟨2816,3906,882,27464⟩,690700839813120,6603573924229⟩,45,3,1,385979,34⟩

theorem rank1042 : P3_7_1.BankOK src1042.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3906_882 27464

theorem width1042 : Lower6960.HelperSource.WidthGuard src1042.bank 179730 2308 src1042.reserve := requestWidth (by decide)

def ends1042 : List ℕ := [2308, 2313]

theorem inside1042 : Research6966.TerminalBanks.inside src1042.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1042 : Cover (Triangular src1042) 2313 2308 ends1042 := triangleCover (by decide +kernel)

def src1043 : Request := ⟨⟨⟨5718,7951,1750,64247⟩,5677314604007424,111025751789870⟩,110,3,1,385979,34⟩

theorem rank1043 : P3_7_1.BankOK src1043.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5718_7951_1750 64247

theorem width1043 : Lower6960.HelperSource.WidthGuard src1043.bank 179730 2308 src1043.reserve := requestWidth (by decide)

def ends1043 : List ℕ := [2308, 2309, 2313]




theorem cover1043 : Cover (Triangular src1043) 2313 2308 ends1043 := triangleCover (by decide +kernel)

def src1044 : Request := ⟨⟨⟨6929,9621,2118,91403⟩,10091370476994560,238016971510476⟩,145,3,1,385979,34⟩

theorem rank1044 : P3_7_1.BankOK src1044.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6929_9621_2118 91403

theorem width1044 : Lower6960.HelperSource.WidthGuard src1044.bank 179730 2308 src1044.reserve := requestWidth (by decide)

def ends1044 : List ℕ := [2308, 2309, 2313]




theorem cover1044 : Cover (Triangular src1044) 2313 2308 ends1044 := triangleCover (by decide +kernel)

def src1045 : Request := ⟨⟨⟨10036,13934,3070,102835⟩,30674238602215424,1047589984979998⟩,190,3,1,385979,34⟩

theorem rank1045 : P3_7_1.BankOK src1045.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10036_13934_3070 102835

theorem width1045 : Lower6960.HelperSource.WidthGuard src1045.bank 179730 2308 src1045.reserve := requestWidth (by decide)

def ends1045 : List ℕ := [2308, 2309, 2313]




theorem cover1045 : Cover (Triangular src1045) 2313 2308 ends1045 := triangleCover (by decide +kernel)

def src1046 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,0,3,1,385979,35⟩

theorem rank1046 : P3_7_1.BankOK src1046.bank := by
  simpa only [src1046, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 5419

theorem width1046 : Lower6960.HelperSource.WidthGuard src1046.bank 179730 2308 src1046.reserve := requestWidth (by decide)

def ends1046 : List ℕ := [2308, 2309, 2313]

theorem inside1046 : Research6966.TerminalBanks.inside src1046.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1046 : Cover (Triangular src1046) 2313 2308 ends1046 := triangleCover (by decide +kernel)

def src1047 : Request := ⟨⟨⟨562,781,176,5419⟩,5526256353280,10627925923⟩,1,3,1,385979,35⟩

theorem rank1047 : P3_7_1.BankOK src1047.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 5419

theorem width1047 : Lower6960.HelperSource.WidthGuard src1047.bank 179730 2308 src1047.reserve := requestWidth (by decide)

def ends1047 : List ℕ := [2308, 2313]

theorem inside1047 : Research6966.TerminalBanks.inside src1047.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1047 : Cover (Triangular src1047) 2313 2308 ends1047 := triangleCover (by decide +kernel)

def src1048 : Request := ⟨⟨⟨562,781,176,6096⟩,5526256353280,10627925923⟩,2,3,1,385979,35⟩

theorem rank1048 : P3_7_1.BankOK src1048.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 6096

theorem width1048 : Lower6960.HelperSource.WidthGuard src1048.bank 179730 2308 src1048.reserve := requestWidth (by decide)

def ends1048 : List ℕ := [2308, 2313]

theorem inside1048 : Research6966.TerminalBanks.inside src1048.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1048 : Cover (Triangular src1048) 2313 2308 ends1048 := triangleCover (by decide +kernel)

def src1049 : Request := ⟨⟨⟨691,961,208,6847⟩,9953791705088,23566853761⟩,3,3,1,385979,35⟩

theorem rank1049 : P3_7_1.BankOK src1049.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_961_208 6847

theorem width1049 : Lower6960.HelperSource.WidthGuard src1049.bank 179730 2308 src1049.reserve := requestWidth (by decide)

def ends1049 : List ℕ := [2308, 2309, 2313]

theorem inside1049 : Research6966.TerminalBanks.inside src1049.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1049 : Cover (Triangular src1049) 2313 2308 ends1049 := triangleCover (by decide +kernel)

def src105 : Request := ⟨⟨⟨2807,3905,882,35655⟩,685761434222592,6598128215989⟩,85,2,1,278103,49⟩

theorem rank105 : P3_7_1.BankOK src105.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2807_3905_882 35655

theorem width105 : Lower6960.HelperSource.WidthGuard src105.bank 179730 2308 src105.reserve := requestWidth (by decide)

def ends105 : List ℕ := [2308, 2309, 2313]

theorem inside105 : Research6966.TerminalBanks.inside src105.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover105 : Cover (Triangular src105) 2313 2308 ends105 := triangleCover (by decide +kernel)

def src1050 : Request := ⟨⟨⟨692,962,217,6858⟩,10311018217472,24434817260⟩,4,3,1,385979,35⟩

theorem rank1050 : P3_7_1.BankOK src1050.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_217 6858

theorem width1050 : Lower6960.HelperSource.WidthGuard src1050.bank 179730 2308 src1050.reserve := requestWidth (by decide)

def ends1050 : List ℕ := [2308, 2313]

theorem inside1050 : Research6966.TerminalBanks.inside src1050.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1050 : Cover (Triangular src1050) 2313 2308 ends1050 := triangleCover (by decide +kernel)

def src1051 : Request := ⟨⟨⟨826,1151,253,9763⟩,17208151113728,49010625289⟩,8,3,1,385979,35⟩

theorem rank1051 : P3_7_1.BankOK src1051.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_253 9763

theorem width1051 : Lower6960.HelperSource.WidthGuard src1051.bank 179730 2308 src1051.reserve := requestWidth (by decide)

def ends1051 : List ℕ := [2308, 2313]

theorem inside1051 : Research6966.TerminalBanks.inside src1051.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1051 : Cover (Triangular src1051) 2313 2308 ends1051 := triangleCover (by decide +kernel)

def src1052 : Request := ⟨⟨⟨1200,1674,368,13899⟩,52718727069696,218807905514⟩,16,3,1,385979,35⟩

theorem rank1052 : P3_7_1.BankOK src1052.bank := by
  simpa only [src1052, _root_.Research6969.TransitionBanks.bank228] using _root_.Research6969.TransitionBanks.rank228 13899

theorem width1052 : Lower6960.HelperSource.WidthGuard src1052.bank 179730 2308 src1052.reserve := requestWidth (by decide)

def ends1052 : List ℕ := [2309, 2313]

theorem inside1052 : Research6966.TerminalBanks.inside src1052.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1052 : Cover (Triangular src1052) 2313 2308 ends1052 := triangleCover (by decide +kernel)

def src1053 : Request := ⟨⟨⟨2107,2929,662,19788⟩,290170711048192,2090961110089⟩,32,3,1,385979,35⟩

theorem rank1053 : P3_7_1.BankOK src1053.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2107_2929_662 19788

theorem width1053 : Lower6960.HelperSource.WidthGuard src1053.bank 179730 2308 src1053.reserve := requestWidth (by decide)

def ends1053 : List ℕ := [2308, 2309, 2313]

theorem inside1053 : Research6966.TerminalBanks.inside src1053.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1053 : Cover (Triangular src1053) 2313 2308 ends1053 := triangleCover (by decide +kernel)

def src1054 : Request := ⟨⟨⟨2323,3224,718,35402⟩,383999087738880,3033622538054⟩,46,3,1,385979,35⟩

theorem rank1054 : P3_7_1.BankOK src1054.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2323_3224_718 35402

theorem width1054 : Lower6960.HelperSource.WidthGuard src1054.bank 179730 2308 src1054.reserve := requestWidth (by decide)

def ends1054 : List ℕ := [2308, 2309, 2313]

theorem inside1054 : Research6966.TerminalBanks.inside src1054.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1054 : Cover (Triangular src1054) 2313 2308 ends1054 := triangleCover (by decide +kernel)

def src1055 : Request := ⟨⟨⟨2600,3611,793,27408⟩,532875289296896,4721067870510⟩,45,3,1,385979,35⟩

theorem rank1055 : P3_7_1.BankOK src1055.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3611_793 27408

theorem width1055 : Lower6960.HelperSource.WidthGuard src1055.bank 179730 2308 src1055.reserve := requestWidth (by decide)

def ends1055 : List ℕ := [2308, 2309, 2313]

theorem inside1055 : Research6966.TerminalBanks.inside src1055.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1055 : Cover (Triangular src1055) 2313 2308 ends1055 := triangleCover (by decide +kernel)

def src1056 : Request := ⟨⟨⟨3210,4464,1008,40111⟩,1024863250415616,11262426748352⟩,65,3,1,385979,35⟩

theorem rank1056 : P3_7_1.BankOK src1056.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3210_4464_1008 40111

theorem width1056 : Lower6960.HelperSource.WidthGuard src1056.bank 179730 2308 src1056.reserve := requestWidth (by decide)

def ends1056 : List ℕ := [2308, 2309, 2313]




theorem cover1056 : Cover (Triangular src1056) 2313 2308 ends1056 := triangleCover (by decide +kernel)

def src1057 : Request := ⟨⟨⟨6924,9625,2118,81311⟩,10075072601784320,238335796784464⟩,145,3,1,385979,35⟩

theorem rank1057 : P3_7_1.BankOK src1057.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6924_9625_2118 81311

theorem width1057 : Lower6960.HelperSource.WidthGuard src1057.bank 179730 2308 src1057.reserve := requestWidth (by decide)

def ends1057 : List ℕ := [2308, 2313]



theorem cover1057 : Cover (Triangular src1057) 2313 2308 ends1057 := triangleCover (by decide +kernel)

def src1058 : Request := ⟨⟨⟨8348,11577,2615,115771⟩,17976439182721024,509018341309343⟩,190,3,1,385979,35⟩

theorem rank1058 : P3_7_1.BankOK src1058.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8348_11577_2615 115771

theorem width1058 : Lower6960.HelperSource.WidthGuard src1058.bank 179730 2308 src1058.reserve := requestWidth (by decide)

def ends1058 : List ℕ := [2309, 2313]



theorem cover1058 : Cover (Triangular src1058) 2313 2308 ends1058 := triangleCover (by decide +kernel)

def src1059 : Request := ⟨⟨⟨471,654,144,4802⟩,3199755878400,5143543252⟩,0,3,1,385979,36⟩

theorem rank1059 : P3_7_1.BankOK src1059.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_654_144 4802

theorem width1059 : Lower6960.HelperSource.WidthGuard src1059.bank 179730 2308 src1059.reserve := requestWidth (by decide)

def ends1059 : List ℕ := [2308, 2309, 2313]

theorem inside1059 : Research6966.TerminalBanks.inside src1059.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1059 : Cover (Triangular src1059) 2313 2308 ends1059 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources04

section Pack_R6970Height2313CommonSources05

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src106 : Request := ⟨⟨⟨2316,3213,724,31694⟩,383822462976000,3019856947443⟩,85,2,1,283522,58⟩

theorem rank106 : P3_7_1.BankOK src106.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2316_3213_724 31694

theorem width106 : Lower6960.HelperSource.WidthGuard src106.bank 179730 2308 src106.reserve := requestWidth (by decide)

def ends106 : List ℕ := [2308, 2309, 2313]

theorem inside106 : Research6966.TerminalBanks.inside src106.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover106 : Cover (Triangular src106) 2313 2308 ends106 := triangleCover (by decide +kernel)

def src1060 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,1,3,1,385979,36⟩

theorem rank1060 : P3_7_1.BankOK src1060.bank := by
  simpa only [src1060, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 5419

theorem width1060 : Lower6960.HelperSource.WidthGuard src1060.bank 179730 2308 src1060.reserve := requestWidth (by decide)

def ends1060 : List ℕ := [2313]

theorem inside1060 : Research6966.TerminalBanks.inside src1060.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1060 : Cover (Triangular src1060) 2313 2308 ends1060 := triangleCover (by decide +kernel)

def src1061 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,2,3,1,385979,36⟩

theorem rank1061 : P3_7_1.BankOK src1061.bank := by
  simpa only [src1061, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 6096

theorem width1061 : Lower6960.HelperSource.WidthGuard src1061.bank 179730 2308 src1061.reserve := requestWidth (by decide)

def ends1061 : List ℕ := [2313]

theorem inside1061 : Research6966.TerminalBanks.inside src1061.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1061 : Cover (Triangular src1061) 2313 2308 ends1061 := triangleCover (by decide +kernel)

def src1062 : Request := ⟨⟨⟨561,781,172,6858⟩,5409683537920,10440670587⟩,3,3,1,385979,36⟩

theorem rank1062 : P3_7_1.BankOK src1062.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 6858

theorem width1062 : Lower6960.HelperSource.WidthGuard src1062.bank 179730 2308 src1062.reserve := requestWidth (by decide)

def ends1062 : List ℕ := [2308, 2309, 2313]

theorem inside1062 : Research6966.TerminalBanks.inside src1062.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1062 : Cover (Triangular src1062) 2313 2308 ends1062 := triangleCover (by decide +kernel)

def src1063 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,6,3,1,385979,36⟩

theorem rank1063 : P3_7_1.BankOK src1063.bank := by
  simpa only [src1063, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 8679

theorem width1063 : Lower6960.HelperSource.WidthGuard src1063.bank 179730 2308 src1063.reserve := requestWidth (by decide)

def ends1063 : List ℕ := [2308, 2313]

theorem inside1063 : Research6966.TerminalBanks.inside src1063.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1063 : Cover (Triangular src1063) 2313 2308 ends1063 := triangleCover (by decide +kernel)

def src1064 : Request := ⟨⟨⟨827,1151,253,8679⟩,17254793609216,49010625289⟩,8,3,1,385979,36⟩

theorem rank1064 : P3_7_1.BankOK src1064.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_253 8679

theorem width1064 : Lower6960.HelperSource.WidthGuard src1064.bank 179730 2308 src1064.reserve := requestWidth (by decide)

def ends1064 : List ℕ := [2308, 2309, 2313]

theorem inside1064 : Research6966.TerminalBanks.inside src1064.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1064 : Cover (Triangular src1064) 2313 2308 ends1064 := triangleCover (by decide +kernel)

def src1065 : Request := ⟨⟨⟨1203,1674,368,12355⟩,53014143959040,218807905514⟩,16,3,1,385979,36⟩

theorem rank1065 : P3_7_1.BankOK src1065.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_368 12355

theorem width1065 : Lower6960.HelperSource.WidthGuard src1065.bank 179730 2308 src1065.reserve := requestWidth (by decide)

def ends1065 : List ℕ := [2308, 2309, 2313]

theorem inside1065 : Research6966.TerminalBanks.inside src1065.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1065 : Cover (Triangular src1065) 2313 2308 ends1065 := triangleCover (by decide +kernel)

def src1066 : Request := ⟨⟨⟨2101,2913,645,24956⟩,282697978609664,2013318131288⟩,40,3,1,385979,36⟩

theorem rank1066 : P3_7_1.BankOK src1066.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2101_2913_645 24956

theorem width1066 : Lower6960.HelperSource.WidthGuard src1066.bank 179730 2308 src1066.reserve := requestWidth (by decide)

def ends1066 : List ℕ := [2308, 2309, 2313]

theorem inside1066 : Research6966.TerminalBanks.inside src1066.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1066 : Cover (Triangular src1066) 2313 2308 ends1066 := triangleCover (by decide +kernel)

def src1067 : Request := ⟨⟨⟨2300,3208,702,31694⟩,369170633195520,2933547980091⟩,45,3,1,385979,36⟩

theorem rank1067 : P3_7_1.BankOK src1067.bank := by
  simpa only [src1067, _root_.Research6969.TerminalAuxBanks.bank33] using _root_.Research6969.PackedRanks.TerminalRanks32To35.rank33 31694

theorem width1067 : Lower6960.HelperSource.WidthGuard src1067.bank 179730 2308 src1067.reserve := requestWidth (by decide)

def ends1067 : List ℕ := [2309, 2313]

theorem inside1067 : Research6966.TerminalBanks.inside src1067.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1067 : Cover (Triangular src1067) 2313 2308 ends1067 := triangleCover (by decide +kernel)

def src1068 : Request := ⟨⟨⟨2313,3208,724,26494⟩,382708934246400,3004743122568⟩,45,3,1,385979,36⟩

theorem rank1068 : P3_7_1.BankOK src1068.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2313_3208_724 26494

theorem width1068 : Lower6960.HelperSource.WidthGuard src1068.bank 179730 2308 src1068.reserve := requestWidth (by decide)

def ends1068 : List ℕ := [2309, 2313]

theorem inside1068 : Research6966.TerminalBanks.inside src1068.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1068 : Cover (Triangular src1068) 2313 2308 ends1068 := triangleCover (by decide +kernel)

def src1069 : Request := ⟨⟨⟨4800,6663,1474,71803⟩,3367547627110400,54982628702281⟩,110,3,1,385979,36⟩

theorem rank1069 : P3_7_1.BankOK src1069.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4800_6663_1474 71803

theorem width1069 : Lower6960.HelperSource.WidthGuard src1069.bank 179730 2308 src1069.reserve := requestWidth (by decide)

def ends1069 : List ℕ := [2308, 2309, 2313]




theorem cover1069 : Cover (Triangular src1069) 2313 2308 ends1069 := triangleCover (by decide +kernel)

def src107 : Request := ⟨⟨⟨2588,3593,793,24077⟩,527385327042560,4645717944219⟩,85,2,1,283522,58⟩

theorem rank107 : P3_7_1.BankOK src107.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 24077

theorem width107 : Lower6960.HelperSource.WidthGuard src107.bank 179730 2308 src107.reserve := requestWidth (by decide)

def ends107 : List ℕ := [2308, 2309, 2313]

theorem inside107 : Research6966.TerminalBanks.inside src107.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover107 : Cover (Triangular src107) 2313 2308 ends107 := triangleCover (by decide +kernel)

def src1070 : Request := ⟨⟨⟨6921,9609,2118,72222⟩,10065300542455808,237062237065760⟩,145,3,1,385979,36⟩

theorem rank1070 : P3_7_1.BankOK src1070.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6921_9609_2118 72222

theorem width1070 : Lower6960.HelperSource.WidthGuard src1070.bank 179730 2308 src1070.reserve := requestWidth (by decide)

def ends1070 : List ℕ := [2308, 2309, 2313]




theorem cover1070 : Cover (Triangular src1070) 2313 2308 ends1070 := triangleCover (by decide +kernel)

def src1071 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,3,1,385979,37⟩

theorem rank1071 : P3_7_1.BankOK src1071.bank := by
  simpa only [src1071, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4817

theorem width1071 : Lower6960.HelperSource.WidthGuard src1071.bank 179730 2308 src1071.reserve := requestWidth (by decide)

def ends1071 : List ℕ := [2313]

theorem inside1071 : Research6966.TerminalBanks.inside src1071.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1071 : Cover (Triangular src1071) 2313 2308 ends1071 := triangleCover (by decide +kernel)

def src1072 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,1,3,1,385979,37⟩

theorem rank1072 : P3_7_1.BankOK src1072.bank := by
  simpa only [src1072, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 5419

theorem width1072 : Lower6960.HelperSource.WidthGuard src1072.bank 179730 2308 src1072.reserve := requestWidth (by decide)

def ends1072 : List ℕ := [2308, 2309, 2313]

theorem inside1072 : Research6966.TerminalBanks.inside src1072.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1072 : Cover (Triangular src1072) 2313 2308 ends1072 := triangleCover (by decide +kernel)

def src1073 : Request := ⟨⟨⟨562,781,172,5419⟩,5431270572032,10440670587⟩,2,3,1,385979,37⟩

theorem rank1073 : P3_7_1.BankOK src1073.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 5419

theorem width1073 : Lower6960.HelperSource.WidthGuard src1073.bank 179730 2308 src1073.reserve := requestWidth (by decide)

def ends1073 : List ℕ := [2308, 2313]

theorem inside1073 : Research6966.TerminalBanks.inside src1073.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1073 : Cover (Triangular src1073) 2313 2308 ends1073 := triangleCover (by decide +kernel)

def src1074 : Request := ⟨⟨⟨562,781,172,6096⟩,5431270572032,10440670587⟩,3,3,1,385979,37⟩

theorem rank1074 : P3_7_1.BankOK src1074.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 6096

theorem width1074 : Lower6960.HelperSource.WidthGuard src1074.bank 179730 2308 src1074.reserve := requestWidth (by decide)

def ends1074 : List ℕ := [2308, 2313]

theorem inside1074 : Research6966.TerminalBanks.inside src1074.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1074 : Cover (Triangular src1074) 2313 2308 ends1074 := triangleCover (by decide +kernel)

def src1075 : Request := ⟨⟨⟨562,781,172,7715⟩,5431270572032,10440670587⟩,4,3,1,385979,37⟩

theorem rank1075 : P3_7_1.BankOK src1075.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 7715

theorem width1075 : Lower6960.HelperSource.WidthGuard src1075.bank 179730 2308 src1075.reserve := requestWidth (by decide)

def ends1075 : List ℕ := [2308, 2309, 2313]

theorem inside1075 : Research6966.TerminalBanks.inside src1075.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1075 : Cover (Triangular src1075) 2313 2308 ends1075 := triangleCover (by decide +kernel)

def src1076 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,6,3,1,385979,37⟩

theorem rank1076 : P3_7_1.BankOK src1076.bank := by
  simpa only [src1076, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 7715

theorem width1076 : Lower6960.HelperSource.WidthGuard src1076.bank 179730 2308 src1076.reserve := requestWidth (by decide)

def ends1076 : List ℕ := [2308, 2313]

theorem inside1076 : Research6966.TerminalBanks.inside src1076.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1076 : Cover (Triangular src1076) 2313 2308 ends1076 := triangleCover (by decide +kernel)

def src1077 : Request := ⟨⟨⟨828,1151,253,9763⟩,17301502689280,49010625289⟩,10,3,1,385979,37⟩

theorem rank1077 : P3_7_1.BankOK src1077.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_253 9763

theorem width1077 : Lower6960.HelperSource.WidthGuard src1077.bank 179730 2308 src1077.reserve := requestWidth (by decide)

def ends1077 : List ℕ := [2308, 2309, 2313]

theorem inside1077 : Research6966.TerminalBanks.inside src1077.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1077 : Cover (Triangular src1077) 2313 2308 ends1077 := triangleCover (by decide +kernel)

def src1078 : Request := ⟨⟨⟨1455,2022,457,15636⟩,95625142599680,475487789910⟩,25,3,1,385979,37⟩

theorem rank1078 : P3_7_1.BankOK src1078.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2022_457 15636

theorem width1078 : Lower6960.HelperSource.WidthGuard src1078.bank 179730 2308 src1078.reserve := requestWidth (by decide)

def ends1078 : List ℕ := [2308, 2309, 2313]

theorem inside1078 : Research6966.TerminalBanks.inside src1078.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1078 : Cover (Triangular src1078) 2313 2308 ends1078 := triangleCover (by decide +kernel)

def src1079 : Request := ⟨⟨⟨2313,3208,724,24026⟩,382708934246400,3004743122568⟩,45,3,1,385979,37⟩

theorem rank1079 : P3_7_1.BankOK src1079.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2313_3208_724 24026

theorem width1079 : Lower6960.HelperSource.WidthGuard src1079.bank 179730 2308 src1079.reserve := requestWidth (by decide)

def ends1079 : List ℕ := [2308, 2313]

theorem inside1079 : Research6966.TerminalBanks.inside src1079.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1079 : Cover (Triangular src1079) 2313 2308 ends1079 := triangleCover (by decide +kernel)

def src108 : Request := ⟨⟨⟨2311,3207,720,22082⟩,380369684660224,2988850718069⟩,63,2,1,285209,49⟩

theorem rank108 : P3_7_1.BankOK src108.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2311_3207_720 22082

theorem width108 : Lower6960.HelperSource.WidthGuard src108.bank 179730 2308 src108.reserve := requestWidth (by decide)

def ends108 : List ℕ := [2308, 2309, 2313]

theorem inside108 : Research6966.TerminalBanks.inside src108.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover108 : Cover (Triangular src108) 2313 2308 ends108 := triangleCover (by decide +kernel)

def src1080 : Request := ⟨⟨⟨2816,3905,882,40111⟩,690700839813120,6598128215989⟩,63,3,1,385979,37⟩

theorem rank1080 : P3_7_1.BankOK src1080.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 40111

theorem width1080 : Lower6960.HelperSource.WidthGuard src1080.bank 179730 2308 src1080.reserve := requestWidth (by decide)

def ends1080 : List ℕ := [2309, 2313]

theorem inside1080 : Research6966.TerminalBanks.inside src1080.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1080 : Cover (Triangular src1080) 2313 2308 ends1080 := triangleCover (by decide +kernel)

def src1081 : Request := ⟨⟨⟨3950,5510,1213,45124⟩,1877062482395136,25622281045803⟩,85,3,1,385979,37⟩

theorem rank1081 : P3_7_1.BankOK src1081.bank := by
  simpa only [src1081, _root_.Research6969.TransitionBanks.bank310] using _root_.Research6969.TransitionBanks.rank310 45124

theorem width1081 : Lower6960.HelperSource.WidthGuard src1081.bank 179730 2308 src1081.reserve := requestWidth (by decide)

def ends1081 : List ℕ := [2308, 2309, 2313]




theorem cover1081 : Cover (Triangular src1081) 2313 2308 ends1081 := triangleCover (by decide +kernel)

def src1082 : Request := ⟨⟨⟨8330,11577,2548,91474⟩,17540864495845376,498847383098023⟩,190,3,1,385979,37⟩

theorem rank1082 : P3_7_1.BankOK src1082.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8330_11577_2548 91474

theorem width1082 : Lower6960.HelperSource.WidthGuard src1082.bank 179730 2308 src1082.reserve := requestWidth (by decide)

def ends1082 : List ℕ := [2308, 2309, 2313]




theorem cover1082 : Cover (Triangular src1082) 2313 2308 ends1082 := triangleCover (by decide +kernel)

def src1083 : Request := ⟨⟨⟨10034,13932,3070,130196⟩,30660552045363200,1047105796376127⟩,245,3,1,385979,37⟩

theorem rank1083 : P3_7_1.BankOK src1083.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10034_13932_3070 130196

theorem width1083 : Lower6960.HelperSource.WidthGuard src1083.bank 179730 2308 src1083.reserve := requestWidth (by decide)

def ends1083 : List ℕ := [2308, 2309, 2313]




theorem cover1083 : Cover (Triangular src1083) 2313 2308 ends1083 := triangleCover (by decide +kernel)

def src1084 : Request := ⟨⟨⟨402,558,123,4817⟩,1994022977536,2734096379⟩,0,3,1,385979,38⟩

theorem rank1084 : P3_7_1.BankOK src1084.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_402_558_123 4817

theorem width1084 : Lower6960.HelperSource.WidthGuard src1084.bank 179730 2308 src1084.reserve := requestWidth (by decide)

def ends1084 : List ℕ := [2308, 2313]

theorem inside1084 : Research6966.TerminalBanks.inside src1084.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1084 : Cover (Triangular src1084) 2313 2308 ends1084 := triangleCover (by decide +kernel)

def src1085 : Request := ⟨⟨⟨471,654,144,4808⟩,3199755878400,5143543252⟩,1,3,1,385979,38⟩

theorem rank1085 : P3_7_1.BankOK src1085.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_654_144 4808

theorem width1085 : Lower6960.HelperSource.WidthGuard src1085.bank 179730 2308 src1085.reserve := requestWidth (by decide)

def ends1085 : List ℕ := [2308, 2309, 2313]

theorem inside1085 : Research6966.TerminalBanks.inside src1085.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1085 : Cover (Triangular src1085) 2313 2308 ends1085 := triangleCover (by decide +kernel)

def src1086 : Request := ⟨⟨⟨562,781,169,6096⟩,5359435776000,10299257375⟩,3,3,1,385979,38⟩

theorem rank1086 : P3_7_1.BankOK src1086.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_169 6096

theorem width1086 : Lower6960.HelperSource.WidthGuard src1086.bank 179730 2308 src1086.reserve := requestWidth (by decide)

def ends1086 : List ℕ := [2309, 2313]

theorem inside1086 : Research6966.TerminalBanks.inside src1086.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1086 : Cover (Triangular src1086) 2313 2308 ends1086 := triangleCover (by decide +kernel)

def src1087 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,4,3,1,385979,38⟩

theorem rank1087 : P3_7_1.BankOK src1087.bank := by
  simpa only [src1087, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 6858

theorem width1087 : Lower6960.HelperSource.WidthGuard src1087.bank 179730 2308 src1087.reserve := requestWidth (by decide)

def ends1087 : List ℕ := [2309, 2313]

theorem inside1087 : Research6966.TerminalBanks.inside src1087.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1087 : Cover (Triangular src1087) 2313 2308 ends1087 := triangleCover (by decide +kernel)

def src1088 : Request := ⟨⟨⟨692,962,212,6858⟩,10131154665472,23997864317⟩,6,3,1,385979,38⟩

theorem rank1088 : P3_7_1.BankOK src1088.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_212 6858

theorem width1088 : Lower6960.HelperSource.WidthGuard src1088.bank 179730 2308 src1088.reserve := requestWidth (by decide)

def ends1088 : List ℕ := [2308, 2309, 2313]

theorem inside1088 : Research6966.TerminalBanks.inside src1088.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1088 : Cover (Triangular src1088) 2313 2308 ends1088 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources05

section Pack_R6970Height2313CommonSources06

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1089 : Request := ⟨⟨⟨826,1151,260,8679⟩,17566568546304,50057971890⟩,10,3,1,385979,38⟩

theorem rank1089 : P3_7_1.BankOK src1089.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_260 8679

theorem width1089 : Lower6960.HelperSource.WidthGuard src1089.bank 179730 2308 src1089.reserve := requestWidth (by decide)

def ends1089 : List ℕ := [2308, 2309, 2313]

theorem inside1089 : Research6966.TerminalBanks.inside src1089.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1089 : Cover (Triangular src1089) 2313 2308 ends1089 := triangleCover (by decide +kernel)

def src109 : Request := ⟨⟨⟨2803,3905,882,35655⟩,683572161150976,6598128215989⟩,85,2,1,285209,49⟩

theorem rank109 : P3_7_1.BankOK src109.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2803_3905_882 35655

theorem width109 : Lower6960.HelperSource.WidthGuard src109.bank 179730 2308 src109.reserve := requestWidth (by decide)

def ends109 : List ℕ := [2308, 2309, 2313]

theorem inside109 : Research6966.TerminalBanks.inside src109.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover109 : Cover (Triangular src109) 2313 2308 ends109 := triangleCover (by decide +kernel)

def src1090 : Request := ⟨⟨⟨1003,1395,315,12355⟩,31367332102144,107844841957⟩,16,3,1,385979,38⟩

theorem rank1090 : P3_7_1.BankOK src1090.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_315 12355

theorem width1090 : Lower6960.HelperSource.WidthGuard src1090.bank 179730 2308 src1090.reserve := requestWidth (by decide)

def ends1090 : List ℕ := [2308, 2313]

theorem inside1090 : Research6966.TerminalBanks.inside src1090.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1090 : Cover (Triangular src1090) 2313 2308 ends1090 := triangleCover (by decide +kernel)

def src1091 : Request := ⟨⟨⟨1753,2441,551,17590⟩,167236956323840,1008217465165⟩,32,3,1,385979,38⟩

theorem rank1091 : P3_7_1.BankOK src1091.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2441_551 17590

theorem width1091 : Lower6960.HelperSource.WidthGuard src1091.bank 179730 2308 src1091.reserve := requestWidth (by decide)

def ends1091 : List ℕ := [2309, 2313]

theorem inside1091 : Research6966.TerminalBanks.inside src1091.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1091 : Cover (Triangular src1091) 2313 2308 ends1091 := triangleCover (by decide +kernel)

def src1092 : Request := ⟨⟨⟨2767,3841,854,34307⟩,648028618752000,6101300343282⟩,63,3,1,385979,38⟩

theorem rank1092 : P3_7_1.BankOK src1092.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2767_3841_854 34307

theorem width1092 : Lower6960.HelperSource.WidthGuard src1092.bank 179730 2308 src1092.reserve := requestWidth (by decide)

def ends1092 : List ℕ := [2308, 2309, 2313]

theorem inside1092 : Research6966.TerminalBanks.inside src1092.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1092 : Cover (Triangular src1092) 2313 2308 ends1092 := triangleCover (by decide +kernel)

def src1093 : Request := ⟨⟨⟨2789,3873,854,35113⟩,659623697448960,6266506033362⟩,63,3,1,385979,38⟩

theorem rank1093 : P3_7_1.BankOK src1093.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 35113

theorem width1093 : Lower6960.HelperSource.WidthGuard src1093.bank 179730 2308 src1093.reserve := requestWidth (by decide)

def ends1093 : List ℕ := [2308, 2309, 2313]

theorem inside1093 : Research6966.TerminalBanks.inside src1093.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1093 : Cover (Triangular src1093) 2313 2308 ends1093 := triangleCover (by decide +kernel)

def src1094 : Request := ⟨⟨⟨3965,5506,1213,40085⟩,1893061344362496,25562434272925⟩,85,3,1,385979,38⟩

theorem rank1094 : P3_7_1.BankOK src1094.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3965_5506_1213 40085

theorem width1094 : Lower6960.HelperSource.WidthGuard src1094.bank 179730 2308 src1094.reserve := requestWidth (by decide)

def ends1094 : List ℕ := [2308, 2309, 2313]




theorem cover1094 : Cover (Triangular src1094) 2313 2308 ends1094 := triangleCover (by decide +kernel)

def src1095 : Request := ⟨⟨⟨5733,7950,1796,91474⟩,5824240852664320,113242283843565⟩,145,3,1,385979,38⟩

theorem rank1095 : P3_7_1.BankOK src1095.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5733_7950_1796 91474

theorem width1095 : Lower6960.HelperSource.WidthGuard src1095.bank 179730 2308 src1095.reserve := requestWidth (by decide)

def ends1095 : List ℕ := [2308, 2309, 2313]




theorem cover1095 : Cover (Triangular src1095) 2313 2308 ends1095 := triangleCover (by decide +kernel)

def src1096 : Request := ⟨⟨⟨8348,11577,2615,81311⟩,17976439182721024,509018341309343⟩,190,3,1,385979,38⟩

theorem rank1096 : P3_7_1.BankOK src1096.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8348_11577_2615 81311

theorem width1096 : Lower6960.HelperSource.WidthGuard src1096.bank 179730 2308 src1096.reserve := requestWidth (by decide)

def ends1096 : List ℕ := [2308, 2313]



theorem cover1096 : Cover (Triangular src1096) 2313 2308 ends1096 := triangleCover (by decide +kernel)

def src1097 : Request := ⟨⟨⟨401,558,126,4282⟩,2019210559488,2785382344⟩,0,3,1,385979,39⟩

theorem rank1097 : P3_7_1.BankOK src1097.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_126 4282

theorem width1097 : Lower6960.HelperSource.WidthGuard src1097.bank 179730 2308 src1097.reserve := requestWidth (by decide)

def ends1097 : List ℕ := [2308, 2313]

theorem inside1097 : Research6966.TerminalBanks.inside src1097.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1097 : Cover (Triangular src1097) 2313 2308 ends1097 := triangleCover (by decide +kernel)

def src1098 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,3,1,385979,39⟩

theorem rank1098 : P3_7_1.BankOK src1098.bank := by
  simpa only [src1098, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4817

theorem width1098 : Lower6960.HelperSource.WidthGuard src1098.bank 179730 2308 src1098.reserve := requestWidth (by decide)

def ends1098 : List ℕ := [2313]

theorem inside1098 : Research6966.TerminalBanks.inside src1098.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1098 : Cover (Triangular src1098) 2313 2308 ends1098 := triangleCover (by decide +kernel)

def src1099 : Request := ⟨⟨⟨471,655,144,5419⟩,3199755878400,5168862572⟩,2,3,1,385979,39⟩

theorem rank1099 : P3_7_1.BankOK src1099.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 5419

theorem width1099 : Lower6960.HelperSource.WidthGuard src1099.bank 179730 2308 src1099.reserve := requestWidth (by decide)

def ends1099 : List ℕ := [2308, 2313]

theorem inside1099 : Research6966.TerminalBanks.inside src1099.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1099 : Cover (Triangular src1099) 2313 2308 ends1099 := triangleCover (by decide +kernel)

def src11 : Request := ⟨⟨⟨2311,3204,724,34283⟩,381967532032000,2992689220368⟩,150,1,1,128659,129⟩

theorem rank11 : P3_7_1.BankOK src11.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2311_3204_724 34283

theorem width11 : Lower6960.HelperSource.WidthGuard src11.bank 179730 2308 src11.reserve := requestWidth (by decide)

def ends11 : List ℕ := [2308, 2309, 2313]

theorem inside11 : Research6966.TerminalBanks.inside src11.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover11 : Cover (Triangular src11) 2313 2308 ends11 := triangleCover (by decide +kernel)

def src110 : Request := ⟨⟨⟨2588,3593,793,31694⟩,527385327042560,4645717944219⟩,85,2,1,285209,53⟩

theorem rank110 : P3_7_1.BankOK src110.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 31694

theorem width110 : Lower6960.HelperSource.WidthGuard src110.bank 179730 2308 src110.reserve := requestWidth (by decide)

def ends110 : List ℕ := [2308, 2309, 2313]

theorem inside110 : Research6966.TerminalBanks.inside src110.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover110 : Cover (Triangular src110) 2313 2308 ends110 := triangleCover (by decide +kernel)

def src1100 : Request := ⟨⟨⟨561,781,172,5419⟩,5409683537920,10440670587⟩,3,3,1,385979,39⟩

theorem rank1100 : P3_7_1.BankOK src1100.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 5419

theorem width1100 : Lower6960.HelperSource.WidthGuard src1100.bank 179730 2308 src1100.reserve := requestWidth (by decide)

def ends1100 : List ℕ := [2308, 2313]

theorem inside1100 : Research6966.TerminalBanks.inside src1100.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1100 : Cover (Triangular src1100) 2313 2308 ends1100 := triangleCover (by decide +kernel)

def src1101 : Request := ⟨⟨⟨561,781,172,6096⟩,5409683537920,10440670587⟩,4,3,1,385979,39⟩

theorem rank1101 : P3_7_1.BankOK src1101.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 6096

theorem width1101 : Lower6960.HelperSource.WidthGuard src1101.bank 179730 2308 src1101.reserve := requestWidth (by decide)

def ends1101 : List ℕ := [2308, 2313]

theorem inside1101 : Research6966.TerminalBanks.inside src1101.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1101 : Cover (Triangular src1101) 2313 2308 ends1101 := triangleCover (by decide +kernel)

def src1102 : Request := ⟨⟨⟨692,962,217,7715⟩,10311018217472,24434817260⟩,8,3,1,385979,39⟩

theorem rank1102 : P3_7_1.BankOK src1102.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_217 7715

theorem width1102 : Lower6960.HelperSource.WidthGuard src1102.bank 179730 2308 src1102.reserve := requestWidth (by decide)

def ends1102 : List ℕ := [2308, 2313]

theorem inside1102 : Research6966.TerminalBanks.inside src1102.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1102 : Cover (Triangular src1102) 2313 2308 ends1102 := triangleCover (by decide +kernel)

def src1103 : Request := ⟨⟨⟨1452,2022,457,13899⟩,95183734833152,475487789910⟩,25,3,1,385979,39⟩

theorem rank1103 : P3_7_1.BankOK src1103.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1452_2022_457 13899

theorem width1103 : Lower6960.HelperSource.WidthGuard src1103.bank 179730 2308 src1103.reserve := requestWidth (by decide)

def ends1103 : List ℕ := [2309, 2313]

theorem inside1103 : Research6966.TerminalBanks.inside src1103.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1103 : Cover (Triangular src1103) 2313 2308 ends1103 := triangleCover (by decide +kernel)

def src1104 : Request := ⟨⟨⟨2008,2789,614,27618⟩,246075572879360,1684443651648⟩,45,3,1,385979,39⟩

theorem rank1104 : P3_7_1.BankOK src1104.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2008_2789_614 27618

theorem width1104 : Lower6960.HelperSource.WidthGuard src1104.bank 179730 2308 src1104.reserve := requestWidth (by decide)

def ends1104 : List ℕ := [2308, 2309, 2313]

theorem inside1104 : Research6966.TerminalBanks.inside src1104.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1104 : Cover (Triangular src1104) 2313 2308 ends1104 := triangleCover (by decide +kernel)

def src1105 : Request := ⟨⟨⟨2789,3873,854,30964⟩,659623697448960,6266506033362⟩,63,3,1,385979,39⟩

theorem rank1105 : P3_7_1.BankOK src1105.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 30964

theorem width1105 : Lower6960.HelperSource.WidthGuard src1105.bank 179730 2308 src1105.reserve := requestWidth (by decide)

def ends1105 : List ℕ := [2308, 2309, 2313]

theorem inside1105 : Research6966.TerminalBanks.inside src1105.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1105 : Cover (Triangular src1105) 2313 2308 ends1105 := triangleCover (by decide +kernel)

def src1106 : Request := ⟨⟨⟨4800,6695,1474,50764⟩,3367547627110400,55837558620681⟩,110,3,1,385979,39⟩

theorem rank1106 : P3_7_1.BankOK src1106.bank := by
  simpa only [src1106, _root_.Research6969.TransitionBanks.bank324] using _root_.Research6969.TransitionBanks.rank324 50764

theorem width1106 : Lower6960.HelperSource.WidthGuard src1106.bank 179730 2308 src1106.reserve := requestWidth (by decide)

def ends1106 : List ℕ := [2308, 2313]



theorem cover1106 : Cover (Triangular src1106) 2313 2308 ends1106 := triangleCover (by decide +kernel)

def src1107 : Request := ⟨⟨⟨5717,7950,1750,72277⟩,5675091598508032,110980791054694⟩,145,3,1,385979,39⟩

theorem rank1107 : P3_7_1.BankOK src1107.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5717_7950_1750 72277

theorem width1107 : Lower6960.HelperSource.WidthGuard src1107.bank 179730 2308 src1107.reserve := requestWidth (by decide)

def ends1107 : List ℕ := [2308, 2309, 2313]




theorem cover1107 : Cover (Triangular src1107) 2313 2308 ends1107 := triangleCover (by decide +kernel)

def src1108 : Request := ⟨⟨⟨8301,11577,2548,81311⟩,17404404995719168,498847383098023⟩,190,3,1,385979,39⟩

theorem rank1108 : P3_7_1.BankOK src1108.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8301_11577_2548 81311

theorem width1108 : Lower6960.HelperSource.WidthGuard src1108.bank 179730 2308 src1108.reserve := requestWidth (by decide)

def ends1108 : List ℕ := [2308, 2309, 2313]




theorem cover1108 : Cover (Triangular src1108) 2313 2308 ends1108 := triangleCover (by decide +kernel)

def src1109 : Request := ⟨⟨⟨10005,13948,3150,102908⟩,31062458345717760,1072221490229155⟩,245,3,1,385979,39⟩

theorem rank1109 : P3_7_1.BankOK src1109.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10005_13948_3150 102908

theorem width1109 : Lower6960.HelperSource.WidthGuard src1109.bank 179730 2308 src1109.reserve := requestWidth (by decide)

def ends1109 : List ℕ := [2308, 2309, 2313]




theorem cover1109 : Cover (Triangular src1109) 2313 2308 ends1109 := triangleCover (by decide +kernel)

def src111 : Request := ⟨⟨⟨2612,3625,819,27821⟩,551730216960000,4901614794409⟩,85,2,1,285209,53⟩

theorem rank111 : P3_7_1.BankOK src111.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3625_819 27821

theorem width111 : Lower6960.HelperSource.WidthGuard src111.bank 179730 2308 src111.reserve := requestWidth (by decide)

def ends111 : List ℕ := [2308, 2309, 2313]

theorem inside111 : Research6966.TerminalBanks.inside src111.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover111 : Cover (Triangular src111) 2313 2308 ends111 := triangleCover (by decide +kernel)

def src1110 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,0,3,1,385979,40⟩

theorem rank1110 : P3_7_1.BankOK src1110.bank := by
  simpa only [src1110, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4282

theorem width1110 : Lower6960.HelperSource.WidthGuard src1110.bank 179730 2308 src1110.reserve := requestWidth (by decide)

def ends1110 : List ℕ := [2313]

theorem inside1110 : Research6966.TerminalBanks.inside src1110.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1110 : Cover (Triangular src1110) 2313 2308 ends1110 := triangleCover (by decide +kernel)

def src1111 : Request := ⟨⟨⟨471,655,148,4282⟩,3266464186368,5279398867⟩,1,3,1,385979,40⟩

theorem rank1111 : P3_7_1.BankOK src1111.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 4282

theorem width1111 : Lower6960.HelperSource.WidthGuard src1111.bank 179730 2308 src1111.reserve := requestWidth (by decide)

def ends1111 : List ℕ := [2313]

theorem inside1111 : Research6966.TerminalBanks.inside src1111.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1111 : Cover (Triangular src1111) 2313 2308 ends1111 := triangleCover (by decide +kernel)

def src1112 : Request := ⟨⟨⟨471,655,148,4817⟩,3266464186368,5279398867⟩,2,3,1,385979,40⟩

theorem rank1112 : P3_7_1.BankOK src1112.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 4817

theorem width1112 : Lower6960.HelperSource.WidthGuard src1112.bank 179730 2308 src1112.reserve := requestWidth (by decide)

def ends1112 : List ℕ := [2313]

theorem inside1112 : Research6966.TerminalBanks.inside src1112.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1112 : Cover (Triangular src1112) 2313 2308 ends1112 := triangleCover (by decide +kernel)

def src1113 : Request := ⟨⟨⟨561,781,169,5419⟩,5338156236800,10299257375⟩,3,3,1,385979,40⟩

theorem rank1113 : P3_7_1.BankOK src1113.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_169 5419

theorem width1113 : Lower6960.HelperSource.WidthGuard src1113.bank 179730 2308 src1113.reserve := requestWidth (by decide)

def ends1113 : List ℕ := [2308, 2313]

theorem inside1113 : Research6966.TerminalBanks.inside src1113.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1113 : Cover (Triangular src1113) 2313 2308 ends1113 := triangleCover (by decide +kernel)

def src1114 : Request := ⟨⟨⟨562,781,176,5419⟩,5526256353280,10627925923⟩,4,3,1,385979,40⟩

theorem rank1114 : P3_7_1.BankOK src1114.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 5419

theorem width1114 : Lower6960.HelperSource.WidthGuard src1114.bank 179730 2308 src1114.reserve := requestWidth (by decide)

def ends1114 : List ℕ := [2308, 2313]

theorem inside1114 : Research6966.TerminalBanks.inside src1114.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1114 : Cover (Triangular src1114) 2313 2308 ends1114 := triangleCover (by decide +kernel)

def src1115 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,8,3,1,385979,40⟩

theorem rank1115 : P3_7_1.BankOK src1115.bank := by
  simpa only [src1115, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 7715

theorem width1115 : Lower6960.HelperSource.WidthGuard src1115.bank 179730 2308 src1115.reserve := requestWidth (by decide)

def ends1115 : List ℕ := [2313]

theorem inside1115 : Research6966.TerminalBanks.inside src1115.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1115 : Cover (Triangular src1115) 2313 2308 ends1115 := triangleCover (by decide +kernel)

def src1116 : Request := ⟨⟨⟨827,1151,253,10983⟩,17254793609216,49010625289⟩,13,3,1,385979,40⟩

theorem rank1116 : P3_7_1.BankOK src1116.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_253 10983

theorem width1116 : Lower6960.HelperSource.WidthGuard src1116.bank 179730 2308 src1116.reserve := requestWidth (by decide)

def ends1116 : List ℕ := [2308, 2309, 2313]

theorem inside1116 : Research6966.TerminalBanks.inside src1116.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1116 : Cover (Triangular src1116) 2313 2308 ends1116 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources06

section Pack_R6970Height2313CommonSources07

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1117 : Request := ⟨⟨⟨1200,1674,368,12355⟩,52718727069696,218807905514⟩,20,3,1,385979,40⟩

theorem rank1117 : P3_7_1.BankOK src1117.bank := by
  simpa only [src1117, _root_.Research6969.TransitionBanks.bank228] using _root_.Research6969.TransitionBanks.rank228 12355

theorem width1117 : Lower6960.HelperSource.WidthGuard src1117.bank 179730 2308 src1117.reserve := requestWidth (by decide)

def ends1117 : List ℕ := [2313]

theorem inside1117 : Research6966.TerminalBanks.inside src1117.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1117 : Cover (Triangular src1117) 2313 2308 ends1117 := triangleCover (by decide +kernel)

def src1118 : Request := ⟨⟨⟨1757,2441,551,22261⟩,168093600972800,1008217465165⟩,40,3,1,385979,40⟩

theorem rank1118 : P3_7_1.BankOK src1118.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2441_551 22261

theorem width1118 : Lower6960.HelperSource.WidthGuard src1118.bank 179730 2308 src1118.reserve := requestWidth (by decide)

def ends1118 : List ℕ := [2308, 2309, 2313]

theorem inside1118 : Research6966.TerminalBanks.inside src1118.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1118 : Cover (Triangular src1118) 2313 2308 ends1118 := triangleCover (by decide +kernel)

def src1119 : Request := ⟨⟨⟨2607,3626,793,35655⟩,536091608743936,4784491173220⟩,63,3,1,385979,40⟩

theorem rank1119 : P3_7_1.BankOK src1119.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3626_793 35655

theorem width1119 : Lower6960.HelperSource.WidthGuard src1119.bank 179730 2308 src1119.reserve := requestWidth (by decide)

def ends1119 : List ℕ := [2308, 2309, 2313]

theorem inside1119 : Research6966.TerminalBanks.inside src1119.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1119 : Cover (Triangular src1119) 2313 2308 ends1119 := triangleCover (by decide +kernel)

def src112 : Request := ⟨⟨⟨2588,3593,793,31219⟩,527385327042560,4645717944219⟩,85,2,1,287630,53⟩

theorem rank112 : P3_7_1.BankOK src112.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 31219

theorem width112 : Lower6960.HelperSource.WidthGuard src112.bank 179730 2308 src112.reserve := requestWidth (by decide)

def ends112 : List ℕ := [2308, 2309, 2313]

theorem inside112 : Research6966.TerminalBanks.inside src112.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover112 : Cover (Triangular src112) 2313 2308 ends112 := triangleCover (by decide +kernel)

def src1120 : Request := ⟨⟨⟨2816,3905,882,27436⟩,690700839813120,6598128215989⟩,63,3,1,385979,40⟩

theorem rank1120 : P3_7_1.BankOK src1120.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 27436

theorem width1120 : Lower6960.HelperSource.WidthGuard src1120.bank 179730 2308 src1120.reserve := requestWidth (by decide)

def ends1120 : List ℕ := [2308, 2313]

theorem inside1120 : Research6966.TerminalBanks.inside src1120.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1120 : Cover (Triangular src1120) 2313 2308 ends1120 := triangleCover (by decide +kernel)

def src1121 : Request := ⟨⟨⟨5717,7950,1750,64247⟩,5675091598508032,110980791054694⟩,145,3,1,385979,40⟩

theorem rank1121 : P3_7_1.BankOK src1121.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5717_7950_1750 64247

theorem width1121 : Lower6960.HelperSource.WidthGuard src1121.bank 179730 2308 src1121.reserve := requestWidth (by decide)

def ends1121 : List ℕ := [2309, 2313]



theorem cover1121 : Cover (Triangular src1121) 2313 2308 ends1121 := triangleCover (by decide +kernel)

def src1122 : Request := ⟨⟨⟨6939,9623,2174,91474⟩,10326467844505600,243058712908678⟩,190,3,1,385979,40⟩

theorem rank1122 : P3_7_1.BankOK src1122.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6939_9623_2174 91474

theorem width1122 : Lower6960.HelperSource.WidthGuard src1122.bank 179730 2308 src1122.reserve := requestWidth (by decide)

def ends1122 : List ℕ := [2309, 2313]



theorem cover1122 : Cover (Triangular src1122) 2313 2308 ends1122 := triangleCover (by decide +kernel)

def src1123 : Request := ⟨⟨⟨401,558,126,3807⟩,2019210559488,2785382344⟩,0,3,1,385979,41⟩

theorem rank1123 : P3_7_1.BankOK src1123.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_126 3807

theorem width1123 : Lower6960.HelperSource.WidthGuard src1123.bank 179730 2308 src1123.reserve := requestWidth (by decide)

def ends1123 : List ℕ := [2313]

theorem inside1123 : Research6966.TerminalBanks.inside src1123.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1123 : Cover (Triangular src1123) 2313 2308 ends1123 := triangleCover (by decide +kernel)

def src1124 : Request := ⟨⟨⟨470,655,144,4282⟩,3184589537280,5168862572⟩,1,3,1,385979,41⟩

theorem rank1124 : P3_7_1.BankOK src1124.bank := by
  simpa only [src1124, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4282

theorem width1124 : Lower6960.HelperSource.WidthGuard src1124.bank 179730 2308 src1124.reserve := requestWidth (by decide)

def ends1124 : List ℕ := [2313]

theorem inside1124 : Research6966.TerminalBanks.inside src1124.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1124 : Cover (Triangular src1124) 2313 2308 ends1124 := triangleCover (by decide +kernel)

def src1125 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,2,3,1,385979,41⟩

theorem rank1125 : P3_7_1.BankOK src1125.bank := by
  simpa only [src1125, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4817

theorem width1125 : Lower6960.HelperSource.WidthGuard src1125.bank 179730 2308 src1125.reserve := requestWidth (by decide)

def ends1125 : List ℕ := [2313]

theorem inside1125 : Research6966.TerminalBanks.inside src1125.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1125 : Cover (Triangular src1125) 2313 2308 ends1125 := triangleCover (by decide +kernel)

def src1126 : Request := ⟨⟨⟨472,655,144,5419⟩,3214960230400,5168862572⟩,3,3,1,385979,41⟩

theorem rank1126 : P3_7_1.BankOK src1126.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_472_655_144 5419

theorem width1126 : Lower6960.HelperSource.WidthGuard src1126.bank 179730 2308 src1126.reserve := requestWidth (by decide)

def ends1126 : List ℕ := [2309, 2313]

theorem inside1126 : Research6966.TerminalBanks.inside src1126.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1126 : Cover (Triangular src1126) 2313 2308 ends1126 := triangleCover (by decide +kernel)

def src1127 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,4,3,1,385979,41⟩

theorem rank1127 : P3_7_1.BankOK src1127.bank := by
  simpa only [src1127, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 5419

theorem width1127 : Lower6960.HelperSource.WidthGuard src1127.bank 179730 2308 src1127.reserve := requestWidth (by decide)

def ends1127 : List ℕ := [2308, 2313]

theorem inside1127 : Research6966.TerminalBanks.inside src1127.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1127 : Cover (Triangular src1127) 2313 2308 ends1127 := triangleCover (by decide +kernel)

def src1128 : Request := ⟨⟨⟨562,781,176,6858⟩,5526256353280,10627925923⟩,6,3,1,385979,41⟩

theorem rank1128 : P3_7_1.BankOK src1128.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 6858

theorem width1128 : Lower6960.HelperSource.WidthGuard src1128.bank 179730 2308 src1128.reserve := requestWidth (by decide)

def ends1128 : List ℕ := [2308, 2313]

theorem inside1128 : Research6966.TerminalBanks.inside src1128.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1128 : Cover (Triangular src1128) 2313 2308 ends1128 := triangleCover (by decide +kernel)

def src1129 : Request := ⟨⟨⟨692,962,217,8679⟩,10311018217472,24434817260⟩,10,3,1,385979,41⟩

theorem rank1129 : P3_7_1.BankOK src1129.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_217 8679

theorem width1129 : Lower6960.HelperSource.WidthGuard src1129.bank 179730 2308 src1129.reserve := requestWidth (by decide)

def ends1129 : List ℕ := [2308, 2309, 2313]

theorem inside1129 : Research6966.TerminalBanks.inside src1129.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1129 : Cover (Triangular src1129) 2313 2308 ends1129 := triangleCover (by decide +kernel)

def src113 : Request := ⟨⟨⟨2612,3625,819,27738⟩,551730216960000,4901614794409⟩,85,2,1,287630,53⟩

theorem rank113 : P3_7_1.BankOK src113.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3625_819 27738

theorem width113 : Lower6960.HelperSource.WidthGuard src113.bank 179730 2308 src113.reserve := requestWidth (by decide)

def ends113 : List ℕ := [2308, 2309, 2313]

theorem inside113 : Research6966.TerminalBanks.inside src113.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover113 : Cover (Triangular src113) 2313 2308 ends113 := triangleCover (by decide +kernel)

def src1130 : Request := ⟨⟨⟨1005,1395,307,9763⟩,30900543815680,105715278267⟩,16,3,1,385979,41⟩

theorem rank1130 : P3_7_1.BankOK src1130.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1005_1395_307 9763

theorem width1130 : Lower6960.HelperSource.WidthGuard src1130.bank 179730 2308 src1130.reserve := requestWidth (by decide)

def ends1130 : List ℕ := [2308, 2309, 2313]

theorem inside1130 : Research6966.TerminalBanks.inside src1130.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1130 : Cover (Triangular src1130) 2313 2308 ends1130 := triangleCover (by decide +kernel)

def src1131 : Request := ⟨⟨⟨1452,2022,457,17590⟩,95183734833152,475487789910⟩,32,3,1,385979,41⟩

theorem rank1131 : P3_7_1.BankOK src1131.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1452_2022_457 17590

theorem width1131 : Lower6960.HelperSource.WidthGuard src1131.bank 179730 2308 src1131.reserve := requestWidth (by decide)

def ends1131 : List ℕ := [2308, 2309, 2313]

theorem inside1131 : Research6966.TerminalBanks.inside src1131.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1131 : Cover (Triangular src1131) 2313 2308 ends1131 := triangleCover (by decide +kernel)

def src1132 : Request := ⟨⟨⟨2600,3626,793,31694⟩,532875289296896,4784491173220⟩,63,3,1,385979,41⟩

theorem rank1132 : P3_7_1.BankOK src1132.bank := by
  simpa only [src1132, _root_.Research6969.TerminalAuxBanks.bank48] using _root_.Research6969.PackedRanks.TerminalRanks48To51.rank48 31694

theorem width1132 : Lower6960.HelperSource.WidthGuard src1132.bank 179730 2308 src1132.reserve := requestWidth (by decide)

def ends1132 : List ℕ := [2308, 2313]

theorem inside1132 : Research6966.TerminalBanks.inside src1132.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1132 : Cover (Triangular src1132) 2313 2308 ends1132 := triangleCover (by decide +kernel)

def src1133 : Request := ⟨⟨⟨2614,3626,819,27309⟩,552677752176640,4905972788959⟩,63,3,1,385979,41⟩

theorem rank1133 : P3_7_1.BankOK src1133.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3626_819 27309

theorem width1133 : Lower6960.HelperSource.WidthGuard src1133.bank 179730 2308 src1133.reserve := requestWidth (by decide)

def ends1133 : List ℕ := [2309, 2313]

theorem inside1133 : Research6966.TerminalBanks.inside src1133.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1133 : Cover (Triangular src1133) 2313 2308 ends1133 := triangleCover (by decide +kernel)

def src1134 : Request := ⟨⟨⟨2609,3626,798,31694⟩,539583537479680,4807957255301⟩,65,3,1,385979,41⟩

theorem rank1134 : P3_7_1.BankOK src1134.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2609_3626_798 31694

theorem width1134 : Lower6960.HelperSource.WidthGuard src1134.bank 179730 2308 src1134.reserve := requestWidth (by decide)

def ends1134 : List ℕ := [2308, 2309, 2313]

theorem inside1134 : Research6966.TerminalBanks.inside src1134.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1134 : Cover (Triangular src1134) 2313 2308 ends1134 := triangleCover (by decide +kernel)

def src1135 : Request := ⟨⟨⟨6907,9623,2174,81311⟩,10219979603968000,243058712908678⟩,190,3,1,385979,41⟩

theorem rank1135 : P3_7_1.BankOK src1135.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6907_9623_2174 81311

theorem width1135 : Lower6960.HelperSource.WidthGuard src1135.bank 179730 2308 src1135.reserve := requestWidth (by decide)

def ends1135 : List ℕ := [2308, 2309, 2313]




theorem cover1135 : Cover (Triangular src1135) 2313 2308 ends1135 := triangleCover (by decide +kernel)

def src1136 : Request := ⟨⟨⟨2312,3207,724,31694⟩,382338138112000,3001726552718⟩,63,3,1,385979,43⟩

theorem rank1136 : P3_7_1.BankOK src1136.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 31694

theorem width1136 : Lower6960.HelperSource.WidthGuard src1136.bank 179730 2308 src1136.reserve := requestWidth (by decide)

def ends1136 : List ℕ := [2308, 2309, 2313]

theorem inside1136 : Research6966.TerminalBanks.inside src1136.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1136 : Cover (Triangular src1136) 2313 2308 ends1136 := triangleCover (by decide +kernel)

def src1137 : Request := ⟨⟨⟨2614,3626,819,24442⟩,552677752176640,4905972788959⟩,63,3,1,385979,43⟩

theorem rank1137 : P3_7_1.BankOK src1137.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3626_819 24442

theorem width1137 : Lower6960.HelperSource.WidthGuard src1137.bank 179730 2308 src1137.reserve := requestWidth (by decide)

def ends1137 : List ℕ := [2308, 2313]

theorem inside1137 : Research6966.TerminalBanks.inside src1137.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1137 : Cover (Triangular src1137) 2313 2308 ends1137 := triangleCover (by decide +kernel)

def src1138 : Request := ⟨⟨⟨2300,3207,702,28173⟩,369170633195520,2930605494152⟩,63,3,1,385979,45⟩

theorem rank1138 : P3_7_1.BankOK src1138.bank := by
  simpa only [src1138, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 28173

theorem width1138 : Lower6960.HelperSource.WidthGuard src1138.bank 179730 2308 src1138.reserve := requestWidth (by decide)

def ends1138 : List ℕ := [2308, 2313]

theorem inside1138 : Research6966.TerminalBanks.inside src1138.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1138 : Cover (Triangular src1138) 2313 2308 ends1138 := triangleCover (by decide +kernel)

def src1139 : Request := ⟨⟨⟨2312,3207,724,24192⟩,382338138112000,3001726552718⟩,63,3,1,385979,45⟩

theorem rank1139 : P3_7_1.BankOK src1139.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 24192

theorem width1139 : Lower6960.HelperSource.WidthGuard src1139.bank 179730 2308 src1139.reserve := requestWidth (by decide)

def ends1139 : List ℕ := [2309, 2313]

theorem inside1139 : Research6966.TerminalBanks.inside src1139.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1139 : Cover (Triangular src1139) 2313 2308 ends1139 := triangleCover (by decide +kernel)

def src114 : Request := ⟨⟨⟨2816,3909,882,31761⟩,690700839813120,6619929415349⟩,85,2,1,288407,49⟩

theorem rank114 : P3_7_1.BankOK src114.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3909_882 31761

theorem width114 : Lower6960.HelperSource.WidthGuard src114.bank 179730 2308 src114.reserve := requestWidth (by decide)

def ends114 : List ℕ := [2308, 2309, 2313]

theorem inside114 : Research6966.TerminalBanks.inside src114.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover114 : Cover (Triangular src114) 2313 2308 ends114 := triangleCover (by decide +kernel)

def src1140 : Request := ⟨⟨⟨2805,3905,854,35655⟩,668124618424320,6434729640882⟩,85,3,1,385979,47⟩

theorem rank1140 : P3_7_1.BankOK src1140.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3905_854 35655

theorem width1140 : Lower6960.HelperSource.WidthGuard src1140.bank 179730 2308 src1140.reserve := requestWidth (by decide)

def ends1140 : List ℕ := [2308, 2309, 2313]

theorem inside1140 : Research6966.TerminalBanks.inside src1140.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1140 : Cover (Triangular src1140) 2313 2308 ends1140 := triangleCover (by decide +kernel)

def src1141 : Request := ⟨⟨⟨2816,3905,882,30635⟩,690700839813120,6598128215989⟩,85,3,1,385979,47⟩

theorem rank1141 : P3_7_1.BankOK src1141.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 30635

theorem width1141 : Lower6960.HelperSource.WidthGuard src1141.bank 179730 2308 src1141.reserve := requestWidth (by decide)

def ends1141 : List ℕ := [2309, 2313]

theorem inside1141 : Research6966.TerminalBanks.inside src1141.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1141 : Cover (Triangular src1141) 2313 2308 ends1141 := triangleCover (by decide +kernel)

def src1142 : Request := ⟨⟨⟨2603,3625,819,35655⟩,547476948910080,4901614794409⟩,85,3,1,385979,49⟩

theorem rank1142 : P3_7_1.BankOK src1142.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3625_819 35655

theorem width1142 : Lower6960.HelperSource.WidthGuard src1142.bank 179730 2308 src1142.reserve := requestWidth (by decide)

def ends1142 : List ℕ := [2308, 2309, 2313]

theorem inside1142 : Research6966.TerminalBanks.inside src1142.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1142 : Cover (Triangular src1142) 2313 2308 ends1142 := triangleCover (by decide +kernel)

def src1143 : Request := ⟨⟨⟨2816,3905,882,27582⟩,690700839813120,6598128215989⟩,85,3,1,385979,49⟩

theorem rank1143 : P3_7_1.BankOK src1143.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 27582

theorem width1143 : Lower6960.HelperSource.WidthGuard src1143.bank 179730 2308 src1143.reserve := requestWidth (by decide)

def ends1143 : List ℕ := [2308, 2313]

theorem inside1143 : Research6966.TerminalBanks.inside src1143.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1143 : Cover (Triangular src1143) 2313 2308 ends1143 := triangleCover (by decide +kernel)

def src1144 : Request := ⟨⟨⟨2287,3175,702,27467⟩,364515722002432,2837502581224⟩,85,3,1,385979,57⟩

theorem rank1144 : P3_7_1.BankOK src1144.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2287_3175_702 27467

theorem width1144 : Lower6960.HelperSource.WidthGuard src1144.bank 179730 2308 src1144.reserve := requestWidth (by decide)

def ends1144 : List ℕ := [2308, 2309, 2313]

theorem inside1144 : Research6966.TerminalBanks.inside src1144.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1144 : Cover (Triangular src1144) 2313 2308 ends1144 := triangleCover (by decide +kernel)

def src1145 : Request := ⟨⟨⟨2303,3199,702,28120⟩,370249266364416,2907137852544⟩,85,3,1,385979,57⟩

theorem rank1145 : P3_7_1.BankOK src1145.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3199_702 28120

theorem width1145 : Lower6960.HelperSource.WidthGuard src1145.bank 179730 2308 src1145.reserve := requestWidth (by decide)

def ends1145 : List ℕ := [2308, 2309, 2313]

theorem inside1145 : Research6966.TerminalBanks.inside src1145.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1145 : Cover (Triangular src1145) 2313 2308 ends1145 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources07

section Pack_R6970Height2313CommonSources10

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1203 : Request := ⟨⟨⟨555,772,170,8569⟩,5234703728640,9968090926⟩,10,3,2,437023,4⟩

theorem rank1203 : P3_7_1.BankOK src1203.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_772_170 8569

theorem width1203 : Lower6960.HelperSource.WidthGuard src1203.bank 179730 2308 src1203.reserve := requestWidth (by decide)

def ends1203 : List ℕ := [2308, 2309, 2313]

theorem inside1203 : Research6966.TerminalBanks.inside src1203.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1203 : Cover (Triangular src1203) 2313 2308 ends1203 := triangleCover (by decide +kernel)

def src1204 : Request := ⟨⟨⟨555,772,170,8677⟩,5234703728640,9968090926⟩,10,3,2,437037,3⟩

theorem rank1204 : P3_7_1.BankOK src1204.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_772_170 8677

theorem width1204 : Lower6960.HelperSource.WidthGuard src1204.bank 179730 2308 src1204.reserve := requestWidth (by decide)

def ends1204 : List ℕ := [2308, 2309, 2313]

theorem inside1204 : Research6966.TerminalBanks.inside src1204.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1204 : Cover (Triangular src1204) 2313 2308 ends1204 := triangleCover (by decide +kernel)

def src1205 : Request := ⟨⟨⟨555,772,170,8786⟩,5234703728640,9968090926⟩,10,3,2,437044,2⟩

theorem rank1205 : P3_7_1.BankOK src1205.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_772_170 8786

theorem width1205 : Lower6960.HelperSource.WidthGuard src1205.bank 179730 2308 src1205.reserve := requestWidth (by decide)

def ends1205 : List ℕ := [2308, 2309, 2313]

theorem inside1205 : Research6966.TerminalBanks.inside src1205.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1205 : Cover (Triangular src1205) 2313 2308 ends1205 := triangleCover (by decide +kernel)

def src1206 : Request := ⟨⟨⟨560,781,169,25043⟩,5316921262080,10299257375⟩,0,4,1,514639,1⟩

theorem rank1206 : P3_7_1.BankOK src1206.bank := by
  simpa only [src1206, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 25043

theorem width1206 : Lower6960.HelperSource.WidthGuard src1206.bank 179730 2308 src1206.reserve := requestWidth (by decide)

def ends1206 : List ℕ := [2308, 2313]

theorem inside1206 : Research6966.TerminalBanks.inside src1206.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1206 : Cover (Triangular src1206) 2313 2308 ends1206 := triangleCover (by decide +kernel)

def src1207 : Request := ⟨⟨⟨560,781,170,28787⟩,5340718694400,10346489473⟩,1,4,1,514639,1⟩

theorem rank1207 : P3_7_1.BankOK src1207.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_560_781_170 28787

theorem width1207 : Lower6960.HelperSource.WidthGuard src1207.bank 179730 2308 src1207.reserve := requestWidth (by decide)

def ends1207 : List ℕ := [2308, 2309, 2313]

theorem inside1207 : Research6966.TerminalBanks.inside src1207.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1207 : Cover (Triangular src1207) 2313 2308 ends1207 := triangleCover (by decide +kernel)

def src1208 : Request := ⟨⟨⟨692,962,209,28782⟩,10022400819200,23734012058⟩,2,4,1,514639,1⟩

theorem rank1208 : P3_7_1.BankOK src1208.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_209 28782

theorem width1208 : Lower6960.HelperSource.WidthGuard src1208.bank 179730 2308 src1208.reserve := requestWidth (by decide)

def ends1208 : List ℕ := [2308, 2309, 2313]

theorem inside1208 : Research6966.TerminalBanks.inside src1208.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1208 : Cover (Triangular src1208) 2313 2308 ends1208 := triangleCover (by decide +kernel)

def src1209 : Request := ⟨⟨⟨560,781,169,45124⟩,5316921262080,10299257375⟩,3,4,1,514639,1⟩

theorem rank1209 : P3_7_1.BankOK src1209.bank := by
  simpa only [src1209, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 45124

theorem width1209 : Lower6960.HelperSource.WidthGuard src1209.bank 179730 2308 src1209.reserve := requestWidth (by decide)

def ends1209 : List ℕ := [2308, 2313]

theorem inside1209 : Research6966.TerminalBanks.inside src1209.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1209 : Cover (Triangular src1209) 2313 2308 ends1209 := triangleCover (by decide +kernel)

def src121 : Request := ⟨⟨⟨2813,3905,882,31694⟩,689052288024576,6598128215989⟩,85,2,1,290650,49⟩

theorem rank121 : P3_7_1.BankOK src121.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2813_3905_882 31694

theorem width121 : Lower6960.HelperSource.WidthGuard src121.bank 179730 2308 src121.reserve := requestWidth (by decide)

def ends121 : List ℕ := [2308, 2309, 2313]

theorem inside121 : Research6966.TerminalBanks.inside src121.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover121 : Cover (Triangular src121) 2313 2308 ends121 := triangleCover (by decide +kernel)

def src1210 : Request := ⟨⟨⟨692,962,209,32442⟩,10022400819200,23734012058⟩,3,4,1,514639,1⟩

theorem rank1210 : P3_7_1.BankOK src1210.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_209 32442

theorem width1210 : Lower6960.HelperSource.WidthGuard src1210.bank 179730 2308 src1210.reserve := requestWidth (by decide)

def ends1210 : List ℕ := [2308, 2309, 2313]

theorem inside1210 : Research6966.TerminalBanks.inside src1210.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1210 : Cover (Triangular src1210) 2313 2308 ends1210 := triangleCover (by decide +kernel)

def src1211 : Request := ⟨⟨⟨828,1151,250,40385⟩,17145746161664,48558751904⟩,6,4,1,514639,1⟩

theorem rank1211 : P3_7_1.BankOK src1211.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_250 40385

theorem width1211 : Lower6960.HelperSource.WidthGuard src1211.bank 179730 2308 src1211.reserve := requestWidth (by decide)

def ends1211 : List ℕ := [2308, 2309, 2313]

theorem inside1211 : Research6966.TerminalBanks.inside src1211.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1211 : Cover (Triangular src1211) 2313 2308 ends1211 := triangleCover (by decide +kernel)

def src1212 : Request := ⟨⟨⟨1205,1674,368,45700⟩,53211572207616,218807905514⟩,10,4,1,515031,1⟩

theorem rank1212 : P3_7_1.BankOK src1212.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 45700

theorem width1212 : Lower6960.HelperSource.WidthGuard src1212.bank 179730 2308 src1212.reserve := requestWidth (by decide)

def ends1212 : List ℕ := [2308, 2309, 2313]

theorem inside1212 : Research6966.TerminalBanks.inside src1212.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1212 : Cover (Triangular src1212) 2313 2308 ends1212 := triangleCover (by decide +kernel)

def src1213 : Request := ⟨⟨⟨1456,2023,445,51958⟩,93862507577344,466511127281⟩,13,4,1,515031,1⟩

theorem rank1213 : P3_7_1.BankOK src1213.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 51958

theorem width1213 : Lower6960.HelperSource.WidthGuard src1213.bank 179730 2308 src1213.reserve := requestWidth (by decide)

def ends1213 : List ℕ := [2308, 2309, 2313]

theorem inside1213 : Research6966.TerminalBanks.inside src1213.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1213 : Cover (Triangular src1213) 2313 2308 ends1213 := triangleCover (by decide +kernel)

def src1214 : Request := ⟨⟨⟨2100,2922,632,81221⟩,278060332482560,2001435395356⟩,25,4,1,514639,1⟩

theorem rank1214 : P3_7_1.BankOK src1214.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2100_2922_632 81221

theorem width1214 : Lower6960.HelperSource.WidthGuard src1214.bank 179730 2308 src1214.reserve := requestWidth (by decide)

def ends1214 : List ℕ := [2308, 2309, 2313]

theorem inside1214 : Research6966.TerminalBanks.inside src1214.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1214 : Cover (Triangular src1214) 2313 2308 ends1214 := triangleCover (by decide +kernel)

def src1215 : Request := ⟨⟨⟨2793,3882,854,132989⟩,661743548497920,6313512679932⟩,45,4,1,515031,1⟩

theorem rank1215 : P3_7_1.BankOK src1215.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2793_3882_854 132989

theorem width1215 : Lower6960.HelperSource.WidthGuard src1215.bank 179730 2308 src1215.reserve := requestWidth (by decide)

def ends1215 : List ℕ := [2308, 2309, 2313]

theorem inside1215 : Research6966.TerminalBanks.inside src1215.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1215 : Cover (Triangular src1215) 2313 2308 ends1215 := triangleCover (by decide +kernel)

def src1216 : Request := ⟨⟨⟨2588,3610,777,467488⟩,519272186249216,4642531995782⟩,61,4,1,514639,1⟩

theorem rank1216 : P3_7_1.BankOK src1216.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3610_777 467488

theorem width1216 : Lower6960.HelperSource.WidthGuard src1216.bank 179730 2308 src1216.reserve := requestWidth (by decide)

def ends1216 : List ℕ := [2308, 2309, 2313]

theorem inside1216 : Research6966.TerminalBanks.inside src1216.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1216 : Cover (Triangular src1216) 2313 2308 ends1216 := triangleCover (by decide +kernel)

def src1217 : Request := ⟨⟨⟨4819,6697,1474,166551⟩,3397470270259200,55891290082931⟩,65,4,1,515031,1⟩

theorem rank1217 : P3_7_1.BankOK src1217.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4819_6697_1474 166551

theorem width1217 : Lower6960.HelperSource.WidthGuard src1217.bank 179730 2308 src1217.reserve := requestWidth (by decide)

def ends1217 : List ℕ := [2308, 2309, 2313]




theorem cover1217 : Cover (Triangular src1217) 2313 2308 ends1217 := triangleCover (by decide +kernel)

def src1218 : Request := ⟨⟨⟨6926,9626,2118,269820⟩,10081590085419008,238415548481346⟩,110,4,1,515031,1⟩

theorem rank1218 : P3_7_1.BankOK src1218.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6926_9626_2118 269820

theorem width1218 : Lower6960.HelperSource.WidthGuard src1218.bank 179730 2308 src1218.reserve := requestWidth (by decide)

def ends1218 : List ℕ := [2308, 2309, 2313]




theorem cover1218 : Cover (Triangular src1218) 2313 2308 ends1218 := triangleCover (by decide +kernel)

def src1219 : Request := ⟨⟨⟨693,963,212,22419⟩,10163930791936,24078187611⟩,0,4,1,515031,2⟩

theorem rank1219 : P3_7_1.BankOK src1219.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_963_212 22419

theorem width1219 : Lower6960.HelperSource.WidthGuard src1219.bank 179730 2308 src1219.reserve := requestWidth (by decide)

def ends1219 : List ℕ := [2308, 2309, 2313]

theorem inside1219 : Research6966.TerminalBanks.inside src1219.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1219 : Cover (Triangular src1219) 2313 2308 ends1219 := triangleCover (by decide +kernel)

def src122 : Request := ⟨⟨⟨2596,3609,775,28025⟩,521841608228864,4629076405017⟩,85,2,1,290657,57⟩

theorem rank122 : P3_7_1.BankOK src122.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2596_3609_775 28025

theorem width122 : Lower6960.HelperSource.WidthGuard src122.bank 179730 2308 src122.reserve := requestWidth (by decide)

def ends122 : List ℕ := [2308, 2309, 2313]

theorem inside122 : Research6966.TerminalBanks.inside src122.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover122 : Cover (Triangular src122) 2313 2308 ends122 := triangleCover (by decide +kernel)

def src1220 : Request := ⟨⟨⟨687,955,208,24942⟩,9825477984256,23097088014⟩,1,4,1,514639,2⟩

theorem rank1220 : P3_7_1.BankOK src1220.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_687_955_208 24942

theorem width1220 : Lower6960.HelperSource.WidthGuard src1220.bank 179730 2308 src1220.reserve := requestWidth (by decide)

def ends1220 : List ℕ := [2308, 2309, 2313]

theorem inside1220 : Research6966.TerminalBanks.inside src1220.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1220 : Cover (Triangular src1220) 2313 2308 ends1220 := triangleCover (by decide +kernel)

def src1221 : Request := ⟨⟨⟨690,960,208,31636⟩,9921631092736,23488112384⟩,3,4,1,514639,2⟩

theorem rank1221 : P3_7_1.BankOK src1221.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_960_208 31636

theorem width1221 : Lower6960.HelperSource.WidthGuard src1221.bank 179730 2308 src1221.reserve := requestWidth (by decide)

def ends1221 : List ℕ := [2308, 2309, 2313]

theorem inside1221 : Research6966.TerminalBanks.inside src1221.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1221 : Cover (Triangular src1221) 2313 2308 ends1221 := triangleCover (by decide +kernel)

def src1222 : Request := ⟨⟨⟨1004,1395,307,40924⟩,30831793405952,105715278267⟩,8,4,1,515031,2⟩

theorem rank1222 : P3_7_1.BankOK src1222.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_307 40924

theorem width1222 : Lower6960.HelperSource.WidthGuard src1222.bank 179730 2308 src1222.reserve := requestWidth (by decide)

def ends1222 : List ℕ := [2308, 2309, 2313]

theorem inside1222 : Research6966.TerminalBanks.inside src1222.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1222 : Cover (Triangular src1222) 2313 2308 ends1222 := triangleCover (by decide +kernel)

def src1223 : Request := ⟨⟨⟨1433,1991,436,50543⟩,89183141232640,436191362606⟩,13,4,1,514639,2⟩

theorem rank1223 : P3_7_1.BankOK src1223.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1433_1991_436 50543

theorem width1223 : Lower6960.HelperSource.WidthGuard src1223.bank 179730 2308 src1223.reserve := requestWidth (by decide)

def ends1223 : List ℕ := [2308, 2309, 2313]

theorem inside1223 : Research6966.TerminalBanks.inside src1223.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1223 : Cover (Triangular src1223) 2313 2308 ends1223 := triangleCover (by decide +kernel)

def src1224 : Request := ⟨⟨⟨1757,2441,537,66028⟩,164848525115392,988269431527⟩,20,4,1,515031,2⟩

theorem rank1224 : P3_7_1.BankOK src1224.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2441_537 66028

theorem width1224 : Lower6960.HelperSource.WidthGuard src1224.bank 179730 2308 src1224.reserve := requestWidth (by decide)

def ends1224 : List ℕ := [2308, 2309, 2313]

theorem inside1224 : Research6966.TerminalBanks.inside src1224.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1224 : Cover (Triangular src1224) 2313 2308 ends1224 := triangleCover (by decide +kernel)

def src1225 : Request := ⟨⟨⟨1756,2441,537,132149⟩,164638596792320,988269431527⟩,32,4,1,515031,2⟩

theorem rank1225 : P3_7_1.BankOK src1225.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1756_2441_537 132149

theorem width1225 : Lower6960.HelperSource.WidthGuard src1225.bank 179730 2308 src1225.reserve := requestWidth (by decide)

def ends1225 : List ℕ := [2308, 2309, 2313]

theorem inside1225 : Research6966.TerminalBanks.inside src1225.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1225 : Cover (Triangular src1225) 2313 2308 ends1225 := triangleCover (by decide +kernel)

def src1226 : Request := ⟨⟨⟨2304,3203,702,94324⟩,370609179328512,2918855628076⟩,32,4,1,515031,2⟩

theorem rank1226 : P3_7_1.BankOK src1226.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2304_3203_702 94324

theorem width1226 : Lower6960.HelperSource.WidthGuard src1226.bank 179730 2308 src1226.reserve := requestWidth (by decide)

def ends1226 : List ℕ := [2308, 2309, 2313]

theorem inside1226 : Research6966.TerminalBanks.inside src1226.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1226 : Cover (Triangular src1226) 2313 2308 ends1226 := triangleCover (by decide +kernel)

def src1227 : Request := ⟨⟨⟨3921,5447,1189,130279⟩,1818515773849600,24309649468876⟩,50,4,1,514639,2⟩

theorem rank1227 : P3_7_1.BankOK src1227.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3921_5447_1189 130279

theorem width1227 : Lower6960.HelperSource.WidthGuard src1227.bank 179730 2308 src1227.reserve := requestWidth (by decide)

def ends1227 : List ℕ := [2308, 2309, 2313]




theorem cover1227 : Cover (Triangular src1227) 2313 2308 ends1227 := triangleCover (by decide +kernel)

def src1228 : Request := ⟨⟨⟨2609,3626,793,425934⟩,537012430438400,4784491173220⟩,62,4,1,514639,2⟩

theorem rank1228 : P3_7_1.BankOK src1228.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2609_3626_793 425934

theorem width1228 : Lower6960.HelperSource.WidthGuard src1228.bank 179730 2308 src1228.reserve := requestWidth (by decide)

def ends1228 : List ℕ := [2308, 2309, 2313]

theorem inside1228 : Research6966.TerminalBanks.inside src1228.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1228 : Cover (Triangular src1228) 2313 2308 ends1228 := triangleCover (by decide +kernel)

def src1229 : Request := ⟨⟨⟨5678,7888,1716,208734⟩,5505996296028160,106576249969594⟩,85,4,1,514639,2⟩

theorem rank1229 : P3_7_1.BankOK src1229.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5678_7888_1716 208734

theorem width1229 : Lower6960.HelperSource.WidthGuard src1229.bank 179730 2308 src1229.reserve := requestWidth (by decide)

def ends1229 : List ℕ := [2308, 2309, 2313]




theorem cover1229 : Cover (Triangular src1229) 2313 2308 ends1229 := triangleCover (by decide +kernel)

def src123 : Request := ⟨⟨⟨2588,3593,793,24689⟩,527385327042560,4645717944219⟩,85,2,1,290657,57⟩

theorem rank123 : P3_7_1.BankOK src123.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 24689

theorem width123 : Lower6960.HelperSource.WidthGuard src123.bank 179730 2308 src123.reserve := requestWidth (by decide)

def ends123 : List ℕ := [2308, 2309, 2313]

theorem inside123 : Research6966.TerminalBanks.inside src123.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover123 : Cover (Triangular src123) 2313 2308 ends123 := triangleCover (by decide +kernel)

def src1230 : Request := ⟨⟨⟨10000,13946,3014,342423⟩,30005043269468160,1035526291565475⟩,145,4,1,514639,2⟩

theorem rank1230 : P3_7_1.BankOK src1230.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13946_3014 342423

theorem width1230 : Lower6960.HelperSource.WidthGuard src1230.bank 179730 2308 src1230.reserve := requestWidth (by decide)

def ends1230 : List ℕ := [2308, 2309, 2313]




theorem cover1230 : Cover (Triangular src1230) 2313 2308 ends1230 := triangleCover (by decide +kernel)

def src1231 : Request := ⟨⟨⟨560,779,169,22223⟩,5316921262080,10214741280⟩,0,4,1,514639,4⟩

theorem rank1231 : P3_7_1.BankOK src1231.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_560_779_169 22223

theorem width1231 : Lower6960.HelperSource.WidthGuard src1231.bank 179730 2308 src1231.reserve := requestWidth (by decide)

def ends1231 : List ℕ := [2308, 2309, 2313]

theorem inside1231 : Research6966.TerminalBanks.inside src1231.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1231 : Cover (Triangular src1231) 2313 2308 ends1231 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources10

section Pack_R6970Height2313CommonSources11

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1232 : Request := ⟨⟨⟨562,781,172,25427⟩,5431270572032,10440670587⟩,1,4,1,515031,4⟩

theorem rank1232 : P3_7_1.BankOK src1232.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 25427

theorem width1232 : Lower6960.HelperSource.WidthGuard src1232.bank 179730 2308 src1232.reserve := requestWidth (by decide)

def ends1232 : List ℕ := [2308, 2309, 2313]

theorem inside1232 : Research6966.TerminalBanks.inside src1232.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1232 : Cover (Triangular src1232) 2313 2308 ends1232 := triangleCover (by decide +kernel)

def src1233 : Request := ⟨⟨⟨693,962,212,28733⟩,10163930791936,23997864317⟩,3,4,1,515031,4⟩

theorem rank1233 : P3_7_1.BankOK src1233.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_212 28733

theorem width1233 : Lower6960.HelperSource.WidthGuard src1233.bank 179730 2308 src1233.reserve := requestWidth (by decide)

def ends1233 : List ℕ := [2308, 2309, 2313]

theorem inside1233 : Research6966.TerminalBanks.inside src1233.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1233 : Cover (Triangular src1233) 2313 2308 ends1233 := triangleCover (by decide +kernel)

def src1234 : Request := ⟨⟨⟨1004,1395,307,45279⟩,30831793405952,105715278267⟩,10,4,1,515031,4⟩

theorem rank1234 : P3_7_1.BankOK src1234.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_307 45279

theorem width1234 : Lower6960.HelperSource.WidthGuard src1234.bank 179730 2308 src1234.reserve := requestWidth (by decide)

def ends1234 : List ℕ := [2308, 2309, 2313]

theorem inside1234 : Research6966.TerminalBanks.inside src1234.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1234 : Cover (Triangular src1234) 2313 2308 ends1234 := triangleCover (by decide +kernel)

def src1235 : Request := ⟨⟨⟨1750,2441,527,64247⟩,161065121873920,973912060302⟩,20,4,1,514639,4⟩

theorem rank1235 : P3_7_1.BankOK src1235.bank := by
  simpa only [src1235, _root_.Research6969.TransitionBanks.bank241] using _root_.Research6969.TransitionBanks.rank241 64247

theorem width1235 : Lower6960.HelperSource.WidthGuard src1235.bank 179730 2308 src1235.reserve := requestWidth (by decide)

def ends1235 : List ℕ := [2309, 2313]

theorem inside1235 : Research6966.TerminalBanks.inside src1235.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1235 : Cover (Triangular src1235) 2313 2308 ends1235 := triangleCover (by decide +kernel)

def src1236 : Request := ⟨⟨⟨2108,2929,645,92791⟩,284810981146624,2049139102608⟩,32,4,1,515031,4⟩

theorem rank1236 : P3_7_1.BankOK src1236.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2108_2929_645 92791

theorem width1236 : Lower6960.HelperSource.WidthGuard src1236.bank 179730 2308 src1236.reserve := requestWidth (by decide)

def ends1236 : List ℕ := [2308, 2309, 2313]

theorem inside1236 : Research6966.TerminalBanks.inside src1236.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1236 : Cover (Triangular src1236) 2313 2308 ends1236 := triangleCover (by decide +kernel)

def src1237 : Request := ⟨⟨⟨2793,3882,854,119782⟩,661743548497920,6313512679932⟩,45,4,1,515031,4⟩

theorem rank1237 : P3_7_1.BankOK src1237.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2793_3882_854 119782

theorem width1237 : Lower6960.HelperSource.WidthGuard src1237.bank 179730 2308 src1237.reserve := requestWidth (by decide)

def ends1237 : List ℕ := [2308, 2309, 2313]

theorem inside1237 : Research6966.TerminalBanks.inside src1237.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1237 : Cover (Triangular src1237) 2313 2308 ends1237 := triangleCover (by decide +kernel)

def src1238 : Request := ⟨⟨⟨2119,2945,645,420984⟩,288148178862080,2085391291848⟩,50,4,1,514639,4⟩

theorem rank1238 : P3_7_1.BankOK src1238.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2119_2945_645 420984

theorem width1238 : Lower6960.HelperSource.WidthGuard src1238.bank 179730 2308 src1238.reserve := requestWidth (by decide)

def ends1238 : List ℕ := [2308, 2309, 2313]

theorem inside1238 : Research6966.TerminalBanks.inside src1238.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1238 : Cover (Triangular src1238) 2313 2308 ends1238 := triangleCover (by decide +kernel)

def src1239 : Request := ⟨⟨⟨2600,3626,781,530820⟩,526728636923904,4727964653217⟩,63,4,1,515031,4⟩

theorem rank1239 : P3_7_1.BankOK src1239.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3626_781 530820

theorem width1239 : Lower6960.HelperSource.WidthGuard src1239.bank 179730 2308 src1239.reserve := requestWidth (by decide)

def ends1239 : List ℕ := [2308, 2309, 2313]

theorem inside1239 : Research6966.TerminalBanks.inside src1239.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1239 : Cover (Triangular src1239) 2313 2308 ends1239 := triangleCover (by decide +kernel)

def src124 : Request := ⟨⟨⟨2814,3905,870,33999⟩,682484369981440,6528319804485⟩,64,2,1,291368,41⟩

theorem rank124 : P3_7_1.BankOK src124.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2814_3905_870 33999

theorem width124 : Lower6960.HelperSource.WidthGuard src124.bank 179730 2308 src124.reserve := requestWidth (by decide)

def ends124 : List ℕ := [2308, 2309, 2313]

theorem inside124 : Research6966.TerminalBanks.inside src124.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover124 : Cover (Triangular src124) 2313 2308 ends124 := triangleCover (by decide +kernel)

def src1240 : Request := ⟨⟨⟨4819,6697,1474,150051⟩,3397470270259200,55891290082931⟩,65,4,1,515031,4⟩

theorem rank1240 : P3_7_1.BankOK src1240.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4819_6697_1474 150051

theorem width1240 : Lower6960.HelperSource.WidthGuard src1240.bank 179730 2308 src1240.reserve := requestWidth (by decide)

def ends1240 : List ℕ := [2308, 2309, 2313]




theorem cover1240 : Cover (Triangular src1240) 2313 2308 ends1240 := triangleCover (by decide +kernel)

def src1241 : Request := ⟨⟨⟨3210,4463,982,1199515⟩,1004762418380800,11028049925768⟩,85,4,1,515031,4⟩

theorem rank1241 : P3_7_1.BankOK src1241.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3210_4463_982 1199515

theorem width1241 : Lower6960.HelperSource.WidthGuard src1241.bank 179730 2308 src1241.reserve := requestWidth (by decide)

def ends1241 : List ℕ := [2308, 2309, 2313]




theorem cover1241 : Cover (Triangular src1241) 2313 2308 ends1241 := triangleCover (by decide +kernel)

def src1242 : Request := ⟨⟨⟨10039,13950,3070,434360⟩,30694774475325440,1051468979452278⟩,190,4,1,515031,4⟩

theorem rank1242 : P3_7_1.BankOK src1242.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10039_13950_3070 434360

theorem width1242 : Lower6960.HelperSource.WidthGuard src1242.bank 179730 2308 src1242.reserve := requestWidth (by decide)

def ends1242 : List ℕ := [2308, 2309, 2313]




theorem cover1242 : Cover (Triangular src1242) 2313 2308 ends1242 := triangleCover (by decide +kernel)

def src1243 : Request := ⟨⟨⟨562,781,172,17827⟩,5431270572032,10440670587⟩,0,4,1,515031,9⟩

theorem rank1243 : P3_7_1.BankOK src1243.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 17827

theorem width1243 : Lower6960.HelperSource.WidthGuard src1243.bank 179730 2308 src1243.reserve := requestWidth (by decide)

def ends1243 : List ℕ := [2308, 2309, 2313]

theorem inside1243 : Research6966.TerminalBanks.inside src1243.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1243 : Cover (Triangular src1243) 2313 2308 ends1243 := triangleCover (by decide +kernel)

def src1244 : Request := ⟨⟨⟨690,963,208,19788⟩,9921631092736,23724874690⟩,1,4,1,514639,9⟩

theorem rank1244 : P3_7_1.BankOK src1244.bank := by
  simpa only [src1244, _root_.Research6969.TransitionBanks.bank195] using _root_.Research6969.TransitionBanks.rank195 19788

theorem width1244 : Lower6960.HelperSource.WidthGuard src1244.bank 179730 2308 src1244.reserve := requestWidth (by decide)

def ends1244 : List ℕ := [2308, 2313]

theorem inside1244 : Research6966.TerminalBanks.inside src1244.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1244 : Cover (Triangular src1244) 2313 2308 ends1244 := triangleCover (by decide +kernel)

def src1245 : Request := ⟨⟨⟨690,962,208,22261⟩,9921631092736,23645774460⟩,2,4,1,514639,9⟩

theorem rank1245 : P3_7_1.BankOK src1245.bank := by
  simpa only [src1245, _root_.Research6969.TransitionBanks.bank192] using _root_.Research6969.TransitionBanks.rank192 22261

theorem width1245 : Lower6960.HelperSource.WidthGuard src1245.bank 179730 2308 src1245.reserve := requestWidth (by decide)

def ends1245 : List ℕ := [2313]

theorem inside1245 : Research6966.TerminalBanks.inside src1245.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1245 : Cover (Triangular src1245) 2313 2308 ends1245 := triangleCover (by decide +kernel)

def src1246 : Request := ⟨⟨⟨690,962,208,28173⟩,9921631092736,23645774460⟩,4,4,1,514639,9⟩

theorem rank1246 : P3_7_1.BankOK src1246.bank := by
  simpa only [src1246, _root_.Research6969.TransitionBanks.bank192] using _root_.Research6969.TransitionBanks.rank192 28173

theorem width1246 : Lower6960.HelperSource.WidthGuard src1246.bank 179730 2308 src1246.reserve := requestWidth (by decide)

def ends1246 : List ℕ := [2308, 2309, 2313]

theorem inside1246 : Research6966.TerminalBanks.inside src1246.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1246 : Cover (Triangular src1246) 2313 2308 ends1246 := triangleCover (by decide +kernel)

def src1247 : Request := ⟨⟨⟨825,1149,248,25040⟩,16903818182656,47987412873⟩,4,4,1,514639,9⟩

theorem rank1247 : P3_7_1.BankOK src1247.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_825_1149_248 25040

theorem width1247 : Lower6960.HelperSource.WidthGuard src1247.bank 179730 2308 src1247.reserve := requestWidth (by decide)

def ends1247 : List ℕ := [2308, 2309, 2313]

theorem inside1247 : Research6966.TerminalBanks.inside src1247.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1247 : Cover (Triangular src1247) 2313 2308 ends1247 := triangleCover (by decide +kernel)

def src1248 : Request := ⟨⟨⟨981,1363,301,31597⟩,28839211696128,96617256623⟩,8,4,1,514639,9⟩

theorem rank1248 : P3_7_1.BankOK src1248.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_981_1363_301 31597

theorem width1248 : Lower6960.HelperSource.WidthGuard src1248.bank 179730 2308 src1248.reserve := requestWidth (by decide)

def ends1248 : List ℕ := [2308, 2309, 2313]

theorem inside1248 : Research6966.TerminalBanks.inside src1248.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1248 : Cover (Triangular src1248) 2313 2308 ends1248 := triangleCover (by decide +kernel)

def src1249 : Request := ⟨⟨⟨1205,1674,368,52284⟩,53211572207616,218807905514⟩,16,4,1,515031,9⟩

theorem rank1249 : P3_7_1.BankOK src1249.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 52284

theorem width1249 : Lower6960.HelperSource.WidthGuard src1249.bank 179730 2308 src1249.reserve := requestWidth (by decide)

def ends1249 : List ℕ := [2308, 2309, 2313]

theorem inside1249 : Research6966.TerminalBanks.inside src1249.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1249 : Cover (Triangular src1249) 2313 2308 ends1249 := triangleCover (by decide +kernel)

def src125 : Request := ⟨⟨⟨2913,4044,900,31566⟩,756649935765504,7501830777122⟩,65,2,1,291368,41⟩

theorem rank125 : P3_7_1.BankOK src125.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2913_4044_900 31566

theorem width125 : Lower6960.HelperSource.WidthGuard src125.bank 179730 2308 src125.reserve := requestWidth (by decide)

def ends125 : List ℕ := [2308, 2309, 2313]

theorem inside125 : Research6966.TerminalBanks.inside src125.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover125 : Cover (Triangular src125) 2313 2308 ends125 := triangleCover (by decide +kernel)

def src1250 : Request := ⟨⟨⟨2109,2930,645,58310⟩,285113516032000,2051392203643⟩,25,4,1,515031,9⟩

theorem rank1250 : P3_7_1.BankOK src1250.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2109_2930_645 58310

theorem width1250 : Lower6960.HelperSource.WidthGuard src1250.bank 179730 2308 src1250.reserve := requestWidth (by decide)

def ends1250 : List ℕ := [2308, 2309, 2313]

theorem inside1250 : Research6966.TerminalBanks.inside src1250.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1250 : Cover (Triangular src1250) 2313 2308 ends1250 := triangleCover (by decide +kernel)

def src1251 : Request := ⟨⟨⟨2602,3615,794,101532⟩,534304627097600,4742574286177⟩,44,4,1,514639,9⟩

theorem rank1251 : P3_7_1.BankOK src1251.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3615_794 101532

theorem width1251 : Lower6960.HelperSource.WidthGuard src1251.bank 179730 2308 src1251.reserve := requestWidth (by decide)

def ends1251 : List ℕ := [2308, 2309, 2313]

theorem inside1251 : Research6966.TerminalBanks.inside src1251.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1251 : Cover (Triangular src1251) 2313 2308 ends1251 := triangleCover (by decide +kernel)

def src1252 : Request := ⟨⟨⟨2597,3620,776,419076⟩,522804981923840,4679328083011⟩,62,4,1,514639,9⟩

theorem rank1252 : P3_7_1.BankOK src1252.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2597_3620_776 419076

theorem width1252 : Lower6960.HelperSource.WidthGuard src1252.bank 179730 2308 src1252.reserve := requestWidth (by decide)

def ends1252 : List ℕ := [2308, 2309, 2313]

theorem inside1252 : Research6966.TerminalBanks.inside src1252.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1252 : Cover (Triangular src1252) 2313 2308 ends1252 := triangleCover (by decide +kernel)

def src1253 : Request := ⟨⟨⟨3210,4463,982,978009⟩,1004762418380800,11028049925768⟩,85,4,1,515031,9⟩

theorem rank1253 : P3_7_1.BankOK src1253.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3210_4463_982 978009

theorem width1253 : Lower6960.HelperSource.WidthGuard src1253.bank 179730 2308 src1253.reserve := requestWidth (by decide)

def ends1253 : List ℕ := [2308, 2309, 2313]




theorem cover1253 : Cover (Triangular src1253) 2313 2308 ends1253 := triangleCover (by decide +kernel)

def src1254 : Request := ⟨⟨⟨4819,6696,1474,168470⟩,3397470270259200,55864419956306⟩,85,4,1,515031,9⟩

theorem rank1254 : P3_7_1.BankOK src1254.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4819_6696_1474 168470

theorem width1254 : Lower6960.HelperSource.WidthGuard src1254.bank 179730 2308 src1254.reserve := requestWidth (by decide)

def ends1254 : List ℕ := [2308, 2309, 2313]




theorem cover1254 : Cover (Triangular src1254) 2313 2308 ends1254 := triangleCover (by decide +kernel)

def src1255 : Request := ⟨⟨⟨8333,11579,2548,264293⟩,17555013069701120,499124969898998⟩,145,4,1,515031,9⟩

theorem rank1255 : P3_7_1.BankOK src1255.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8333_11579_2548 264293

theorem width1255 : Lower6960.HelperSource.WidthGuard src1255.bank 179730 2308 src1255.reserve := requestWidth (by decide)

def ends1255 : List ℕ := [2308, 2309, 2313]




theorem cover1255 : Cover (Triangular src1255) 2313 2308 ends1255 := triangleCover (by decide +kernel)

def src1256 : Request := ⟨⟨⟨2810,3905,855,79367⟩,671390068899840,6440596481529⟩,44,4,1,514639,13⟩

theorem rank1256 : P3_7_1.BankOK src1256.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3905_855 79367

theorem width1256 : Lower6960.HelperSource.WidthGuard src1256.bank 179730 2308 src1256.reserve := requestWidth (by decide)

def ends1256 : List ℕ := [2308, 2309, 2313]

theorem inside1256 : Research6966.TerminalBanks.inside src1256.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1256 : Cover (Triangular src1256) 2313 2308 ends1256 := triangleCover (by decide +kernel)

def src1257 : Request := ⟨⟨⟨2597,3622,779,379312⟩,524345068748800,4701788394678⟩,63,4,1,514639,13⟩

theorem rank1257 : P3_7_1.BankOK src1257.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2597_3622_779 379312

theorem width1257 : Lower6960.HelperSource.WidthGuard src1257.bank 179730 2308 src1257.reserve := requestWidth (by decide)

def ends1257 : List ℕ := [2308, 2309, 2313]

theorem inside1257 : Research6966.TerminalBanks.inside src1257.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1257 : Cover (Triangular src1257) 2313 2308 ends1257 := triangleCover (by decide +kernel)

def src1258 : Request := ⟨⟨⟨692,963,212,12355⟩,10131154665472,24078187611⟩,0,4,1,514639,16⟩

theorem rank1258 : P3_7_1.BankOK src1258.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_963_212 12355

theorem width1258 : Lower6960.HelperSource.WidthGuard src1258.bank 179730 2308 src1258.reserve := requestWidth (by decide)

def ends1258 : List ℕ := [2308, 2309, 2313]

theorem inside1258 : Research6966.TerminalBanks.inside src1258.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1258 : Cover (Triangular src1258) 2313 2308 ends1258 := triangleCover (by decide +kernel)

def src1259 : Request := ⟨⟨⟨690,959,208,13860⟩,9921631092736,23409550120⟩,1,4,1,514639,16⟩

theorem rank1259 : P3_7_1.BankOK src1259.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_959_208 13860

theorem width1259 : Lower6960.HelperSource.WidthGuard src1259.bank 179730 2308 src1259.reserve := requestWidth (by decide)

def ends1259 : List ℕ := [2308, 2309, 2313]

theorem inside1259 : Research6966.TerminalBanks.inside src1259.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1259 : Cover (Triangular src1259) 2313 2308 ends1259 := triangleCover (by decide +kernel)

def src126 : Request := ⟨⟨⟨2816,3909,882,31391⟩,690700839813120,6619929415349⟩,85,2,1,292947,49⟩

theorem rank126 : P3_7_1.BankOK src126.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3909_882 31391

theorem width126 : Lower6960.HelperSource.WidthGuard src126.bank 179730 2308 src126.reserve := requestWidth (by decide)

def ends126 : List ℕ := [2308, 2309, 2313]

theorem inside126 : Research6966.TerminalBanks.inside src126.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover126 : Cover (Triangular src126) 2313 2308 ends126 := triangleCover (by decide +kernel)

def src1260 : Request := ⟨⟨⟨814,1135,248,17560⟩,16404081541120,46132494262⟩,4,4,1,514639,16⟩

theorem rank1260 : P3_7_1.BankOK src1260.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_814_1135_248 17560

theorem width1260 : Lower6960.HelperSource.WidthGuard src1260.bank 179730 2308 src1260.reserve := requestWidth (by decide)

def ends1260 : List ℕ := [2308, 2309, 2313]

theorem inside1260 : Research6966.TerminalBanks.inside src1260.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1260 : Cover (Triangular src1260) 2313 2308 ends1260 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources11

section Pack_R6970Height2313CommonSources12

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1261 : Request := ⟨⟨⟨1003,1395,307,22261⟩,30763123736576,105715278267⟩,8,4,1,514639,16⟩

theorem rank1261 : P3_7_1.BankOK src1261.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_307 22261

theorem width1261 : Lower6960.HelperSource.WidthGuard src1261.bank 179730 2308 src1261.reserve := requestWidth (by decide)

def ends1261 : List ℕ := [2308, 2309, 2313]

theorem inside1261 : Research6966.TerminalBanks.inside src1261.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1261 : Cover (Triangular src1261) 2313 2308 ends1261 := triangleCover (by decide +kernel)

def src1262 : Request := ⟨⟨⟨1454,2023,445,40111⟩,93574192168960,466511127281⟩,20,4,1,514639,16⟩

theorem rank1262 : P3_7_1.BankOK src1262.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2023_445 40111

theorem width1262 : Lower6960.HelperSource.WidthGuard src1262.bank 179730 2308 src1262.reserve := requestWidth (by decide)

def ends1262 : List ℕ := [2308, 2309, 2313]

theorem inside1262 : Research6966.TerminalBanks.inside src1262.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1262 : Cover (Triangular src1262) 2313 2308 ends1262 := triangleCover (by decide +kernel)

def src1263 : Request := ⟨⟨⟨2107,2929,645,243513⟩,284508615606272,2049139102608⟩,50,4,1,515031,16⟩

theorem rank1263 : P3_7_1.BankOK src1263.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2107_2929_645 243513

theorem width1263 : Lower6960.HelperSource.WidthGuard src1263.bank 179730 2308 src1263.reserve := requestWidth (by decide)

def ends1263 : List ℕ := [2308, 2309, 2313]

theorem inside1263 : Research6966.TerminalBanks.inside src1263.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1263 : Cover (Triangular src1263) 2313 2308 ends1263 := triangleCover (by decide +kernel)

def src1264 : Request := ⟨⟨⟨3215,4464,986,72942⟩,1011387794980864,11070973355058⟩,50,4,1,514639,16⟩

theorem rank1264 : P3_7_1.BankOK src1264.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3215_4464_986 72942

theorem width1264 : Lower6960.HelperSource.WidthGuard src1264.bank 179730 2308 src1264.reserve := requestWidth (by decide)

def ends1264 : List ℕ := [2308, 2309, 2313]




theorem cover1264 : Cover (Triangular src1264) 2313 2308 ends1264 := triangleCover (by decide +kernel)

def src1265 : Request := ⟨⟨⟨8340,11579,2552,187261⟩,17609037937377280,499735082985067⟩,145,4,1,514639,16⟩

theorem rank1265 : P3_7_1.BankOK src1265.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8340_11579_2552 187261

theorem width1265 : Lower6960.HelperSource.WidthGuard src1265.bank 179730 2308 src1265.reserve := requestWidth (by decide)

def ends1265 : List ℕ := [2308, 2309, 2313]




theorem cover1265 : Cover (Triangular src1265) 2313 2308 ends1265 := triangleCover (by decide +kernel)

def src1266 : Request := ⟨⟨⟨6923,9623,2118,898554⟩,10071814693191680,238176347849000⟩,190,4,1,515031,16⟩

theorem rank1266 : P3_7_1.BankOK src1266.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6923_9623_2118 898554

theorem width1266 : Lower6960.HelperSource.WidthGuard src1266.bank 179730 2308 src1266.reserve := requestWidth (by decide)

def ends1266 : List ℕ := [2308, 2309, 2313]




theorem cover1266 : Cover (Triangular src1266) 2313 2308 ends1266 := triangleCover (by decide +kernel)

def src1267 : Request := ⟨⟨⟨8372,11639,2548,4904504⟩,17739491789766656,507501527779128⟩,245,4,1,515031,16⟩

theorem rank1267 : P3_7_1.BankOK src1267.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8372_11639_2548 4904504

theorem width1267 : Lower6960.HelperSource.WidthGuard src1267.bank 179730 2308 src1267.reserve := requestWidth (by decide)

def ends1267 : List ℕ := [2308, 2309, 2313]




theorem cover1267 : Cover (Triangular src1267) 2313 2308 ends1267 := triangleCover (by decide +kernel)

def src1268 : Request := ⟨⟨⟨2911,4041,897,67044⟩,753575953694720,7464523841124⟩,47,4,1,514639,17⟩

theorem rank1268 : P3_7_1.BankOK src1268.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2911_4041_897 67044

theorem width1268 : Lower6960.HelperSource.WidthGuard src1268.bank 179730 2308 src1268.reserve := requestWidth (by decide)

def ends1268 : List ℕ := [2308, 2309, 2313]

theorem inside1268 : Research6966.TerminalBanks.inside src1268.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1268 : Cover (Triangular src1268) 2313 2308 ends1268 := triangleCover (by decide +kernel)

def src1269 : Request := ⟨⟨⟨2600,3626,791,289400⟩,531853527220224,4775090569881⟩,64,4,1,514639,17⟩

theorem rank1269 : P3_7_1.BankOK src1269.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3626_791 289400

theorem width1269 : Lower6960.HelperSource.WidthGuard src1269.bank 179730 2308 src1269.reserve := requestWidth (by decide)

def ends1269 : List ℕ := [2308, 2309, 2313]

theorem inside1269 : Research6966.TerminalBanks.inside src1269.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1269 : Cover (Triangular src1269) 2313 2308 ends1269 := triangleCover (by decide +kernel)

def src127 : Request := ⟨⟨⟨2809,3905,882,31694⟩,686857459597312,6598128215989⟩,85,2,1,292947,49⟩

theorem rank127 : P3_7_1.BankOK src127.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3905_882 31694

theorem width127 : Lower6960.HelperSource.WidthGuard src127.bank 179730 2308 src127.reserve := requestWidth (by decide)

def ends127 : List ℕ := [2308, 2309, 2313]

theorem inside127 : Research6966.TerminalBanks.inside src127.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover127 : Cover (Triangular src127) 2313 2308 ends127 := triangleCover (by decide +kernel)

def src1270 : Request := ⟨⟨⟨2768,3842,854,50673⟩,648553314385920,6106417618032⟩,45,4,1,514639,21⟩

theorem rank1270 : P3_7_1.BankOK src1270.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2768_3842_854 50673

theorem width1270 : Lower6960.HelperSource.WidthGuard src1270.bank 179730 2308 src1270.reserve := requestWidth (by decide)

def ends1270 : List ℕ := [2308, 2309, 2313]

theorem inside1270 : Research6966.TerminalBanks.inside src1270.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1270 : Cover (Triangular src1270) 2313 2308 ends1270 := triangleCover (by decide +kernel)

def src1271 : Request := ⟨⟨⟨2605,3618,791,210061⟩,534145111425024,4741262283081⟩,64,4,1,514639,21⟩

theorem rank1271 : P3_7_1.BankOK src1271.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3618_791 210061

theorem width1271 : Lower6960.HelperSource.WidthGuard src1271.bank 179730 2308 src1271.reserve := requestWidth (by decide)

def ends1271 : List ℕ := [2308, 2309, 2313]

theorem inside1271 : Research6966.TerminalBanks.inside src1271.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1271 : Cover (Triangular src1271) 2313 2308 ends1271 := triangleCover (by decide +kernel)

def src1272 : Request := ⟨⟨⟨2615,3627,819,39802⟩,553151842222080,4910333421859⟩,45,4,1,514639,25⟩

theorem rank1272 : P3_7_1.BankOK src1272.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 39802

theorem width1272 : Lower6960.HelperSource.WidthGuard src1272.bank 179730 2308 src1272.reserve := requestWidth (by decide)

def ends1272 : List ℕ := [2308, 2309, 2313]

theorem inside1272 : Research6966.TerminalBanks.inside src1272.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1272 : Cover (Triangular src1272) 2313 2308 ends1272 := triangleCover (by decide +kernel)

def src1273 : Request := ⟨⟨⟨2562,3561,775,147835⟩,506680843436032,4433868945913⟩,63,4,1,514639,25⟩

theorem rank1273 : P3_7_1.BankOK src1273.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2562_3561_775 147835

theorem width1273 : Lower6960.HelperSource.WidthGuard src1273.bank 179730 2308 src1273.reserve := requestWidth (by decide)

def ends1273 : List ℕ := [2308, 2309, 2313]

theorem inside1273 : Research6966.TerminalBanks.inside src1273.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1273 : Cover (Triangular src1273) 2313 2308 ends1273 := triangleCover (by decide +kernel)

def src1274 : Request := ⟨⟨⟨470,655,144,7715⟩,3184589537280,5168862572⟩,0,4,1,514639,26⟩

theorem rank1274 : P3_7_1.BankOK src1274.bank := by
  simpa only [src1274, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 7715

theorem width1274 : Lower6960.HelperSource.WidthGuard src1274.bank 179730 2308 src1274.reserve := requestWidth (by decide)

def ends1274 : List ℕ := [2313]

theorem inside1274 : Research6966.TerminalBanks.inside src1274.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1274 : Cover (Triangular src1274) 2313 2308 ends1274 := triangleCover (by decide +kernel)

def src1275 : Request := ⟨⟨⟨561,781,172,7715⟩,5409683537920,10440670587⟩,1,4,1,514639,26⟩

theorem rank1275 : P3_7_1.BankOK src1275.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 7715

theorem width1275 : Lower6960.HelperSource.WidthGuard src1275.bank 179730 2308 src1275.reserve := requestWidth (by decide)

def ends1275 : List ℕ := [2308, 2309, 2313]

theorem inside1275 : Research6966.TerminalBanks.inside src1275.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1275 : Cover (Triangular src1275) 2313 2308 ends1275 := triangleCover (by decide +kernel)

def src1276 : Request := ⟨⟨⟨561,779,172,8675⟩,5409683537920,10354949952⟩,2,4,1,514639,26⟩

theorem rank1276 : P3_7_1.BankOK src1276.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_779_172 8675

theorem width1276 : Lower6960.HelperSource.WidthGuard src1276.bank 179730 2308 src1276.reserve := requestWidth (by decide)

def ends1276 : List ℕ := [2308, 2309, 2313]

theorem inside1276 : Research6966.TerminalBanks.inside src1276.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1276 : Cover (Triangular src1276) 2313 2308 ends1276 := triangleCover (by decide +kernel)

def src1277 : Request := ⟨⟨⟨690,958,212,12401⟩,10065769922560,23678394421⟩,6,4,1,514639,26⟩

theorem rank1277 : P3_7_1.BankOK src1277.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_958_212 12401

theorem width1277 : Lower6960.HelperSource.WidthGuard src1277.bank 179730 2308 src1277.reserve := requestWidth (by decide)

def ends1277 : List ℕ := [2308, 2309, 2313]

theorem inside1277 : Research6966.TerminalBanks.inside src1277.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1277 : Cover (Triangular src1277) 2313 2308 ends1277 := triangleCover (by decide +kernel)

def src1278 : Request := ⟨⟨⟨1200,1666,361,19773⟩,51955677528064,212267437130⟩,16,4,1,514639,26⟩

theorem rank1278 : P3_7_1.BankOK src1278.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1666_361 19773

theorem width1278 : Lower6960.HelperSource.WidthGuard src1278.bank 179730 2308 src1278.reserve := requestWidth (by decide)

def ends1278 : List ℕ := [2308, 2309, 2313]

theorem inside1278 : Research6966.TerminalBanks.inside src1278.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1278 : Cover (Triangular src1278) 2313 2308 ends1278 := triangleCover (by decide +kernel)

def src1279 : Request := ⟨⟨⟨2604,3627,798,45124⟩,537271175741440,4812227595495⟩,50,4,1,514639,26⟩

theorem rank1279 : P3_7_1.BankOK src1279.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3627_798 45124

theorem width1279 : Lower6960.HelperSource.WidthGuard src1279.bank 179730 2308 src1279.reserve := requestWidth (by decide)

def ends1279 : List ℕ := [2308, 2309, 2313]

theorem inside1279 : Research6966.TerminalBanks.inside src1279.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1279 : Cover (Triangular src1279) 2313 2308 ends1279 := triangleCover (by decide +kernel)

def src128 : Request := ⟨⟨⟨326,453,100,3008⟩,1068355026944,1193036697⟩,0,2,1,292947,51⟩

theorem rank128 : P3_7_1.BankOK src128.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 3008

theorem width128 : Lower6960.HelperSource.WidthGuard src128.bank 179730 2308 src128.reserve := requestWidth (by decide)

def ends128 : List ℕ := [2313]

theorem inside128 : Research6966.TerminalBanks.inside src128.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover128 : Cover (Triangular src128) 2313 2308 ends128 := triangleCover (by decide +kernel)

def src1280 : Request := ⟨⟨⟨3227,4479,998,231145⟩,1029267100532736,11296993100967⟩,85,4,1,514639,26⟩

theorem rank1280 : P3_7_1.BankOK src1280.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3227_4479_998 231145

theorem width1280 : Lower6960.HelperSource.WidthGuard src1280.bank 179730 2308 src1280.reserve := requestWidth (by decide)

def ends1280 : List ℕ := [2308, 2309, 2313]




theorem cover1280 : Cover (Triangular src1280) 2313 2308 ends1280 := triangleCover (by decide +kernel)

def src1281 : Request := ⟨⟨⟨8300,11577,2548,164837⟩,17399709518790656,498847383098023⟩,190,4,1,514639,26⟩

theorem rank1281 : P3_7_1.BankOK src1281.bank := by
  simpa only [src1281, _root_.Research6969.TransitionBanks.bank365] using _root_.Research6969.TransitionBanks.rank365 164837

theorem width1281 : Lower6960.HelperSource.WidthGuard src1281.bank 179730 2308 src1281.reserve := requestWidth (by decide)

def ends1281 : List ℕ := [2308, 2313]



theorem cover1281 : Cover (Triangular src1281) 2313 2308 ends1281 := triangleCover (by decide +kernel)

def src1282 : Request := ⟨⟨⟨10059,13950,3150,130242⟩,31439703866081280,1072717072025530⟩,190,4,1,514639,26⟩

theorem rank1282 : P3_7_1.BankOK src1282.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10059_13950_3150 130242

theorem width1282 : Lower6960.HelperSource.WidthGuard src1282.bank 179730 2308 src1282.reserve := requestWidth (by decide)

def ends1282 : List ℕ := [2309, 2313]



theorem cover1282 : Cover (Triangular src1282) 2313 2308 ends1282 := triangleCover (by decide +kernel)

def src1283 : Request := ⟨⟨⟨8328,11575,2548,2228542⟩,17531435454300160,498569901356632⟩,245,4,1,515031,26⟩

theorem rank1283 : P3_7_1.BankOK src1283.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8328_11575_2548 2228542

theorem width1283 : Lower6960.HelperSource.WidthGuard src1283.bank 179730 2308 src1283.reserve := requestWidth (by decide)

def ends1283 : List ℕ := [2308, 2309, 2313]




theorem cover1283 : Cover (Triangular src1283) 2313 2308 ends1283 := triangleCover (by decide +kernel)

def src1284 : Request := ⟨⟨⟨2585,3594,775,91293⟩,516910921809920,4567459193957⟩,63,4,1,514639,29⟩

theorem rank1284 : P3_7_1.BankOK src1284.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2585_3594_775 91293

theorem width1284 : Lower6960.HelperSource.WidthGuard src1284.bank 179730 2308 src1284.reserve := requestWidth (by decide)

def ends1284 : List ℕ := [2308, 2309, 2313]

theorem inside1284 : Research6966.TerminalBanks.inside src1284.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1284 : Cover (Triangular src1284) 2313 2308 ends1284 := triangleCover (by decide +kernel)

def src1285 : Request := ⟨⟨⟨2825,3921,870,51260⟩,688474539950080,6614859312501⟩,64,4,1,514639,29⟩

theorem rank1285 : P3_7_1.BankOK src1285.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2825_3921_870 51260

theorem width1285 : Lower6960.HelperSource.WidthGuard src1285.bank 179730 2308 src1285.reserve := requestWidth (by decide)

def ends1285 : List ℕ := [2308, 2309, 2313]

theorem inside1285 : Research6966.TerminalBanks.inside src1285.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1285 : Cover (Triangular src1285) 2313 2308 ends1285 := triangleCover (by decide +kernel)

def src1286 : Request := ⟨⟨⟨400,558,123,6858⟩,1971918995456,2734096379⟩,0,4,1,514639,30⟩

theorem rank1286 : P3_7_1.BankOK src1286.bank := by
  simpa only [src1286, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 6858

theorem width1286 : Lower6960.HelperSource.WidthGuard src1286.bank 179730 2308 src1286.reserve := requestWidth (by decide)

def ends1286 : List ℕ := [2308, 2313]

theorem inside1286 : Research6966.TerminalBanks.inside src1286.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1286 : Cover (Triangular src1286) 2313 2308 ends1286 := triangleCover (by decide +kernel)

def src1287 : Request := ⟨⟨⟨470,655,144,6858⟩,3184589537280,5168862572⟩,1,4,1,514639,30⟩

theorem rank1287 : P3_7_1.BankOK src1287.bank := by
  simpa only [src1287, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 6858

theorem width1287 : Lower6960.HelperSource.WidthGuard src1287.bank 179730 2308 src1287.reserve := requestWidth (by decide)

def ends1287 : List ℕ := [2313]

theorem inside1287 : Research6966.TerminalBanks.inside src1287.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1287 : Cover (Triangular src1287) 2313 2308 ends1287 := triangleCover (by decide +kernel)

def src1288 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,3,4,1,514639,30⟩

theorem rank1288 : P3_7_1.BankOK src1288.bank := by
  simpa only [src1288, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 7715

theorem width1288 : Lower6960.HelperSource.WidthGuard src1288.bank 179730 2308 src1288.reserve := requestWidth (by decide)

def ends1288 : List ℕ := [2309, 2313]

theorem inside1288 : Research6966.TerminalBanks.inside src1288.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1288 : Cover (Triangular src1288) 2313 2308 ends1288 := triangleCover (by decide +kernel)

def src1289 : Request := ⟨⟨⟨690,960,208,9762⟩,9921631092736,23488112384⟩,6,4,1,514639,30⟩

theorem rank1289 : P3_7_1.BankOK src1289.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_960_208 9762

theorem width1289 : Lower6960.HelperSource.WidthGuard src1289.bank 179730 2308 src1289.reserve := requestWidth (by decide)

def ends1289 : List ℕ := [2308, 2309, 2313]

theorem inside1289 : Research6966.TerminalBanks.inside src1289.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1289 : Cover (Triangular src1289) 2313 2308 ends1289 := triangleCover (by decide +kernel)

def src129 : Request := ⟨⟨⟨400,558,123,3384⟩,1971918995456,2734096379⟩,1,2,1,292947,51⟩

theorem rank129 : P3_7_1.BankOK src129.bank := by
  simpa only [src129, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 3384

theorem width129 : Lower6960.HelperSource.WidthGuard src129.bank 179730 2308 src129.reserve := requestWidth (by decide)

def ends129 : List ℕ := [2313]

theorem inside129 : Research6966.TerminalBanks.inside src129.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover129 : Cover (Triangular src129) 2313 2308 ends129 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources12

section Pack_R6970Height2313CommonSources14

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1319 : Request := ⟨⟨⟨4819,6694,1512,72277⟩,3463686924009472,56926029739529⟩,145,4,1,514639,38⟩

theorem rank1319 : P3_7_1.BankOK src1319.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4819_6694_1512 72277

theorem width1319 : Lower6960.HelperSource.WidthGuard src1319.bank 179730 2308 src1319.reserve := requestWidth (by decide)

def ends1319 : List ℕ := [2308, 2313]



theorem cover1319 : Cover (Triangular src1319) 2313 2308 ends1319 := triangleCover (by decide +kernel)

def src132 : Request := ⟨⟨⟨470,655,144,4282⟩,3184589537280,5168862572⟩,4,2,1,292947,51⟩

theorem rank132 : P3_7_1.BankOK src132.bank := by
  simpa only [src132, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4282

theorem width132 : Lower6960.HelperSource.WidthGuard src132.bank 179730 2308 src132.reserve := requestWidth (by decide)

def ends132 : List ℕ := [2313]

theorem inside132 : Research6966.TerminalBanks.inside src132.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover132 : Cover (Triangular src132) 2313 2308 ends132 := triangleCover (by decide +kernel)

def src1320 : Request := ⟨⟨⟨8339,11575,2615,102908⟩,17933010479349760,508734991702659⟩,245,4,1,514639,38⟩

theorem rank1320 : P3_7_1.BankOK src1320.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8339_11575_2615 102908

theorem width1320 : Lower6960.HelperSource.WidthGuard src1320.bank 179730 2308 src1320.reserve := requestWidth (by decide)

def ends1320 : List ℕ := [2308, 2313]



theorem cover1320 : Cover (Triangular src1320) 2313 2308 ends1320 := triangleCover (by decide +kernel)

def src1321 : Request := ⟨⟨⟨326,453,100,3807⟩,1068355026944,1193036697⟩,0,4,1,514639,41⟩

theorem rank1321 : P3_7_1.BankOK src1321.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 3807

theorem width1321 : Lower6960.HelperSource.WidthGuard src1321.bank 179730 2308 src1321.reserve := requestWidth (by decide)

def ends1321 : List ℕ := [2313]

theorem inside1321 : Research6966.TerminalBanks.inside src1321.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1321 : Cover (Triangular src1321) 2313 2308 ends1321 := triangleCover (by decide +kernel)

def src1322 : Request := ⟨⟨⟨401,558,126,3807⟩,2019210559488,2785382344⟩,1,4,1,514639,41⟩

theorem rank1322 : P3_7_1.BankOK src1322.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_126 3807

theorem width1322 : Lower6960.HelperSource.WidthGuard src1322.bank 179730 2308 src1322.reserve := requestWidth (by decide)

def ends1322 : List ℕ := [2313]

theorem inside1322 : Research6966.TerminalBanks.inside src1322.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1322 : Cover (Triangular src1322) 2313 2308 ends1322 := triangleCover (by decide +kernel)

def src1323 : Request := ⟨⟨⟨401,558,126,4282⟩,2019210559488,2785382344⟩,2,4,1,514639,41⟩

theorem rank1323 : P3_7_1.BankOK src1323.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_126 4282

theorem width1323 : Lower6960.HelperSource.WidthGuard src1323.bank 179730 2308 src1323.reserve := requestWidth (by decide)

def ends1323 : List ℕ := [2308, 2313]

theorem inside1323 : Research6966.TerminalBanks.inside src1323.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1323 : Cover (Triangular src1323) 2313 2308 ends1323 := triangleCover (by decide +kernel)

def src1324 : Request := ⟨⟨⟨401,558,123,5419⟩,1982954733568,2734096379⟩,3,4,1,514639,41⟩

theorem rank1324 : P3_7_1.BankOK src1324.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_123 5419

theorem width1324 : Lower6960.HelperSource.WidthGuard src1324.bank 179730 2308 src1324.reserve := requestWidth (by decide)

def ends1324 : List ℕ := [2308, 2313]

theorem inside1324 : Research6966.TerminalBanks.inside src1324.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1324 : Cover (Triangular src1324) 2313 2308 ends1324 := triangleCover (by decide +kernel)

def src1325 : Request := ⟨⟨⟨470,653,141,5404⟩,3134317133824,5035569706⟩,4,4,1,514639,41⟩

theorem rank1325 : P3_7_1.BankOK src1325.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_470_653_141 5404

theorem width1325 : Lower6960.HelperSource.WidthGuard src1325.bank 179730 2308 src1325.reserve := requestWidth (by decide)

def ends1325 : List ℕ := [2308, 2309, 2313]

theorem inside1325 : Research6966.TerminalBanks.inside src1325.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1325 : Cover (Triangular src1325) 2313 2308 ends1325 := triangleCover (by decide +kernel)

def src1326 : Request := ⟨⟨⟨561,781,176,6858⟩,5504262995968,10627925923⟩,8,4,1,514639,41⟩

theorem rank1326 : P3_7_1.BankOK src1326.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_176 6858

theorem width1326 : Lower6960.HelperSource.WidthGuard src1326.bank 179730 2308 src1326.reserve := requestWidth (by decide)

def ends1326 : List ℕ := [2308, 2313]

theorem inside1326 : Research6966.TerminalBanks.inside src1326.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1326 : Cover (Triangular src1326) 2313 2308 ends1326 := triangleCover (by decide +kernel)

def src1327 : Request := ⟨⟨⟨826,1150,253,9763⟩,17208151113728,48873782027⟩,16,4,1,514639,41⟩

theorem rank1327 : P3_7_1.BankOK src1327.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1150_253 9763

theorem width1327 : Lower6960.HelperSource.WidthGuard src1327.bank 179730 2308 src1327.reserve := requestWidth (by decide)

def ends1327 : List ℕ := [2308, 2313]

theorem inside1327 : Research6966.TerminalBanks.inside src1327.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1327 : Cover (Triangular src1327) 2313 2308 ends1327 := triangleCover (by decide +kernel)

def src1328 : Request := ⟨⟨⟨2800,3905,854,45124⟩,665461916958720,6434729640882⟩,85,4,1,514639,41⟩

theorem rank1328 : P3_7_1.BankOK src1328.bank := by
  simpa only [src1328, _root_.Research6969.TerminalAuxBanks.bank66] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank66 45124

theorem width1328 : Lower6960.HelperSource.WidthGuard src1328.bank 179730 2308 src1328.reserve := requestWidth (by decide)

def ends1328 : List ℕ := [2308, 2309, 2313]

theorem inside1328 : Research6966.TerminalBanks.inside src1328.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1328 : Cover (Triangular src1328) 2313 2308 ends1328 := triangleCover (by decide +kernel)

def src1329 : Request := ⟨⟨⟨2816,3905,882,36829⟩,690700839813120,6598128215989⟩,85,4,1,514639,41⟩

theorem rank1329 : P3_7_1.BankOK src1329.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 36829

theorem width1329 : Lower6960.HelperSource.WidthGuard src1329.bank 179730 2308 src1329.reserve := requestWidth (by decide)

def ends1329 : List ℕ := [2309, 2313]

theorem inside1329 : Research6966.TerminalBanks.inside src1329.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1329 : Cover (Triangular src1329) 2313 2308 ends1329 := triangleCover (by decide +kernel)

def src133 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,6,2,1,292947,51⟩

theorem rank133 : P3_7_1.BankOK src133.bank := by
  simpa only [src133, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 5419

theorem width133 : Lower6960.HelperSource.WidthGuard src133.bank 179730 2308 src133.reserve := requestWidth (by decide)

def ends133 : List ℕ := [2309, 2313]

theorem inside133 : Research6966.TerminalBanks.inside src133.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover133 : Cover (Triangular src133) 2313 2308 ends133 := triangleCover (by decide +kernel)

def src1330 : Request := ⟨⟨⟨3205,4463,1008,31694⟩,1021287165853696,11254299374432⟩,85,4,1,514639,41⟩

theorem rank1330 : P3_7_1.BankOK src1330.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3205_4463_1008 31694

theorem width1330 : Lower6960.HelperSource.WidthGuard src1330.bank 179730 2308 src1330.reserve := requestWidth (by decide)

def ends1330 : List ℕ := [2308, 2309, 2313]




theorem cover1330 : Cover (Triangular src1330) 2313 2308 ends1330 := triangleCover (by decide +kernel)

def src1331 : Request := ⟨⟨⟨4816,6694,1474,57109⟩,3392736362496000,55810706074581⟩,145,4,1,514639,41⟩

theorem rank1331 : P3_7_1.BankOK src1331.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4816_6694_1474 57109

theorem width1331 : Lower6960.HelperSource.WidthGuard src1331.bank 179730 2308 src1331.reserve := requestWidth (by decide)

def ends1331 : List ℕ := [2308, 2309, 2313]




theorem cover1331 : Cover (Triangular src1331) 2313 2308 ends1331 := triangleCover (by decide +kernel)

def src1332 : Request := ⟨⟨⟨5731,7948,1796,91474⟩,5819686050070528,113150499898987⟩,190,4,1,514639,41⟩

theorem rank1332 : P3_7_1.BankOK src1332.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5731_7948_1796 91474

theorem width1332 : Lower6960.HelperSource.WidthGuard src1332.bank 179730 2308 src1332.reserve := requestWidth (by decide)

def ends1332 : List ℕ := [2309, 2313]



theorem cover1332 : Cover (Triangular src1332) 2313 2308 ends1332 := triangleCover (by decide +kernel)

def src1333 : Request := ⟨⟨⟨8300,11575,2548,91474⟩,17399709518790656,498569901356632⟩,245,4,1,514639,41⟩

theorem rank1333 : P3_7_1.BankOK src1333.bank := by
  simpa only [src1333, _root_.Research6969.TransitionBanks.bank362] using _root_.Research6969.TransitionBanks.rank362 91474

theorem width1333 : Lower6960.HelperSource.WidthGuard src1333.bank 179730 2308 src1333.reserve := requestWidth (by decide)

def ends1333 : List ℕ := [2308, 2313]



theorem cover1333 : Cover (Triangular src1333) 2313 2308 ends1333 := triangleCover (by decide +kernel)

def src1334 : Request := ⟨⟨⟨325,453,98,3384⟩,1045036793856,1174588250⟩,0,4,1,514639,45⟩

theorem rank1334 : P3_7_1.BankOK src1334.bank := by
  simpa only [src1334, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 3384

theorem width1334 : Lower6960.HelperSource.WidthGuard src1334.bank 179730 2308 src1334.reserve := requestWidth (by decide)

def ends1334 : List ℕ := [2313]

theorem inside1334 : Research6966.TerminalBanks.inside src1334.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1334 : Cover (Triangular src1334) 2313 2308 ends1334 := triangleCover (by decide +kernel)

def src1335 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,1,4,1,514639,45⟩

theorem rank1335 : P3_7_1.BankOK src1335.bank := by
  simpa only [src1335, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 3807

theorem width1335 : Lower6960.HelperSource.WidthGuard src1335.bank 179730 2308 src1335.reserve := requestWidth (by decide)

def ends1335 : List ℕ := [2308, 2313]

theorem inside1335 : Research6966.TerminalBanks.inside src1335.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1335 : Cover (Triangular src1335) 2313 2308 ends1335 := triangleCover (by decide +kernel)

def src1336 : Request := ⟨⟨⟨400,558,123,3807⟩,1971918995456,2734096379⟩,2,4,1,514639,45⟩

theorem rank1336 : P3_7_1.BankOK src1336.bank := by
  simpa only [src1336, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 3807

theorem width1336 : Lower6960.HelperSource.WidthGuard src1336.bank 179730 2308 src1336.reserve := requestWidth (by decide)

def ends1336 : List ℕ := [2313]

theorem inside1336 : Research6966.TerminalBanks.inside src1336.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1336 : Cover (Triangular src1336) 2313 2308 ends1336 := triangleCover (by decide +kernel)

def src1337 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,3,4,1,514639,45⟩

theorem rank1337 : P3_7_1.BankOK src1337.bank := by
  simpa only [src1337, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4282

theorem width1337 : Lower6960.HelperSource.WidthGuard src1337.bank 179730 2308 src1337.reserve := requestWidth (by decide)

def ends1337 : List ℕ := [2308, 2313]

theorem inside1337 : Research6966.TerminalBanks.inside src1337.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1337 : Cover (Triangular src1337) 2313 2308 ends1337 := triangleCover (by decide +kernel)

def src1338 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,4,4,1,514639,45⟩

theorem rank1338 : P3_7_1.BankOK src1338.bank := by
  simpa only [src1338, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 5419

theorem width1338 : Lower6960.HelperSource.WidthGuard src1338.bank 179730 2308 src1338.reserve := requestWidth (by decide)

def ends1338 : List ℕ := [2313]

theorem inside1338 : Research6966.TerminalBanks.inside src1338.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1338 : Cover (Triangular src1338) 2313 2308 ends1338 := triangleCover (by decide +kernel)

def src1339 : Request := ⟨⟨⟨471,655,144,5419⟩,3199755878400,5168862572⟩,6,4,1,514639,45⟩

theorem rank1339 : P3_7_1.BankOK src1339.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 5419

theorem width1339 : Lower6960.HelperSource.WidthGuard src1339.bank 179730 2308 src1339.reserve := requestWidth (by decide)

def ends1339 : List ℕ := [2308, 2313]

theorem inside1339 : Research6966.TerminalBanks.inside src1339.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1339 : Cover (Triangular src1339) 2313 2308 ends1339 := triangleCover (by decide +kernel)

def src134 : Request := ⟨⟨⟨561,781,172,5419⟩,5409683537920,10440670587⟩,8,2,1,292947,51⟩

theorem rank134 : P3_7_1.BankOK src134.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 5419

theorem width134 : Lower6960.HelperSource.WidthGuard src134.bank 179730 2308 src134.reserve := requestWidth (by decide)

def ends134 : List ℕ := [2309, 2313]

theorem inside134 : Research6966.TerminalBanks.inside src134.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover134 : Cover (Triangular src134) 2313 2308 ends134 := triangleCover (by decide +kernel)

def src1340 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,13,4,1,514639,45⟩

theorem rank1340 : P3_7_1.BankOK src1340.bank := by
  simpa only [src1340, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 7715

theorem width1340 : Lower6960.HelperSource.WidthGuard src1340.bank 179730 2308 src1340.reserve := requestWidth (by decide)

def ends1340 : List ℕ := [2313]

theorem inside1340 : Research6966.TerminalBanks.inside src1340.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1340 : Cover (Triangular src1340) 2313 2308 ends1340 := triangleCover (by decide +kernel)

def src1341 : Request := ⟨⟨⟨1199,1665,368,13898⟩,52620448235520,215044511783⟩,32,4,1,514639,45⟩

theorem rank1341 : P3_7_1.BankOK src1341.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1199_1665_368 13898

theorem width1341 : Lower6960.HelperSource.WidthGuard src1341.bank 179730 2308 src1341.reserve := requestWidth (by decide)

def ends1341 : List ℕ := [2308, 2309, 2313]

theorem inside1341 : Research6966.TerminalBanks.inside src1341.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1341 : Cover (Triangular src1341) 2313 2308 ends1341 := triangleCover (by decide +kernel)

def src1342 : Request := ⟨⟨⟨2102,2928,662,25043⟩,288629091991552,2088662039796⟩,65,4,1,514639,45⟩

theorem rank1342 : P3_7_1.BankOK src1342.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2102_2928_662 25043

theorem width1342 : Lower6960.HelperSource.WidthGuard src1342.bank 179730 2308 src1342.reserve := requestWidth (by decide)

def ends1342 : List ℕ := [2308, 2309, 2313]

theorem inside1342 : Research6966.TerminalBanks.inside src1342.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1342 : Cover (Triangular src1342) 2313 2308 ends1342 := triangleCover (by decide +kernel)

def src1343 : Request := ⟨⟨⟨5703,7948,1796,64247⟩,5756116664320000,113150499898987⟩,190,4,1,514639,45⟩

theorem rank1343 : P3_7_1.BankOK src1343.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5703_7948_1796 64247

theorem width1343 : Lower6960.HelperSource.WidthGuard src1343.bank 179730 2308 src1343.reserve := requestWidth (by decide)

def ends1343 : List ℕ := [2308, 2309, 2313]




theorem cover1343 : Cover (Triangular src1343) 2313 2308 ends1343 := triangleCover (by decide +kernel)

def src1344 : Request := ⟨⟨⟨6930,9621,2174,91474⟩,10296459014963200,242895948111878⟩,245,4,1,514639,45⟩

theorem rank1344 : P3_7_1.BankOK src1344.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6930_9621_2174 91474

theorem width1344 : Lower6960.HelperSource.WidthGuard src1344.bank 179730 2308 src1344.reserve := requestWidth (by decide)

def ends1344 : List ℕ := [2313]


theorem cover1344 : Cover (Triangular src1344) 2313 2308 ends1344 := triangleCover (by decide +kernel)

def src1345 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,0,4,1,514639,49⟩

theorem rank1345 : P3_7_1.BankOK src1345.bank := by
  simpa only [src1345, _root_.Research6969.TransitionBanks.bank78] using _root_.Research6969.TransitionBanks.rank78 3384

theorem width1345 : Lower6960.HelperSource.WidthGuard src1345.bank 179730 2308 src1345.reserve := requestWidth (by decide)

def ends1345 : List ℕ := [2308, 2313]

theorem inside1345 : Research6966.TerminalBanks.inside src1345.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1345 : Cover (Triangular src1345) 2313 2308 ends1345 := triangleCover (by decide +kernel)

def src1346 : Request := ⟨⟨⟨325,453,98,3384⟩,1045036793856,1174588250⟩,1,4,1,514639,49⟩

theorem rank1346 : P3_7_1.BankOK src1346.bank := by
  simpa only [src1346, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 3384

theorem width1346 : Lower6960.HelperSource.WidthGuard src1346.bank 179730 2308 src1346.reserve := requestWidth (by decide)

def ends1346 : List ℕ := [2308, 2313]

theorem inside1346 : Research6966.TerminalBanks.inside src1346.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1346 : Cover (Triangular src1346) 2313 2308 ends1346 := triangleCover (by decide +kernel)

def src1347 : Request := ⟨⟨⟨326,453,100,3807⟩,1068355026944,1193036697⟩,2,4,1,514639,49⟩

theorem rank1347 : P3_7_1.BankOK src1347.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 3807

theorem width1347 : Lower6960.HelperSource.WidthGuard src1347.bank 179730 2308 src1347.reserve := requestWidth (by decide)

def ends1347 : List ℕ := [2313]

theorem inside1347 : Research6966.TerminalBanks.inside src1347.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1347 : Cover (Triangular src1347) 2313 2308 ends1347 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources14

section Pack_R6970Height2313CommonSources27

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1694 : Request := ⟨⟨⟨3200,4446,982,64181⟩,997767489781760,10893360067896⟩,110,7,1,900619,1⟩

theorem rank1694 : P3_7_1.BankOK src1694.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4446_982 64181

theorem width1694 : Lower6960.HelperSource.WidthGuard src1694.bank 179730 2308 src1694.reserve := requestWidth (by decide)

def ends1694 : List ℕ := [2308, 2309, 2313]




theorem cover1694 : Cover (Triangular src1694) 2313 2308 ends1694 := triangleCover (by decide +kernel)

def src1695 : Request := ⟨⟨⟨8336,11559,2615,130238⟩,17918546588729344,506472061276259⟩,245,7,1,900619,1⟩

theorem rank1695 : P3_7_1.BankOK src1695.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8336_11559_2615 130238

theorem width1695 : Lower6960.HelperSource.WidthGuard src1695.bank 179730 2308 src1695.reserve := requestWidth (by decide)

def ends1695 : List ℕ := [2308, 2309, 2313]




theorem cover1695 : Cover (Triangular src1695) 2313 2308 ends1695 := triangleCover (by decide +kernel)

def src1696 : Request := ⟨⟨⟨325,453,100,5419⟩,1061047500800,1193036697⟩,0,7,1,900619,2⟩

theorem rank1696 : P3_7_1.BankOK src1696.bank := by
  simpa only [src1696, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 5419

theorem width1696 : Lower6960.HelperSource.WidthGuard src1696.bank 179730 2308 src1696.reserve := requestWidth (by decide)

def ends1696 : List ℕ := [2313]

theorem inside1696 : Research6966.TerminalBanks.inside src1696.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1696 : Cover (Triangular src1696) 2313 2308 ends1696 := triangleCover (by decide +kernel)

def src1697 : Request := ⟨⟨⟨326,453,98,6096⟩,1052225568768,1174588250⟩,1,7,1,900619,2⟩

theorem rank1697 : P3_7_1.BankOK src1697.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_98 6096

theorem width1697 : Lower6960.HelperSource.WidthGuard src1697.bank 179730 2308 src1697.reserve := requestWidth (by decide)

def ends1697 : List ℕ := [2308, 2309, 2313]

theorem inside1697 : Research6966.TerminalBanks.inside src1697.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1697 : Cover (Triangular src1697) 2313 2308 ends1697 := triangleCover (by decide +kernel)

def src1698 : Request := ⟨⟨⟨325,451,98,7679⟩,1045036793856,1158025616⟩,3,7,1,900619,2⟩

theorem rank1698 : P3_7_1.BankOK src1698.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 7679

theorem width1698 : Lower6960.HelperSource.WidthGuard src1698.bank 179730 2308 src1698.reserve := requestWidth (by decide)

def ends1698 : List ℕ := [2308, 2309, 2313]

theorem inside1698 : Research6966.TerminalBanks.inside src1698.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1698 : Cover (Triangular src1698) 2313 2308 ends1698 := triangleCover (by decide +kernel)

def src1699 : Request := ⟨⟨⟨471,655,148,9763⟩,3266464186368,5279398867⟩,8,7,1,900619,2⟩

theorem rank1699 : P3_7_1.BankOK src1699.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 9763

theorem width1699 : Lower6960.HelperSource.WidthGuard src1699.bank 179730 2308 src1699.reserve := requestWidth (by decide)

def ends1699 : List ℕ := [2308, 2309, 2313]

theorem inside1699 : Research6966.TerminalBanks.inside src1699.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1699 : Cover (Triangular src1699) 2313 2308 ends1699 := triangleCover (by decide +kernel)

def src17 : Request := ⟨⟨⟨2305,3202,702,76453⟩,370969276579840,2915923177462⟩,249,1,1,128659,1025⟩

theorem rank17 : P3_7_1.BankOK src17.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3202_702 76453

theorem width17 : Lower6960.HelperSource.WidthGuard src17.bank 179730 2308 src17.reserve := requestWidth (by decide)

def ends17 : List ℕ := [2308, 2309, 2313]

theorem inside17 : Research6966.TerminalBanks.inside src17.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover17 : Cover (Triangular src17) 2313 2308 ends17 := triangleCover (by decide +kernel)

def src170 : Request := ⟨⟨⟨2434,3388,761,29578⟩,445535742066688,3723773825908⟩,67,2,1,303410,46⟩

theorem rank170 : P3_7_1.BankOK src170.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2434_3388_761 29578

theorem width170 : Lower6960.HelperSource.WidthGuard src170.bank 179730 2308 src170.reserve := requestWidth (by decide)

def ends170 : List ℕ := [2308, 2309, 2313]

theorem inside170 : Research6966.TerminalBanks.inside src170.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover170 : Cover (Triangular src170) 2313 2308 ends170 := triangleCover (by decide +kernel)

def src1700 : Request := ⟨⟨⟨684,954,208,12329⟩,9729817968640,23019418180⟩,13,7,1,900619,2⟩

theorem rank1700 : P3_7_1.BankOK src1700.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_684_954_208 12329

theorem width1700 : Lower6960.HelperSource.WidthGuard src1700.bank 179730 2308 src1700.reserve := requestWidth (by decide)

def ends1700 : List ℕ := [2308, 2309, 2313]

theorem inside1700 : Research6966.TerminalBanks.inside src1700.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1700 : Cover (Triangular src1700) 2313 2308 ends1700 := triangleCover (by decide +kernel)

def src1701 : Request := ⟨⟨⟨828,1150,260,15636⟩,17662013865984,49918096074⟩,20,7,1,900619,2⟩

theorem rank1701 : P3_7_1.BankOK src1701.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1150_260 15636

theorem width1701 : Lower6960.HelperSource.WidthGuard src1701.bank 179730 2308 src1701.reserve := requestWidth (by decide)

def ends1701 : List ℕ := [2309, 2313]

theorem inside1701 : Research6966.TerminalBanks.inside src1701.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1701 : Cover (Triangular src1701) 2313 2308 ends1701 := triangleCover (by decide +kernel)

def src1702 : Request := ⟨⟨⟨1750,2440,537,31694⟩,163381988556800,986966790957⟩,50,7,1,900619,2⟩

theorem rank1702 : P3_7_1.BankOK src1702.bank := by
  simpa only [src1702, _root_.Research6969.TransitionBanks.bank240] using _root_.Research6969.TransitionBanks.rank240 31694

theorem width1702 : Lower6960.HelperSource.WidthGuard src1702.bank 179730 2308 src1702.reserve := requestWidth (by decide)

def ends1702 : List ℕ := [2313]

theorem inside1702 : Research6966.TerminalBanks.inside src1702.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1702 : Cover (Triangular src1702) 2313 2308 ends1702 := triangleCover (by decide +kernel)

def src1703 : Request := ⟨⟨⟨1757,2439,539,91409⟩,165314219212800,988517960901⟩,85,7,1,900619,2⟩

theorem rank1703 : P3_7_1.BankOK src1703.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2439_539 91409

theorem width1703 : Lower6960.HelperSource.WidthGuard src1703.bank 179730 2308 src1703.reserve := requestWidth (by decide)

def ends1703 : List ℕ := [2308, 2309, 2313]

theorem inside1703 : Research6966.TerminalBanks.inside src1703.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1703 : Cover (Triangular src1703) 2313 2308 ends1703 := triangleCover (by decide +kernel)

def src1704 : Request := ⟨⟨⟨3969,5507,1244,81311⟩,1933998970634240,26084011577468⟩,145,7,1,900619,2⟩

theorem rank1704 : P3_7_1.BankOK src1704.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3969_5507_1244 81311

theorem width1704 : Lower6960.HelperSource.WidthGuard src1704.bank 179730 2308 src1704.reserve := requestWidth (by decide)

def ends1704 : List ℕ := [2308, 2309, 2313]




theorem cover1704 : Cover (Triangular src1704) 2313 2308 ends1704 := triangleCover (by decide +kernel)

def src1705 : Request := ⟨⟨⟨6934,9621,2174,130242⟩,10309790570905600,242895948111878⟩,245,7,1,900619,2⟩

theorem rank1705 : P3_7_1.BankOK src1705.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6934_9621_2174 130242

theorem width1705 : Lower6960.HelperSource.WidthGuard src1705.bank 179730 2308 src1705.reserve := requestWidth (by decide)

def ends1705 : List ℕ := [2308, 2309, 2313]




theorem cover1705 : Cover (Triangular src1705) 2313 2308 ends1705 := triangleCover (by decide +kernel)

def src1706 : Request := ⟨⟨⟨275,383,84,5419⟩,640970915840,608607683⟩,0,7,1,900619,4⟩

theorem rank1706 : P3_7_1.BankOK src1706.bank := by
  simpa only [src1706, _root_.Research6969.TransitionBanks.bank79] using _root_.Research6969.TransitionBanks.rank79 5419

theorem width1706 : Lower6960.HelperSource.WidthGuard src1706.bank 179730 2308 src1706.reserve := requestWidth (by decide)

def ends1706 : List ℕ := [2313]

theorem inside1706 : Research6966.TerminalBanks.inside src1706.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1706 : Cover (Triangular src1706) 2313 2308 ends1706 := triangleCover (by decide +kernel)

def src1707 : Request := ⟨⟨⟨325,453,98,6096⟩,1045036793856,1174588250⟩,1,7,1,900619,4⟩

theorem rank1707 : P3_7_1.BankOK src1707.bank := by
  simpa only [src1707, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 6096

theorem width1707 : Lower6960.HelperSource.WidthGuard src1707.bank 179730 2308 src1707.reserve := requestWidth (by decide)

def ends1707 : List ℕ := [2313]

theorem inside1707 : Research6966.TerminalBanks.inside src1707.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1707 : Cover (Triangular src1707) 2313 2308 ends1707 := triangleCover (by decide +kernel)

def src1708 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,2,7,1,900619,4⟩

theorem rank1708 : P3_7_1.BankOK src1708.bank := by
  simpa only [src1708, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 6858

theorem width1708 : Lower6960.HelperSource.WidthGuard src1708.bank 179730 2308 src1708.reserve := requestWidth (by decide)

def ends1708 : List ℕ := [2313]

theorem inside1708 : Research6966.TerminalBanks.inside src1708.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1708 : Cover (Triangular src1708) 2313 2308 ends1708 := triangleCover (by decide +kernel)

def src1709 : Request := ⟨⟨⟨325,452,98,8663⟩,1045036793856,1166286935⟩,4,7,1,900619,4⟩

theorem rank1709 : P3_7_1.BankOK src1709.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_452_98 8663

theorem width1709 : Lower6960.HelperSource.WidthGuard src1709.bank 179730 2308 src1709.reserve := requestWidth (by decide)

def ends1709 : List ℕ := [2308, 2309, 2313]

theorem inside1709 : Research6966.TerminalBanks.inside src1709.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1709 : Cover (Triangular src1709) 2313 2308 ends1709 := triangleCover (by decide +kernel)

def src171 : Request := ⟨⟨⟨2762,3836,861,29133⟩,649412627660800,6114405280540⟩,75,2,1,303410,46⟩

theorem rank171 : P3_7_1.BankOK src171.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2762_3836_861 29133

theorem width171 : Lower6960.HelperSource.WidthGuard src171.bank 179730 2308 src171.reserve := requestWidth (by decide)

def ends171 : List ℕ := [2308, 2309, 2313]

theorem inside171 : Research6966.TerminalBanks.inside src171.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover171 : Cover (Triangular src171) 2313 2308 ends171 := triangleCover (by decide +kernel)

def src1710 : Request := ⟨⟨⟨470,655,144,9763⟩,3184589537280,5168862572⟩,8,7,1,900619,4⟩

theorem rank1710 : P3_7_1.BankOK src1710.bank := by
  simpa only [src1710, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 9763

theorem width1710 : Lower6960.HelperSource.WidthGuard src1710.bank 179730 2308 src1710.reserve := requestWidth (by decide)

def ends1710 : List ℕ := [2313]

theorem inside1710 : Research6966.TerminalBanks.inside src1710.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1710 : Cover (Triangular src1710) 2313 2308 ends1710 := triangleCover (by decide +kernel)

def src1711 : Request := ⟨⟨⟨825,1150,253,15636⟩,17161575202816,48873782027⟩,20,7,1,900619,4⟩

theorem rank1711 : P3_7_1.BankOK src1711.bank := by
  simpa only [src1711, _root_.Research6969.TransitionBanks.bank201] using _root_.Research6969.TransitionBanks.rank201 15636

theorem width1711 : Lower6960.HelperSource.WidthGuard src1711.bank 179730 2308 src1711.reserve := requestWidth (by decide)

def ends1711 : List ℕ := [2308, 2313]

theorem inside1711 : Research6966.TerminalBanks.inside src1711.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1711 : Cover (Triangular src1711) 2313 2308 ends1711 := triangleCover (by decide +kernel)

def src1712 : Request := ⟨⟨⟨828,1149,254,31991⟩,17353252536320,48886547370⟩,32,7,1,900619,4⟩

theorem rank1712 : P3_7_1.BankOK src1712.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1149_254 31991

theorem width1712 : Lower6960.HelperSource.WidthGuard src1712.bank 179730 2308 src1712.reserve := requestWidth (by decide)

def ends1712 : List ℕ := [2308, 2309, 2313]

theorem inside1712 : Research6966.TerminalBanks.inside src1712.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1712 : Cover (Triangular src1712) 2313 2308 ends1712 := triangleCover (by decide +kernel)

def src1713 : Request := ⟨⟨⟨1445,2006,445,24930⟩,92282560184320,454009341867⟩,40,7,1,900619,4⟩

theorem rank1713 : P3_7_1.BankOK src1713.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1445_2006_445 24930

theorem width1713 : Lower6960.HelperSource.WidthGuard src1713.bank 179730 2308 src1713.reserve := requestWidth (by decide)

def ends1713 : List ℕ := [2308, 2309, 2313]

theorem inside1713 : Research6966.TerminalBanks.inside src1713.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1713 : Cover (Triangular src1713) 2313 2308 ends1713 := triangleCover (by decide +kernel)

def src1714 : Request := ⟨⟨⟨2610,3623,802,267582⟩,542100642856960,4813846676377⟩,145,7,1,900619,4⟩

theorem rank1714 : P3_7_1.BankOK src1714.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3623_802 267582

theorem width1714 : Lower6960.HelperSource.WidthGuard src1714.bank 179730 2308 src1714.reserve := requestWidth (by decide)

def ends1714 : List ℕ := [2308, 2309, 2313]

theorem inside1714 : Research6966.TerminalBanks.inside src1714.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1714 : Cover (Triangular src1714) 2313 2308 ends1714 := triangleCover (by decide +kernel)

def src1715 : Request := ⟨⟨⟨3956,5507,1213,81311⟩,1883453434626048,25577387039299⟩,145,7,1,900619,4⟩

theorem rank1715 : P3_7_1.BankOK src1715.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3956_5507_1213 81311

theorem width1715 : Lower6960.HelperSource.WidthGuard src1715.bank 179730 2308 src1715.reserve := requestWidth (by decide)

def ends1715 : List ℕ := [2308, 2309, 2313]




theorem cover1715 : Cover (Triangular src1715) 2313 2308 ends1715 := triangleCover (by decide +kernel)

def src1716 : Request := ⟨⟨⟨6908,9621,2118,130242⟩,10023012722278400,238016971510476⟩,245,7,1,900619,4⟩

theorem rank1716 : P3_7_1.BankOK src1716.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9621_2118 130242

theorem width1716 : Lower6960.HelperSource.WidthGuard src1716.bank 179730 2308 src1716.reserve := requestWidth (by decide)

def ends1716 : List ℕ := [2308, 2309, 2313]




theorem cover1716 : Cover (Triangular src1716) 2313 2308 ends1716 := triangleCover (by decide +kernel)

def src1717 : Request := ⟨⟨⟨325,453,100,4817⟩,1061047500800,1193036697⟩,0,7,1,900619,9⟩

theorem rank1717 : P3_7_1.BankOK src1717.bank := by
  simpa only [src1717, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 4817

theorem width1717 : Lower6960.HelperSource.WidthGuard src1717.bank 179730 2308 src1717.reserve := requestWidth (by decide)

def ends1717 : List ℕ := [2308, 2313]

theorem inside1717 : Research6966.TerminalBanks.inside src1717.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1717 : Cover (Triangular src1717) 2313 2308 ends1717 := triangleCover (by decide +kernel)

def src1718 : Request := ⟨⟨⟨325,451,98,5391⟩,1045036793856,1158025616⟩,1,7,1,900619,9⟩

theorem rank1718 : P3_7_1.BankOK src1718.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 5391

theorem width1718 : Lower6960.HelperSource.WidthGuard src1718.bank 179730 2308 src1718.reserve := requestWidth (by decide)

def ends1718 : List ℕ := [2308, 2309, 2313]

theorem inside1718 : Research6966.TerminalBanks.inside src1718.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1718 : Cover (Triangular src1718) 2313 2308 ends1718 := triangleCover (by decide +kernel)

def src1719 : Request := ⟨⟨⟨325,451,98,6857⟩,1045036793856,1158025616⟩,3,7,1,900619,9⟩

theorem rank1719 : P3_7_1.BankOK src1719.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 6857

theorem width1719 : Lower6960.HelperSource.WidthGuard src1719.bank 179730 2308 src1719.reserve := requestWidth (by decide)

def ends1719 : List ℕ := [2308, 2309, 2313]

theorem inside1719 : Research6966.TerminalBanks.inside src1719.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1719 : Cover (Triangular src1719) 2313 2308 ends1719 := triangleCover (by decide +kernel)

def src172 : Request := ⟨⟨⟨2601,3622,793,48764⟩,533334139076608,4767521972754⟩,15,2,1,303418,25⟩

theorem rank172 : P3_7_1.BankOK src172.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3622_793 48764

theorem width172 : Lower6960.HelperSource.WidthGuard src172.bank 179730 2308 src172.reserve := requestWidth (by decide)

def ends172 : List ℕ := [2308, 2309, 2313]

theorem inside172 : Research6966.TerminalBanks.inside src172.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover172 : Cover (Triangular src172) 2313 2308 ends172 := triangleCover (by decide +kernel)

def src1720 : Request := ⟨⟨⟨472,655,148,8679⟩,3282009849856,5279398867⟩,8,7,1,900619,9⟩

theorem rank1720 : P3_7_1.BankOK src1720.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_472_655_148 8679

theorem width1720 : Lower6960.HelperSource.WidthGuard src1720.bank 179730 2308 src1720.reserve := requestWidth (by decide)

def ends1720 : List ℕ := [2308, 2313]

theorem inside1720 : Research6966.TerminalBanks.inside src1720.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1720 : Cover (Triangular src1720) 2313 2308 ends1720 := triangleCover (by decide +kernel)

def src1721 : Request := ⟨⟨⟨829,1150,260,13899⟩,17709839155200,49918096074⟩,20,7,1,900619,9⟩

theorem rank1721 : P3_7_1.BankOK src1721.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_829_1150_260 13899

theorem width1721 : Lower6960.HelperSource.WidthGuard src1721.bank 179730 2308 src1721.reserve := requestWidth (by decide)

def ends1721 : List ℕ := [2309, 2313]

theorem inside1721 : Research6966.TerminalBanks.inside src1721.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1721 : Cover (Triangular src1721) 2313 2308 ends1721 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources27

section Pack_R6970Height2313CommonSources28

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1722 : Request := ⟨⟨⟨1002,1393,311,103870⟩,30996708720640,106290385107⟩,50,7,1,900619,9⟩

theorem rank1722 : P3_7_1.BankOK src1722.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1393_311 103870

theorem width1722 : Lower6960.HelperSource.WidthGuard src1722.bank 179730 2308 src1722.reserve := requestWidth (by decide)

def ends1722 : List ℕ := [2308, 2309, 2313]

theorem inside1722 : Research6966.TerminalBanks.inside src1722.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1722 : Cover (Triangular src1722) 2313 2308 ends1722 := triangleCover (by decide +kernel)

def src1723 : Request := ⟨⟨⟨2100,2928,645,35655⟩,282396798484480,2046887686018⟩,65,7,1,900619,9⟩

theorem rank1723 : P3_7_1.BankOK src1723.bank := by
  simpa only [src1723, _root_.Research6969.TransitionBanks.bank247] using _root_.Research6969.TransitionBanks.rank247 35655

theorem width1723 : Lower6960.HelperSource.WidthGuard src1723.bank 179730 2308 src1723.reserve := requestWidth (by decide)

def ends1723 : List ℕ := [2313]

theorem inside1723 : Research6966.TerminalBanks.inside src1723.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1723 : Cover (Triangular src1723) 2313 2308 ends1723 := triangleCover (by decide +kernel)

def src1724 : Request := ⟨⟨⟨3211,4459,1008,602179⟩,1025579260837888,11221829825062⟩,190,7,1,900619,9⟩

theorem rank1724 : P3_7_1.BankOK src1724.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3211_4459_1008 602179

theorem width1724 : Lower6960.HelperSource.WidthGuard src1724.bank 179730 2308 src1724.reserve := requestWidth (by decide)

def ends1724 : List ℕ := [2308, 2309, 2313]




theorem cover1724 : Cover (Triangular src1724) 2313 2308 ends1724 := triangleCover (by decide +kernel)

def src1725 : Request := ⟨⟨⟨5680,7884,1750,91425⟩,5593163081973760,108040693109459⟩,190,7,1,900619,9⟩

theorem rank1725 : P3_7_1.BankOK src1725.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5680_7884_1750 91425

theorem width1725 : Lower6960.HelperSource.WidthGuard src1725.bank 179730 2308 src1725.reserve := requestWidth (by decide)

def ends1725 : List ℕ := [2308, 2309, 2313]




theorem cover1725 : Cover (Triangular src1725) 2313 2308 ends1725 := triangleCover (by decide +kernel)

def src1726 : Request := ⟨⟨⟨3991,5536,1244,2110431⟩,1958113417625600,26529200910168⟩,245,7,1,900619,9⟩

theorem rank1726 : P3_7_1.BankOK src1726.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3991_5536_1244 2110431

theorem width1726 : Lower6960.HelperSource.WidthGuard src1726.bank 179730 2308 src1726.reserve := requestWidth (by decide)

def ends1726 : List ℕ := [2308, 2309, 2313]




theorem cover1726 : Cover (Triangular src1726) 2313 2308 ends1726 := triangleCover (by decide +kernel)

def src1727 : Request := ⟨⟨⟨325,453,100,4282⟩,1061047500800,1193036697⟩,0,7,1,900619,16⟩

theorem rank1727 : P3_7_1.BankOK src1727.bank := by
  simpa only [src1727, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 4282

theorem width1727 : Lower6960.HelperSource.WidthGuard src1727.bank 179730 2308 src1727.reserve := requestWidth (by decide)

def ends1727 : List ℕ := [2313]

theorem inside1727 : Research6966.TerminalBanks.inside src1727.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1727 : Cover (Triangular src1727) 2313 2308 ends1727 := triangleCover (by decide +kernel)

def src1728 : Request := ⟨⟨⟨325,452,98,4810⟩,1045036793856,1166286935⟩,1,7,1,900619,16⟩

theorem rank1728 : P3_7_1.BankOK src1728.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_452_98 4810

theorem width1728 : Lower6960.HelperSource.WidthGuard src1728.bank 179730 2308 src1728.reserve := requestWidth (by decide)

def ends1728 : List ℕ := [2308, 2309, 2313]

theorem inside1728 : Research6966.TerminalBanks.inside src1728.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1728 : Cover (Triangular src1728) 2313 2308 ends1728 := triangleCover (by decide +kernel)

def src1729 : Request := ⟨⟨⟨326,453,98,5419⟩,1052225568768,1174588250⟩,2,7,1,900619,16⟩

theorem rank1729 : P3_7_1.BankOK src1729.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_98 5419

theorem width1729 : Lower6960.HelperSource.WidthGuard src1729.bank 179730 2308 src1729.reserve := requestWidth (by decide)

def ends1729 : List ℕ := [2308, 2313]

theorem inside1729 : Research6966.TerminalBanks.inside src1729.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1729 : Cover (Triangular src1729) 2313 2308 ends1729 := triangleCover (by decide +kernel)

def src173 : Request := ⟨⟨⟨2998,4178,900,90315⟩,806961139154944,8331876423452⟩,21,2,1,303418,25⟩

theorem rank173 : P3_7_1.BankOK src173.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4178_900 90315

theorem width173 : Lower6960.HelperSource.WidthGuard src173.bank 179730 2308 src173.reserve := requestWidth (by decide)

def ends173 : List ℕ := [2308, 2309, 2313]

theorem inside173 : Research6966.TerminalBanks.inside src173.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover173 : Cover (Triangular src173) 2313 2308 ends173 := triangleCover (by decide +kernel)

def src1730 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,4,7,1,900619,16⟩

theorem rank1730 : P3_7_1.BankOK src1730.bank := by
  simpa only [src1730, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 6096

theorem width1730 : Lower6960.HelperSource.WidthGuard src1730.bank 179730 2308 src1730.reserve := requestWidth (by decide)

def ends1730 : List ℕ := [2313]

theorem inside1730 : Research6966.TerminalBanks.inside src1730.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1730 : Cover (Triangular src1730) 2313 2308 ends1730 := triangleCover (by decide +kernel)

def src1731 : Request := ⟨⟨⟨471,655,148,7715⟩,3266464186368,5279398867⟩,8,7,1,900619,16⟩

theorem rank1731 : P3_7_1.BankOK src1731.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 7715

theorem width1731 : Lower6960.HelperSource.WidthGuard src1731.bank 179730 2308 src1731.reserve := requestWidth (by decide)

def ends1731 : List ℕ := [2309, 2313]

theorem inside1731 : Research6966.TerminalBanks.inside src1731.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1731 : Cover (Triangular src1731) 2313 2308 ends1731 := triangleCover (by decide +kernel)

def src1732 : Request := ⟨⟨⟨687,954,212,10961⟩,9968111583232,23361831549⟩,16,7,1,900619,16⟩

theorem rank1732 : P3_7_1.BankOK src1732.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_687_954_212 10961

theorem width1732 : Lower6960.HelperSource.WidthGuard src1732.bank 179730 2308 src1732.reserve := requestWidth (by decide)

def ends1732 : List ℕ := [2308, 2309, 2313]

theorem inside1732 : Research6966.TerminalBanks.inside src1732.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1732 : Cover (Triangular src1732) 2313 2308 ends1732 := triangleCover (by decide +kernel)

def src1733 : Request := ⟨⟨⟨1194,1657,368,22218⟩,52130505031680,211736467619⟩,40,7,1,900619,16⟩

theorem rank1733 : P3_7_1.BankOK src1733.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1194_1657_368 22218

theorem width1733 : Lower6960.HelperSource.WidthGuard src1733.bank 179730 2308 src1733.reserve := requestWidth (by decide)

def ends1733 : List ℕ := [2308, 2309, 2313]

theorem inside1733 : Research6966.TerminalBanks.inside src1733.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1733 : Cover (Triangular src1733) 2313 2308 ends1733 := triangleCover (by decide +kernel)

def src1734 : Request := ⟨⟨⟨1756,2439,538,72316⟩,164871213416448,987092092177⟩,85,7,1,900619,16⟩

theorem rank1734 : P3_7_1.BankOK src1734.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1756_2439_538 72316

theorem width1734 : Lower6960.HelperSource.WidthGuard src1734.bank 179730 2308 src1734.reserve := requestWidth (by decide)

def ends1734 : List ℕ := [2308, 2309, 2313]

theorem inside1734 : Research6966.TerminalBanks.inside src1734.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1734 : Cover (Triangular src1734) 2313 2308 ends1734 := triangleCover (by decide +kernel)

def src1735 : Request := ⟨⟨⟨3966,5507,1244,64247⟩,1930722875801600,26084011577468⟩,145,7,1,900619,16⟩

theorem rank1735 : P3_7_1.BankOK src1735.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3966_5507_1244 64247

theorem width1735 : Lower6960.HelperSource.WidthGuard src1735.bank 179730 2308 src1735.reserve := requestWidth (by decide)

def ends1735 : List ℕ := [2308, 2309, 2313]




theorem cover1735 : Cover (Triangular src1735) 2313 2308 ends1735 := triangleCover (by decide +kernel)

def src1736 : Request := ⟨⟨⟨3226,4475,1008,477599⟩,1036351157567488,11352091862286⟩,190,7,1,900619,16⟩

theorem rank1736 : P3_7_1.BankOK src1736.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3226_4475_1008 477599

theorem width1736 : Lower6960.HelperSource.WidthGuard src1736.bank 179730 2308 src1736.reserve := requestWidth (by decide)

def ends1736 : List ℕ := [2308, 2309, 2313]




theorem cover1736 : Cover (Triangular src1736) 2313 2308 ends1736 := triangleCover (by decide +kernel)

def src1737 : Request := ⟨⟨⟨6938,9621,2174,102908⟩,10323131249459200,242895948111878⟩,245,7,1,900619,16⟩

theorem rank1737 : P3_7_1.BankOK src1737.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6938_9621_2174 102908

theorem width1737 : Lower6960.HelperSource.WidthGuard src1737.bank 179730 2308 src1737.reserve := requestWidth (by decide)

def ends1737 : List ℕ := [2308, 2309, 2313]




theorem cover1737 : Cover (Triangular src1737) 2313 2308 ends1737 := triangleCover (by decide +kernel)

def src1738 : Request := ⟨⟨⟨226,314,69,4282⟩,356954931200,276676118⟩,0,7,1,900619,26⟩

theorem rank1738 : P3_7_1.BankOK src1738.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_226_314_69 4282

theorem width1738 : Lower6960.HelperSource.WidthGuard src1738.bank 179730 2308 src1738.reserve := requestWidth (by decide)

def ends1738 : List ℕ := [2313]

theorem inside1738 : Research6966.TerminalBanks.inside src1738.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1738 : Cover (Triangular src1738) 2313 2308 ends1738 := triangleCover (by decide +kernel)

def src1739 : Request := ⟨⟨⟨275,382,83,4274⟩,635228389376,597984703⟩,1,7,1,900619,26⟩

theorem rank1739 : P3_7_1.BankOK src1739.bank := by
  simpa only [src1739, _root_.Research6969.TransitionBanks.bank77] using _root_.Research6969.TransitionBanks.rank77 4274

theorem width1739 : Lower6960.HelperSource.WidthGuard src1739.bank 179730 2308 src1739.reserve := requestWidth (by decide)

def ends1739 : List ℕ := [2308, 2309, 2313]

theorem inside1739 : Research6966.TerminalBanks.inside src1739.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1739 : Cover (Triangular src1739) 2313 2308 ends1739 := triangleCover (by decide +kernel)

def src174 : Request := ⟨⟨⟨2779,3857,861,33491⟩,658403560521728,6222886282400⟩,75,2,1,303625,45⟩

theorem rank174 : P3_7_1.BankOK src174.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2779_3857_861 33491

theorem width174 : Lower6960.HelperSource.WidthGuard src174.bank 179730 2308 src174.reserve := requestWidth (by decide)

def ends174 : List ℕ := [2308, 2309, 2313]

theorem inside174 : Research6966.TerminalBanks.inside src174.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover174 : Cover (Triangular src174) 2313 2308 ends174 := triangleCover (by decide +kernel)

def src1740 : Request := ⟨⟨⟨326,452,100,4815⟩,1068355026944,1184600066⟩,3,7,1,900619,26⟩

theorem rank1740 : P3_7_1.BankOK src1740.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_452_100 4815

theorem width1740 : Lower6960.HelperSource.WidthGuard src1740.bank 179730 2308 src1740.reserve := requestWidth (by decide)

def ends1740 : List ℕ := [2308, 2309, 2313]

theorem inside1740 : Research6966.TerminalBanks.inside src1740.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1740 : Cover (Triangular src1740) 2313 2308 ends1740 := triangleCover (by decide +kernel)

def src1741 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,6,7,1,900619,26⟩

theorem rank1741 : P3_7_1.BankOK src1741.bank := by
  simpa only [src1741, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 6096

theorem width1741 : Lower6960.HelperSource.WidthGuard src1741.bank 179730 2308 src1741.reserve := requestWidth (by decide)

def ends1741 : List ℕ := [2313]

theorem inside1741 : Research6966.TerminalBanks.inside src1741.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1741 : Cover (Triangular src1741) 2313 2308 ends1741 := triangleCover (by decide +kernel)

def src1742 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,13,7,1,900619,26⟩

theorem rank1742 : P3_7_1.BankOK src1742.bank := by
  simpa only [src1742, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 8679

theorem width1742 : Lower6960.HelperSource.WidthGuard src1742.bank 179730 2308 src1742.reserve := requestWidth (by decide)

def ends1742 : List ℕ := [2308, 2309, 2313]

theorem inside1742 : Research6966.TerminalBanks.inside src1742.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1742 : Cover (Triangular src1742) 2313 2308 ends1742 := triangleCover (by decide +kernel)

def src1743 : Request := ⟨⟨⟨1000,1386,307,15618⟩,30557599170560,103536241407⟩,32,7,1,900619,26⟩

theorem rank1743 : P3_7_1.BankOK src1743.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1386_307 15618

theorem width1743 : Lower6960.HelperSource.WidthGuard src1743.bank 179730 2308 src1743.reserve := requestWidth (by decide)

def ends1743 : List ℕ := [2308, 2309, 2313]

theorem inside1743 : Research6966.TerminalBanks.inside src1743.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1743 : Cover (Triangular src1743) 2313 2308 ends1743 := triangleCover (by decide +kernel)

def src1744 : Request := ⟨⟨⟨2600,3624,798,50764⟩,535425056505856,4799424311630⟩,110,7,1,900619,26⟩

theorem rank1744 : P3_7_1.BankOK src1744.bank := by
  simpa only [src1744, _root_.Research6969.TransitionBanks.bank260] using _root_.Research6969.TransitionBanks.rank260 50764

theorem width1744 : Lower6960.HelperSource.WidthGuard src1744.bank 179730 2308 src1744.reserve := requestWidth (by decide)

def ends1744 : List ℕ := [2313]

theorem inside1744 : Research6966.TerminalBanks.inside src1744.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1744 : Cover (Triangular src1744) 2313 2308 ends1744 := triangleCover (by decide +kernel)

def src1745 : Request := ⟨⟨⟨2606,3623,819,164837⟩,548892770304000,4892906717079⟩,145,7,1,900619,26⟩

theorem rank1745 : P3_7_1.BankOK src1745.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3623_819 164837

theorem width1745 : Lower6960.HelperSource.WidthGuard src1745.bank 179730 2308 src1745.reserve := requestWidth (by decide)

def ends1745 : List ℕ := [2308, 2309, 2313]

theorem inside1745 : Research6966.TerminalBanks.inside src1745.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1745 : Cover (Triangular src1745) 2313 2308 ends1745 := triangleCover (by decide +kernel)

def src1746 : Request := ⟨⟨⟨3211,4459,1008,422931⟩,1025579260837888,11221829825062⟩,190,7,1,900619,26⟩

theorem rank1746 : P3_7_1.BankOK src1746.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3211_4459_1008 422931

theorem width1746 : Lower6960.HelperSource.WidthGuard src1746.bank 179730 2308 src1746.reserve := requestWidth (by decide)

def ends1746 : List ℕ := [2308, 2309, 2313]




theorem cover1746 : Cover (Triangular src1746) 2313 2308 ends1746 := triangleCover (by decide +kernel)

def src1747 : Request := ⟨⟨⟨4802,6692,1512,72277⟩,3436345657393152,56871238465897⟩,190,7,1,900619,26⟩

theorem rank1747 : P3_7_1.BankOK src1747.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4802_6692_1512 72277

theorem width1747 : Lower6960.HelperSource.WidthGuard src1747.bank 179730 2308 src1747.reserve := requestWidth (by decide)

def ends1747 : List ℕ := [2308, 2309, 2313]




theorem cover1747 : Cover (Triangular src1747) 2313 2308 ends1747 := triangleCover (by decide +kernel)

def src1748 : Request := ⟨⟨⟨3991,5536,1244,1475347⟩,1958113417625600,26529200910168⟩,245,7,1,900619,26⟩

theorem rank1748 : P3_7_1.BankOK src1748.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3991_5536_1244 1475347

theorem width1748 : Lower6960.HelperSource.WidthGuard src1748.bank 179730 2308 src1748.reserve := requestWidth (by decide)

def ends1748 : List ℕ := [2308, 2309, 2313]




theorem cover1748 : Cover (Triangular src1748) 2313 2308 ends1748 := triangleCover (by decide +kernel)

def src1749 : Request := ⟨⟨⟨225,314,68,3384⟩,349597597696,273591980⟩,0,7,1,900619,41⟩

theorem rank1749 : P3_7_1.BankOK src1749.bank := by
  simpa only [src1749, _root_.Research6969.TransitionBanks.bank59] using _root_.Research6969.TransitionBanks.rank59 3384

theorem width1749 : Lower6960.HelperSource.WidthGuard src1749.bank 179730 2308 src1749.reserve := requestWidth (by decide)

def ends1749 : List ℕ := [2313]

theorem inside1749 : Research6966.TerminalBanks.inside src1749.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1749 : Cover (Triangular src1749) 2313 2308 ends1749 := triangleCover (by decide +kernel)

def src175 : Request := ⟨⟨⟨2814,3905,870,30246⟩,682484369981440,6528319804485⟩,74,2,1,303625,45⟩

theorem rank175 : P3_7_1.BankOK src175.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2814_3905_870 30246

theorem width175 : Lower6960.HelperSource.WidthGuard src175.bank 179730 2308 src175.reserve := requestWidth (by decide)

def ends175 : List ℕ := [2308, 2309, 2313]

theorem inside175 : Research6966.TerminalBanks.inside src175.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover175 : Cover (Triangular src175) 2313 2308 ends175 := triangleCover (by decide +kernel)

def src1750 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,1,7,1,900619,41⟩

theorem rank1750 : P3_7_1.BankOK src1750.bank := by
  simpa only [src1750, _root_.Research6969.TransitionBanks.bank78] using _root_.Research6969.TransitionBanks.rank78 3384

theorem width1750 : Lower6960.HelperSource.WidthGuard src1750.bank 179730 2308 src1750.reserve := requestWidth (by decide)

def ends1750 : List ℕ := [2313]

theorem inside1750 : Research6966.TerminalBanks.inside src1750.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1750 : Cover (Triangular src1750) 2313 2308 ends1750 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources28

section Pack_R6970Height2313CommonSources60

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src969 : Request := ⟨⟨⟨10040,13952,3070,130242⟩,30701621376450560,1051954539834997⟩,145,3,1,385979,28⟩

theorem rank969 : P3_7_1.BankOK src969.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10040_13952_3070 130242

theorem width969 : Lower6960.HelperSource.WidthGuard src969.bank 179730 2308 src969.reserve := requestWidth (by decide)

def ends969 : List ℕ := [2308, 2313]



theorem cover969 : Cover (Triangular src969) 2313 2308 ends969 := triangleCover (by decide +kernel)

def src97 : Request := ⟨⟨⟨3004,4175,898,119239⟩,809203095306240,8298222886581⟩,325,2,1,257515,1025⟩

theorem rank97 : P3_7_1.BankOK src97.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3004_4175_898 119239

theorem width97 : Lower6960.HelperSource.WidthGuard src97.bank 179730 2308 src97.reserve := requestWidth (by decide)

def ends97 : List ℕ := [2308, 2309, 2313]

theorem inside97 : Research6966.TerminalBanks.inside src97.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover97 : Cover (Triangular src97) 2313 2308 ends97 := triangleCover (by decide +kernel)

def src970 : Request := ⟨⟨⟨693,963,212,7715⟩,10163930791936,24078187611⟩,0,3,1,385979,29⟩

theorem rank970 : P3_7_1.BankOK src970.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_963_212 7715

theorem width970 : Lower6960.HelperSource.WidthGuard src970.bank 179730 2308 src970.reserve := requestWidth (by decide)

def ends970 : List ℕ := [2309, 2313]

theorem inside970 : Research6966.TerminalBanks.inside src970.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover970 : Cover (Triangular src970) 2313 2308 ends970 := triangleCover (by decide +kernel)

def src971 : Request := ⟨⟨⟨694,963,212,8679⟩,10196762755072,24078187611⟩,1,3,1,385979,29⟩

theorem rank971 : P3_7_1.BankOK src971.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_694_963_212 8679

theorem width971 : Lower6960.HelperSource.WidthGuard src971.bank 179730 2308 src971.reserve := requestWidth (by decide)

def ends971 : List ℕ := [2308, 2309, 2313]

theorem inside971 : Research6966.TerminalBanks.inside src971.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover971 : Cover (Triangular src971) 2313 2308 ends971 := triangleCover (by decide +kernel)

def src972 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,2,3,1,385979,29⟩

theorem rank972 : P3_7_1.BankOK src972.bank := by
  simpa only [src972, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 9763

theorem width972 : Lower6960.HelperSource.WidthGuard src972.bank 179730 2308 src972.reserve := requestWidth (by decide)

def ends972 : List ℕ := [2313]

theorem inside972 : Research6966.TerminalBanks.inside src972.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover972 : Cover (Triangular src972) 2313 2308 ends972 := triangleCover (by decide +kernel)

def src973 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,3,3,1,385979,29⟩

theorem rank973 : P3_7_1.BankOK src973.bank := by
  simpa only [src973, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 10983

theorem width973 : Lower6960.HelperSource.WidthGuard src973.bank 179730 2308 src973.reserve := requestWidth (by decide)

def ends973 : List ℕ := [2313]

theorem inside973 : Research6966.TerminalBanks.inside src973.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover973 : Cover (Triangular src973) 2313 2308 ends973 := triangleCover (by decide +kernel)

def src974 : Request := ⟨⟨⟨1002,1391,307,12313⟩,30694534807552,104743003887⟩,6,3,1,385979,29⟩

theorem rank974 : P3_7_1.BankOK src974.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1391_307 12313

theorem width974 : Lower6960.HelperSource.WidthGuard src974.bank 179730 2308 src974.reserve := requestWidth (by decide)

def ends974 : List ℕ := [2308, 2309, 2313]

theorem inside974 : Research6966.TerminalBanks.inside src974.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover974 : Cover (Triangular src974) 2313 2308 ends974 := triangleCover (by decide +kernel)

def src975 : Request := ⟨⟨⟨1457,2023,447,22409⟩,94327162273792,468139690480⟩,16,3,1,385979,29⟩

theorem rank975 : P3_7_1.BankOK src975.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1457_2023_447 22409

theorem width975 : Lower6960.HelperSource.WidthGuard src975.bank 179730 2308 src975.reserve := requestWidth (by decide)

def ends975 : List ℕ := [2308, 2309, 2313]

theorem inside975 : Research6966.TerminalBanks.inside src975.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover975 : Cover (Triangular src975) 2313 2308 ends975 := triangleCover (by decide +kernel)

def src976 : Request := ⟨⟨⟨2601,3611,798,31550⟩,535886272135168,4744211205591⟩,32,3,1,385979,29⟩

theorem rank976 : P3_7_1.BankOK src976.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3611_798 31550

theorem width976 : Lower6960.HelperSource.WidthGuard src976.bank 179730 2308 src976.reserve := requestWidth (by decide)

def ends976 : List ℕ := [2308, 2309, 2313]

theorem inside976 : Research6966.TerminalBanks.inside src976.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover976 : Cover (Triangular src976) 2313 2308 ends976 := triangleCover (by decide +kernel)

def src977 : Request := ⟨⟨⟨2615,3627,819,31108⟩,553151842222080,4910333421859⟩,32,3,1,385979,29⟩

theorem rank977 : P3_7_1.BankOK src977.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 31108

theorem width977 : Lower6960.HelperSource.WidthGuard src977.bank 179730 2308 src977.reserve := requestWidth (by decide)

def ends977 : List ℕ := [2309, 2313]

theorem inside977 : Research6966.TerminalBanks.inside src977.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover977 : Cover (Triangular src977) 2313 2308 ends977 := triangleCover (by decide +kernel)

def src978 : Request := ⟨⟨⟨2860,3984,871,81311⟩,708336323395584,6969433801209⟩,45,3,1,386273,29⟩

theorem rank978 : P3_7_1.BankOK src978.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2860_3984_871 81311

theorem width978 : Lower6960.HelperSource.WidthGuard src978.bank 179730 2308 src978.reserve := requestWidth (by decide)

def ends978 : List ℕ := [2308, 2309, 2313]

theorem inside978 : Research6966.TerminalBanks.inside src978.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover978 : Cover (Triangular src978) 2313 2308 ends978 := triangleCover (by decide +kernel)

def src979 : Request := ⟨⟨⟨4918,6829,1503,130242⟩,3608781531381760,60426714374650⟩,85,3,1,386273,29⟩

theorem rank979 : P3_7_1.BankOK src979.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4918_6829_1503 130242

theorem width979 : Lower6960.HelperSource.WidthGuard src979.bank 179730 2308 src979.reserve := requestWidth (by decide)

def ends979 : List ℕ := [2309, 2313]



theorem cover979 : Cover (Triangular src979) 2313 2308 ends979 := triangleCover (by decide +kernel)

def src98 : Request := ⟨⟨⟨2808,3900,854,113974⟩,669724928901120,6408244632207⟩,325,2,1,257319,2049⟩

theorem rank98 : P3_7_1.BankOK src98.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 113974

theorem width98 : Lower6960.HelperSource.WidthGuard src98.bank 179730 2308 src98.reserve := requestWidth (by decide)

def ends98 : List ℕ := [2308, 2309, 2313]

theorem inside98 : Research6966.TerminalBanks.inside src98.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover98 : Cover (Triangular src98) 2313 2308 ends98 := triangleCover (by decide +kernel)

def src980 : Request := ⟨⟨⟨5701,7920,1750,72204⟩,5639585936441344,109637722514009⟩,85,3,1,385979,29⟩

theorem rank980 : P3_7_1.BankOK src980.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5701_7920_1750 72204

theorem width980 : Lower6960.HelperSource.WidthGuard src980.bank 179730 2308 src980.reserve := requestWidth (by decide)

def ends980 : List ℕ := [2308, 2309, 2313]




theorem cover980 : Cover (Triangular src980) 2313 2308 ends980 := triangleCover (by decide +kernel)

def src981 : Request := ⟨⟨⟨6900,9626,2118,102908⟩,9997036108906496,238415548481346⟩,110,3,1,385979,29⟩

theorem rank981 : P3_7_1.BankOK src981.bank := by
  simpa only [src981, _root_.Research6969.TransitionBanks.bank356] using _root_.Research6969.TransitionBanks.rank356 102908

theorem width981 : Lower6960.HelperSource.WidthGuard src981.bank 179730 2308 src981.reserve := requestWidth (by decide)

def ends981 : List ℕ := [2308, 2313]



theorem cover981 : Cover (Triangular src981) 2313 2308 ends981 := triangleCover (by decide +kernel)

def src982 : Request := ⟨⟨⟨10040,13952,3070,115771⟩,30701621376450560,1051954539834997⟩,145,3,1,385979,29⟩

theorem rank982 : P3_7_1.BankOK src982.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10040_13952_3070 115771

theorem width982 : Lower6960.HelperSource.WidthGuard src982.bank 179730 2308 src982.reserve := requestWidth (by decide)

def ends982 : List ℕ := [2309, 2313]



theorem cover982 : Cover (Triangular src982) 2313 2308 ends982 := triangleCover (by decide +kernel)

def src983 : Request := ⟨⟨⟨560,777,169,8657⟩,5316921262080,10130698125⟩,0,3,1,385979,30⟩

theorem rank983 : P3_7_1.BankOK src983.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_560_777_169 8657

theorem width983 : Lower6960.HelperSource.WidthGuard src983.bank 179730 2308 src983.reserve := requestWidth (by decide)

def ends983 : List ℕ := [2308, 2309, 2313]

theorem inside983 : Research6966.TerminalBanks.inside src983.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover983 : Cover (Triangular src983) 2313 2308 ends983 := triangleCover (by decide +kernel)

def src984 : Request := ⟨⟨⟨691,963,208,8679⟩,9953791705088,23724874690⟩,1,3,1,385979,30⟩

theorem rank984 : P3_7_1.BankOK src984.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_963_208 8679

theorem width984 : Lower6960.HelperSource.WidthGuard src984.bank 179730 2308 src984.reserve := requestWidth (by decide)

def ends984 : List ℕ := [2308, 2309, 2313]

theorem inside984 : Research6966.TerminalBanks.inside src984.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover984 : Cover (Triangular src984) 2313 2308 ends984 := triangleCover (by decide +kernel)

def src985 : Request := ⟨⟨⟨686,954,208,9566⟩,9793536524288,23019418180⟩,2,3,1,385979,30⟩

theorem rank985 : P3_7_1.BankOK src985.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_686_954_208 9566

theorem width985 : Lower6960.HelperSource.WidthGuard src985.bank 179730 2308 src985.reserve := requestWidth (by decide)

def ends985 : List ℕ := [2308, 2309, 2313]

theorem inside985 : Research6966.TerminalBanks.inside src985.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover985 : Cover (Triangular src985) 2313 2308 ends985 := triangleCover (by decide +kernel)

def src986 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,4,3,1,385979,30⟩

theorem rank986 : P3_7_1.BankOK src986.bank := by
  simpa only [src986, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 10983

theorem width986 : Lower6960.HelperSource.WidthGuard src986.bank 179730 2308 src986.reserve := requestWidth (by decide)

def ends986 : List ℕ := [2313]

theorem inside986 : Research6966.TerminalBanks.inside src986.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover986 : Cover (Triangular src986) 2313 2308 ends986 := triangleCover (by decide +kernel)

def src987 : Request := ⟨⟨⟨1003,1395,315,10983⟩,31367332102144,107844841957⟩,6,3,1,385979,30⟩

theorem rank987 : P3_7_1.BankOK src987.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_315 10983

theorem width987 : Lower6960.HelperSource.WidthGuard src987.bank 179730 2308 src987.reserve := requestWidth (by decide)

def ends987 : List ℕ := [2308, 2309, 2313]

theorem inside987 : Research6966.TerminalBanks.inside src987.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover987 : Cover (Triangular src987) 2313 2308 ends987 := triangleCover (by decide +kernel)

def src988 : Request := ⟨⟨⟨1204,1674,378,13899⟩,54201301073920,223406703910⟩,10,3,1,385979,30⟩

theorem rank988 : P3_7_1.BankOK src988.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1204_1674_378 13899

theorem width988 : Lower6960.HelperSource.WidthGuard src988.bank 179730 2308 src988.reserve := requestWidth (by decide)

def ends988 : List ℕ := [2309, 2313]

theorem inside988 : Research6966.TerminalBanks.inside src988.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover988 : Cover (Triangular src988) 2313 2308 ends988 := triangleCover (by decide +kernel)

def src989 : Request := ⟨⟨⟨2101,2930,645,25043⟩,282697978609664,2051392203643⟩,25,3,1,385979,30⟩

theorem rank989 : P3_7_1.BankOK src989.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2101_2930_645 25043

theorem width989 : Lower6960.HelperSource.WidthGuard src989.bank 179730 2308 src989.reserve := requestWidth (by decide)

def ends989 : List ℕ := [2308, 2309, 2313]

theorem inside989 : Research6966.TerminalBanks.inside src989.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover989 : Cover (Triangular src989) 2313 2308 ends989 := triangleCover (by decide +kernel)

def src99 : Request := ⟨⟨⟨2805,3896,853,116061⟩,667529745268736,6381285980181⟩,325,2,1,257319,2049⟩

theorem rank99 : P3_7_1.BankOK src99.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3896_853 116061

theorem width99 : Lower6960.HelperSource.WidthGuard src99.bank 179730 2308 src99.reserve := requestWidth (by decide)

def ends99 : List ℕ := [2308, 2309, 2313]

theorem inside99 : Research6966.TerminalBanks.inside src99.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover99 : Cover (Triangular src99) 2313 2308 ends99 := triangleCover (by decide +kernel)

def src990 : Request := ⟨⟨⟨2288,3177,702,31509⟩,364872686370816,2843261695012⟩,32,3,1,385979,30⟩

theorem rank990 : P3_7_1.BankOK src990.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2288_3177_702 31509

theorem width990 : Lower6960.HelperSource.WidthGuard src990.bank 179730 2308 src990.reserve := requestWidth (by decide)

def ends990 : List ℕ := [2308, 2309, 2313]

theorem inside990 : Research6966.TerminalBanks.inside src990.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover990 : Cover (Triangular src990) 2313 2308 ends990 := triangleCover (by decide +kernel)

def src991 : Request := ⟨⟨⟨2813,3906,862,50090⟩,677178014171136,6486944896419⟩,45,3,1,385979,30⟩

theorem rank991 : P3_7_1.BankOK src991.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2813_3906_862 50090

theorem width991 : Lower6960.HelperSource.WidthGuard src991.bank 179730 2308 src991.reserve := requestWidth (by decide)

def ends991 : List ℕ := [2308, 2309, 2313]

theorem inside991 : Research6966.TerminalBanks.inside src991.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover991 : Cover (Triangular src991) 2313 2308 ends991 := triangleCover (by decide +kernel)

def src992 : Request := ⟨⟨⟨3950,5510,1213,64247⟩,1877062482395136,25622281045803⟩,65,3,1,385979,30⟩

theorem rank992 : P3_7_1.BankOK src992.bank := by
  simpa only [src992, _root_.Research6969.TransitionBanks.bank310] using _root_.Research6969.TransitionBanks.rank310 64247

theorem width992 : Lower6960.HelperSource.WidthGuard src992.bank 179730 2308 src992.reserve := requestWidth (by decide)

def ends992 : List ℕ := [2308, 2309, 2313]




theorem cover992 : Cover (Triangular src992) 2313 2308 ends992 := triangleCover (by decide +kernel)

def src993 : Request := ⟨⟨⟨5726,7952,1796,64247⟩,5808307287359488,113334118485107⟩,85,3,1,385979,30⟩

theorem rank993 : P3_7_1.BankOK src993.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5726_7952_1796 64247

theorem width993 : Lower6960.HelperSource.WidthGuard src993.bank 179730 2308 src993.reserve := requestWidth (by decide)

def ends993 : List ℕ := [2308, 2313]



theorem cover993 : Cover (Triangular src993) 2313 2308 ends993 := triangleCover (by decide +kernel)

def src994 : Request := ⟨⟨⟨8339,11579,2556,116829⟩,17625278836113408,500344869187388⟩,145,3,1,385979,30⟩

theorem rank994 : P3_7_1.BankOK src994.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8339_11579_2556 116829

theorem width994 : Lower6960.HelperSource.WidthGuard src994.bank 179730 2308 src994.reserve := requestWidth (by decide)

def ends994 : List ℕ := [2308, 2309, 2313]




theorem cover994 : Cover (Triangular src994) 2313 2308 ends994 := triangleCover (by decide +kernel)

def src995 : Request := ⟨⟨⟨10047,13950,3102,189517⟩,30992780033523712,1059990587953193⟩,190,3,1,385979,30⟩

theorem rank995 : P3_7_1.BankOK src995.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10047_13950_3102 189517

theorem width995 : Lower6960.HelperSource.WidthGuard src995.bank 179730 2308 src995.reserve := requestWidth (by decide)

def ends995 : List ℕ := [2308, 2309, 2313]




theorem cover995 : Cover (Triangular src995) 2313 2308 ends995 := triangleCover (by decide +kernel)

def src996 : Request := ⟨⟨⟨562,781,172,6858⟩,5431270572032,10440670587⟩,0,3,1,385979,31⟩

theorem rank996 : P3_7_1.BankOK src996.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 6858

theorem width996 : Lower6960.HelperSource.WidthGuard src996.bank 179730 2308 src996.reserve := requestWidth (by decide)

def ends996 : List ℕ := [2308, 2309, 2313]

theorem inside996 : Research6966.TerminalBanks.inside src996.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover996 : Cover (Triangular src996) 2313 2308 ends996 := triangleCover (by decide +kernel)

def src997 : Request := ⟨⟨⟨692,962,208,7692⟩,9986007105536,23645774460⟩,1,3,1,385979,31⟩

theorem rank997 : P3_7_1.BankOK src997.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_208 7692

theorem width997 : Lower6960.HelperSource.WidthGuard src997.bank 179730 2308 src997.reserve := requestWidth (by decide)

def ends997 : List ℕ := [2308, 2309, 2313]

theorem inside997 : Research6966.TerminalBanks.inside src997.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover997 : Cover (Triangular src997) 2313 2308 ends997 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources60

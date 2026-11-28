import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_adf41cb1614b9a70
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks27
import ProximityPrize.SubmissionLower.Bundle6970_6ed322075960e0ab
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks60
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks64
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks68
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks73
import ProximityPrize.SubmissionLower.Bundle6970_ceea66e6500ee0de
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Bundle6970_ec9790ff7fc8ae2f
import ProximityPrize.SubmissionLower.Bundle6970_fa0707633ba569a9
import ProximityPrize.SubmissionLower.Bundle6970_c51a423b59d0dd6b
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks47
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks50
import ProximityPrize.SubmissionLower.Z6969Pack0655
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks38
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks41
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks61
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks71
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks77
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks56
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks31
import ProximityPrize.SubmissionLower.Bundle6970_fa78e5af1890b063
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks72
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks63
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks54
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks65
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks67
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks78
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks79
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0647

section Pack_R6970Height2313CommonSources03

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1001 : Request := ⟨⟨⟨1001,1395,307,12355⟩,30626026618880,105715278267⟩,8,3,1,385979,31⟩

theorem rank1001 : P3_7_1.BankOK src1001.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1001_1395_307 12355

theorem width1001 : Lower6960.HelperSource.WidthGuard src1001.bank 179730 2308 src1001.reserve := requestWidth (by decide)

def ends1001 : List ℕ := [2308, 2309, 2313]

theorem inside1001 : Research6966.TerminalBanks.inside src1001.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1001 : Cover (Triangular src1001) 2313 2308 ends1001 := triangleCover (by decide +kernel)

def src1002 : Request := ⟨⟨⟨1452,2023,445,17590⟩,93286344425472,466511127281⟩,16,3,1,385979,31⟩

theorem rank1002 : P3_7_1.BankOK src1002.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1452_2023_445 17590

theorem width1002 : Lower6960.HelperSource.WidthGuard src1002.bank 179730 2308 src1002.reserve := requestWidth (by decide)

def ends1002 : List ℕ := [2309, 2313]

theorem inside1002 : Research6966.TerminalBanks.inside src1002.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1002 : Cover (Triangular src1002) 2313 2308 ends1002 := triangleCover (by decide +kernel)

def src1003 : Request := ⟨⟨⟨2110,2929,647,31864⟩,286087808286720,2054078646343⟩,32,3,1,385979,31⟩

theorem rank1003 : P3_7_1.BankOK src1003.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2110_2929_647 31864

theorem width1003 : Lower6960.HelperSource.WidthGuard src1003.bank 179730 2308 src1003.reserve := requestWidth (by decide)

def ends1003 : List ℕ := [2308, 2309, 2313]

theorem inside1003 : Research6966.TerminalBanks.inside src1003.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1003 : Cover (Triangular src1003) 2313 2308 ends1003 := triangleCover (by decide +kernel)

def src1004 : Request := ⟨⟨⟨2776,3858,834,57109⟩,641102151680000,6075528370197⟩,45,3,1,386273,31⟩

theorem rank1004 : P3_7_1.BankOK src1004.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2776_3858_834 57109

theorem width1004 : Lower6960.HelperSource.WidthGuard src1004.bank 179730 2308 src1004.reserve := requestWidth (by decide)

def ends1004 : List ℕ := [2308, 2313]

theorem inside1004 : Research6966.TerminalBanks.inside src1004.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1004 : Cover (Triangular src1004) 2313 2308 ends1004 := triangleCover (by decide +kernel)

def src1005 : Request := ⟨⟨⟨2768,3842,854,39931⟩,648553314385920,6106417618032⟩,45,3,1,385979,31⟩

theorem rank1005 : P3_7_1.BankOK src1005.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2768_3842_854 39931

theorem width1005 : Lower6960.HelperSource.WidthGuard src1005.bank 179730 2308 src1005.reserve := requestWidth (by decide)

def ends1005 : List ℕ := [2308, 2309, 2313]

theorem inside1005 : Research6966.TerminalBanks.inside src1005.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1005 : Cover (Triangular src1005) 2313 2308 ends1005 := triangleCover (by decide +kernel)

def src1006 : Request := ⟨⟨⟨3963,5502,1213,50706⟩,1890924025610240,25502682687359⟩,65,3,1,385979,31⟩

theorem rank1006 : P3_7_1.BankOK src1006.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3963_5502_1213 50706

theorem width1006 : Lower6960.HelperSource.WidthGuard src1006.bank 179730 2308 src1006.reserve := requestWidth (by decide)

def ends1006 : List ℕ := [2308, 2309, 2313]




theorem cover1006 : Cover (Triangular src1006) 2313 2308 ends1006 := triangleCover (by decide +kernel)

def src1007 : Request := ⟨⟨⟨5841,8110,1785,115771⟩,6044716112543744,120174411265203⟩,110,3,1,386273,31⟩

theorem rank1007 : P3_7_1.BankOK src1007.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5841_8110_1785 115771

theorem width1007 : Lower6960.HelperSource.WidthGuard src1007.bank 179730 2308 src1007.reserve := requestWidth (by decide)

def ends1007 : List ℕ := [2308, 2313]



theorem cover1007 : Cover (Triangular src1007) 2313 2308 ends1007 := triangleCover (by decide +kernel)

def src1008 : Request := ⟨⟨⟨8333,11579,2548,102908⟩,17555013069701120,499124969898998⟩,145,3,1,385979,31⟩

theorem rank1008 : P3_7_1.BankOK src1008.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8333_11579_2548 102908

theorem width1008 : Lower6960.HelperSource.WidthGuard src1008.bank 179730 2308 src1008.reserve := requestWidth (by decide)

def ends1008 : List ℕ := [2308, 2309, 2313]




theorem cover1008 : Cover (Triangular src1008) 2313 2308 ends1008 := triangleCover (by decide +kernel)

def src1009 : Request := ⟨⟨⟨562,781,176,6096⟩,5526256353280,10627925923⟩,0,3,1,385979,32⟩

theorem rank1009 : P3_7_1.BankOK src1009.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 6096

theorem width1009 : Lower6960.HelperSource.WidthGuard src1009.bank 179730 2308 src1009.reserve := requestWidth (by decide)

def ends1009 : List ℕ := [2308, 2313]

theorem inside1009 : Research6966.TerminalBanks.inside src1009.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1009 : Cover (Triangular src1009) 2313 2308 ends1009 := triangleCover (by decide +kernel)

def src101 : Request := ⟨⟨⟨2748,3824,812,151700⟩,614083158081536,5782986158433⟩,325,2,1,257319,4097⟩

theorem rank101 : P3_7_1.BankOK src101.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 151700

theorem width101 : Lower6960.HelperSource.WidthGuard src101.bank 179730 2308 src101.reserve := requestWidth (by decide)

def ends101 : List ℕ := [2308, 2309, 2313]

theorem inside101 : Research6966.TerminalBanks.inside src101.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover101 : Cover (Triangular src101) 2313 2308 ends101 := triangleCover (by decide +kernel)

def src1010 : Request := ⟨⟨⟨690,963,212,6858⟩,10065769922560,24078187611⟩,1,3,1,385979,32⟩

theorem rank1010 : P3_7_1.BankOK src1010.bank := by
  simpa only [src1010, _root_.Research6969.TransitionBanks.bank196] using _root_.Research6969.TransitionBanks.rank196 6858

theorem width1010 : Lower6960.HelperSource.WidthGuard src1010.bank 179730 2308 src1010.reserve := requestWidth (by decide)

def ends1010 : List ℕ := [2309, 2313]

theorem inside1010 : Research6966.TerminalBanks.inside src1010.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1010 : Cover (Triangular src1010) 2313 2308 ends1010 := triangleCover (by decide +kernel)

def src1011 : Request := ⟨⟨⟨690,958,208,7696⟩,9921631092736,23331166760⟩,2,3,1,385979,32⟩

theorem rank1011 : P3_7_1.BankOK src1011.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_958_208 7696

theorem width1011 : Lower6960.HelperSource.WidthGuard src1011.bank 179730 2308 src1011.reserve := requestWidth (by decide)

def ends1011 : List ℕ := [2308, 2309, 2313]

theorem inside1011 : Research6966.TerminalBanks.inside src1011.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1011 : Cover (Triangular src1011) 2313 2308 ends1011 := triangleCover (by decide +kernel)

def src1012 : Request := ⟨⟨⟨693,962,213,9689⟩,10200167219200,24085532067⟩,4,3,1,385979,32⟩

theorem rank1012 : P3_7_1.BankOK src1012.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_213 9689

theorem width1012 : Lower6960.HelperSource.WidthGuard src1012.bank 179730 2308 src1012.reserve := requestWidth (by decide)

def ends1012 : List ℕ := [2308, 2309, 2313]

theorem inside1012 : Research6966.TerminalBanks.inside src1012.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1012 : Cover (Triangular src1012) 2313 2308 ends1012 := triangleCover (by decide +kernel)

def src1013 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,6,3,1,385979,32⟩

theorem rank1013 : P3_7_1.BankOK src1013.bank := by
  simpa only [src1013, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 10983

theorem width1013 : Lower6960.HelperSource.WidthGuard src1013.bank 179730 2308 src1013.reserve := requestWidth (by decide)

def ends1013 : List ℕ := [2309, 2313]

theorem inside1013 : Research6966.TerminalBanks.inside src1013.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1013 : Cover (Triangular src1013) 2313 2308 ends1013 := triangleCover (by decide +kernel)

def src1014 : Request := ⟨⟨⟨1001,1395,307,13899⟩,30626026618880,105715278267⟩,10,3,1,385979,32⟩

theorem rank1014 : P3_7_1.BankOK src1014.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1001_1395_307 13899

theorem width1014 : Lower6960.HelperSource.WidthGuard src1014.bank 179730 2308 src1014.reserve := requestWidth (by decide)

def ends1014 : List ℕ := [2308, 2309, 2313]

theorem inside1014 : Research6966.TerminalBanks.inside src1014.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1014 : Cover (Triangular src1014) 2313 2308 ends1014 := triangleCover (by decide +kernel)

def src1015 : Request := ⟨⟨⟨1736,2409,537,22157⟩,160469647360000,947161992087⟩,25,3,1,385979,32⟩

theorem rank1015 : P3_7_1.BankOK src1015.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1736_2409_537 22157

theorem width1015 : Lower6960.HelperSource.WidthGuard src1015.bank 179730 2308 src1015.reserve := requestWidth (by decide)

def ends1015 : List ℕ := [2308, 2309, 2313]

theorem inside1015 : Research6966.TerminalBanks.inside src1015.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1015 : Cover (Triangular src1015) 2313 2308 ends1015 := triangleCover (by decide +kernel)

def src1016 : Request := ⟨⟨⟨3965,5506,1213,45109⟩,1893061344362496,25562434272925⟩,65,3,1,385979,32⟩

theorem rank1016 : P3_7_1.BankOK src1016.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3965_5506_1213 45109

theorem width1016 : Lower6960.HelperSource.WidthGuard src1016.bank 179730 2308 src1016.reserve := requestWidth (by decide)

def ends1016 : List ℕ := [2308, 2309, 2313]




theorem cover1016 : Cover (Triangular src1016) 2313 2308 ends1016 := triangleCover (by decide +kernel)

def src1017 : Request := ⟨⟨⟨4828,6696,1512,57109⟩,3478208117211136,56980856955989⟩,85,3,1,385979,32⟩

theorem rank1017 : P3_7_1.BankOK src1017.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4828_6696_1512 57109

theorem width1017 : Lower6960.HelperSource.WidthGuard src1017.bank 179730 2308 src1017.reserve := requestWidth (by decide)

def ends1017 : List ℕ := [2309, 2313]



theorem cover1017 : Cover (Triangular src1017) 2313 2308 ends1017 := triangleCover (by decide +kernel)

def src1018 : Request := ⟨⟨⟨5707,7951,1750,91474⟩,5652886789292032,111025751789870⟩,110,3,1,385979,32⟩

theorem rank1018 : P3_7_1.BankOK src1018.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5707_7951_1750 91474

theorem width1018 : Lower6960.HelperSource.WidthGuard src1018.bank 179730 2308 src1018.reserve := requestWidth (by decide)

def ends1018 : List ℕ := [2308, 2309, 2313]




theorem cover1018 : Cover (Triangular src1018) 2313 2308 ends1018 := triangleCover (by decide +kernel)

def src1019 : Request := ⟨⟨⟨8317,11547,2548,91400⟩,17479623502462976,494696176813958⟩,145,3,1,385979,32⟩

theorem rank1019 : P3_7_1.BankOK src1019.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8317_11547_2548 91400

theorem width1019 : Lower6960.HelperSource.WidthGuard src1019.bank 179730 2308 src1019.reserve := requestWidth (by decide)

def ends1019 : List ℕ := [2308, 2309, 2313]




theorem cover1019 : Cover (Triangular src1019) 2313 2308 ends1019 := triangleCover (by decide +kernel)

def src102 : Request := ⟨⟨⟨2000,2782,610,166218⟩,242679148707840,1662397981334⟩,249,2,1,257319,8193⟩

theorem rank102 : P3_7_1.BankOK src102.bank := by
  simpa only [src102, _root_.Research6969.TerminalAuxBanks.bank15] using _root_.Research6969.PackedRanks.TerminalRanks12To15.rank15 166218

theorem width102 : Lower6960.HelperSource.WidthGuard src102.bank 179730 2308 src102.reserve := requestWidth (by decide)

def ends102 : List ℕ := [2308, 2309, 2313]

theorem inside102 : Research6966.TerminalBanks.inside src102.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover102 : Cover (Triangular src102) 2313 2308 ends102 := triangleCover (by decide +kernel)

def src1020 : Request := ⟨⟨⟨562,781,169,6096⟩,5359435776000,10299257375⟩,0,3,1,385979,33⟩

theorem rank1020 : P3_7_1.BankOK src1020.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_169 6096

theorem width1020 : Lower6960.HelperSource.WidthGuard src1020.bank 179730 2308 src1020.reserve := requestWidth (by decide)

def ends1020 : List ℕ := [2308, 2309, 2313]

theorem inside1020 : Research6966.TerminalBanks.inside src1020.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1020 : Cover (Triangular src1020) 2313 2308 ends1020 := triangleCover (by decide +kernel)

def src1021 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,1,3,1,385979,33⟩

theorem rank1021 : P3_7_1.BankOK src1021.bank := by
  simpa only [src1021, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 6858

theorem width1021 : Lower6960.HelperSource.WidthGuard src1021.bank 179730 2308 src1021.reserve := requestWidth (by decide)

def ends1021 : List ℕ := [2308, 2313]

theorem inside1021 : Research6966.TerminalBanks.inside src1021.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1021 : Cover (Triangular src1021) 2313 2308 ends1021 := triangleCover (by decide +kernel)

def src1022 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,2,3,1,385979,33⟩

theorem rank1022 : P3_7_1.BankOK src1022.bank := by
  simpa only [src1022, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 6858

theorem width1022 : Lower6960.HelperSource.WidthGuard src1022.bank 179730 2308 src1022.reserve := requestWidth (by decide)

def ends1022 : List ℕ := [2308, 2309, 2313]

theorem inside1022 : Research6966.TerminalBanks.inside src1022.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1022 : Cover (Triangular src1022) 2313 2308 ends1022 := triangleCover (by decide +kernel)

def src1023 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,3,3,1,385979,33⟩

theorem rank1023 : P3_7_1.BankOK src1023.bank := by
  simpa only [src1023, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 7715

theorem width1023 : Lower6960.HelperSource.WidthGuard src1023.bank 179730 2308 src1023.reserve := requestWidth (by decide)

def ends1023 : List ℕ := [2308, 2313]

theorem inside1023 : Research6966.TerminalBanks.inside src1023.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1023 : Cover (Triangular src1023) 2313 2308 ends1023 := triangleCover (by decide +kernel)

def src1024 : Request := ⟨⟨⟨691,962,212,8679⟩,10098434375680,23997864317⟩,4,3,1,385979,33⟩

theorem rank1024 : P3_7_1.BankOK src1024.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 8679

theorem width1024 : Lower6960.HelperSource.WidthGuard src1024.bank 179730 2308 src1024.reserve := requestWidth (by decide)

def ends1024 : List ℕ := [2309, 2313]

theorem inside1024 : Research6966.TerminalBanks.inside src1024.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1024 : Cover (Triangular src1024) 2313 2308 ends1024 := triangleCover (by decide +kernel)

def src1025 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,6,3,1,385979,33⟩

theorem rank1025 : P3_7_1.BankOK src1025.bank := by
  simpa only [src1025, _root_.Research6969.TransitionBanks.bank204] using _root_.Research6969.TransitionBanks.rank204 9763

theorem width1025 : Lower6960.HelperSource.WidthGuard src1025.bank 179730 2308 src1025.reserve := requestWidth (by decide)

def ends1025 : List ℕ := [2308, 2313]

theorem inside1025 : Research6966.TerminalBanks.inside src1025.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1025 : Cover (Triangular src1025) 2313 2308 ends1025 := triangleCover (by decide +kernel)

def src1026 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,10,3,1,385979,33⟩

theorem rank1026 : P3_7_1.BankOK src1026.bank := by
  simpa only [src1026, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 12355

theorem width1026 : Lower6960.HelperSource.WidthGuard src1026.bank 179730 2308 src1026.reserve := requestWidth (by decide)

def ends1026 : List ℕ := [2308, 2313]

theorem inside1026 : Research6966.TerminalBanks.inside src1026.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1026 : Cover (Triangular src1026) 2313 2308 ends1026 := triangleCover (by decide +kernel)

def src1027 : Request := ⟨⟨⟨1747,2425,537,19710⟩,162755588390912,967567137727⟩,25,3,1,385979,33⟩

theorem rank1027 : P3_7_1.BankOK src1027.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1747_2425_537 19710

theorem width1027 : Lower6960.HelperSource.WidthGuard src1027.bank 179730 2308 src1027.reserve := requestWidth (by decide)

def ends1027 : List ℕ := [2308, 2309, 2313]

theorem inside1027 : Research6966.TerminalBanks.inside src1027.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1027 : Cover (Triangular src1027) 2313 2308 ends1027 := triangleCover (by decide +kernel)

def src1028 : Request := ⟨⟨⟨2586,3595,775,50764⟩,517358148911104,4571549555917⟩,45,3,1,386273,33⟩

theorem rank1028 : P3_7_1.BankOK src1028.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2586_3595_775 50764

theorem width1028 : Lower6960.HelperSource.WidthGuard src1028.bank 179730 2308 src1028.reserve := requestWidth (by decide)

def ends1028 : List ℕ := [2309, 2313]

theorem inside1028 : Research6966.TerminalBanks.inside src1028.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1028 : Cover (Triangular src1028) 2313 2308 ends1028 := triangleCover (by decide +kernel)

def src1029 : Request := ⟨⟨⟨2790,3874,854,30835⟩,660153324011520,6271717193952⟩,45,3,1,385979,33⟩

theorem rank1029 : P3_7_1.BankOK src1029.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2790_3874_854 30835

theorem width1029 : Lower6960.HelperSource.WidthGuard src1029.bank 179730 2308 src1029.reserve := requestWidth (by decide)

def ends1029 : List ℕ := [2308, 2309, 2313]

theorem inside1029 : Research6966.TerminalBanks.inside src1029.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1029 : Cover (Triangular src1029) 2313 2308 ends1029 := triangleCover (by decide +kernel)

def src103 : Request := ⟨⟨⟨1202,1670,365,139467⟩,52587979866112,215752938462⟩,150,2,1,257319,32769⟩

theorem rank103 : P3_7_1.BankOK src103.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1670_365 139467

theorem width103 : Lower6960.HelperSource.WidthGuard src103.bank 179730 2308 src103.reserve := requestWidth (by decide)

def ends103 : List ℕ := [2308, 2309, 2313]

theorem inside103 : Research6966.TerminalBanks.inside src103.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover103 : Cover (Triangular src103) 2313 2308 ends103 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources03

section Pack_R6970Height2313CommonSources08

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1146 : Request := ⟨⟨⟨2002,2788,630,28173⟩,249240464392192,1716449496361⟩,85,3,1,385979,65⟩

theorem rank1146 : P3_7_1.BankOK src1146.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2002_2788_630 28173

theorem width1146 : Lower6960.HelperSource.WidthGuard src1146.bank 179730 2308 src1146.reserve := requestWidth (by decide)

def ends1146 : List ℕ := [2308, 2309, 2313]

theorem inside1146 : Research6966.TerminalBanks.inside src1146.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1146 : Cover (Triangular src1146) 2313 2308 ends1146 := triangleCover (by decide +kernel)

def src1147 : Request := ⟨⟨⟨2788,3871,854,30059⟩,659094295019520,6256092552882⟩,115,3,1,385979,65⟩

theorem rank1147 : P3_7_1.BankOK src1147.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2788_3871_854 30059

theorem width1147 : Lower6960.HelperSource.WidthGuard src1147.bank 179730 2308 src1147.reserve := requestWidth (by decide)

def ends1147 : List ℕ := [2308, 2309, 2313]

theorem inside1147 : Research6966.TerminalBanks.inside src1147.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1147 : Cover (Triangular src1147) 2313 2308 ends1147 := triangleCover (by decide +kernel)

def src1148 : Request := ⟨⟨⟨2009,2787,630,31694⟩,251198456463360,1714466862180⟩,115,3,1,385979,97⟩

theorem rank1148 : P3_7_1.BankOK src1148.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2009_2787_630 31694

theorem width1148 : Lower6960.HelperSource.WidthGuard src1148.bank 179730 2308 src1148.reserve := requestWidth (by decide)

def ends1148 : List ℕ := [2308, 2309, 2313]

theorem inside1148 : Research6966.TerminalBanks.inside src1148.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1148 : Cover (Triangular src1148) 2313 2308 ends1148 := triangleCover (by decide +kernel)

def src1149 : Request := ⟨⟨⟨2612,3623,818,34273⟩,551220579926016,4888271640312⟩,150,3,1,385979,97⟩

theorem rank1149 : P3_7_1.BankOK src1149.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3623_818 34273

theorem width1149 : Lower6960.HelperSource.WidthGuard src1149.bank 179730 2308 src1149.reserve := requestWidth (by decide)

def ends1149 : List ℕ := [2308, 2309, 2313]

theorem inside1149 : Research6966.TerminalBanks.inside src1149.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1149 : Cover (Triangular src1149) 2313 2308 ends1149 := triangleCover (by decide +kernel)

def src115 : Request := ⟨⟨⟨2816,3909,882,31761⟩,690700839813120,6619929415349⟩,85,2,1,288407,49⟩

theorem rank115 : P3_7_1.BankOK src115.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3909_882 31761

theorem width115 : Lower6960.HelperSource.WidthGuard src115.bank 179730 2308 src115.reserve := requestWidth (by decide)

def ends115 : List ℕ := [2308, 2309, 2313]

theorem inside115 : Research6966.TerminalBanks.inside src115.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover115 : Cover (Triangular src115) 2313 2308 ends115 := triangleCover (by decide +kernel)

def src1150 : Request := ⟨⟨⟨1754,2438,551,28225⟩,167450900430848,1004231319985⟩,115,3,1,385979,129⟩

theorem rank1150 : P3_7_1.BankOK src1150.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2438_551 28225

theorem width1150 : Lower6960.HelperSource.WidthGuard src1150.bank 179730 2308 src1150.reserve := requestWidth (by decide)

def ends1150 : List ℕ := [2308, 2309, 2313]

theorem inside1150 : Research6966.TerminalBanks.inside src1150.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1150 : Cover (Triangular src1150) 2313 2308 ends1150 := triangleCover (by decide +kernel)

def src1151 : Request := ⟨⟨⟨2307,3204,702,33552⟩,371690023944192,2921790084349⟩,150,3,1,385979,129⟩

theorem rank1151 : P3_7_1.BankOK src1151.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3204_702 33552

theorem width1151 : Lower6960.HelperSource.WidthGuard src1151.bank 179730 2308 src1151.reserve := requestWidth (by decide)

def ends1151 : List ℕ := [2308, 2309, 2313]

theorem inside1151 : Research6966.TerminalBanks.inside src1151.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1151 : Cover (Triangular src1151) 2313 2308 ends1151 := triangleCover (by decide +kernel)

def src1152 : Request := ⟨⟨⟨2302,3203,702,50764⟩,369889537687552,2918855628076⟩,195,3,1,385979,257⟩

theorem rank1152 : P3_7_1.BankOK src1152.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3203_702 50764

theorem width1152 : Lower6960.HelperSource.WidthGuard src1152.bank 179730 2308 src1152.reserve := requestWidth (by decide)

def ends1152 : List ℕ := [2308, 2309, 2313]

theorem inside1152 : Research6966.TerminalBanks.inside src1152.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1152 : Cover (Triangular src1152) 2313 2308 ends1152 := triangleCover (by decide +kernel)

def src1153 : Request := ⟨⟨⟨2990,4156,894,57422⟩,798073951354880,8148885667208⟩,249,3,1,385979,257⟩

theorem rank1153 : P3_7_1.BankOK src1153.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2990_4156_894 57422

theorem width1153 : Lower6960.HelperSource.WidthGuard src1153.bank 179730 2308 src1153.reserve := requestWidth (by decide)

def ends1153 : List ℕ := [2308, 2309, 2313]

theorem inside1153 : Research6966.TerminalBanks.inside src1153.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1153 : Cover (Triangular src1153) 2313 2308 ends1153 := triangleCover (by decide +kernel)

def src1154 : Request := ⟨⟨⟨1202,1670,378,35412⟩,53999714697216,221692026804⟩,115,3,1,385979,513⟩

theorem rank1154 : P3_7_1.BankOK src1154.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1670_378 35412

theorem width1154 : Lower6960.HelperSource.WidthGuard src1154.bank 179730 2308 src1154.reserve := requestWidth (by decide)

def ends1154 : List ℕ := [2309, 2313]

theorem inside1154 : Research6966.TerminalBanks.inside src1154.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1154 : Cover (Triangular src1154) 2313 2308 ends1154 := triangleCover (by decide +kernel)

def src1155 : Request := ⟨⟨⟨2593,3604,775,60527⟩,520494434484224,4608474947497⟩,249,3,1,385979,513⟩

theorem rank1155 : P3_7_1.BankOK src1155.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2593_3604_775 60527

theorem width1155 : Lower6960.HelperSource.WidthGuard src1155.bank 179730 2308 src1155.reserve := requestWidth (by decide)

def ends1155 : List ℕ := [2308, 2309, 2313]

theorem inside1155 : Research6966.TerminalBanks.inside src1155.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1155 : Cover (Triangular src1155) 2313 2308 ends1155 := triangleCover (by decide +kernel)

def src1156 : Request := ⟨⟨⟨2305,3201,702,80478⟩,370969276579840,2912992731804⟩,250,3,1,385979,1025⟩

theorem rank1156 : P3_7_1.BankOK src1156.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3201_702 80478

theorem width1156 : Lower6960.HelperSource.WidthGuard src1156.bank 179730 2308 src1156.reserve := requestWidth (by decide)

def ends1156 : List ℕ := [2308, 2309, 2313]

theorem inside1156 : Research6966.TerminalBanks.inside src1156.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1156 : Cover (Triangular src1156) 2313 2308 ends1156 := triangleCover (by decide +kernel)

def src1157 : Request := ⟨⟨⟨3001,4171,898,115015⟩,807397411258368,8272669034533⟩,325,3,1,386273,1025⟩

theorem rank1157 : P3_7_1.BankOK src1157.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3001_4171_898 115015

theorem width1157 : Lower6960.HelperSource.WidthGuard src1157.bank 179730 2308 src1157.reserve := requestWidth (by decide)

def ends1157 : List ℕ := [2308, 2309, 2313]

theorem inside1157 : Research6966.TerminalBanks.inside src1157.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1157 : Cover (Triangular src1157) 2313 2308 ends1157 := triangleCover (by decide +kernel)

def src1158 : Request := ⟨⟨⟨1750,2435,522,70068⟩,159899889172480,959076692411⟩,195,3,1,385979,2049⟩

theorem rank1158 : P3_7_1.BankOK src1158.bank := by
  simpa only [src1158, _root_.Research6969.TerminalAuxBanks.bank8] using _root_.Research6969.PackedRanks.TerminalRanks8To11.rank8 70068

theorem width1158 : Lower6960.HelperSource.WidthGuard src1158.bank 179730 2308 src1158.reserve := requestWidth (by decide)

def ends1158 : List ℕ := [2308, 2313]

theorem inside1158 : Research6966.TerminalBanks.inside src1158.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1158 : Cover (Triangular src1158) 2313 2308 ends1158 := triangleCover (by decide +kernel)

def src1159 : Request := ⟨⟨⟨2808,3900,854,113571⟩,669724928901120,6408244632207⟩,325,3,1,385979,2049⟩

theorem rank1159 : P3_7_1.BankOK src1159.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 113571

theorem width1159 : Lower6960.HelperSource.WidthGuard src1159.bank 179730 2308 src1159.reserve := requestWidth (by decide)

def ends1159 : List ℕ := [2308, 2309, 2313]

theorem inside1159 : Research6966.TerminalBanks.inside src1159.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1159 : Cover (Triangular src1159) 2313 2308 ends1159 := triangleCover (by decide +kernel)

def src116 : Request := ⟨⟨⟨2604,3625,819,31694⟩,547948674416640,4901614794409⟩,85,2,1,288407,52⟩

theorem rank116 : P3_7_1.BankOK src116.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3625_819 31694

theorem width116 : Lower6960.HelperSource.WidthGuard src116.bank 179730 2308 src116.reserve := requestWidth (by decide)

def ends116 : List ℕ := [2308, 2309, 2313]

theorem inside116 : Research6966.TerminalBanks.inside src116.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover116 : Cover (Triangular src116) 2313 2308 ends116 := triangleCover (by decide +kernel)

def src1160 : Request := ⟨⟨⟨2748,3824,812,151381⟩,614083158081536,5782986158433⟩,325,3,1,385979,4097⟩

theorem rank1160 : P3_7_1.BankOK src1160.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 151381

theorem width1160 : Lower6960.HelperSource.WidthGuard src1160.bank 179730 2308 src1160.reserve := requestWidth (by decide)

def ends1160 : List ℕ := [2308, 2309, 2313]

theorem inside1160 : Research6966.TerminalBanks.inside src1160.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1160 : Cover (Triangular src1160) 2313 2308 ends1160 := triangleCover (by decide +kernel)

def src1161 : Request := ⟨⟨⟨2754,3832,812,152303⟩,617082439073792,5821985239441⟩,325,3,1,385979,4097⟩

theorem rank1161 : P3_7_1.BankOK src1161.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2754_3832_812 152303

theorem width1161 : Lower6960.HelperSource.WidthGuard src1161.bank 179730 2308 src1161.reserve := requestWidth (by decide)

def ends1161 : List ℕ := [2308, 2309, 2313]

theorem inside1161 : Research6966.TerminalBanks.inside src1161.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1161 : Cover (Triangular src1161) 2313 2308 ends1161 := triangleCover (by decide +kernel)

def src1162 : Request := ⟨⟨⟨2000,2776,604,187507⟩,240862397726720,1638230896114⟩,248,3,1,385979,8193⟩

theorem rank1162 : P3_7_1.BankOK src1162.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2000_2776_604 187507

theorem width1162 : Lower6960.HelperSource.WidthGuard src1162.bank 179730 2308 src1162.reserve := requestWidth (by decide)

def ends1162 : List ℕ := [2308, 2309, 2313]

theorem inside1162 : Research6966.TerminalBanks.inside src1162.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1162 : Cover (Triangular src1162) 2313 2308 ends1162 := triangleCover (by decide +kernel)

def src1163 : Request := ⟨⟨⟨1202,1670,365,139436⟩,52587979866112,215752938462⟩,150,3,1,385979,32769⟩

theorem rank1163 : P3_7_1.BankOK src1163.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1670_365 139436

theorem width1163 : Lower6960.HelperSource.WidthGuard src1163.bank 179730 2308 src1163.reserve := requestWidth (by decide)

def ends1163 : List ℕ := [2308, 2309, 2313]

theorem inside1163 : Research6966.TerminalBanks.inside src1163.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1163 : Cover (Triangular src1163) 2313 2308 ends1163 := triangleCover (by decide +kernel)

def src1164 : Request := ⟨⟨⟨550,763,170,4556⟩,5129809428480,9599221867⟩,10,3,2,421606,52⟩

theorem rank1164 : P3_7_1.BankOK src1164.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 4556

theorem width1164 : Lower6960.HelperSource.WidthGuard src1164.bank 179730 2308 src1164.reserve := requestWidth (by decide)

def ends1164 : List ℕ := [2308, 2309, 2313]

theorem inside1164 : Research6966.TerminalBanks.inside src1164.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1164 : Cover (Triangular src1164) 2313 2308 ends1164 := triangleCover (by decide +kernel)

def src1165 : Request := ⟨⟨⟨544,755,170,5105⟩,5005415546880,9279237547⟩,10,3,2,424744,42⟩

theorem rank1165 : P3_7_1.BankOK src1165.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_544_755_170 5105

theorem width1165 : Lower6960.HelperSource.WidthGuard src1165.bank 179730 2308 src1165.reserve := requestWidth (by decide)

def ends1165 : List ℕ := [2308, 2309, 2313]

theorem inside1165 : Research6966.TerminalBanks.inside src1165.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1165 : Cover (Triangular src1165) 2313 2308 ends1165 := triangleCover (by decide +kernel)

def src1166 : Request := ⟨⟨⟨550,763,170,5173⟩,5129809428480,9599221867⟩,10,3,2,432343,41⟩

theorem rank1166 : P3_7_1.BankOK src1166.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 5173

theorem width1166 : Lower6960.HelperSource.WidthGuard src1166.bank 179730 2308 src1166.reserve := requestWidth (by decide)

def ends1166 : List ℕ := [2308, 2309, 2313]

theorem inside1166 : Research6966.TerminalBanks.inside src1166.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1166 : Cover (Triangular src1166) 2313 2308 ends1166 := triangleCover (by decide +kernel)

def src1167 : Request := ⟨⟨⟨550,763,170,5241⟩,5129809428480,9599221867⟩,10,3,2,432577,40⟩

theorem rank1167 : P3_7_1.BankOK src1167.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 5241

theorem width1167 : Lower6960.HelperSource.WidthGuard src1167.bank 179730 2308 src1167.reserve := requestWidth (by decide)

def ends1167 : List ℕ := [2308, 2309, 2313]

theorem inside1167 : Research6966.TerminalBanks.inside src1167.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1167 : Cover (Triangular src1167) 2313 2308 ends1167 := triangleCover (by decide +kernel)

def src1168 : Request := ⟨⟨⟨550,763,170,5310⟩,5129809428480,9599221867⟩,10,3,2,432805,39⟩

theorem rank1168 : P3_7_1.BankOK src1168.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 5310

theorem width1168 : Lower6960.HelperSource.WidthGuard src1168.bank 179730 2308 src1168.reserve := requestWidth (by decide)

def ends1168 : List ℕ := [2308, 2309, 2313]

theorem inside1168 : Research6966.TerminalBanks.inside src1168.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1168 : Cover (Triangular src1168) 2313 2308 ends1168 := triangleCover (by decide +kernel)

def src1169 : Request := ⟨⟨⟨545,756,170,5377⟩,5026035793920,9318832198⟩,10,3,2,433027,38⟩

theorem rank1169 : P3_7_1.BankOK src1169.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5377

theorem width1169 : Lower6960.HelperSource.WidthGuard src1169.bank 179730 2308 src1169.reserve := requestWidth (by decide)

def ends1169 : List ℕ := [2308, 2309, 2313]

theorem inside1169 : Research6966.TerminalBanks.inside src1169.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1169 : Cover (Triangular src1169) 2313 2308 ends1169 := triangleCover (by decide +kernel)

def src117 : Request := ⟨⟨⟨2789,3873,854,27863⟩,659623697448960,6266506033362⟩,85,2,1,288407,52⟩

theorem rank117 : P3_7_1.BankOK src117.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 27863

theorem width117 : Lower6960.HelperSource.WidthGuard src117.bank 179730 2308 src117.reserve := requestWidth (by decide)

def ends117 : List ℕ := [2308, 2309, 2313]

theorem inside117 : Research6966.TerminalBanks.inside src117.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover117 : Cover (Triangular src117) 2313 2308 ends117 := triangleCover (by decide +kernel)

def src1170 : Request := ⟨⟨⟨556,772,171,5468⟩,5279150768128,10013440706⟩,10,3,2,433244,37⟩

theorem rank1170 : P3_7_1.BankOK src1170.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 5468

theorem width1170 : Lower6960.HelperSource.WidthGuard src1170.bank 179730 2308 src1170.reserve := requestWidth (by decide)

def ends1170 : List ℕ := [2308, 2309, 2313]

theorem inside1170 : Research6966.TerminalBanks.inside src1170.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1170 : Cover (Triangular src1170) 2313 2308 ends1170 := triangleCover (by decide +kernel)

def src1171 : Request := ⟨⟨⟨554,770,170,5555⟩,5213635215360,9885300877⟩,10,3,2,433454,36⟩

theorem rank1171 : P3_7_1.BankOK src1171.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_554_770_170 5555

theorem width1171 : Lower6960.HelperSource.WidthGuard src1171.bank 179730 2308 src1171.reserve := requestWidth (by decide)

def ends1171 : List ℕ := [2308, 2309, 2313]

theorem inside1171 : Research6966.TerminalBanks.inside src1171.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1171 : Cover (Triangular src1171) 2313 2308 ends1171 := triangleCover (by decide +kernel)

def src1172 : Request := ⟨⟨⟨555,771,171,5613⟩,5257936502784,9971791336⟩,10,3,2,433658,35⟩

theorem rank1172 : P3_7_1.BankOK src1172.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_771_171 5613

theorem width1172 : Lower6960.HelperSource.WidthGuard src1172.bank 179730 2308 src1172.reserve := requestWidth (by decide)

def ends1172 : List ℕ := [2308, 2309, 2313]

theorem inside1172 : Research6966.TerminalBanks.inside src1172.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1172 : Cover (Triangular src1172) 2313 2308 ends1172 := triangleCover (by decide +kernel)

def src1173 : Request := ⟨⟨⟨555,771,171,5690⟩,5257936502784,9971791336⟩,10,3,2,433856,34⟩

theorem rank1173 : P3_7_1.BankOK src1173.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_771_171 5690

theorem width1173 : Lower6960.HelperSource.WidthGuard src1173.bank 179730 2308 src1173.reserve := requestWidth (by decide)

def ends1173 : List ℕ := [2308, 2309, 2313]

theorem inside1173 : Research6966.TerminalBanks.inside src1173.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1173 : Cover (Triangular src1173) 2313 2308 ends1173 := triangleCover (by decide +kernel)

def src1174 : Request := ⟨⟨⟨555,771,171,5769⟩,5257936502784,9971791336⟩,10,3,2,434049,33⟩

theorem rank1174 : P3_7_1.BankOK src1174.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_771_171 5769

theorem width1174 : Lower6960.HelperSource.WidthGuard src1174.bank 179730 2308 src1174.reserve := requestWidth (by decide)

def ends1174 : List ℕ := [2308, 2309, 2313]

theorem inside1174 : Research6966.TerminalBanks.inside src1174.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1174 : Cover (Triangular src1174) 2313 2308 ends1174 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources08

section Pack_R6970Height2313CommonSources13

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1290 : Request := ⟨⟨⟨827,1151,260,9763⟩,17614256996352,50057971890⟩,8,4,1,514639,30⟩

theorem rank1290 : P3_7_1.BankOK src1290.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_260 9763

theorem width1290 : Lower6960.HelperSource.WidthGuard src1290.bank 179730 2308 src1290.reserve := requestWidth (by decide)

def ends1290 : List ℕ := [2309, 2313]

theorem inside1290 : Research6966.TerminalBanks.inside src1290.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1290 : Cover (Triangular src1290) 2313 2308 ends1290 := triangleCover (by decide +kernel)

def src1291 : Request := ⟨⟨⟨1203,1674,378,13899⟩,54100458209280,223406703910⟩,16,4,1,514639,30⟩

theorem rank1291 : P3_7_1.BankOK src1291.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_378 13899

theorem width1291 : Lower6960.HelperSource.WidthGuard src1291.bank 179730 2308 src1291.reserve := requestWidth (by decide)

def ends1291 : List ℕ := [2308, 2313]

theorem inside1291 : Research6966.TerminalBanks.inside src1291.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1291 : Cover (Triangular src1291) 2313 2308 ends1291 := triangleCover (by decide +kernel)

def src1292 : Request := ⟨⟨⟨2107,2929,645,28173⟩,284508615606272,2049139102608⟩,40,4,1,514639,30⟩

theorem rank1292 : P3_7_1.BankOK src1292.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2107_2929_645 28173

theorem width1292 : Lower6960.HelperSource.WidthGuard src1292.bank 179730 2308 src1292.reserve := requestWidth (by decide)

def ends1292 : List ℕ := [2308, 2309, 2313]

theorem inside1292 : Research6966.TerminalBanks.inside src1292.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1292 : Cover (Triangular src1292) 2313 2308 ends1292 := triangleCover (by decide +kernel)

def src1293 : Request := ⟨⟨⟨3965,5509,1213,224917⟩,1893061344362496,25607310424524⟩,110,4,1,515031,30⟩

theorem rank1293 : P3_7_1.BankOK src1293.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3965_5509_1213 224917

theorem width1293 : Lower6960.HelperSource.WidthGuard src1293.bank 179730 2308 src1293.reserve := requestWidth (by decide)

def ends1293 : List ℕ := [2308, 2309, 2313]




theorem cover1293 : Cover (Triangular src1293) 2313 2308 ends1293 := triangleCover (by decide +kernel)

def src1294 : Request := ⟨⟨⟨4800,6695,1474,72277⟩,3367547627110400,55837558620681⟩,110,4,1,514639,30⟩

theorem rank1294 : P3_7_1.BankOK src1294.bank := by
  simpa only [src1294, _root_.Research6969.TransitionBanks.bank324] using _root_.Research6969.TransitionBanks.rank324 72277

theorem width1294 : Lower6960.HelperSource.WidthGuard src1294.bank 179730 2308 src1294.reserve := requestWidth (by decide)

def ends1294 : List ℕ := [2308, 2309, 2313]




theorem cover1294 : Cover (Triangular src1294) 2313 2308 ends1294 := triangleCover (by decide +kernel)

def src1295 : Request := ⟨⟨⟨8300,11577,2548,115771⟩,17399709518790656,498847383098023⟩,190,4,1,514639,30⟩

theorem rank1295 : P3_7_1.BankOK src1295.bank := by
  simpa only [src1295, _root_.Research6969.TransitionBanks.bank365] using _root_.Research6969.TransitionBanks.rank365 115771

theorem width1295 : Lower6960.HelperSource.WidthGuard src1295.bank 179730 2308 src1295.reserve := requestWidth (by decide)

def ends1295 : List ℕ := [2309, 2313]



theorem cover1295 : Cover (Triangular src1295) 2313 2308 ends1295 := triangleCover (by decide +kernel)

def src1296 : Request := ⟨⟨⟨8328,11575,2548,718044⟩,17531435454300160,498569901356632⟩,245,4,1,515031,30⟩

theorem rank1296 : P3_7_1.BankOK src1296.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8328_11575_2548 718044

theorem width1296 : Lower6960.HelperSource.WidthGuard src1296.bank 179730 2308 src1296.reserve := requestWidth (by decide)

def ends1296 : List ℕ := [2308, 2309, 2313]




theorem cover1296 : Cover (Triangular src1296) 2313 2308 ends1296 := triangleCover (by decide +kernel)

def src1297 : Request := ⟨⟨⟨1784,2488,544,115771⟩,172257669283840,1061475222728⟩,45,4,1,515031,33⟩

theorem rank1297 : P3_7_1.BankOK src1297.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1784_2488_544 115771

theorem width1297 : Lower6960.HelperSource.WidthGuard src1297.bank 179730 2308 src1297.reserve := requestWidth (by decide)

def ends1297 : List ℕ := [2309, 2313]

theorem inside1297 : Research6966.TerminalBanks.inside src1297.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1297 : Cover (Triangular src1297) 2313 2308 ends1297 := triangleCover (by decide +kernel)

def src1298 : Request := ⟨⟨⟨2816,3905,882,34312⟩,690700839813120,6598128215989⟩,63,4,1,514639,33⟩

theorem rank1298 : P3_7_1.BankOK src1298.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 34312

theorem width1298 : Lower6960.HelperSource.WidthGuard src1298.bank 179730 2308 src1298.reserve := requestWidth (by decide)

def ends1298 : List ℕ := [2309, 2313]

theorem inside1298 : Research6966.TerminalBanks.inside src1298.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1298 : Cover (Triangular src1298) 2313 2308 ends1298 := triangleCover (by decide +kernel)

def src1299 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,0,4,1,514639,34⟩

theorem rank1299 : P3_7_1.BankOK src1299.bank := by
  simpa only [src1299, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4817

theorem width1299 : Lower6960.HelperSource.WidthGuard src1299.bank 179730 2308 src1299.reserve := requestWidth (by decide)

def ends1299 : List ℕ := [2308, 2309, 2313]

theorem inside1299 : Research6966.TerminalBanks.inside src1299.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1299 : Cover (Triangular src1299) 2313 2308 ends1299 := triangleCover (by decide +kernel)

def src13 : Request := ⟨⟨⟨2311,3205,722,44178⟩,381169062379520,2989278090495⟩,195,1,1,128659,257⟩

theorem rank13 : P3_7_1.BankOK src13.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2311_3205_722 44178

theorem width13 : Lower6960.HelperSource.WidthGuard src13.bank 179730 2308 src13.reserve := requestWidth (by decide)

def ends13 : List ℕ := [2308, 2309, 2313]

theorem inside13 : Research6966.TerminalBanks.inside src13.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover13 : Cover (Triangular src13) 2313 2308 ends13 := triangleCover (by decide +kernel)

def src130 : Request := ⟨⟨⟨400,557,120,3787⟩,1935519252480,2666981483⟩,2,2,1,292947,51⟩

theorem rank130 : P3_7_1.BankOK src130.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_400_557_120 3787

theorem width130 : Lower6960.HelperSource.WidthGuard src130.bank 179730 2308 src130.reserve := requestWidth (by decide)

def ends130 : List ℕ := [2308, 2309, 2313]

theorem inside130 : Research6966.TerminalBanks.inside src130.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover130 : Cover (Triangular src130) 2313 2308 ends130 := triangleCover (by decide +kernel)

def src1300 : Request := ⟨⟨⟨471,655,141,5419⟩,3149225525248,5085275599⟩,1,4,1,514639,34⟩

theorem rank1300 : P3_7_1.BankOK src1300.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_141 5419

theorem width1300 : Lower6960.HelperSource.WidthGuard src1300.bank 179730 2308 src1300.reserve := requestWidth (by decide)

def ends1300 : List ℕ := [2308, 2309, 2313]

theorem inside1300 : Research6966.TerminalBanks.inside src1300.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1300 : Cover (Triangular src1300) 2313 2308 ends1300 := triangleCover (by decide +kernel)

def src1301 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,2,4,1,514639,34⟩

theorem rank1301 : P3_7_1.BankOK src1301.bank := by
  simpa only [src1301, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 6096

theorem width1301 : Lower6960.HelperSource.WidthGuard src1301.bank 179730 2308 src1301.reserve := requestWidth (by decide)

def ends1301 : List ℕ := [2313]

theorem inside1301 : Research6966.TerminalBanks.inside src1301.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1301 : Cover (Triangular src1301) 2313 2308 ends1301 := triangleCover (by decide +kernel)

def src1302 : Request := ⟨⟨⟨469,651,144,6824⟩,3169461207040,5068091922⟩,3,4,1,514639,34⟩

theorem rank1302 : P3_7_1.BankOK src1302.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_469_651_144 6824

theorem width1302 : Lower6960.HelperSource.WidthGuard src1302.bank 179730 2308 src1302.reserve := requestWidth (by decide)

def ends1302 : List ℕ := [2308, 2309, 2313]

theorem inside1302 : Research6966.TerminalBanks.inside src1302.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1302 : Cover (Triangular src1302) 2313 2308 ends1302 := triangleCover (by decide +kernel)

def src1303 : Request := ⟨⟨⟨561,779,169,6849⟩,5338156236800,10214741280⟩,4,4,1,514639,34⟩

theorem rank1303 : P3_7_1.BankOK src1303.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_779_169 6849

theorem width1303 : Lower6960.HelperSource.WidthGuard src1303.bank 179730 2308 src1303.reserve := requestWidth (by decide)

def ends1303 : List ℕ := [2308, 2309, 2313]

theorem inside1303 : Research6966.TerminalBanks.inside src1303.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1303 : Cover (Triangular src1303) 2313 2308 ends1303 := triangleCover (by decide +kernel)

def src1304 : Request := ⟨⟨⟨691,962,212,8679⟩,10098434375680,23997864317⟩,8,4,1,514639,34⟩

theorem rank1304 : P3_7_1.BankOK src1304.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 8679

theorem width1304 : Lower6960.HelperSource.WidthGuard src1304.bank 179730 2308 src1304.reserve := requestWidth (by decide)

def ends1304 : List ℕ := [2308, 2313]

theorem inside1304 : Research6966.TerminalBanks.inside src1304.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1304 : Cover (Triangular src1304) 2313 2308 ends1304 := triangleCover (by decide +kernel)

def src1305 : Request := ⟨⟨⟨1205,1673,369,19728⟩,53321182740480,218848410398⟩,25,4,1,514639,34⟩

theorem rank1305 : P3_7_1.BankOK src1305.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1673_369 19728

theorem width1305 : Lower6960.HelperSource.WidthGuard src1305.bank 179730 2308 src1305.reserve := requestWidth (by decide)

def ends1305 : List ℕ := [2308, 2309, 2313]

theorem inside1305 : Research6966.TerminalBanks.inside src1305.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1305 : Cover (Triangular src1305) 2313 2308 ends1305 := triangleCover (by decide +kernel)

def src1306 : Request := ⟨⟨⟨2606,3618,798,40012⟩,538195492077568,4773887316825⟩,65,4,1,514639,34⟩

theorem rank1306 : P3_7_1.BankOK src1306.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3618_798 40012

theorem width1306 : Lower6960.HelperSource.WidthGuard src1306.bank 179730 2308 src1306.reserve := requestWidth (by decide)

def ends1306 : List ℕ := [2308, 2309, 2313]

theorem inside1306 : Research6966.TerminalBanks.inside src1306.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1306 : Cover (Triangular src1306) 2313 2308 ends1306 := triangleCover (by decide +kernel)

def src1307 : Request := ⟨⟨⟨6931,9623,2174,102908⟩,10299791048704000,243058712908678⟩,190,4,1,514639,34⟩

theorem rank1307 : P3_7_1.BankOK src1307.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6931_9623_2174 102908

theorem width1307 : Lower6960.HelperSource.WidthGuard src1307.bank 179730 2308 src1307.reserve := requestWidth (by decide)

def ends1307 : List ℕ := [2308, 2313]



theorem cover1307 : Cover (Triangular src1307) 2313 2308 ends1307 := triangleCover (by decide +kernel)

def src1308 : Request := ⟨⟨⟨8347,11575,2607,164967⟩,17929957132992512,507525945959908⟩,245,4,1,514639,34⟩

theorem rank1308 : P3_7_1.BankOK src1308.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8347_11575_2607 164967

theorem width1308 : Lower6960.HelperSource.WidthGuard src1308.bank 179730 2308 src1308.reserve := requestWidth (by decide)

def ends1308 : List ℕ := [2308, 2309, 2313]




theorem cover1308 : Cover (Triangular src1308) 2313 2308 ends1308 := triangleCover (by decide +kernel)

def src1309 : Request := ⟨⟨⟨10008,13948,3070,115771⟩,30482919842381824,1050983571587703⟩,245,4,1,514639,34⟩

theorem rank1309 : P3_7_1.BankOK src1309.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10008_13948_3070 115771

theorem width1309 : Lower6960.HelperSource.WidthGuard src1309.bank 179730 2308 src1309.reserve := requestWidth (by decide)

def ends1309 : List ℕ := [2308, 2309, 2313]




theorem cover1309 : Cover (Triangular src1309) 2313 2308 ends1309 := triangleCover (by decide +kernel)

def src131 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,3,2,1,292947,51⟩

theorem rank131 : P3_7_1.BankOK src131.bank := by
  simpa only [src131, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4282

theorem width131 : Lower6960.HelperSource.WidthGuard src131.bank 179730 2308 src131.reserve := requestWidth (by decide)

def ends131 : List ℕ := [2313]

theorem inside131 : Research6966.TerminalBanks.inside src131.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover131 : Cover (Triangular src131) 2313 2308 ends131 := triangleCover (by decide +kernel)

def src1310 : Request := ⟨⟨⟨326,453,100,4817⟩,1068355026944,1193036697⟩,0,4,1,514639,38⟩

theorem rank1310 : P3_7_1.BankOK src1310.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 4817

theorem width1310 : Lower6960.HelperSource.WidthGuard src1310.bank 179730 2308 src1310.reserve := requestWidth (by decide)

def ends1310 : List ℕ := [2309, 2313]

theorem inside1310 : Research6966.TerminalBanks.inside src1310.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1310 : Cover (Triangular src1310) 2313 2308 ends1310 := triangleCover (by decide +kernel)

def src1311 : Request := ⟨⟨⟨400,557,120,4803⟩,1935519252480,2666981483⟩,1,4,1,514639,38⟩

theorem rank1311 : P3_7_1.BankOK src1311.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_400_557_120 4803

theorem width1311 : Lower6960.HelperSource.WidthGuard src1311.bank 179730 2308 src1311.reserve := requestWidth (by decide)

def ends1311 : List ℕ := [2308, 2309, 2313]

theorem inside1311 : Research6966.TerminalBanks.inside src1311.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1311 : Cover (Triangular src1311) 2313 2308 ends1311 := triangleCover (by decide +kernel)

def src1312 : Request := ⟨⟨⟨401,558,123,5419⟩,1982954733568,2734096379⟩,2,4,1,514639,38⟩

theorem rank1312 : P3_7_1.BankOK src1312.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_123 5419

theorem width1312 : Lower6960.HelperSource.WidthGuard src1312.bank 179730 2308 src1312.reserve := requestWidth (by decide)

def ends1312 : List ℕ := [2308, 2313]

theorem inside1312 : Research6966.TerminalBanks.inside src1312.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1312 : Cover (Triangular src1312) 2313 2308 ends1312 := triangleCover (by decide +kernel)

def src1313 : Request := ⟨⟨⟨471,655,144,6096⟩,3199755878400,5168862572⟩,4,4,1,514639,38⟩

theorem rank1313 : P3_7_1.BankOK src1313.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 6096

theorem width1313 : Lower6960.HelperSource.WidthGuard src1313.bank 179730 2308 src1313.reserve := requestWidth (by decide)

def ends1313 : List ℕ := [2308, 2313]

theorem inside1313 : Research6966.TerminalBanks.inside src1313.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1313 : Cover (Triangular src1313) 2313 2308 ends1313 := triangleCover (by decide +kernel)

def src1314 : Request := ⟨⟨⟨561,779,169,6853⟩,5338156236800,10214741280⟩,6,4,1,514639,38⟩

theorem rank1314 : P3_7_1.BankOK src1314.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_779_169 6853

theorem width1314 : Lower6960.HelperSource.WidthGuard src1314.bank 179730 2308 src1314.reserve := requestWidth (by decide)

def ends1314 : List ℕ := [2308, 2309, 2313]

theorem inside1314 : Research6966.TerminalBanks.inside src1314.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1314 : Cover (Triangular src1314) 2313 2308 ends1314 := triangleCover (by decide +kernel)

def src1315 : Request := ⟨⟨⟨690,958,208,8650⟩,9921631092736,23331166760⟩,10,4,1,514639,38⟩

theorem rank1315 : P3_7_1.BankOK src1315.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_958_208 8650

theorem width1315 : Lower6960.HelperSource.WidthGuard src1315.bank 179730 2308 src1315.reserve := requestWidth (by decide)

def ends1315 : List ℕ := [2308, 2309, 2313]

theorem inside1315 : Research6966.TerminalBanks.inside src1315.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1315 : Cover (Triangular src1315) 2313 2308 ends1315 := triangleCover (by decide +kernel)

def src1316 : Request := ⟨⟨⟨999,1387,307,12302⟩,30489252462592,103776832835⟩,20,4,1,514639,38⟩

theorem rank1316 : P3_7_1.BankOK src1316.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_999_1387_307 12302

theorem width1316 : Lower6960.HelperSource.WidthGuard src1316.bank 179730 2308 src1316.reserve := requestWidth (by decide)

def ends1316 : List ℕ := [2308, 2309, 2313]

theorem inside1316 : Research6966.TerminalBanks.inside src1316.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1316 : Cover (Triangular src1316) 2313 2308 ends1316 := triangleCover (by decide +kernel)

def src1317 : Request := ⟨⟨⟨1752,2441,537,19788⟩,163800293834752,988269431527⟩,40,4,1,514639,38⟩

theorem rank1317 : P3_7_1.BankOK src1317.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2441_537 19788

theorem width1317 : Lower6960.HelperSource.WidthGuard src1317.bank 179730 2308 src1317.reserve := requestWidth (by decide)

def ends1317 : List ℕ := [2309, 2313]

theorem inside1317 : Research6966.TerminalBanks.inside src1317.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1317 : Cover (Triangular src1317) 2313 2308 ends1317 := triangleCover (by decide +kernel)

def src1318 : Request := ⟨⟨⟨2607,3626,819,28173⟩,549365140684800,4905972788959⟩,65,4,1,514639,38⟩

theorem rank1318 : P3_7_1.BankOK src1318.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3626_819 28173

theorem width1318 : Lower6960.HelperSource.WidthGuard src1318.bank 179730 2308 src1318.reserve := requestWidth (by decide)

def ends1318 : List ℕ := [2308, 2309, 2313]

theorem inside1318 : Research6966.TerminalBanks.inside src1318.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1318 : Cover (Triangular src1318) 2313 2308 ends1318 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources13

section Pack_R6970Height2313CommonSources15

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1348 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,4,4,1,514639,49⟩

theorem rank1348 : P3_7_1.BankOK src1348.bank := by
  simpa only [src1348, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4282

theorem width1348 : Lower6960.HelperSource.WidthGuard src1348.bank 179730 2308 src1348.reserve := requestWidth (by decide)

def ends1348 : List ℕ := [2313]

theorem inside1348 : Research6966.TerminalBanks.inside src1348.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1348 : Cover (Triangular src1348) 2313 2308 ends1348 := triangleCover (by decide +kernel)

def src1349 : Request := ⟨⟨⟨471,655,144,6096⟩,3199755878400,5168862572⟩,8,4,1,514639,49⟩

theorem rank1349 : P3_7_1.BankOK src1349.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 6096

theorem width1349 : Lower6960.HelperSource.WidthGuard src1349.bank 179730 2308 src1349.reserve := requestWidth (by decide)

def ends1349 : List ℕ := [2308, 2313]

theorem inside1349 : Research6966.TerminalBanks.inside src1349.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1349 : Cover (Triangular src1349) 2313 2308 ends1349 := triangleCover (by decide +kernel)

def src135 : Request := ⟨⟨⟨691,962,217,6858⟩,10277672714240,24434817260⟩,13,2,1,292947,51⟩

theorem rank135 : P3_7_1.BankOK src135.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_217 6858

theorem width135 : Lower6960.HelperSource.WidthGuard src135.bank 179730 2308 src135.reserve := requestWidth (by decide)

def ends135 : List ℕ := [2308, 2309, 2313]

theorem inside135 : Research6966.TerminalBanks.inside src135.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover135 : Cover (Triangular src135) 2313 2308 ends135 := triangleCover (by decide +kernel)

def src1350 : Request := ⟨⟨⟨692,962,217,7715⟩,10311018217472,24434817260⟩,16,4,1,514639,49⟩

theorem rank1350 : P3_7_1.BankOK src1350.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_217 7715

theorem width1350 : Lower6960.HelperSource.WidthGuard src1350.bank 179730 2308 src1350.reserve := requestWidth (by decide)

def ends1350 : List ℕ := [2308, 2309, 2313]

theorem inside1350 : Research6966.TerminalBanks.inside src1350.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1350 : Cover (Triangular src1350) 2313 2308 ends1350 := triangleCover (by decide +kernel)

def src1351 : Request := ⟨⟨⟨1451,2014,445,13847⟩,93142595928064,459863749271⟩,40,4,1,514639,49⟩

theorem rank1351 : P3_7_1.BankOK src1351.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2014_445 13847

theorem width1351 : Lower6960.HelperSource.WidthGuard src1351.bank 179730 2308 src1351.reserve := requestWidth (by decide)

def ends1351 : List ℕ := [2308, 2309, 2313]

theorem inside1351 : Research6966.TerminalBanks.inside src1351.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1351 : Cover (Triangular src1351) 2313 2308 ends1351 := triangleCover (by decide +kernel)

def src1352 : Request := ⟨⟨⟨2577,3593,775,31399⟩,513340428255232,4563371321017⟩,85,4,1,514639,49⟩

theorem rank1352 : P3_7_1.BankOK src1352.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2577_3593_775 31399

theorem width1352 : Lower6960.HelperSource.WidthGuard src1352.bank 179730 2308 src1352.reserve := requestWidth (by decide)

def ends1352 : List ℕ := [2308, 2309, 2313]

theorem inside1352 : Research6966.TerminalBanks.inside src1352.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1352 : Cover (Triangular src1352) 2313 2308 ends1352 := triangleCover (by decide +kernel)

def src1353 : Request := ⟨⟨⟨2588,3593,793,27454⟩,527385327042560,4645717944219⟩,85,4,1,514639,49⟩

theorem rank1353 : P3_7_1.BankOK src1353.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 27454

theorem width1353 : Lower6960.HelperSource.WidthGuard src1353.bank 179730 2308 src1353.reserve := requestWidth (by decide)

def ends1353 : List ℕ := [2308, 2309, 2313]

theorem inside1353 : Research6966.TerminalBanks.inside src1353.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1353 : Cover (Triangular src1353) 2313 2308 ends1353 := triangleCover (by decide +kernel)

def src1354 : Request := ⟨⟨⟨3208,4454,982,35581⟩,1003361371160576,10956603240596⟩,110,4,1,514639,49⟩

theorem rank1354 : P3_7_1.BankOK src1354.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3208_4454_982 35581

theorem width1354 : Lower6960.HelperSource.WidthGuard src1354.bank 179730 2308 src1354.reserve := requestWidth (by decide)

def ends1354 : List ℕ := [2308, 2309, 2313]




theorem cover1354 : Cover (Triangular src1354) 2313 2308 ends1354 := triangleCover (by decide +kernel)

def src1355 : Request := ⟨⟨⟨3961,5499,1213,50744⟩,1888787979829248,25457931418119⟩,145,4,1,514639,49⟩

theorem rank1355 : P3_7_1.BankOK src1355.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3961_5499_1213 50744

theorem width1355 : Lower6960.HelperSource.WidthGuard src1355.bank 179730 2308 src1355.reserve := requestWidth (by decide)

def ends1355 : List ℕ := [2308, 2309, 2313]




theorem cover1355 : Cover (Triangular src1355) 2313 2308 ends1355 := triangleCover (by decide +kernel)

def src1356 : Request := ⟨⟨⟨5700,7948,1750,57109⟩,5637370734182400,110890906752819⟩,190,4,1,514639,49⟩

theorem rank1356 : P3_7_1.BankOK src1356.bank := by
  simpa only [src1356, _root_.Research6969.TransitionBanks.bank336] using _root_.Research6969.TransitionBanks.rank336 57109

theorem width1356 : Lower6960.HelperSource.WidthGuard src1356.bank 179730 2308 src1356.reserve := requestWidth (by decide)

def ends1356 : List ℕ := [2308, 2313]



theorem cover1356 : Cover (Triangular src1356) 2313 2308 ends1356 := triangleCover (by decide +kernel)

def src1357 : Request := ⟨⟨⟨6906,9621,2174,72277⟩,10216661254144000,242895948111878⟩,245,4,1,514639,49⟩

theorem rank1357 : P3_7_1.BankOK src1357.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6906_9621_2174 72277

theorem width1357 : Lower6960.HelperSource.WidthGuard src1357.bank 179730 2308 src1357.reserve := requestWidth (by decide)

def ends1357 : List ℕ := [2308, 2309, 2313]




theorem cover1357 : Cover (Triangular src1357) 2313 2308 ends1357 := triangleCover (by decide +kernel)

def src1358 : Request := ⟨⟨⟨276,383,87,2674⟩,663397335040,625236061⟩,0,4,1,514639,53⟩

theorem rank1358 : P3_7_1.BankOK src1358.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_276_383_87 2674

theorem width1358 : Lower6960.HelperSource.WidthGuard src1358.bank 179730 2308 src1358.reserve := requestWidth (by decide)

def ends1358 : List ℕ := [2313]

theorem inside1358 : Research6966.TerminalBanks.inside src1358.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1358 : Cover (Triangular src1358) 2313 2308 ends1358 := triangleCover (by decide +kernel)

def src1359 : Request := ⟨⟨⟨326,453,98,3008⟩,1052225568768,1174588250⟩,1,4,1,514639,53⟩

theorem rank1359 : P3_7_1.BankOK src1359.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_98 3008

theorem width1359 : Lower6960.HelperSource.WidthGuard src1359.bank 179730 2308 src1359.reserve := requestWidth (by decide)

def ends1359 : List ℕ := [2308, 2313]

theorem inside1359 : Research6966.TerminalBanks.inside src1359.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1359 : Cover (Triangular src1359) 2313 2308 ends1359 := triangleCover (by decide +kernel)

def src136 : Request := ⟨⟨⟨1003,1394,315,10983⟩,31367332102144,107596110457⟩,25,2,1,292947,51⟩

theorem rank136 : P3_7_1.BankOK src136.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1394_315 10983

theorem width136 : Lower6960.HelperSource.WidthGuard src136.bank 179730 2308 src136.reserve := requestWidth (by decide)

def ends136 : List ℕ := [2308, 2309, 2313]

theorem inside136 : Research6966.TerminalBanks.inside src136.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover136 : Cover (Triangular src136) 2313 2308 ends136 := triangleCover (by decide +kernel)

def src1360 : Request := ⟨⟨⟨325,451,98,3357⟩,1045036793856,1158025616⟩,2,4,1,514639,53⟩

theorem rank1360 : P3_7_1.BankOK src1360.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 3357

theorem width1360 : Lower6960.HelperSource.WidthGuard src1360.bank 179730 2308 src1360.reserve := requestWidth (by decide)

def ends1360 : List ℕ := [2308, 2309, 2313]

theorem inside1360 : Research6966.TerminalBanks.inside src1360.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1360 : Cover (Triangular src1360) 2313 2308 ends1360 := triangleCover (by decide +kernel)

def src1361 : Request := ⟨⟨⟨326,453,102,3807⟩,1084353413120,1211360939⟩,3,4,1,514639,53⟩

theorem rank1361 : P3_7_1.BankOK src1361.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_102 3807

theorem width1361 : Lower6960.HelperSource.WidthGuard src1361.bank 179730 2308 src1361.reserve := requestWidth (by decide)

def ends1361 : List ℕ := [2313]

theorem inside1361 : Research6966.TerminalBanks.inside src1361.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1361 : Cover (Triangular src1361) 2313 2308 ends1361 := triangleCover (by decide +kernel)

def src1362 : Request := ⟨⟨⟨400,558,123,3807⟩,1971918995456,2734096379⟩,4,4,1,514639,53⟩

theorem rank1362 : P3_7_1.BankOK src1362.bank := by
  simpa only [src1362, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 3807

theorem width1362 : Lower6960.HelperSource.WidthGuard src1362.bank 179730 2308 src1362.reserve := requestWidth (by decide)

def ends1362 : List ℕ := [2313]

theorem inside1362 : Research6966.TerminalBanks.inside src1362.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1362 : Cover (Triangular src1362) 2313 2308 ends1362 := triangleCover (by decide +kernel)

def src1363 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,6,4,1,514639,53⟩

theorem rank1363 : P3_7_1.BankOK src1363.bank := by
  simpa only [src1363, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4817

theorem width1363 : Lower6960.HelperSource.WidthGuard src1363.bank 179730 2308 src1363.reserve := requestWidth (by decide)

def ends1363 : List ℕ := [2308, 2309, 2313]

theorem inside1363 : Research6966.TerminalBanks.inside src1363.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1363 : Cover (Triangular src1363) 2313 2308 ends1363 := triangleCover (by decide +kernel)

def src1364 : Request := ⟨⟨⟨471,655,148,4817⟩,3266464186368,5279398867⟩,8,4,1,514639,53⟩

theorem rank1364 : P3_7_1.BankOK src1364.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 4817

theorem width1364 : Lower6960.HelperSource.WidthGuard src1364.bank 179730 2308 src1364.reserve := requestWidth (by decide)

def ends1364 : List ℕ := [2308, 2313]

theorem inside1364 : Research6966.TerminalBanks.inside src1364.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1364 : Cover (Triangular src1364) 2313 2308 ends1364 := triangleCover (by decide +kernel)

def src1365 : Request := ⟨⟨⟨691,960,212,6855⟩,10098434375680,23837765139⟩,16,4,1,514639,53⟩

theorem rank1365 : P3_7_1.BankOK src1365.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_960_212 6855

theorem width1365 : Lower6960.HelperSource.WidthGuard src1365.bank 179730 2308 src1365.reserve := requestWidth (by decide)

def ends1365 : List ℕ := [2308, 2309, 2313]

theorem inside1365 : Research6966.TerminalBanks.inside src1365.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1365 : Cover (Triangular src1365) 2313 2308 ends1365 := triangleCover (by decide +kernel)

def src1366 : Request := ⟨⟨⟨1002,1394,307,13899⟩,30694534807552,105471636407⟩,32,4,1,514639,53⟩

theorem rank1366 : P3_7_1.BankOK src1366.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1394_307 13899

theorem width1366 : Lower6960.HelperSource.WidthGuard src1366.bank 179730 2308 src1366.reserve := requestWidth (by decide)

def ends1366 : List ℕ := [2309, 2313]

theorem inside1366 : Research6966.TerminalBanks.inside src1366.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1366 : Cover (Triangular src1366) 2313 2308 ends1366 := triangleCover (by decide +kernel)

def src1367 : Request := ⟨⟨⟨1451,2022,457,17590⟩,95036839034880,475487789910⟩,50,4,1,514639,53⟩

theorem rank1367 : P3_7_1.BankOK src1367.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2022_457 17590

theorem width1367 : Lower6960.HelperSource.WidthGuard src1367.bank 179730 2308 src1367.reserve := requestWidth (by decide)

def ends1367 : List ℕ := [2309, 2313]

theorem inside1367 : Research6966.TerminalBanks.inside src1367.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1367 : Cover (Triangular src1367) 2313 2308 ends1367 := triangleCover (by decide +kernel)

def src1368 : Request := ⟨⟨⟨4808,6692,1512,57109⟩,3445982427611136,56871238465897⟩,190,4,1,514639,53⟩

theorem rank1368 : P3_7_1.BankOK src1368.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4808_6692_1512 57109

theorem width1368 : Lower6960.HelperSource.WidthGuard src1368.bank 179730 2308 src1368.reserve := requestWidth (by decide)

def ends1368 : List ℕ := [2308, 2309, 2313]




theorem cover1368 : Cover (Triangular src1368) 2313 2308 ends1368 := triangleCover (by decide +kernel)

def src1369 : Request := ⟨⟨⟨2600,3624,793,35655⟩,532875289296896,4776001446129⟩,115,4,1,514639,65⟩

theorem rank1369 : P3_7_1.BankOK src1369.bank := by
  simpa only [src1369, _root_.Research6969.TerminalAuxBanks.bank43] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank43 35655

theorem width1369 : Lower6960.HelperSource.WidthGuard src1369.bank 179730 2308 src1369.reserve := requestWidth (by decide)

def ends1369 : List ℕ := [2313]

theorem inside1369 : Research6966.TerminalBanks.inside src1369.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1369 : Cover (Triangular src1369) 2313 2308 ends1369 := triangleCover (by decide +kernel)

def src137 : Request := ⟨⟨⟨2104,2928,662,25043⟩,289245218209792,2088662039796⟩,65,2,1,292947,51⟩

theorem rank137 : P3_7_1.BankOK src137.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2104_2928_662 25043

theorem width137 : Lower6960.HelperSource.WidthGuard src137.bank 179730 2308 src137.reserve := requestWidth (by decide)

def ends137 : List ℕ := [2308, 2309, 2313]

theorem inside137 : Research6966.TerminalBanks.inside src137.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover137 : Cover (Triangular src137) 2313 2308 ends137 := triangleCover (by decide +kernel)

def src1370 : Request := ⟨⟨⟨2613,3624,819,29473⟩,552203877089280,4897259437389⟩,115,4,1,514639,65⟩

theorem rank1370 : P3_7_1.BankOK src1370.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2613_3624_819 29473

theorem width1370 : Lower6960.HelperSource.WidthGuard src1370.bank 179730 2308 src1370.reserve := requestWidth (by decide)

def ends1370 : List ℕ := [2308, 2309, 2313]

theorem inside1370 : Research6966.TerminalBanks.inside src1370.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1370 : Cover (Triangular src1370) 2313 2308 ends1370 := triangleCover (by decide +kernel)

def src1371 : Request := ⟨⟨⟨2003,2787,610,31694⟩,243494574096384,1672034111214⟩,115,4,1,514639,97⟩

theorem rank1371 : P3_7_1.BankOK src1371.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2003_2787_610 31694

theorem width1371 : Lower6960.HelperSource.WidthGuard src1371.bank 179730 2308 src1371.reserve := requestWidth (by decide)

def ends1371 : List ℕ := [2308, 2309, 2313]

theorem inside1371 : Research6966.TerminalBanks.inside src1371.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1371 : Cover (Triangular src1371) 2313 2308 ends1371 := triangleCover (by decide +kernel)

def src1372 : Request := ⟨⟨⟨2608,3623,801,34532⟩,540658700124160,4809178421847⟩,151,4,1,514639,97⟩

theorem rank1372 : P3_7_1.BankOK src1372.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3623_801 34532

theorem width1372 : Lower6960.HelperSource.WidthGuard src1372.bank 179730 2308 src1372.reserve := requestWidth (by decide)

def ends1372 : List ℕ := [2308, 2309, 2313]

theorem inside1372 : Research6966.TerminalBanks.inside src1372.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1372 : Cover (Triangular src1372) 2313 2308 ends1372 := triangleCover (by decide +kernel)

def src1373 : Request := ⟨⟨⟨1755,2438,536,28333⟩,164196333912064,982939289346⟩,115,4,1,514639,129⟩

theorem rank1373 : P3_7_1.BankOK src1373.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2438_536 28333

theorem width1373 : Lower6960.HelperSource.WidthGuard src1373.bank 179730 2308 src1373.reserve := requestWidth (by decide)

def ends1373 : List ℕ := [2308, 2309, 2313]

theorem inside1373 : Research6966.TerminalBanks.inside src1373.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1373 : Cover (Triangular src1373) 2313 2308 ends1373 := triangleCover (by decide +kernel)

def src1374 : Request := ⟨⟨⟨2953,4114,894,42838⟩,776154682490880,7886833980213⟩,195,4,1,514639,129⟩

theorem rank1374 : P3_7_1.BankOK src1374.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2953_4114_894 42838

theorem width1374 : Lower6960.HelperSource.WidthGuard src1374.bank 179730 2308 src1374.reserve := requestWidth (by decide)

def ends1374 : List ℕ := [2308, 2309, 2313]

theorem inside1374 : Research6966.TerminalBanks.inside src1374.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1374 : Cover (Triangular src1374) 2313 2308 ends1374 := triangleCover (by decide +kernel)

def src1375 : Request := ⟨⟨⟨2307,3203,702,45920⟩,371690023944192,2918855628076⟩,195,4,1,514639,257⟩

theorem rank1375 : P3_7_1.BankOK src1375.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3203_702 45920

theorem width1375 : Lower6960.HelperSource.WidthGuard src1375.bank 179730 2308 src1375.reserve := requestWidth (by decide)

def ends1375 : List ℕ := [2308, 2309, 2313]

theorem inside1375 : Research6966.TerminalBanks.inside src1375.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1375 : Cover (Triangular src1375) 2313 2308 ends1375 := triangleCover (by decide +kernel)

def src1376 : Request := ⟨⟨⟨2957,4108,894,55917⟩,778508848332800,7849872303328⟩,250,4,1,514639,257⟩

theorem rank1376 : P3_7_1.BankOK src1376.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2957_4108_894 55917

theorem width1376 : Lower6960.HelperSource.WidthGuard src1376.bank 179730 2308 src1376.reserve := requestWidth (by decide)

def ends1376 : List ℕ := [2308, 2309, 2313]

theorem inside1376 : Research6966.TerminalBanks.inside src1376.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1376 : Cover (Triangular src1376) 2313 2308 ends1376 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources15

section Pack_R6970Height2313CommonSources16

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1377 : Request := ⟨⟨⟨2002,2784,610,50419⟩,243222605463552,1666247886835⟩,195,4,1,514639,513⟩

theorem rank1377 : P3_7_1.BankOK src1377.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2002_2784_610 50419

theorem width1377 : Lower6960.HelperSource.WidthGuard src1377.bank 179730 2308 src1377.reserve := requestWidth (by decide)

def ends1377 : List ℕ := [2308, 2309, 2313]

theorem inside1377 : Research6966.TerminalBanks.inside src1377.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1377 : Cover (Triangular src1377) 2313 2308 ends1377 := triangleCover (by decide +kernel)

def src1378 : Request := ⟨⟨⟨2593,3604,775,59786⟩,520494434484224,4608474947497⟩,249,4,1,514639,513⟩

theorem rank1378 : P3_7_1.BankOK src1378.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2593_3604_775 59786

theorem width1378 : Lower6960.HelperSource.WidthGuard src1378.bank 179730 2308 src1378.reserve := requestWidth (by decide)

def ends1378 : List ℕ := [2308, 2309, 2313]

theorem inside1378 : Research6966.TerminalBanks.inside src1378.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1378 : Cover (Triangular src1378) 2313 2308 ends1378 := triangleCover (by decide +kernel)

def src1379 : Request := ⟨⟨⟨1450,2018,432,49853⟩,90926432911360,452250342305⟩,150,4,1,514639,1025⟩

theorem rank1379 : P3_7_1.BankOK src1379.bank := by
  simpa only [src1379, _root_.Research6969.TerminalAuxBanks.bank5] using _root_.Research6969.PackedRanks.TerminalRanks4To7.rank5 49853

theorem width1379 : Lower6960.HelperSource.WidthGuard src1379.bank 179730 2308 src1379.reserve := requestWidth (by decide)

def ends1379 : List ℕ := [2313]

theorem inside1379 : Research6966.TerminalBanks.inside src1379.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1379 : Cover (Triangular src1379) 2313 2308 ends1379 := triangleCover (by decide +kernel)

def src138 : Request := ⟨⟨⟨5680,7884,1750,64493⟩,5593163081973760,108040693109459⟩,190,2,1,292947,51⟩

theorem rank138 : P3_7_1.BankOK src138.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5680_7884_1750 64493

theorem width138 : Lower6960.HelperSource.WidthGuard src138.bank 179730 2308 src138.reserve := requestWidth (by decide)

def ends138 : List ℕ := [2308, 2309, 2313]




theorem cover138 : Cover (Triangular src138) 2313 2308 ends138 := triangleCover (by decide +kernel)

def src1380 : Request := ⟨⟨⟨3001,4171,898,112159⟩,807397411258368,8272669034533⟩,325,4,1,515031,1025⟩

theorem rank1380 : P3_7_1.BankOK src1380.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3001_4171_898 112159

theorem width1380 : Lower6960.HelperSource.WidthGuard src1380.bank 179730 2308 src1380.reserve := requestWidth (by decide)

def ends1380 : List ℕ := [2308, 2309, 2313]

theorem inside1380 : Research6966.TerminalBanks.inside src1380.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1380 : Cover (Triangular src1380) 2313 2308 ends1380 := triangleCover (by decide +kernel)

def src1381 : Request := ⟨⟨⟨2808,3900,854,113178⟩,669724928901120,6408244632207⟩,325,4,1,514639,2049⟩

theorem rank1381 : P3_7_1.BankOK src1381.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 113178

theorem width1381 : Lower6960.HelperSource.WidthGuard src1381.bank 179730 2308 src1381.reserve := requestWidth (by decide)

def ends1381 : List ℕ := [2308, 2309, 2313]

theorem inside1381 : Research6966.TerminalBanks.inside src1381.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1381 : Cover (Triangular src1381) 2313 2308 ends1381 := triangleCover (by decide +kernel)

def src1382 : Request := ⟨⟨⟨2804,3896,850,120180⟩,665212455485440,6363799590291⟩,325,4,1,514639,2049⟩

theorem rank1382 : P3_7_1.BankOK src1382.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2804_3896_850 120180

theorem width1382 : Lower6960.HelperSource.WidthGuard src1382.bank 179730 2308 src1382.reserve := requestWidth (by decide)

def ends1382 : List ℕ := [2308, 2309, 2313]

theorem inside1382 : Research6966.TerminalBanks.inside src1382.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1382 : Cover (Triangular src1382) 2313 2308 ends1382 := triangleCover (by decide +kernel)

def src1383 : Request := ⟨⟨⟨1000,1391,304,57945⟩,30330999275520,103947228761⟩,115,4,1,514639,4097⟩

theorem rank1383 : P3_7_1.BankOK src1383.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_304 57945

theorem width1383 : Lower6960.HelperSource.WidthGuard src1383.bank 179730 2308 src1383.reserve := requestWidth (by decide)

def ends1383 : List ℕ := [2308, 2309, 2313]

theorem inside1383 : Research6966.TerminalBanks.inside src1383.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1383 : Cover (Triangular src1383) 2313 2308 ends1383 := triangleCover (by decide +kernel)

def src1384 : Request := ⟨⟨⟨2748,3824,812,151067⟩,614083158081536,5782986158433⟩,325,4,1,514639,4097⟩

theorem rank1384 : P3_7_1.BankOK src1384.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 151067

theorem width1384 : Lower6960.HelperSource.WidthGuard src1384.bank 179730 2308 src1384.reserve := requestWidth (by decide)

def ends1384 : List ℕ := [2308, 2309, 2313]

theorem inside1384 : Research6966.TerminalBanks.inside src1384.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1384 : Cover (Triangular src1384) 2313 2308 ends1384 := triangleCover (by decide +kernel)

def src1385 : Request := ⟨⟨⟨2002,2782,602,214047⟩,240792766513152,1645394621605⟩,248,4,1,514639,8193⟩

theorem rank1385 : P3_7_1.BankOK src1385.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2002_2782_602 214047

theorem width1385 : Lower6960.HelperSource.WidthGuard src1385.bank 179730 2308 src1385.reserve := requestWidth (by decide)

def ends1385 : List ℕ := [2308, 2309, 2313]

theorem inside1385 : Research6966.TerminalBanks.inside src1385.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1385 : Cover (Triangular src1385) 2313 2308 ends1385 := triangleCover (by decide +kernel)

def src1386 : Request := ⟨⟨⟨1202,1670,365,139405⟩,52587979866112,215752938462⟩,150,4,1,514639,32769⟩

theorem rank1386 : P3_7_1.BankOK src1386.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1670_365 139405

theorem width1386 : Lower6960.HelperSource.WidthGuard src1386.bank 179730 2308 src1386.reserve := requestWidth (by decide)

def ends1386 : List ℕ := [2308, 2309, 2313]

theorem inside1386 : Research6966.TerminalBanks.inside src1386.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1386 : Cover (Triangular src1386) 2313 2308 ends1386 := triangleCover (by decide +kernel)

def src1387 : Request := ⟨⟨⟨556,772,170,8278⟩,5255817068544,9968090926⟩,10,4,2,514638,2⟩

theorem rank1387 : P3_7_1.BankOK src1387.bank := by
  simpa only [src1387, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 8278

theorem width1387 : Lower6960.HelperSource.WidthGuard src1387.bank 179730 2308 src1387.reserve := requestWidth (by decide)

def ends1387 : List ℕ := [2308, 2309, 2313]

theorem inside1387 : Research6966.TerminalBanks.inside src1387.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1387 : Cover (Triangular src1387) 2313 2308 ends1387 := triangleCover (by decide +kernel)

def src1388 : Request := ⟨⟨⟨555,770,170,8178⟩,5234703728640,9885300877⟩,10,4,2,514638,3⟩

theorem rank1388 : P3_7_1.BankOK src1388.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 8178

theorem width1388 : Lower6960.HelperSource.WidthGuard src1388.bank 179730 2308 src1388.reserve := requestWidth (by decide)

def ends1388 : List ℕ := [2308, 2309, 2313]

theorem inside1388 : Research6966.TerminalBanks.inside src1388.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1388 : Cover (Triangular src1388) 2313 2308 ends1388 := triangleCover (by decide +kernel)

def src1389 : Request := ⟨⟨⟨556,772,170,7986⟩,5255817068544,9968090926⟩,10,4,2,514638,5⟩

theorem rank1389 : P3_7_1.BankOK src1389.bank := by
  simpa only [src1389, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7986

theorem width1389 : Lower6960.HelperSource.WidthGuard src1389.bank 179730 2308 src1389.reserve := requestWidth (by decide)

def ends1389 : List ℕ := [2308, 2309, 2313]

theorem inside1389 : Research6966.TerminalBanks.inside src1389.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1389 : Cover (Triangular src1389) 2313 2308 ends1389 := triangleCover (by decide +kernel)

def src139 : Request := ⟨⟨⟨2778,3857,854,35655⟩,653812598046720,6183527699682⟩,63,2,1,294092,41⟩

theorem rank139 : P3_7_1.BankOK src139.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2778_3857_854 35655

theorem width139 : Lower6960.HelperSource.WidthGuard src139.bank 179730 2308 src139.reserve := requestWidth (by decide)

def ends139 : List ℕ := [2308, 2309, 2313]

theorem inside139 : Research6966.TerminalBanks.inside src139.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover139 : Cover (Triangular src139) 2313 2308 ends139 := triangleCover (by decide +kernel)

def src1390 : Request := ⟨⟨⟨555,770,170,7886⟩,5234703728640,9885300877⟩,10,4,2,514638,6⟩

theorem rank1390 : P3_7_1.BankOK src1390.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 7886

theorem width1390 : Lower6960.HelperSource.WidthGuard src1390.bank 179730 2308 src1390.reserve := requestWidth (by decide)

def ends1390 : List ℕ := [2308, 2309, 2313]

theorem inside1390 : Research6966.TerminalBanks.inside src1390.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1390 : Cover (Triangular src1390) 2313 2308 ends1390 := triangleCover (by decide +kernel)

def src1391 : Request := ⟨⟨⟨556,772,170,7794⟩,5255817068544,9968090926⟩,10,4,2,514638,7⟩

theorem rank1391 : P3_7_1.BankOK src1391.bank := by
  simpa only [src1391, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7794

theorem width1391 : Lower6960.HelperSource.WidthGuard src1391.bank 179730 2308 src1391.reserve := requestWidth (by decide)

def ends1391 : List ℕ := [2308, 2309, 2313]

theorem inside1391 : Research6966.TerminalBanks.inside src1391.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1391 : Cover (Triangular src1391) 2313 2308 ends1391 := triangleCover (by decide +kernel)

def src1392 : Request := ⟨⟨⟨555,770,170,7694⟩,5234703728640,9885300877⟩,10,4,2,514638,8⟩

theorem rank1392 : P3_7_1.BankOK src1392.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 7694

theorem width1392 : Lower6960.HelperSource.WidthGuard src1392.bank 179730 2308 src1392.reserve := requestWidth (by decide)

def ends1392 : List ℕ := [2308, 2309, 2313]

theorem inside1392 : Research6966.TerminalBanks.inside src1392.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1392 : Cover (Triangular src1392) 2313 2308 ends1392 := triangleCover (by decide +kernel)

def src1393 : Request := ⟨⟨⟨556,772,170,7604⟩,5255817068544,9968090926⟩,10,4,2,514638,9⟩

theorem rank1393 : P3_7_1.BankOK src1393.bank := by
  simpa only [src1393, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7604

theorem width1393 : Lower6960.HelperSource.WidthGuard src1393.bank 179730 2308 src1393.reserve := requestWidth (by decide)

def ends1393 : List ℕ := [2308, 2309, 2313]

theorem inside1393 : Research6966.TerminalBanks.inside src1393.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1393 : Cover (Triangular src1393) 2313 2308 ends1393 := triangleCover (by decide +kernel)

def src1394 : Request := ⟨⟨⟨555,770,170,7505⟩,5234703728640,9885300877⟩,10,4,2,514638,10⟩

theorem rank1394 : P3_7_1.BankOK src1394.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 7505

theorem width1394 : Lower6960.HelperSource.WidthGuard src1394.bank 179730 2308 src1394.reserve := requestWidth (by decide)

def ends1394 : List ℕ := [2308, 2309, 2313]

theorem inside1394 : Research6966.TerminalBanks.inside src1394.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1394 : Cover (Triangular src1394) 2313 2308 ends1394 := triangleCover (by decide +kernel)

def src1395 : Request := ⟨⟨⟨556,772,170,7417⟩,5255817068544,9968090926⟩,10,4,2,514638,11⟩

theorem rank1395 : P3_7_1.BankOK src1395.bank := by
  simpa only [src1395, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7417

theorem width1395 : Lower6960.HelperSource.WidthGuard src1395.bank 179730 2308 src1395.reserve := requestWidth (by decide)

def ends1395 : List ℕ := [2308, 2309, 2313]

theorem inside1395 : Research6966.TerminalBanks.inside src1395.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1395 : Cover (Triangular src1395) 2313 2308 ends1395 := triangleCover (by decide +kernel)

def src1396 : Request := ⟨⟨⟨555,771,170,7325⟩,5234703728640,9926637163⟩,10,4,2,514638,12⟩

theorem rank1396 : P3_7_1.BankOK src1396.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_771_170 7325

theorem width1396 : Lower6960.HelperSource.WidthGuard src1396.bank 179730 2308 src1396.reserve := requestWidth (by decide)

def ends1396 : List ℕ := [2308, 2309, 2313]

theorem inside1396 : Research6966.TerminalBanks.inside src1396.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1396 : Cover (Triangular src1396) 2313 2308 ends1396 := triangleCover (by decide +kernel)

def src1397 : Request := ⟨⟨⟨556,772,170,7233⟩,5255817068544,9968090926⟩,10,4,2,514638,13⟩

theorem rank1397 : P3_7_1.BankOK src1397.bank := by
  simpa only [src1397, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7233

theorem width1397 : Lower6960.HelperSource.WidthGuard src1397.bank 179730 2308 src1397.reserve := requestWidth (by decide)

def ends1397 : List ℕ := [2308, 2309, 2313]

theorem inside1397 : Research6966.TerminalBanks.inside src1397.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1397 : Cover (Triangular src1397) 2313 2308 ends1397 := triangleCover (by decide +kernel)

def src1398 : Request := ⟨⟨⟨556,771,170,7141⟩,5255817068544,9926637163⟩,10,4,2,514638,14⟩

theorem rank1398 : P3_7_1.BankOK src1398.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_170 7141

theorem width1398 : Lower6960.HelperSource.WidthGuard src1398.bank 179730 2308 src1398.reserve := requestWidth (by decide)

def ends1398 : List ℕ := [2308, 2309, 2313]

theorem inside1398 : Research6966.TerminalBanks.inside src1398.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1398 : Cover (Triangular src1398) 2313 2308 ends1398 := triangleCover (by decide +kernel)

def src1399 : Request := ⟨⟨⟨556,771,170,7051⟩,5255817068544,9926637163⟩,10,4,2,514638,15⟩

theorem rank1399 : P3_7_1.BankOK src1399.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_170 7051

theorem width1399 : Lower6960.HelperSource.WidthGuard src1399.bank 179730 2308 src1399.reserve := requestWidth (by decide)

def ends1399 : List ℕ := [2308, 2309, 2313]

theorem inside1399 : Research6966.TerminalBanks.inside src1399.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1399 : Cover (Triangular src1399) 2313 2308 ends1399 := triangleCover (by decide +kernel)

def src14 : Request := ⟨⟨⟨2305,3203,724,45124⟩,379747886694400,2989680899568⟩,195,1,1,128659,257⟩

theorem rank14 : P3_7_1.BankOK src14.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3203_724 45124

theorem width14 : Lower6960.HelperSource.WidthGuard src14.bank 179730 2308 src14.reserve := requestWidth (by decide)

def ends14 : List ℕ := [2308, 2309, 2313]

theorem inside14 : Research6966.TerminalBanks.inside src14.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover14 : Cover (Triangular src14) 2313 2308 ends14 := triangleCover (by decide +kernel)

def src140 : Request := ⟨⟨⟨2913,4044,900,31327⟩,756649935765504,7501830777122⟩,65,2,1,294092,41⟩

theorem rank140 : P3_7_1.BankOK src140.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2913_4044_900 31327

theorem width140 : Lower6960.HelperSource.WidthGuard src140.bank 179730 2308 src140.reserve := requestWidth (by decide)

def ends140 : List ℕ := [2308, 2309, 2313]

theorem inside140 : Research6966.TerminalBanks.inside src140.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover140 : Cover (Triangular src140) 2313 2308 ends140 := triangleCover (by decide +kernel)

def src1400 : Request := ⟨⟨⟨555,771,170,6962⟩,5234703728640,9926637163⟩,10,4,2,514638,16⟩

theorem rank1400 : P3_7_1.BankOK src1400.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_771_170 6962

theorem width1400 : Lower6960.HelperSource.WidthGuard src1400.bank 179730 2308 src1400.reserve := requestWidth (by decide)

def ends1400 : List ℕ := [2308, 2309, 2313]

theorem inside1400 : Research6966.TerminalBanks.inside src1400.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1400 : Cover (Triangular src1400) 2313 2308 ends1400 := triangleCover (by decide +kernel)

def src1401 : Request := ⟨⟨⟨556,772,170,6874⟩,5255817068544,9968090926⟩,10,4,2,514638,17⟩

theorem rank1401 : P3_7_1.BankOK src1401.bank := by
  simpa only [src1401, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 6874

theorem width1401 : Lower6960.HelperSource.WidthGuard src1401.bank 179730 2308 src1401.reserve := requestWidth (by decide)

def ends1401 : List ℕ := [2308, 2309, 2313]

theorem inside1401 : Research6966.TerminalBanks.inside src1401.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1401 : Cover (Triangular src1401) 2313 2308 ends1401 := triangleCover (by decide +kernel)

def src1402 : Request := ⟨⟨⟨556,771,171,6770⟩,5279150768128,9971791336⟩,10,4,2,514638,18⟩

theorem rank1402 : P3_7_1.BankOK src1402.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_171 6770

theorem width1402 : Lower6960.HelperSource.WidthGuard src1402.bank 179730 2308 src1402.reserve := requestWidth (by decide)

def ends1402 : List ℕ := [2308, 2309, 2313]

theorem inside1402 : Research6966.TerminalBanks.inside src1402.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1402 : Cover (Triangular src1402) 2313 2308 ends1402 := triangleCover (by decide +kernel)

def src1403 : Request := ⟨⟨⟨556,771,171,6682⟩,5279150768128,9971791336⟩,10,4,2,514638,19⟩

theorem rank1403 : P3_7_1.BankOK src1403.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_171 6682

theorem width1403 : Lower6960.HelperSource.WidthGuard src1403.bank 179730 2308 src1403.reserve := requestWidth (by decide)

def ends1403 : List ℕ := [2308, 2309, 2313]

theorem inside1403 : Research6966.TerminalBanks.inside src1403.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1403 : Cover (Triangular src1403) 2313 2308 ends1403 := triangleCover (by decide +kernel)

def src1404 : Request := ⟨⟨⟨556,772,171,6598⟩,5279150768128,10013440706⟩,10,4,2,514638,20⟩

theorem rank1404 : P3_7_1.BankOK src1404.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6598

theorem width1404 : Lower6960.HelperSource.WidthGuard src1404.bank 179730 2308 src1404.reserve := requestWidth (by decide)

def ends1404 : List ℕ := [2308, 2309, 2313]

theorem inside1404 : Research6966.TerminalBanks.inside src1404.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1404 : Cover (Triangular src1404) 2313 2308 ends1404 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources16

section Pack_R6970Height2313CommonSources17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1405 : Request := ⟨⟨⟨556,772,171,6512⟩,5279150768128,10013440706⟩,10,4,2,514638,21⟩

theorem rank1405 : P3_7_1.BankOK src1405.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6512

theorem width1405 : Lower6960.HelperSource.WidthGuard src1405.bank 179730 2308 src1405.reserve := requestWidth (by decide)

def ends1405 : List ℕ := [2308, 2309, 2313]

theorem inside1405 : Research6966.TerminalBanks.inside src1405.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1405 : Cover (Triangular src1405) 2313 2308 ends1405 := triangleCover (by decide +kernel)

def src1406 : Request := ⟨⟨⟨556,771,171,6424⟩,5279150768128,9971791336⟩,10,4,2,514638,22⟩

theorem rank1406 : P3_7_1.BankOK src1406.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_171 6424

theorem width1406 : Lower6960.HelperSource.WidthGuard src1406.bank 179730 2308 src1406.reserve := requestWidth (by decide)

def ends1406 : List ℕ := [2308, 2309, 2313]

theorem inside1406 : Research6966.TerminalBanks.inside src1406.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1406 : Cover (Triangular src1406) 2313 2308 ends1406 := triangleCover (by decide +kernel)

def src1407 : Request := ⟨⟨⟨556,772,171,6344⟩,5279150768128,10013440706⟩,10,4,2,514638,23⟩

theorem rank1407 : P3_7_1.BankOK src1407.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6344

theorem width1407 : Lower6960.HelperSource.WidthGuard src1407.bank 179730 2308 src1407.reserve := requestWidth (by decide)

def ends1407 : List ℕ := [2308, 2309, 2313]

theorem inside1407 : Research6966.TerminalBanks.inside src1407.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1407 : Cover (Triangular src1407) 2313 2308 ends1407 := triangleCover (by decide +kernel)

def src1408 : Request := ⟨⟨⟨556,772,171,6261⟩,5279150768128,10013440706⟩,10,4,2,514638,24⟩

theorem rank1408 : P3_7_1.BankOK src1408.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6261

theorem width1408 : Lower6960.HelperSource.WidthGuard src1408.bank 179730 2308 src1408.reserve := requestWidth (by decide)

def ends1408 : List ℕ := [2308, 2309, 2313]

theorem inside1408 : Research6966.TerminalBanks.inside src1408.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1408 : Cover (Triangular src1408) 2313 2308 ends1408 := triangleCover (by decide +kernel)

def src1409 : Request := ⟨⟨⟨556,771,171,6176⟩,5279150768128,9971791336⟩,10,4,2,514638,25⟩

theorem rank1409 : P3_7_1.BankOK src1409.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_771_171 6176

theorem width1409 : Lower6960.HelperSource.WidthGuard src1409.bank 179730 2308 src1409.reserve := requestWidth (by decide)

def ends1409 : List ℕ := [2308, 2309, 2313]

theorem inside1409 : Research6966.TerminalBanks.inside src1409.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1409 : Cover (Triangular src1409) 2313 2308 ends1409 := triangleCover (by decide +kernel)

def src141 : Request := ⟨⟨⟨2576,3578,793,31872⟩,521925337284608,4583554892204⟩,63,2,1,294092,43⟩

theorem rank141 : P3_7_1.BankOK src141.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2576_3578_793 31872

theorem width141 : Lower6960.HelperSource.WidthGuard src141.bank 179730 2308 src141.reserve := requestWidth (by decide)

def ends141 : List ℕ := [2308, 2309, 2313]

theorem inside141 : Research6966.TerminalBanks.inside src141.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover141 : Cover (Triangular src141) 2313 2308 ends141 := triangleCover (by decide +kernel)

def src1410 : Request := ⟨⟨⟨556,772,171,6099⟩,5279150768128,10013440706⟩,10,4,2,514638,26⟩

theorem rank1410 : P3_7_1.BankOK src1410.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6099

theorem width1410 : Lower6960.HelperSource.WidthGuard src1410.bank 179730 2308 src1410.reserve := requestWidth (by decide)

def ends1410 : List ℕ := [2308, 2309, 2313]

theorem inside1410 : Research6966.TerminalBanks.inside src1410.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1410 : Cover (Triangular src1410) 2313 2308 ends1410 := triangleCover (by decide +kernel)

def src1411 : Request := ⟨⟨⟨556,772,171,6020⟩,5279150768128,10013440706⟩,10,4,2,514638,27⟩

theorem rank1411 : P3_7_1.BankOK src1411.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6020

theorem width1411 : Lower6960.HelperSource.WidthGuard src1411.bank 179730 2308 src1411.reserve := requestWidth (by decide)

def ends1411 : List ℕ := [2308, 2309, 2313]

theorem inside1411 : Research6966.TerminalBanks.inside src1411.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1411 : Cover (Triangular src1411) 2313 2308 ends1411 := triangleCover (by decide +kernel)

def src1412 : Request := ⟨⟨⟨556,772,171,5942⟩,5279150768128,10013440706⟩,10,4,2,514638,28⟩

theorem rank1412 : P3_7_1.BankOK src1412.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 5942

theorem width1412 : Lower6960.HelperSource.WidthGuard src1412.bank 179730 2308 src1412.reserve := requestWidth (by decide)

def ends1412 : List ℕ := [2308, 2309, 2313]

theorem inside1412 : Research6966.TerminalBanks.inside src1412.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1412 : Cover (Triangular src1412) 2313 2308 ends1412 := triangleCover (by decide +kernel)

def src1413 : Request := ⟨⟨⟨556,772,171,5865⟩,5279150768128,10013440706⟩,10,4,2,514638,29⟩

theorem rank1413 : P3_7_1.BankOK src1413.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 5865

theorem width1413 : Lower6960.HelperSource.WidthGuard src1413.bank 179730 2308 src1413.reserve := requestWidth (by decide)

def ends1413 : List ℕ := [2308, 2309, 2313]

theorem inside1413 : Research6966.TerminalBanks.inside src1413.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1413 : Cover (Triangular src1413) 2313 2308 ends1413 := triangleCover (by decide +kernel)

def src1414 : Request := ⟨⟨⟨556,772,171,5790⟩,5279150768128,10013440706⟩,10,4,2,514638,30⟩

theorem rank1414 : P3_7_1.BankOK src1414.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 5790

theorem width1414 : Lower6960.HelperSource.WidthGuard src1414.bank 179730 2308 src1414.reserve := requestWidth (by decide)

def ends1414 : List ℕ := [2308, 2309, 2313]

theorem inside1414 : Research6966.TerminalBanks.inside src1414.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1414 : Cover (Triangular src1414) 2313 2308 ends1414 := triangleCover (by decide +kernel)

def src1415 : Request := ⟨⟨⟨555,770,170,5727⟩,5234703728640,9885300877⟩,10,4,2,514638,31⟩

theorem rank1415 : P3_7_1.BankOK src1415.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 5727

theorem width1415 : Lower6960.HelperSource.WidthGuard src1415.bank 179730 2308 src1415.reserve := requestWidth (by decide)

def ends1415 : List ℕ := [2308, 2309, 2313]

theorem inside1415 : Research6966.TerminalBanks.inside src1415.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1415 : Cover (Triangular src1415) 2313 2308 ends1415 := triangleCover (by decide +kernel)

def src1416 : Request := ⟨⟨⟨555,770,170,5654⟩,5234703728640,9885300877⟩,10,4,2,514638,32⟩

theorem rank1416 : P3_7_1.BankOK src1416.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 5654

theorem width1416 : Lower6960.HelperSource.WidthGuard src1416.bank 179730 2308 src1416.reserve := requestWidth (by decide)

def ends1416 : List ℕ := [2308, 2309, 2313]

theorem inside1416 : Research6966.TerminalBanks.inside src1416.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1416 : Cover (Triangular src1416) 2313 2308 ends1416 := triangleCover (by decide +kernel)

def src1417 : Request := ⟨⟨⟨550,763,170,5552⟩,5129809428480,9599221867⟩,10,4,2,514638,33⟩

theorem rank1417 : P3_7_1.BankOK src1417.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 5552

theorem width1417 : Lower6960.HelperSource.WidthGuard src1417.bank 179730 2308 src1417.reserve := requestWidth (by decide)

def ends1417 : List ℕ := [2308, 2309, 2313]

theorem inside1417 : Research6966.TerminalBanks.inside src1417.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1417 : Cover (Triangular src1417) 2313 2308 ends1417 := triangleCover (by decide +kernel)

def src1418 : Request := ⟨⟨⟨545,756,170,5476⟩,5026035793920,9318832198⟩,10,4,2,514638,34⟩

theorem rank1418 : P3_7_1.BankOK src1418.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5476

theorem width1418 : Lower6960.HelperSource.WidthGuard src1418.bank 179730 2308 src1418.reserve := requestWidth (by decide)

def ends1418 : List ℕ := [2308, 2309, 2313]

theorem inside1418 : Research6966.TerminalBanks.inside src1418.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1418 : Cover (Triangular src1418) 2313 2308 ends1418 := triangleCover (by decide +kernel)

def src1419 : Request := ⟨⟨⟨551,764,170,5415⟩,5150698635264,9639740602⟩,10,4,2,514638,35⟩

theorem rank1419 : P3_7_1.BankOK src1419.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_551_764_170 5415

theorem width1419 : Lower6960.HelperSource.WidthGuard src1419.bank 179730 2308 src1419.reserve := requestWidth (by decide)

def ends1419 : List ℕ := [2308, 2309, 2313]

theorem inside1419 : Research6966.TerminalBanks.inside src1419.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1419 : Cover (Triangular src1419) 2313 2308 ends1419 := triangleCover (by decide +kernel)

def src142 : Request := ⟨⟨⟨2614,3630,815,28031⟩,550633901916160,4904759411010⟩,63,2,1,294092,43⟩

theorem rank142 : P3_7_1.BankOK src142.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3630_815 28031

theorem width142 : Lower6960.HelperSource.WidthGuard src142.bank 179730 2308 src142.reserve := requestWidth (by decide)

def ends142 : List ℕ := [2308, 2309, 2313]

theorem inside142 : Research6966.TerminalBanks.inside src142.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover142 : Cover (Triangular src142) 2313 2308 ends142 := triangleCover (by decide +kernel)

def src1420 : Request := ⟨⟨⟨551,764,170,5348⟩,5150698635264,9639740602⟩,10,4,2,514638,36⟩

theorem rank1420 : P3_7_1.BankOK src1420.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_551_764_170 5348

theorem width1420 : Lower6960.HelperSource.WidthGuard src1420.bank 179730 2308 src1420.reserve := requestWidth (by decide)

def ends1420 : List ℕ := [2308, 2309, 2313]

theorem inside1420 : Research6966.TerminalBanks.inside src1420.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1420 : Cover (Triangular src1420) 2313 2308 ends1420 := triangleCover (by decide +kernel)

def src1421 : Request := ⟨⟨⟨545,756,170,5267⟩,5026035793920,9318832198⟩,10,4,2,514638,37⟩

theorem rank1421 : P3_7_1.BankOK src1421.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5267

theorem width1421 : Lower6960.HelperSource.WidthGuard src1421.bank 179730 2308 src1421.reserve := requestWidth (by decide)

def ends1421 : List ℕ := [2308, 2309, 2313]

theorem inside1421 : Research6966.TerminalBanks.inside src1421.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1421 : Cover (Triangular src1421) 2313 2308 ends1421 := triangleCover (by decide +kernel)

def src1422 : Request := ⟨⟨⟨545,756,170,5201⟩,5026035793920,9318832198⟩,10,4,2,514638,38⟩

theorem rank1422 : P3_7_1.BankOK src1422.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5201

theorem width1422 : Lower6960.HelperSource.WidthGuard src1422.bank 179730 2308 src1422.reserve := requestWidth (by decide)

def ends1422 : List ℕ := [2308, 2309, 2313]

theorem inside1422 : Research6966.TerminalBanks.inside src1422.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1422 : Cover (Triangular src1422) 2313 2308 ends1422 := triangleCover (by decide +kernel)

def src1423 : Request := ⟨⟨⟨544,755,170,5139⟩,5005415546880,9279237547⟩,10,4,2,514638,39⟩

theorem rank1423 : P3_7_1.BankOK src1423.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_544_755_170 5139

theorem width1423 : Lower6960.HelperSource.WidthGuard src1423.bank 179730 2308 src1423.reserve := requestWidth (by decide)

def ends1423 : List ℕ := [2308, 2309, 2313]

theorem inside1423 : Research6966.TerminalBanks.inside src1423.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1423 : Cover (Triangular src1423) 2313 2308 ends1423 := triangleCover (by decide +kernel)

def src1424 : Request := ⟨⟨⟨545,756,170,5072⟩,5026035793920,9318832198⟩,10,4,2,514638,40⟩

theorem rank1424 : P3_7_1.BankOK src1424.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5072

theorem width1424 : Lower6960.HelperSource.WidthGuard src1424.bank 179730 2308 src1424.reserve := requestWidth (by decide)

def ends1424 : List ℕ := [2308, 2309, 2313]

theorem inside1424 : Research6966.TerminalBanks.inside src1424.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1424 : Cover (Triangular src1424) 2313 2308 ends1424 := triangleCover (by decide +kernel)

def src1425 : Request := ⟨⟨⟨545,756,170,5011⟩,5026035793920,9318832198⟩,10,4,2,514638,41⟩

theorem rank1425 : P3_7_1.BankOK src1425.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5011

theorem width1425 : Lower6960.HelperSource.WidthGuard src1425.bank 179730 2308 src1425.reserve := requestWidth (by decide)

def ends1425 : List ℕ := [2308, 2309, 2313]

theorem inside1425 : Research6966.TerminalBanks.inside src1425.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1425 : Cover (Triangular src1425) 2313 2308 ends1425 := triangleCover (by decide +kernel)

def src1426 : Request := ⟨⟨⟨545,756,170,4951⟩,5026035793920,9318832198⟩,10,4,2,514638,42⟩

theorem rank1426 : P3_7_1.BankOK src1426.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 4951

theorem width1426 : Lower6960.HelperSource.WidthGuard src1426.bank 179730 2308 src1426.reserve := requestWidth (by decide)

def ends1426 : List ℕ := [2308, 2309, 2313]

theorem inside1426 : Research6966.TerminalBanks.inside src1426.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1426 : Cover (Triangular src1426) 2313 2308 ends1426 := triangleCover (by decide +kernel)

def src1427 : Request := ⟨⟨⟨400,558,123,12355⟩,1971918995456,2734096379⟩,0,5,1,643299,1⟩

theorem rank1427 : P3_7_1.BankOK src1427.bank := by
  simpa only [src1427, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 12355

theorem width1427 : Lower6960.HelperSource.WidthGuard src1427.bank 179730 2308 src1427.reserve := requestWidth (by decide)

def ends1427 : List ℕ := [2308, 2309, 2313]

theorem inside1427 : Research6966.TerminalBanks.inside src1427.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1427 : Cover (Triangular src1427) 2313 2308 ends1427 := triangleCover (by decide +kernel)

def src1428 : Request := ⟨⟨⟨470,655,141,13899⟩,3134317133824,5085275599⟩,1,5,1,643299,1⟩

theorem rank1428 : P3_7_1.BankOK src1428.bank := by
  simpa only [src1428, _root_.Research6969.TransitionBanks.bank141] using _root_.Research6969.TransitionBanks.rank141 13899

theorem width1428 : Lower6960.HelperSource.WidthGuard src1428.bank 179730 2308 src1428.reserve := requestWidth (by decide)

def ends1428 : List ℕ := [2308, 2313]

theorem inside1428 : Research6966.TerminalBanks.inside src1428.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1428 : Cover (Triangular src1428) 2313 2308 ends1428 := triangleCover (by decide +kernel)

def src1429 : Request := ⟨⟨⟨470,655,141,15636⟩,3134317133824,5085275599⟩,2,5,1,643299,1⟩

theorem rank1429 : P3_7_1.BankOK src1429.bank := by
  simpa only [src1429, _root_.Research6969.TransitionBanks.bank141] using _root_.Research6969.TransitionBanks.rank141 15636

theorem width1429 : Lower6960.HelperSource.WidthGuard src1429.bank 179730 2308 src1429.reserve := requestWidth (by decide)

def ends1429 : List ℕ := [2308, 2313]

theorem inside1429 : Research6966.TerminalBanks.inside src1429.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1429 : Cover (Triangular src1429) 2313 2308 ends1429 := triangleCover (by decide +kernel)

def src143 : Request := ⟨⟨⟨2789,3873,854,35655⟩,659623697448960,6266506033362⟩,63,2,1,295365,41⟩

theorem rank143 : P3_7_1.BankOK src143.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 35655

theorem width143 : Lower6960.HelperSource.WidthGuard src143.bank 179730 2308 src143.reserve := requestWidth (by decide)

def ends143 : List ℕ := [2308, 2309, 2313]

theorem inside143 : Research6966.TerminalBanks.inside src143.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover143 : Cover (Triangular src143) 2313 2308 ends143 := triangleCover (by decide +kernel)

def src1430 : Request := ⟨⟨⟨560,781,169,17590⟩,5316921262080,10299257375⟩,4,5,1,643299,1⟩

theorem rank1430 : P3_7_1.BankOK src1430.bank := by
  simpa only [src1430, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 17590

theorem width1430 : Lower6960.HelperSource.WidthGuard src1430.bank 179730 2308 src1430.reserve := requestWidth (by decide)

def ends1430 : List ℕ := [2309, 2313]

theorem inside1430 : Research6966.TerminalBanks.inside src1430.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1430 : Cover (Triangular src1430) 2313 2308 ends1430 := triangleCover (by decide +kernel)

def src1431 : Request := ⟨⟨⟨690,962,212,22261⟩,10065769922560,23997864317⟩,8,5,1,643299,1⟩

theorem rank1431 : P3_7_1.BankOK src1431.bank := by
  simpa only [src1431, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 22261

theorem width1431 : Lower6960.HelperSource.WidthGuard src1431.bank 179730 2308 src1431.reserve := requestWidth (by decide)

def ends1431 : List ℕ := [2308, 2313]

theorem inside1431 : Research6966.TerminalBanks.inside src1431.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1431 : Cover (Triangular src1431) 2313 2308 ends1431 := triangleCover (by decide +kernel)

def src1432 : Request := ⟨⟨⟨1000,1395,301,28173⟩,30103476895744,104105680031⟩,13,5,1,643299,1⟩

theorem rank1432 : P3_7_1.BankOK src1432.bank := by
  simpa only [src1432, _root_.Research6969.TransitionBanks.bank221] using _root_.Research6969.TransitionBanks.rank221 28173

theorem width1432 : Lower6960.HelperSource.WidthGuard src1432.bank 179730 2308 src1432.reserve := requestWidth (by decide)

def ends1432 : List ℕ := [2308, 2313]

theorem inside1432 : Research6966.TerminalBanks.inside src1432.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1432 : Cover (Triangular src1432) 2313 2308 ends1432 := triangleCover (by decide +kernel)

def src1433 : Request := ⟨⟨⟨1445,2006,445,40225⟩,92282560184320,454009341867⟩,25,5,1,643299,1⟩

theorem rank1433 : P3_7_1.BankOK src1433.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1445_2006_445 40225

theorem width1433 : Lower6960.HelperSource.WidthGuard src1433.bank 179730 2308 src1433.reserve := requestWidth (by decide)

def ends1433 : List ℕ := [2308, 2309, 2313]

theorem inside1433 : Research6966.TerminalBanks.inside src1433.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1433 : Cover (Triangular src1433) 2313 2308 ends1433 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources17

section Pack_R6970Height2313CommonSources19

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1463 : Request := ⟨⟨⟨3204,4462,982,264035⟩,1000562368970752,11020095796464⟩,110,5,1,643299,4⟩

theorem rank1463 : P3_7_1.BankOK src1463.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3204_4462_982 264035

theorem width1463 : Lower6960.HelperSource.WidthGuard src1463.bank 179730 2308 src1463.reserve := requestWidth (by decide)

def ends1463 : List ℕ := [2308, 2309, 2313]




theorem cover1463 : Cover (Triangular src1463) 2313 2308 ends1463 := triangleCover (by decide +kernel)

def src1464 : Request := ⟨⟨⟨8294,11513,2548,209325⟩,17371550689525760,490019965668423⟩,190,5,1,643299,4⟩

theorem rank1464 : P3_7_1.BankOK src1464.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8294_11513_2548 209325

theorem width1464 : Lower6960.HelperSource.WidthGuard src1464.bank 179730 2308 src1464.reserve := requestWidth (by decide)

def ends1464 : List ℕ := [2308, 2309, 2313]




theorem cover1464 : Cover (Triangular src1464) 2313 2308 ends1464 := triangleCover (by decide +kernel)

def src1465 : Request := ⟨⟨⟨401,558,123,9763⟩,1982954733568,2734096379⟩,0,5,1,643299,9⟩

theorem rank1465 : P3_7_1.BankOK src1465.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_123 9763

theorem width1465 : Lower6960.HelperSource.WidthGuard src1465.bank 179730 2308 src1465.reserve := requestWidth (by decide)

def ends1465 : List ℕ := [2308, 2309, 2313]

theorem inside1465 : Research6966.TerminalBanks.inside src1465.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1465 : Cover (Triangular src1465) 2313 2308 ends1465 := triangleCover (by decide +kernel)

def src1466 : Request := ⟨⟨⟨470,654,141,10961⟩,3134317133824,5060381153⟩,1,5,1,643299,9⟩

theorem rank1466 : P3_7_1.BankOK src1466.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_470_654_141 10961

theorem width1466 : Lower6960.HelperSource.WidthGuard src1466.bank 179730 2308 src1466.reserve := requestWidth (by decide)

def ends1466 : List ℕ := [2308, 2309, 2313]

theorem inside1466 : Research6966.TerminalBanks.inside src1466.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1466 : Cover (Triangular src1466) 2313 2308 ends1466 := triangleCover (by decide +kernel)

def src1467 : Request := ⟨⟨⟨464,647,141,13882⟩,3045648498688,4888436051⟩,3,5,1,643299,9⟩

theorem rank1467 : P3_7_1.BankOK src1467.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_464_647_141 13882

theorem width1467 : Lower6960.HelperSource.WidthGuard src1467.bank 179730 2308 src1467.reserve := requestWidth (by decide)

def ends1467 : List ℕ := [2308, 2309, 2313]

theorem inside1467 : Research6966.TerminalBanks.inside src1467.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1467 : Cover (Triangular src1467) 2313 2308 ends1467 := triangleCover (by decide +kernel)

def src1468 : Request := ⟨⟨⟨690,962,212,17590⟩,10065769922560,23997864317⟩,8,5,1,643299,9⟩

theorem rank1468 : P3_7_1.BankOK src1468.bank := by
  simpa only [src1468, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 17590

theorem width1468 : Lower6960.HelperSource.WidthGuard src1468.bank 179730 2308 src1468.reserve := requestWidth (by decide)

def ends1468 : List ℕ := [2308, 2309, 2313]

theorem inside1468 : Research6966.TerminalBanks.inside src1468.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1468 : Cover (Triangular src1468) 2313 2308 ends1468 := triangleCover (by decide +kernel)

def src1469 : Request := ⟨⟨⟨1205,1673,370,35950⟩,53430671114240,219308840266⟩,25,5,1,643299,9⟩

theorem rank1469 : P3_7_1.BankOK src1469.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1673_370 35950

theorem width1469 : Lower6960.HelperSource.WidthGuard src1469.bank 179730 2308 src1469.reserve := requestWidth (by decide)

def ends1469 : List ℕ := [2308, 2309, 2313]

theorem inside1469 : Research6966.TerminalBanks.inside src1469.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1469 : Cover (Triangular src1469) 2313 2308 ends1469 := triangleCover (by decide +kernel)

def src147 : Request := ⟨⟨⟨471,655,148,5419⟩,3266464186368,5279398867⟩,2,2,1,296085,41⟩

theorem rank147 : P3_7_1.BankOK src147.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_148 5419

theorem width147 : Lower6960.HelperSource.WidthGuard src147.bank 179730 2308 src147.reserve := requestWidth (by decide)

def ends147 : List ℕ := [2308, 2309, 2313]

theorem inside147 : Research6966.TerminalBanks.inside src147.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover147 : Cover (Triangular src147) 2313 2308 ends147 := triangleCover (by decide +kernel)

def src1470 : Request := ⟨⟨⟨2087,2897,645,45247⟩,278496867254272,1977925731872⟩,40,5,1,643299,9⟩

theorem rank1470 : P3_7_1.BankOK src1470.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2087_2897_645 45247

theorem width1470 : Lower6960.HelperSource.WidthGuard src1470.bank 179730 2308 src1470.reserve := requestWidth (by decide)

def ends1470 : List ℕ := [2308, 2309, 2313]

theorem inside1470 : Research6966.TerminalBanks.inside src1470.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1470 : Cover (Triangular src1470) 2313 2308 ends1470 := triangleCover (by decide +kernel)

def src1471 : Request := ⟨⟨⟨2609,3620,809,72579⟩,545216719749120,4833555006109⟩,64,5,1,643299,9⟩

theorem rank1471 : P3_7_1.BankOK src1471.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2609_3620_809 72579

theorem width1471 : Lower6960.HelperSource.WidthGuard src1471.bank 179730 2308 src1471.reserve := requestWidth (by decide)

def ends1471 : List ℕ := [2308, 2309, 2313]

theorem inside1471 : Research6966.TerminalBanks.inside src1471.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1471 : Cover (Triangular src1471) 2313 2308 ends1471 := triangleCover (by decide +kernel)

def src1472 : Request := ⟨⟨⟨2300,3207,702,344221⟩,369170633195520,2930605494152⟩,83,5,1,643299,9⟩

theorem rank1472 : P3_7_1.BankOK src1472.bank := by
  simpa only [src1472, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 344221

theorem width1472 : Lower6960.HelperSource.WidthGuard src1472.bank 179730 2308 src1472.reserve := requestWidth (by decide)

def ends1472 : List ℕ := [2308, 2309, 2313]

theorem inside1472 : Research6966.TerminalBanks.inside src1472.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1472 : Cover (Triangular src1472) 2313 2308 ends1472 := triangleCover (by decide +kernel)

def src1473 : Request := ⟨⟨⟨2600,3625,798,164837⟩,535425056505856,4803689494279⟩,85,5,1,643299,9⟩

theorem rank1473 : P3_7_1.BankOK src1473.bank := by
  simpa only [src1473, _root_.Research6969.TransitionBanks.bank262] using _root_.Research6969.TransitionBanks.rank262 164837

theorem width1473 : Lower6960.HelperSource.WidthGuard src1473.bank 179730 2308 src1473.reserve := requestWidth (by decide)

def ends1473 : List ℕ := [2308, 2313]

theorem inside1473 : Research6966.TerminalBanks.inside src1473.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1473 : Cover (Triangular src1473) 2313 2308 ends1473 := triangleCover (by decide +kernel)

def src1474 : Request := ⟨⟨⟨4851,6730,1506,856577⟩,3504887012261888,57739795581494⟩,190,5,1,643299,9⟩

theorem rank1474 : P3_7_1.BankOK src1474.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4851_6730_1506 856577

theorem width1474 : Lower6960.HelperSource.WidthGuard src1474.bank 179730 2308 src1474.reserve := requestWidth (by decide)

def ends1474 : List ℕ := [2308, 2309, 2313]




theorem cover1474 : Cover (Triangular src1474) 2313 2308 ends1474 := triangleCover (by decide +kernel)

def src1475 : Request := ⟨⟨⟨10000,13884,3070,234691⟩,30428373265940480,1035530902486423⟩,245,5,1,643299,9⟩

theorem rank1475 : P3_7_1.BankOK src1475.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13884_3070 234691

theorem width1475 : Lower6960.HelperSource.WidthGuard src1475.bank 179730 2308 src1475.reserve := requestWidth (by decide)

def ends1475 : List ℕ := [2308, 2309, 2313]




theorem cover1475 : Cover (Triangular src1475) 2313 2308 ends1475 := triangleCover (by decide +kernel)

def src1476 : Request := ⟨⟨⟨2604,3616,797,63162⟩,536759858102272,4760749454740⟩,63,5,1,643299,13⟩

theorem rank1476 : P3_7_1.BankOK src1476.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3616_797 63162

theorem width1476 : Lower6960.HelperSource.WidthGuard src1476.bank 179730 2308 src1476.reserve := requestWidth (by decide)

def ends1476 : List ℕ := [2308, 2309, 2313]

theorem inside1476 : Research6966.TerminalBanks.inside src1476.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1476 : Cover (Triangular src1476) 2313 2308 ends1476 := triangleCover (by decide +kernel)

def src1477 : Request := ⟨⟨⟨2300,3207,702,300236⟩,369170633195520,2930605494152⟩,83,5,1,643299,13⟩

theorem rank1477 : P3_7_1.BankOK src1477.bank := by
  simpa only [src1477, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 300236

theorem width1477 : Lower6960.HelperSource.WidthGuard src1477.bank 179730 2308 src1477.reserve := requestWidth (by decide)

def ends1477 : List ℕ := [2308, 2309, 2313]

theorem inside1477 : Research6966.TerminalBanks.inside src1477.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1477 : Cover (Triangular src1477) 2313 2308 ends1477 := triangleCover (by decide +kernel)

def src1478 : Request := ⟨⟨⟨401,558,123,7715⟩,1982954733568,2734096379⟩,0,5,1,643299,16⟩

theorem rank1478 : P3_7_1.BankOK src1478.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_123 7715

theorem width1478 : Lower6960.HelperSource.WidthGuard src1478.bank 179730 2308 src1478.reserve := requestWidth (by decide)

def ends1478 : List ℕ := [2308, 2309, 2313]

theorem inside1478 : Research6966.TerminalBanks.inside src1478.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1478 : Cover (Triangular src1478) 2313 2308 ends1478 := triangleCover (by decide +kernel)

def src1479 : Request := ⟨⟨⟨470,653,141,8668⟩,3134317133824,5035569706⟩,1,5,1,643299,16⟩

theorem rank1479 : P3_7_1.BankOK src1479.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_470_653_141 8668

theorem width1479 : Lower6960.HelperSource.WidthGuard src1479.bank 179730 2308 src1479.reserve := requestWidth (by decide)

def ends1479 : List ℕ := [2308, 2309, 2313]

theorem inside1479 : Research6966.TerminalBanks.inside src1479.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1479 : Cover (Triangular src1479) 2313 2308 ends1479 := triangleCover (by decide +kernel)

def src148 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,3,2,1,296085,41⟩

theorem rank148 : P3_7_1.BankOK src148.bank := by
  simpa only [src148, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 5419

theorem width148 : Lower6960.HelperSource.WidthGuard src148.bank 179730 2308 src148.reserve := requestWidth (by decide)

def ends148 : List ℕ := [2308, 2313]

theorem inside148 : Research6966.TerminalBanks.inside src148.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover148 : Cover (Triangular src148) 2313 2308 ends148 := triangleCover (by decide +kernel)

def src1480 : Request := ⟨⟨⟨470,653,141,9761⟩,3134317133824,5035569706⟩,2,5,1,643299,16⟩

theorem rank1480 : P3_7_1.BankOK src1480.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_470_653_141 9761

theorem width1480 : Lower6960.HelperSource.WidthGuard src1480.bank 179730 2308 src1480.reserve := requestWidth (by decide)

def ends1480 : List ℕ := [2308, 2309, 2313]

theorem inside1480 : Research6966.TerminalBanks.inside src1480.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1480 : Cover (Triangular src1480) 2313 2308 ends1480 := triangleCover (by decide +kernel)

def src1481 : Request := ⟨⟨⟨560,777,169,10944⟩,5316921262080,10130698125⟩,4,5,1,643299,16⟩

theorem rank1481 : P3_7_1.BankOK src1481.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_560_777_169 10944

theorem width1481 : Lower6960.HelperSource.WidthGuard src1481.bank 179730 2308 src1481.reserve := requestWidth (by decide)

def ends1481 : List ℕ := [2308, 2309, 2313]

theorem inside1481 : Research6966.TerminalBanks.inside src1481.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1481 : Cover (Triangular src1481) 2313 2308 ends1481 := triangleCover (by decide +kernel)

def src1482 : Request := ⟨⟨⟨690,962,212,13899⟩,10065769922560,23997864317⟩,8,5,1,643299,16⟩

theorem rank1482 : P3_7_1.BankOK src1482.bank := by
  simpa only [src1482, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 13899

theorem width1482 : Lower6960.HelperSource.WidthGuard src1482.bank 179730 2308 src1482.reserve := requestWidth (by decide)

def ends1482 : List ℕ := [2308, 2309, 2313]

theorem inside1482 : Research6966.TerminalBanks.inside src1482.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1482 : Cover (Triangular src1482) 2313 2308 ends1482 := triangleCover (by decide +kernel)

def src1483 : Request := ⟨⟨⟨1002,1395,307,19788⟩,30694534807552,105715278267⟩,16,5,1,643299,16⟩

theorem rank1483 : P3_7_1.BankOK src1483.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_307 19788

theorem width1483 : Lower6960.HelperSource.WidthGuard src1483.bank 179730 2308 src1483.reserve := requestWidth (by decide)

def ends1483 : List ℕ := [2309, 2313]

theorem inside1483 : Research6966.TerminalBanks.inside src1483.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1483 : Cover (Triangular src1483) 2313 2308 ends1483 := triangleCover (by decide +kernel)

def src1484 : Request := ⟨⟨⟨1751,2441,537,40111⟩,163591070679040,988269431527⟩,40,5,1,643299,16⟩

theorem rank1484 : P3_7_1.BankOK src1484.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2441_537 40111

theorem width1484 : Lower6960.HelperSource.WidthGuard src1484.bank 179730 2308 src1484.reserve := requestWidth (by decide)

def ends1484 : List ℕ := [2308, 2309, 2313]

theorem inside1484 : Research6966.TerminalBanks.inside src1484.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1484 : Cover (Triangular src1484) 2313 2308 ends1484 := triangleCover (by decide +kernel)

def src1485 : Request := ⟨⟨⟨2600,3625,798,130242⟩,535425056505856,4803689494279⟩,85,5,1,643299,16⟩

theorem rank1485 : P3_7_1.BankOK src1485.bank := by
  simpa only [src1485, _root_.Research6969.TransitionBanks.bank262] using _root_.Research6969.TransitionBanks.rank262 130242

theorem width1485 : Lower6960.HelperSource.WidthGuard src1485.bank 179730 2308 src1485.reserve := requestWidth (by decide)

def ends1485 : List ℕ := [2308, 2313]

theorem inside1485 : Research6966.TerminalBanks.inside src1485.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1485 : Cover (Triangular src1485) 2313 2308 ends1485 := triangleCover (by decide +kernel)

def src1486 : Request := ⟨⟨⟨5682,7886,1750,116106⟩,5597575584940032,108128998877830⟩,145,5,1,643299,16⟩

theorem rank1486 : P3_7_1.BankOK src1486.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5682_7886_1750 116106

theorem width1486 : Lower6960.HelperSource.WidthGuard src1486.bank 179730 2308 src1486.reserve := requestWidth (by decide)

def ends1486 : List ℕ := [2308, 2309, 2313]




theorem cover1486 : Cover (Triangular src1486) 2313 2308 ends1486 := triangleCover (by decide +kernel)

def src1487 : Request := ⟨⟨⟨4846,6724,1506,668746⟩,3496796367618048,57574114957143⟩,190,5,1,643299,16⟩

theorem rank1487 : P3_7_1.BankOK src1487.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4846_6724_1506 668746

theorem width1487 : Lower6960.HelperSource.WidthGuard src1487.bank 179730 2308 src1487.reserve := requestWidth (by decide)

def ends1487 : List ℕ := [2308, 2309, 2313]




theorem cover1487 : Cover (Triangular src1487) 2313 2308 ends1487 := triangleCover (by decide +kernel)

def src1488 : Request := ⟨⟨⟨10000,13884,3070,185459⟩,30428373265940480,1035530902486423⟩,245,5,1,643299,16⟩

theorem rank1488 : P3_7_1.BankOK src1488.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13884_3070 185459

theorem width1488 : Lower6960.HelperSource.WidthGuard src1488.bank 179730 2308 src1488.reserve := requestWidth (by decide)

def ends1488 : List ℕ := [2308, 2309, 2313]




theorem cover1488 : Cover (Triangular src1488) 2313 2308 ends1488 := triangleCover (by decide +kernel)

def src1489 : Request := ⟨⟨⟨2567,3562,793,54393⟩,517850014416896,4517874243524⟩,63,5,1,643299,17⟩

theorem rank1489 : P3_7_1.BankOK src1489.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3562_793 54393

theorem width1489 : Lower6960.HelperSource.WidthGuard src1489.bank 179730 2308 src1489.reserve := requestWidth (by decide)

def ends1489 : List ℕ := [2308, 2309, 2313]

theorem inside1489 : Research6966.TerminalBanks.inside src1489.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1489 : Cover (Triangular src1489) 2313 2308 ends1489 := triangleCover (by decide +kernel)

def src149 : Request := ⟨⟨⟨562,781,172,6096⟩,5431270572032,10440670587⟩,4,2,1,296085,41⟩

theorem rank149 : P3_7_1.BankOK src149.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 6096

theorem width149 : Lower6960.HelperSource.WidthGuard src149.bank 179730 2308 src149.reserve := requestWidth (by decide)

def ends149 : List ℕ := [2308, 2309, 2313]

theorem inside149 : Research6966.TerminalBanks.inside src149.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover149 : Cover (Triangular src149) 2313 2308 ends149 := triangleCover (by decide +kernel)

def src1490 : Request := ⟨⟨⟨2306,3207,702,253069⟩,371329558118400,2930605494152⟩,83,5,1,643299,17⟩

theorem rank1490 : P3_7_1.BankOK src1490.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2306_3207_702 253069

theorem width1490 : Lower6960.HelperSource.WidthGuard src1490.bank 179730 2308 src1490.reserve := requestWidth (by decide)

def ends1490 : List ℕ := [2308, 2309, 2313]

theorem inside1490 : Research6966.TerminalBanks.inside src1490.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1490 : Cover (Triangular src1490) 2313 2308 ends1490 := triangleCover (by decide +kernel)

def src1491 : Request := ⟨⟨⟨2767,3841,854,44411⟩,648028618752000,6101300343282⟩,63,5,1,643299,21⟩

theorem rank1491 : P3_7_1.BankOK src1491.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2767_3841_854 44411

theorem width1491 : Lower6960.HelperSource.WidthGuard src1491.bank 179730 2308 src1491.reserve := requestWidth (by decide)

def ends1491 : List ℕ := [2308, 2309, 2313]

theorem inside1491 : Research6966.TerminalBanks.inside src1491.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1491 : Cover (Triangular src1491) 2313 2308 ends1491 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources19

section Pack_R6970Height2313CommonSources20

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1492 : Request := ⟨⟨⟨2300,3207,702,213509⟩,369170633195520,2930605494152⟩,83,5,1,643299,21⟩

theorem rank1492 : P3_7_1.BankOK src1492.bank := by
  simpa only [src1492, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 213509

theorem width1492 : Lower6960.HelperSource.WidthGuard src1492.bank 179730 2308 src1492.reserve := requestWidth (by decide)

def ends1492 : List ℕ := [2308, 2309, 2313]

theorem inside1492 : Research6966.TerminalBanks.inside src1492.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1492 : Cover (Triangular src1492) 2313 2308 ends1492 := triangleCover (by decide +kernel)

def src1493 : Request := ⟨⟨⟨2567,3562,793,39130⟩,517850014416896,4517874243524⟩,63,5,1,643299,25⟩

theorem rank1493 : P3_7_1.BankOK src1493.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3562_793 39130

theorem width1493 : Lower6960.HelperSource.WidthGuard src1493.bank 179730 2308 src1493.reserve := requestWidth (by decide)

def ends1493 : List ℕ := [2308, 2309, 2313]

theorem inside1493 : Research6966.TerminalBanks.inside src1493.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1493 : Cover (Triangular src1493) 2313 2308 ends1493 := triangleCover (by decide +kernel)

def src1494 : Request := ⟨⟨⟨2269,3159,685,475797⟩,351516132638720,2738961313091⟩,85,5,1,643789,25⟩

theorem rank1494 : P3_7_1.BankOK src1494.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2269_3159_685 475797

theorem width1494 : Lower6960.HelperSource.WidthGuard src1494.bank 179730 2308 src1494.reserve := requestWidth (by decide)

def ends1494 : List ℕ := [2308, 2309, 2313]

theorem inside1494 : Research6966.TerminalBanks.inside src1494.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1494 : Cover (Triangular src1494) 2313 2308 ends1494 := triangleCover (by decide +kernel)

def src1495 : Request := ⟨⟨⟨326,453,100,6096⟩,1068355026944,1193036697⟩,0,5,1,643299,26⟩

theorem rank1495 : P3_7_1.BankOK src1495.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 6096

theorem width1495 : Lower6960.HelperSource.WidthGuard src1495.bank 179730 2308 src1495.reserve := requestWidth (by decide)

def ends1495 : List ℕ := [2308, 2313]

theorem inside1495 : Research6966.TerminalBanks.inside src1495.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1495 : Cover (Triangular src1495) 2313 2308 ends1495 := triangleCover (by decide +kernel)

def src1496 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,1,5,1,643299,26⟩

theorem rank1496 : P3_7_1.BankOK src1496.bank := by
  simpa only [src1496, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 6096

theorem width1496 : Lower6960.HelperSource.WidthGuard src1496.bank 179730 2308 src1496.reserve := requestWidth (by decide)

def ends1496 : List ℕ := [2308, 2313]

theorem inside1496 : Research6966.TerminalBanks.inside src1496.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1496 : Cover (Triangular src1496) 2313 2308 ends1496 := triangleCover (by decide +kernel)

def src1497 : Request := ⟨⟨⟨470,655,141,7715⟩,3134317133824,5085275599⟩,3,5,1,643299,26⟩

theorem rank1497 : P3_7_1.BankOK src1497.bank := by
  simpa only [src1497, _root_.Research6969.TransitionBanks.bank141] using _root_.Research6969.TransitionBanks.rank141 7715

theorem width1497 : Lower6960.HelperSource.WidthGuard src1497.bank 179730 2308 src1497.reserve := requestWidth (by decide)

def ends1497 : List ℕ := [2313]

theorem inside1497 : Research6966.TerminalBanks.inside src1497.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1497 : Cover (Triangular src1497) 2313 2308 ends1497 := triangleCover (by decide +kernel)

def src1498 : Request := ⟨⟨⟨562,780,172,8662⟩,5431270572032,10397750152⟩,6,5,1,643299,26⟩

theorem rank1498 : P3_7_1.BankOK src1498.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_780_172 8662

theorem width1498 : Lower6960.HelperSource.WidthGuard src1498.bank 179730 2308 src1498.reserve := requestWidth (by decide)

def ends1498 : List ℕ := [2308, 2309, 2313]

theorem inside1498 : Research6966.TerminalBanks.inside src1498.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1498 : Cover (Triangular src1498) 2313 2308 ends1498 := triangleCover (by decide +kernel)

def src1499 : Request := ⟨⟨⟨826,1151,253,12355⟩,17208151113728,49010625289⟩,13,5,1,643299,26⟩

theorem rank1499 : P3_7_1.BankOK src1499.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_253 12355

theorem width1499 : Lower6960.HelperSource.WidthGuard src1499.bank 179730 2308 src1499.reserve := requestWidth (by decide)

def ends1499 : List ℕ := [2309, 2313]

theorem inside1499 : Research6966.TerminalBanks.inside src1499.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1499 : Cover (Triangular src1499) 2313 2308 ends1499 := triangleCover (by decide +kernel)

def src15 : Request := ⟨⟨⟨2005,2784,610,53957⟩,244038991872000,1666247886835⟩,195,1,1,128659,513⟩

theorem rank15 : P3_7_1.BankOK src15.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2005_2784_610 53957

theorem width15 : Lower6960.HelperSource.WidthGuard src15.bank 179730 2308 src15.reserve := requestWidth (by decide)

def ends15 : List ℕ := [2308, 2309, 2313]

theorem inside15 : Research6966.TerminalBanks.inside src15.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover15 : Cover (Triangular src15) 2313 2308 ends15 := triangleCover (by decide +kernel)

def src150 : Request := ⟨⟨⟨692,962,214,8679⟩,10203306393600,24173060093⟩,8,2,1,296085,41⟩

theorem rank150 : P3_7_1.BankOK src150.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_214 8679

theorem width150 : Lower6960.HelperSource.WidthGuard src150.bank 179730 2308 src150.reserve := requestWidth (by decide)

def ends150 : List ℕ := [2308, 2309, 2313]

theorem inside150 : Research6966.TerminalBanks.inside src150.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover150 : Cover (Triangular src150) 2313 2308 ends150 := triangleCover (by decide +kernel)

def src1500 : Request := ⟨⟨⟨1445,2006,445,22185⟩,92282560184320,454009341867⟩,32,5,1,643299,26⟩

theorem rank1500 : P3_7_1.BankOK src1500.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1445_2006_445 22185

theorem width1500 : Lower6960.HelperSource.WidthGuard src1500.bank 179730 2308 src1500.reserve := requestWidth (by decide)

def ends1500 : List ℕ := [2308, 2309, 2313]

theorem inside1500 : Research6966.TerminalBanks.inside src1500.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1500 : Cover (Triangular src1500) 2313 2308 ends1500 := triangleCover (by decide +kernel)

def src1501 : Request := ⟨⟨⟨3192,4431,982,50725⟩,992190100406272,10775449532456⟩,85,5,1,643299,26⟩

theorem rank1501 : P3_7_1.BankOK src1501.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3192_4431_982 50725

theorem width1501 : Lower6960.HelperSource.WidthGuard src1501.bank 179730 2308 src1501.reserve := requestWidth (by decide)

def ends1501 : List ℕ := [2308, 2309, 2313]




theorem cover1501 : Cover (Triangular src1501) 2313 2308 ends1501 := triangleCover (by decide +kernel)

def src1502 : Request := ⟨⟨⟨3215,4462,990,104207⟩,1014500834672640,11089873652459⟩,110,5,1,643299,26⟩

theorem rank1502 : P3_7_1.BankOK src1502.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3215_4462_990 104207

theorem width1502 : Lower6960.HelperSource.WidthGuard src1502.bank 179730 2308 src1502.reserve := requestWidth (by decide)

def ends1502 : List ℕ := [2308, 2309, 2313]




theorem cover1502 : Cover (Triangular src1502) 2313 2308 ends1502 := triangleCover (by decide +kernel)

def src1503 : Request := ⟨⟨⟨3993,5539,1244,163165⟩,1960313472942080,26575548181548⟩,145,5,1,643299,26⟩

theorem rank1503 : P3_7_1.BankOK src1503.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3993_5539_1244 163165

theorem width1503 : Lower6960.HelperSource.WidthGuard src1503.bank 179730 2308 src1503.reserve := requestWidth (by decide)

def ends1503 : List ℕ := [2308, 2309, 2313]




theorem cover1503 : Cover (Triangular src1503) 2313 2308 ends1503 := triangleCover (by decide +kernel)

def src1504 : Request := ⟨⟨⟨4822,6692,1490,428634⟩,3430214978240512,56227346640330⟩,190,5,1,643299,26⟩

theorem rank1504 : P3_7_1.BankOK src1504.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4822_6692_1490 428634

theorem width1504 : Lower6960.HelperSource.WidthGuard src1504.bank 179730 2308 src1504.reserve := requestWidth (by decide)

def ends1504 : List ℕ := [2308, 2309, 2313]




theorem cover1504 : Cover (Triangular src1504) 2313 2308 ends1504 := triangleCover (by decide +kernel)

def src1505 : Request := ⟨⟨⟨6931,9623,2174,102908⟩,10299791048704000,243058712908678⟩,190,5,1,643299,26⟩

theorem rank1505 : P3_7_1.BankOK src1505.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6931_9623_2174 102908

theorem width1505 : Lower6960.HelperSource.WidthGuard src1505.bank 179730 2308 src1505.reserve := requestWidth (by decide)

def ends1505 : List ℕ := [2309, 2313]



theorem cover1505 : Cover (Triangular src1505) 2313 2308 ends1505 := triangleCover (by decide +kernel)

def src1506 : Request := ⟨⟨⟨2296,3199,701,332779⟩,367337109454848,2903914168659⟩,87,5,1,643299,29⟩

theorem rank1506 : P3_7_1.BankOK src1506.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2296_3199_701 332779

theorem width1506 : Lower6960.HelperSource.WidthGuard src1506.bank 179730 2308 src1506.reserve := requestWidth (by decide)

def ends1506 : List ℕ := [2308, 2309, 2313]

theorem inside1506 : Research6966.TerminalBanks.inside src1506.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1506 : Cover (Triangular src1506) 2313 2308 ends1506 := triangleCover (by decide +kernel)

def src1507 : Request := ⟨⟨⟨2816,3909,878,50702⟩,688328825110528,6596616429360⟩,85,5,1,643299,29⟩

theorem rank1507 : P3_7_1.BankOK src1507.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3909_878 50702

theorem width1507 : Lower6960.HelperSource.WidthGuard src1507.bank 179730 2308 src1507.reserve := requestWidth (by decide)

def ends1507 : List ℕ := [2308, 2309, 2313]

theorem inside1507 : Research6966.TerminalBanks.inside src1507.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1507 : Cover (Triangular src1507) 2313 2308 ends1507 := triangleCover (by decide +kernel)

def src1508 : Request := ⟨⟨⟨2767,3841,854,42827⟩,648028618752000,6101300343282⟩,85,5,1,643299,33⟩

theorem rank1508 : P3_7_1.BankOK src1508.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2767_3841_854 42827

theorem width1508 : Lower6960.HelperSource.WidthGuard src1508.bank 179730 2308 src1508.reserve := requestWidth (by decide)

def ends1508 : List ℕ := [2308, 2309, 2313]

theorem inside1508 : Research6966.TerminalBanks.inside src1508.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1508 : Cover (Triangular src1508) 2313 2308 ends1508 := triangleCover (by decide +kernel)

def src1509 : Request := ⟨⟨⟨2954,4119,894,312168⟩,776742872023040,7917725648063⟩,114,5,1,643299,33⟩

theorem rank1509 : P3_7_1.BankOK src1509.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2954_4119_894 312168

theorem width1509 : Lower6960.HelperSource.WidthGuard src1509.bank 179730 2308 src1509.reserve := requestWidth (by decide)

def ends1509 : List ℕ := [2308, 2309, 2313]

theorem inside1509 : Research6966.TerminalBanks.inside src1509.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1509 : Cover (Triangular src1509) 2313 2308 ends1509 := triangleCover (by decide +kernel)

def src151 : Request := ⟨⟨⟨1000,1391,307,12323⟩,30557599170560,104743003887⟩,16,2,1,296085,41⟩

theorem rank151 : P3_7_1.BankOK src151.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_307 12323

theorem width151 : Lower6960.HelperSource.WidthGuard src151.bank 179730 2308 src151.reserve := requestWidth (by decide)

def ends151 : List ℕ := [2308, 2309, 2313]

theorem inside151 : Research6966.TerminalBanks.inside src151.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover151 : Cover (Triangular src151) 2313 2308 ends151 := triangleCover (by decide +kernel)

def src1510 : Request := ⟨⟨⟨275,383,84,3807⟩,640970915840,608607683⟩,0,5,1,643299,41⟩

theorem rank1510 : P3_7_1.BankOK src1510.bank := by
  simpa only [src1510, _root_.Research6969.TransitionBanks.bank79] using _root_.Research6969.TransitionBanks.rank79 3807

theorem width1510 : Lower6960.HelperSource.WidthGuard src1510.bank 179730 2308 src1510.reserve := requestWidth (by decide)

def ends1510 : List ℕ := [2308, 2313]

theorem inside1510 : Research6966.TerminalBanks.inside src1510.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1510 : Cover (Triangular src1510) 2313 2308 ends1510 := triangleCover (by decide +kernel)

def src1511 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,1,5,1,643299,41⟩

theorem rank1511 : P3_7_1.BankOK src1511.bank := by
  simpa only [src1511, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 3807

theorem width1511 : Lower6960.HelperSource.WidthGuard src1511.bank 179730 2308 src1511.reserve := requestWidth (by decide)

def ends1511 : List ℕ := [2313]

theorem inside1511 : Research6966.TerminalBanks.inside src1511.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1511 : Cover (Triangular src1511) 2313 2308 ends1511 := triangleCover (by decide +kernel)

def src1512 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,3,5,1,643299,41⟩

theorem rank1512 : P3_7_1.BankOK src1512.bank := by
  simpa only [src1512, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 4282

theorem width1512 : Lower6960.HelperSource.WidthGuard src1512.bank 179730 2308 src1512.reserve := requestWidth (by decide)

def ends1512 : List ℕ := [2308, 2309, 2313]

theorem inside1512 : Research6966.TerminalBanks.inside src1512.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1512 : Cover (Triangular src1512) 2313 2308 ends1512 := triangleCover (by decide +kernel)

def src1513 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,6,5,1,643299,41⟩

theorem rank1513 : P3_7_1.BankOK src1513.bank := by
  simpa only [src1513, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 5419

theorem width1513 : Lower6960.HelperSource.WidthGuard src1513.bank 179730 2308 src1513.reserve := requestWidth (by decide)

def ends1513 : List ℕ := [2308, 2313]

theorem inside1513 : Research6966.TerminalBanks.inside src1513.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1513 : Cover (Triangular src1513) 2313 2308 ends1513 := triangleCover (by decide +kernel)

def src1514 : Request := ⟨⟨⟨562,781,172,6858⟩,5431270572032,10440670587⟩,10,5,1,643299,41⟩

theorem rank1514 : P3_7_1.BankOK src1514.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 6858

theorem width1514 : Lower6960.HelperSource.WidthGuard src1514.bank 179730 2308 src1514.reserve := requestWidth (by decide)

def ends1514 : List ℕ := [2308, 2309, 2313]

theorem inside1514 : Research6966.TerminalBanks.inside src1514.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1514 : Cover (Triangular src1514) 2313 2308 ends1514 := triangleCover (by decide +kernel)

def src1515 : Request := ⟨⟨⟨1204,1673,368,13899⟩,53112809717760,218387554859⟩,32,5,1,643299,41⟩

theorem rank1515 : P3_7_1.BankOK src1515.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1204_1673_368 13899

theorem width1515 : Lower6960.HelperSource.WidthGuard src1515.bank 179730 2308 src1515.reserve := requestWidth (by decide)

def ends1515 : List ℕ := [2308, 2309, 2313]

theorem inside1515 : Research6966.TerminalBanks.inside src1515.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1515 : Cover (Triangular src1515) 2313 2308 ends1515 := triangleCover (by decide +kernel)

def src1516 : Request := ⟨⟨⟨2105,2928,645,25043⟩,283904392560640,2046887686018⟩,65,5,1,643299,41⟩

theorem rank1516 : P3_7_1.BankOK src1516.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2928_645 25043

theorem width1516 : Lower6960.HelperSource.WidthGuard src1516.bank 179730 2308 src1516.reserve := requestWidth (by decide)

def ends1516 : List ℕ := [2308, 2309, 2313]

theorem inside1516 : Research6966.TerminalBanks.inside src1516.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1516 : Cover (Triangular src1516) 2313 2308 ends1516 := triangleCover (by decide +kernel)

def src1517 : Request := ⟨⟨⟨2614,3625,819,30949⟩,552677752176640,4901614794409⟩,85,5,1,643299,41⟩

theorem rank1517 : P3_7_1.BankOK src1517.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3625_819 30949

theorem width1517 : Lower6960.HelperSource.WidthGuard src1517.bank 179730 2308 src1517.reserve := requestWidth (by decide)

def ends1517 : List ℕ := [2308, 2309, 2313]

theorem inside1517 : Research6966.TerminalBanks.inside src1517.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1517 : Cover (Triangular src1517) 2313 2308 ends1517 := triangleCover (by decide +kernel)

def src1518 : Request := ⟨⟨⟨2954,4118,894,108234⟩,776742872023040,7911540743403⟩,115,5,1,643299,41⟩

theorem rank1518 : P3_7_1.BankOK src1518.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2954_4118_894 108234

theorem width1518 : Lower6960.HelperSource.WidthGuard src1518.bank 179730 2308 src1518.reserve := requestWidth (by decide)

def ends1518 : List ℕ := [2308, 2309, 2313]

theorem inside1518 : Research6966.TerminalBanks.inside src1518.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1518 : Cover (Triangular src1518) 2313 2308 ends1518 := triangleCover (by decide +kernel)

def src1519 : Request := ⟨⟨⟨3971,5507,1244,57109⟩,1936184665702400,26084011577468⟩,145,5,1,643299,41⟩

theorem rank1519 : P3_7_1.BankOK src1519.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3971_5507_1244 57109

theorem width1519 : Lower6960.HelperSource.WidthGuard src1519.bank 179730 2308 src1519.reserve := requestWidth (by decide)

def ends1519 : List ℕ := [2309, 2313]



theorem cover1519 : Cover (Triangular src1519) 2313 2308 ends1519 := triangleCover (by decide +kernel)

def src152 : Request := ⟨⟨⟨1434,1990,445,13768⟩,90716759654400,442453109011⟩,25,2,1,296085,41⟩

theorem rank152 : P3_7_1.BankOK src152.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1434_1990_445 13768

theorem width152 : Lower6960.HelperSource.WidthGuard src152.bank 179730 2308 src152.reserve := requestWidth (by decide)

def ends152 : List ℕ := [2308, 2309, 2313]

theorem inside152 : Research6966.TerminalBanks.inside src152.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover152 : Cover (Triangular src152) 2313 2308 ends152 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources20

section Pack_R6970Height2313CommonSources22

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src155 : Request := ⟨⟨⟨10050,13948,3150,102908⟩,31376662344499200,1072221490229155⟩,245,2,1,296085,41⟩

theorem rank155 : P3_7_1.BankOK src155.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10050_13948_3150 102908

theorem width155 : Lower6960.HelperSource.WidthGuard src155.bank 179730 2308 src155.reserve := requestWidth (by decide)

def ends155 : List ℕ := [2308, 2313]



theorem cover155 : Cover (Triangular src155) 2313 2308 ends155 := triangleCover (by decide +kernel)

def src1550 : Request := ⟨⟨⟨545,756,170,5415⟩,5026035793920,9318832198⟩,10,5,2,643298,31⟩

theorem rank1550 : P3_7_1.BankOK src1550.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5415

theorem width1550 : Lower6960.HelperSource.WidthGuard src1550.bank 179730 2308 src1550.reserve := requestWidth (by decide)

def ends1550 : List ℕ := [2308, 2309, 2313]

theorem inside1550 : Research6966.TerminalBanks.inside src1550.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1550 : Cover (Triangular src1550) 2313 2308 ends1550 := triangleCover (by decide +kernel)

def src1551 : Request := ⟨⟨⟨545,756,170,5169⟩,5026035793920,9318832198⟩,10,5,2,643298,35⟩

theorem rank1551 : P3_7_1.BankOK src1551.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5169

theorem width1551 : Lower6960.HelperSource.WidthGuard src1551.bank 179730 2308 src1551.reserve := requestWidth (by decide)

def ends1551 : List ℕ := [2308, 2309, 2313]

theorem inside1551 : Research6966.TerminalBanks.inside src1551.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1551 : Cover (Triangular src1551) 2313 2308 ends1551 := triangleCover (by decide +kernel)

def src1552 : Request := ⟨⟨⟨545,756,170,4942⟩,5026035793920,9318832198⟩,10,5,2,643298,39⟩

theorem rank1552 : P3_7_1.BankOK src1552.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 4942

theorem width1552 : Lower6960.HelperSource.WidthGuard src1552.bank 179730 2308 src1552.reserve := requestWidth (by decide)

def ends1552 : List ℕ := [2308, 2309, 2313]

theorem inside1552 : Research6966.TerminalBanks.inside src1552.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1552 : Cover (Triangular src1552) 2313 2308 ends1552 := triangleCover (by decide +kernel)

def src1553 : Request := ⟨⟨⟨551,764,170,4810⟩,5150698635264,9639740602⟩,10,5,2,643298,42⟩

theorem rank1553 : P3_7_1.BankOK src1553.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_551_764_170 4810

theorem width1553 : Lower6960.HelperSource.WidthGuard src1553.bank 179730 2308 src1553.reserve := requestWidth (by decide)

def ends1553 : List ℕ := [2308, 2309, 2313]

theorem inside1553 : Research6966.TerminalBanks.inside src1553.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1553 : Cover (Triangular src1553) 2313 2308 ends1553 := triangleCover (by decide +kernel)

def src1554 : Request := ⟨⟨⟨550,763,170,4618⟩,5129809428480,9599221867⟩,10,5,2,643298,46⟩

theorem rank1554 : P3_7_1.BankOK src1554.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 4618

theorem width1554 : Lower6960.HelperSource.WidthGuard src1554.bank 179730 2308 src1554.reserve := requestWidth (by decide)

def ends1554 : List ℕ := [2308, 2309, 2313]

theorem inside1554 : Research6966.TerminalBanks.inside src1554.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1554 : Cover (Triangular src1554) 2313 2308 ends1554 := triangleCover (by decide +kernel)

def src1555 : Request := ⟨⟨⟨550,764,170,4460⟩,5129809428480,9639740602⟩,10,5,2,643298,50⟩

theorem rank1555 : P3_7_1.BankOK src1555.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4460

theorem width1555 : Lower6960.HelperSource.WidthGuard src1555.bank 179730 2308 src1555.reserve := requestWidth (by decide)

def ends1555 : List ℕ := [2308, 2309, 2313]

theorem inside1555 : Research6966.TerminalBanks.inside src1555.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1555 : Cover (Triangular src1555) 2313 2308 ends1555 := triangleCover (by decide +kernel)

def src1556 : Request := ⟨⟨⟨550,764,170,4314⟩,5129809428480,9639740602⟩,10,5,2,643298,54⟩

theorem rank1556 : P3_7_1.BankOK src1556.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4314

theorem width1556 : Lower6960.HelperSource.WidthGuard src1556.bank 179730 2308 src1556.reserve := requestWidth (by decide)

def ends1556 : List ℕ := [2308, 2309, 2313]

theorem inside1556 : Research6966.TerminalBanks.inside src1556.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1556 : Cover (Triangular src1556) 2313 2308 ends1556 := triangleCover (by decide +kernel)

def src1557 : Request := ⟨⟨⟨325,453,100,7715⟩,1061047500800,1193036697⟩,0,6,1,771959,1⟩

theorem rank1557 : P3_7_1.BankOK src1557.bank := by
  simpa only [src1557, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 7715

theorem width1557 : Lower6960.HelperSource.WidthGuard src1557.bank 179730 2308 src1557.reserve := requestWidth (by decide)

def ends1557 : List ℕ := [2308, 2313]

theorem inside1557 : Research6966.TerminalBanks.inside src1557.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1557 : Cover (Triangular src1557) 2313 2308 ends1557 := triangleCover (by decide +kernel)

def src1558 : Request := ⟨⟨⟨326,453,100,8738⟩,1068355026944,1193036697⟩,1,6,1,772547,1⟩

theorem rank1558 : P3_7_1.BankOK src1558.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 8738

theorem width1558 : Lower6960.HelperSource.WidthGuard src1558.bank 179730 2308 src1558.reserve := requestWidth (by decide)

def ends1558 : List ℕ := [2308, 2309, 2313]

theorem inside1558 : Research6966.TerminalBanks.inside src1558.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1558 : Cover (Triangular src1558) 2313 2308 ends1558 := triangleCover (by decide +kernel)

def src1559 : Request := ⟨⟨⟨400,558,120,9763⟩,1935519252480,2682384904⟩,2,6,1,771959,1⟩

theorem rank1559 : P3_7_1.BankOK src1559.bank := by
  simpa only [src1559, _root_.Research6969.TransitionBanks.bank133] using _root_.Research6969.TransitionBanks.rank133 9763

theorem width1559 : Lower6960.HelperSource.WidthGuard src1559.bank 179730 2308 src1559.reserve := requestWidth (by decide)

def ends1559 : List ℕ := [2313]

theorem inside1559 : Research6966.TerminalBanks.inside src1559.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1559 : Cover (Triangular src1559) 2313 2308 ends1559 := triangleCover (by decide +kernel)

def src156 : Request := ⟨⟨⟨2592,3603,775,35655⟩,520045783416832,4604362149437⟩,32,2,1,296579,33⟩

theorem rank156 : P3_7_1.BankOK src156.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2592_3603_775 35655

theorem width156 : Lower6960.HelperSource.WidthGuard src156.bank 179730 2308 src156.reserve := requestWidth (by decide)

def ends156 : List ℕ := [2308, 2309, 2313]

theorem inside156 : Research6966.TerminalBanks.inside src156.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover156 : Cover (Triangular src156) 2313 2308 ends156 := triangleCover (by decide +kernel)

def src1560 : Request := ⟨⟨⟨470,655,141,10983⟩,3134317133824,5085275599⟩,4,6,1,772547,1⟩

theorem rank1560 : P3_7_1.BankOK src1560.bank := by
  simpa only [src1560, _root_.Research6969.TransitionBanks.bank141] using _root_.Research6969.TransitionBanks.rank141 10983

theorem width1560 : Lower6960.HelperSource.WidthGuard src1560.bank 179730 2308 src1560.reserve := requestWidth (by decide)

def ends1560 : List ℕ := [2308, 2309, 2313]

theorem inside1560 : Research6966.TerminalBanks.inside src1560.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1560 : Cover (Triangular src1560) 2313 2308 ends1560 := triangleCover (by decide +kernel)

def src1561 : Request := ⟨⟨⟨560,781,172,13899⟩,5388141854720,10440670587⟩,8,6,1,771959,1⟩

theorem rank1561 : P3_7_1.BankOK src1561.bank := by
  simpa only [src1561, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 13899

theorem width1561 : Lower6960.HelperSource.WidthGuard src1561.bank 179730 2308 src1561.reserve := requestWidth (by decide)

def ends1561 : List ℕ := [2313]

theorem inside1561 : Research6966.TerminalBanks.inside src1561.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1561 : Cover (Triangular src1561) 2313 2308 ends1561 := triangleCover (by decide +kernel)

def src1562 : Request := ⟨⟨⟨693,962,212,17590⟩,10163930791936,23997864317⟩,13,6,1,772547,1⟩

theorem rank1562 : P3_7_1.BankOK src1562.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_212 17590

theorem width1562 : Lower6960.HelperSource.WidthGuard src1562.bank 179730 2308 src1562.reserve := requestWidth (by decide)

def ends1562 : List ℕ := [2308, 2309, 2313]

theorem inside1562 : Research6966.TerminalBanks.inside src1562.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1562 : Cover (Triangular src1562) 2313 2308 ends1562 := triangleCover (by decide +kernel)

def src1563 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,20,6,1,771959,1⟩

theorem rank1563 : P3_7_1.BankOK src1563.bank := by
  simpa only [src1563, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 22261

theorem width1563 : Lower6960.HelperSource.WidthGuard src1563.bank 179730 2308 src1563.reserve := requestWidth (by decide)

def ends1563 : List ℕ := [2308, 2313]

theorem inside1563 : Research6966.TerminalBanks.inside src1563.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1563 : Cover (Triangular src1563) 2313 2308 ends1563 := triangleCover (by decide +kernel)

def src1564 : Request := ⟨⟨⟨1183,1641,368,24971⟩,51061142323200,205224620315⟩,25,6,1,771959,1⟩

theorem rank1564 : P3_7_1.BankOK src1564.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1183_1641_368 24971

theorem width1564 : Lower6960.HelperSource.WidthGuard src1564.bank 179730 2308 src1564.reserve := requestWidth (by decide)

def ends1564 : List ℕ := [2308, 2309, 2313]

theorem inside1564 : Research6966.TerminalBanks.inside src1564.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1564 : Cover (Triangular src1564) 2313 2308 ends1564 := triangleCover (by decide +kernel)

def src1565 : Request := ⟨⟨⟨1736,2409,537,35481⟩,160469647360000,947161992087⟩,40,6,1,771959,1⟩

theorem rank1565 : P3_7_1.BankOK src1565.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1736_2409_537 35481

theorem width1565 : Lower6960.HelperSource.WidthGuard src1565.bank 179730 2308 src1565.reserve := requestWidth (by decide)

def ends1565 : List ℕ := [2308, 2309, 2313]

theorem inside1565 : Research6966.TerminalBanks.inside src1565.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1565 : Cover (Triangular src1565) 2313 2308 ends1565 := triangleCover (by decide +kernel)

def src1566 : Request := ⟨⟨⟨2763,3835,854,71504⟩,645932077547520,6070657981182⟩,85,6,1,771959,1⟩

theorem rank1566 : P3_7_1.BankOK src1566.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2763_3835_854 71504

theorem width1566 : Lower6960.HelperSource.WidthGuard src1566.bank 179730 2308 src1566.reserve := requestWidth (by decide)

def ends1566 : List ℕ := [2308, 2309, 2313]

theorem inside1566 : Research6966.TerminalBanks.inside src1566.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1566 : Cover (Triangular src1566) 2313 2308 ends1566 := triangleCover (by decide +kernel)

def src1567 : Request := ⟨⟨⟨2554,3560,775,256561⟩,503147779850240,4429862775297⟩,115,6,1,771959,1⟩

theorem rank1567 : P3_7_1.BankOK src1567.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2554_3560_775 256561

theorem width1567 : Lower6960.HelperSource.WidthGuard src1567.bank 179730 2308 src1567.reserve := requestWidth (by decide)

def ends1567 : List ℕ := [2308, 2309, 2313]

theorem inside1567 : Research6966.TerminalBanks.inside src1567.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1567 : Cover (Triangular src1567) 2313 2308 ends1567 := triangleCover (by decide +kernel)

def src1568 : Request := ⟨⟨⟨4800,6694,1474,115771⟩,3367547627110400,55810706074581⟩,145,6,1,771959,1⟩

theorem rank1568 : P3_7_1.BankOK src1568.bank := by
  simpa only [src1568, _root_.Research6969.TransitionBanks.bank322] using _root_.Research6969.TransitionBanks.rank322 115771

theorem width1568 : Lower6960.HelperSource.WidthGuard src1568.bank 179730 2308 src1568.reserve := requestWidth (by decide)

def ends1568 : List ℕ := [2308, 2313]



theorem cover1568 : Cover (Triangular src1568) 2313 2308 ends1568 := triangleCover (by decide +kernel)

def src1569 : Request := ⟨⟨⟨8305,11575,2548,185441⟩,17423193585483776,498569901356632⟩,245,6,1,771959,1⟩

theorem rank1569 : P3_7_1.BankOK src1569.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8305_11575_2548 185441

theorem width1569 : Lower6960.HelperSource.WidthGuard src1569.bank 179730 2308 src1569.reserve := requestWidth (by decide)

def ends1569 : List ℕ := [2308, 2309, 2313]




theorem cover1569 : Cover (Triangular src1569) 2313 2308 ends1569 := triangleCover (by decide +kernel)

def src157 : Request := ⟨⟨⟨2567,3563,793,27013⟩,517850014416896,4521960393814⟩,32,2,1,296579,33⟩

theorem rank157 : P3_7_1.BankOK src157.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3563_793 27013

theorem width157 : Lower6960.HelperSource.WidthGuard src157.bank 179730 2308 src157.reserve := requestWidth (by decide)

def ends157 : List ℕ := [2308, 2309, 2313]

theorem inside157 : Research6966.TerminalBanks.inside src157.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover157 : Cover (Triangular src157) 2313 2308 ends157 := triangleCover (by decide +kernel)

def src1570 : Request := ⟨⟨⟨325,451,98,7679⟩,1045036793856,1158025616⟩,0,6,1,771959,2⟩

theorem rank1570 : P3_7_1.BankOK src1570.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 7679

theorem width1570 : Lower6960.HelperSource.WidthGuard src1570.bank 179730 2308 src1570.reserve := requestWidth (by decide)

def ends1570 : List ℕ := [2308, 2309, 2313]

theorem inside1570 : Research6966.TerminalBanks.inside src1570.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1570 : Cover (Triangular src1570) 2313 2308 ends1570 := triangleCover (by decide +kernel)

def src1571 : Request := ⟨⟨⟨325,453,100,8679⟩,1061047500800,1193036697⟩,1,6,1,771959,2⟩

theorem rank1571 : P3_7_1.BankOK src1571.bank := by
  simpa only [src1571, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 8679

theorem width1571 : Lower6960.HelperSource.WidthGuard src1571.bank 179730 2308 src1571.reserve := requestWidth (by decide)

def ends1571 : List ℕ := [2309, 2313]

theorem inside1571 : Research6966.TerminalBanks.inside src1571.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1571 : Cover (Triangular src1571) 2313 2308 ends1571 := triangleCover (by decide +kernel)

def src1572 : Request := ⟨⟨⟨399,554,123,9752⟩,1960915763200,2671618359⟩,3,6,1,771959,2⟩

theorem rank1572 : P3_7_1.BankOK src1572.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_399_554_123 9752

theorem width1572 : Lower6960.HelperSource.WidthGuard src1572.bank 179730 2308 src1572.reserve := requestWidth (by decide)

def ends1572 : List ℕ := [2308, 2309, 2313]

theorem inside1572 : Research6966.TerminalBanks.inside src1572.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1572 : Cover (Triangular src1572) 2313 2308 ends1572 := triangleCover (by decide +kernel)

def src1573 : Request := ⟨⟨⟨471,654,144,12351⟩,3199755878400,5143543252⟩,6,6,1,771959,2⟩

theorem rank1573 : P3_7_1.BankOK src1573.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_654_144 12351

theorem width1573 : Lower6960.HelperSource.WidthGuard src1573.bank 179730 2308 src1573.reserve := requestWidth (by decide)

def ends1573 : List ℕ := [2308, 2309, 2313]

theorem inside1573 : Research6966.TerminalBanks.inside src1573.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1573 : Cover (Triangular src1573) 2313 2308 ends1573 := triangleCover (by decide +kernel)

def src1574 : Request := ⟨⟨⟨563,781,176,15636⟩,5548296110080,10627925923⟩,10,6,1,771959,2⟩

theorem rank1574 : P3_7_1.BankOK src1574.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_563_781_176 15636

theorem width1574 : Lower6960.HelperSource.WidthGuard src1574.bank 179730 2308 src1574.reserve := requestWidth (by decide)

def ends1574 : List ℕ := [2309, 2313]

theorem inside1574 : Research6966.TerminalBanks.inside src1574.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1574 : Cover (Triangular src1574) 2313 2308 ends1574 := triangleCover (by decide +kernel)

def src1575 : Request := ⟨⟨⟨819,1142,248,19696⟩,16630255452160,47053737158⟩,16,6,1,771959,2⟩

theorem rank1575 : P3_7_1.BankOK src1575.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_819_1142_248 19696

theorem width1575 : Lower6960.HelperSource.WidthGuard src1575.bank 179730 2308 src1575.reserve := requestWidth (by decide)

def ends1575 : List ℕ := [2308, 2309, 2313]

theorem inside1575 : Research6966.TerminalBanks.inside src1575.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1575 : Cover (Triangular src1575) 2313 2308 ends1575 := triangleCover (by decide +kernel)

def src1576 : Request := ⟨⟨⟨1201,1673,368,25043⟩,52817102635008,218387554859⟩,25,6,1,771959,2⟩

theorem rank1576 : P3_7_1.BankOK src1576.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1673_368 25043

theorem width1576 : Lower6960.HelperSource.WidthGuard src1576.bank 179730 2308 src1576.reserve := requestWidth (by decide)

def ends1576 : List ℕ := [2308, 2309, 2313]

theorem inside1576 : Research6966.TerminalBanks.inside src1576.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1576 : Cover (Triangular src1576) 2313 2308 ends1576 := triangleCover (by decide +kernel)

def src1577 : Request := ⟨⟨⟨1205,1674,369,131445⟩,53321182740480,219269681483⟩,50,6,1,771959,2⟩

theorem rank1577 : P3_7_1.BankOK src1577.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_369 131445

theorem width1577 : Lower6960.HelperSource.WidthGuard src1577.bank 179730 2308 src1577.reserve := requestWidth (by decide)

def ends1577 : List ℕ := [2308, 2309, 2313]

theorem inside1577 : Research6966.TerminalBanks.inside src1577.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1577 : Cover (Triangular src1577) 2313 2308 ends1577 := triangleCover (by decide +kernel)

def src1578 : Request := ⟨⟨⟨2615,3626,819,50282⟩,553151842222080,4905972788959⟩,63,6,1,771959,2⟩

theorem rank1578 : P3_7_1.BankOK src1578.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3626_819 50282

theorem width1578 : Lower6960.HelperSource.WidthGuard src1578.bank 179730 2308 src1578.reserve := requestWidth (by decide)

def ends1578 : List ℕ := [2308, 2309, 2313]

theorem inside1578 : Research6966.TerminalBanks.inside src1578.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1578 : Cover (Triangular src1578) 2313 2308 ends1578 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources22

section Pack_R6970Height2313CommonSources23

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1579 : Request := ⟨⟨⟨2109,2928,647,57562⟩,285784336760832,2051821599055⟩,65,6,1,771959,2⟩

theorem rank1579 : P3_7_1.BankOK src1579.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2109_2928_647 57562

theorem width1579 : Lower6960.HelperSource.WidthGuard src1579.bank 179730 2308 src1579.reserve := requestWidth (by decide)

def ends1579 : List ℕ := [2308, 2309, 2313]

theorem inside1579 : Research6966.TerminalBanks.inside src1579.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1579 : Cover (Triangular src1579) 2313 2308 ends1579 := triangleCover (by decide +kernel)

def src158 : Request := ⟨⟨⟨2567,3563,793,27651⟩,517850014416896,4521960393814⟩,45,2,1,296579,37⟩

theorem rank158 : P3_7_1.BankOK src158.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3563_793 27651

theorem width158 : Lower6960.HelperSource.WidthGuard src158.bank 179730 2308 src158.reserve := requestWidth (by decide)

def ends158 : List ℕ := [2308, 2309, 2313]

theorem inside158 : Research6966.TerminalBanks.inside src158.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover158 : Cover (Triangular src158) 2313 2308 ends158 := triangleCover (by decide +kernel)

def src1580 : Request := ⟨⟨⟨2577,3592,775,261865⟩,513340428255232,4559285936321⟩,115,6,1,771959,2⟩

theorem rank1580 : P3_7_1.BankOK src1580.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2577_3592_775 261865

theorem width1580 : Lower6960.HelperSource.WidthGuard src1580.bank 179730 2308 src1580.reserve := requestWidth (by decide)

def ends1580 : List ℕ := [2308, 2309, 2313]

theorem inside1580 : Research6966.TerminalBanks.inside src1580.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1580 : Cover (Triangular src1580) 2313 2308 ends1580 := triangleCover (by decide +kernel)

def src1581 : Request := ⟨⟨⟨4746,6618,1445,115236⟩,3234102093021184,52969844804533⟩,145,6,1,771959,2⟩

theorem rank1581 : P3_7_1.BankOK src1581.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4746_6618_1445 115236

theorem width1581 : Lower6960.HelperSource.WidthGuard src1581.bank 179730 2308 src1581.reserve := requestWidth (by decide)

def ends1581 : List ℕ := [2308, 2309, 2313]




theorem cover1581 : Cover (Triangular src1581) 2313 2308 ends1581 := triangleCover (by decide +kernel)

def src1582 : Request := ⟨⟨⟨8300,11575,2548,185441⟩,17399709518790656,498569901356632⟩,245,6,1,771959,2⟩

theorem rank1582 : P3_7_1.BankOK src1582.bank := by
  simpa only [src1582, _root_.Research6969.TransitionBanks.bank362] using _root_.Research6969.TransitionBanks.rank362 185441

theorem width1582 : Lower6960.HelperSource.WidthGuard src1582.bank 179730 2308 src1582.reserve := requestWidth (by decide)

def ends1582 : List ℕ := [2313]


theorem cover1582 : Cover (Triangular src1582) 2313 2308 ends1582 := triangleCover (by decide +kernel)

def src1583 : Request := ⟨⟨⟨325,453,98,7715⟩,1045036793856,1174588250⟩,0,6,1,771959,4⟩

theorem rank1583 : P3_7_1.BankOK src1583.bank := by
  simpa only [src1583, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 7715

theorem width1583 : Lower6960.HelperSource.WidthGuard src1583.bank 179730 2308 src1583.reserve := requestWidth (by decide)

def ends1583 : List ℕ := [2313]

theorem inside1583 : Research6966.TerminalBanks.inside src1583.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1583 : Cover (Triangular src1583) 2313 2308 ends1583 := triangleCover (by decide +kernel)

def src1584 : Request := ⟨⟨⟨325,453,98,8679⟩,1045036793856,1174588250⟩,1,6,1,771959,4⟩

theorem rank1584 : P3_7_1.BankOK src1584.bank := by
  simpa only [src1584, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 8679

theorem width1584 : Lower6960.HelperSource.WidthGuard src1584.bank 179730 2308 src1584.reserve := requestWidth (by decide)

def ends1584 : List ℕ := [2309, 2313]

theorem inside1584 : Research6966.TerminalBanks.inside src1584.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1584 : Cover (Triangular src1584) 2313 2308 ends1584 := triangleCover (by decide +kernel)

def src1585 : Request := ⟨⟨⟨326,453,100,9763⟩,1068355026944,1193036697⟩,2,6,1,771959,4⟩

theorem rank1585 : P3_7_1.BankOK src1585.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 9763

theorem width1585 : Lower6960.HelperSource.WidthGuard src1585.bank 179730 2308 src1585.reserve := requestWidth (by decide)

def ends1585 : List ℕ := [2308, 2313]

theorem inside1585 : Research6966.TerminalBanks.inside src1585.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1585 : Cover (Triangular src1585) 2313 2308 ends1585 := triangleCover (by decide +kernel)

def src1586 : Request := ⟨⟨⟨400,558,123,10983⟩,1971918995456,2734096379⟩,4,6,1,771959,4⟩

theorem rank1586 : P3_7_1.BankOK src1586.bank := by
  simpa only [src1586, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 10983

theorem width1586 : Lower6960.HelperSource.WidthGuard src1586.bank 179730 2308 src1586.reserve := requestWidth (by decide)

def ends1586 : List ℕ := [2313]

theorem inside1586 : Research6966.TerminalBanks.inside src1586.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1586 : Cover (Triangular src1586) 2313 2308 ends1586 := triangleCover (by decide +kernel)

def src1587 : Request := ⟨⟨⟨470,655,144,12355⟩,3184589537280,5168862572⟩,6,6,1,771959,4⟩

theorem rank1587 : P3_7_1.BankOK src1587.bank := by
  simpa only [src1587, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 12355

theorem width1587 : Lower6960.HelperSource.WidthGuard src1587.bank 179730 2308 src1587.reserve := requestWidth (by decide)

def ends1587 : List ℕ := [2313]

theorem inside1587 : Research6966.TerminalBanks.inside src1587.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1587 : Cover (Triangular src1587) 2313 2308 ends1587 := triangleCover (by decide +kernel)

def src1588 : Request := ⟨⟨⟨690,962,212,13899⟩,10065769922560,23997864317⟩,10,6,1,771959,4⟩

theorem rank1588 : P3_7_1.BankOK src1588.bank := by
  simpa only [src1588, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 13899

theorem width1588 : Lower6960.HelperSource.WidthGuard src1588.bank 179730 2308 src1588.reserve := requestWidth (by decide)

def ends1588 : List ℕ := [2309, 2313]

theorem inside1588 : Research6966.TerminalBanks.inside src1588.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1588 : Cover (Triangular src1588) 2313 2308 ends1588 := triangleCover (by decide +kernel)

def src1589 : Request := ⟨⟨⟨993,1379,307,17509⟩,30080867762176,101862721867⟩,16,6,1,771959,4⟩

theorem rank1589 : P3_7_1.BankOK src1589.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_993_1379_307 17509

theorem width1589 : Lower6960.HelperSource.WidthGuard src1589.bank 179730 2308 src1589.reserve := requestWidth (by decide)

def ends1589 : List ℕ := [2308, 2309, 2313]

theorem inside1589 : Research6966.TerminalBanks.inside src1589.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1589 : Cover (Triangular src1589) 2313 2308 ends1589 := triangleCover (by decide +kernel)

def src159 : Request := ⟨⟨⟨2567,3563,793,27651⟩,517850014416896,4521960393814⟩,45,2,1,296579,37⟩

theorem rank159 : P3_7_1.BankOK src159.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3563_793 27651

theorem width159 : Lower6960.HelperSource.WidthGuard src159.bank 179730 2308 src159.reserve := requestWidth (by decide)

def ends159 : List ℕ := [2308, 2309, 2313]

theorem inside159 : Research6966.TerminalBanks.inside src159.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover159 : Cover (Triangular src159) 2313 2308 ends159 := triangleCover (by decide +kernel)

def src1590 : Request := ⟨⟨⟨1456,2022,447,35995⟩,94182299402240,467395198256⟩,40,6,1,771959,4⟩

theorem rank1590 : P3_7_1.BankOK src1590.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2022_447 35995

theorem width1590 : Lower6960.HelperSource.WidthGuard src1590.bank 179730 2308 src1590.reserve := requestWidth (by decide)

def ends1590 : List ℕ := [2308, 2309, 2313]

theorem inside1590 : Research6966.TerminalBanks.inside src1590.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1590 : Cover (Triangular src1590) 2313 2308 ends1590 := triangleCover (by decide +kernel)

def src1591 : Request := ⟨⟨⟨2262,3139,702,49868⟩,355651506143232,2735191490284⟩,63,6,1,771959,4⟩

theorem rank1591 : P3_7_1.BankOK src1591.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2262_3139_702 49868

theorem width1591 : Lower6960.HelperSource.WidthGuard src1591.bank 179730 2308 src1591.reserve := requestWidth (by decide)

def ends1591 : List ℕ := [2308, 2309, 2313]

theorem inside1591 : Research6966.TerminalBanks.inside src1591.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1591 : Cover (Triangular src1591) 2313 2308 ends1591 := triangleCover (by decide +kernel)

def src1592 : Request := ⟨⟨⟨1461,2029,449,213052⟩,95229640704000,474265839457⟩,65,6,1,771959,4⟩

theorem rank1592 : P3_7_1.BankOK src1592.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1461_2029_449 213052

theorem width1592 : Lower6960.HelperSource.WidthGuard src1592.bank 179730 2308 src1592.reserve := requestWidth (by decide)

def ends1592 : List ℕ := [2308, 2309, 2313]

theorem inside1592 : Research6966.TerminalBanks.inside src1592.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1592 : Cover (Triangular src1592) 2313 2308 ends1592 := triangleCover (by decide +kernel)

def src1593 : Request := ⟨⟨⟨3200,4447,982,64147⟩,997767489781760,10901251843544⟩,85,6,1,771959,4⟩

theorem rank1593 : P3_7_1.BankOK src1593.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4447_982 64147

theorem width1593 : Lower6960.HelperSource.WidthGuard src1593.bank 179730 2308 src1593.reserve := requestWidth (by decide)

def ends1593 : List ℕ := [2308, 2309, 2313]




theorem cover1593 : Cover (Triangular src1593) 2313 2308 ends1593 := triangleCover (by decide +kernel)

def src1594 : Request := ⟨⟨⟨2588,3608,775,259404⟩,518253213384704,4624951115297⟩,115,6,1,771959,4⟩

theorem rank1594 : P3_7_1.BankOK src1594.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3608_775 259404

theorem width1594 : Lower6960.HelperSource.WidthGuard src1594.bank 179730 2308 src1594.reserve := requestWidth (by decide)

def ends1594 : List ℕ := [2308, 2309, 2313]

theorem inside1594 : Research6966.TerminalBanks.inside src1594.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1594 : Cover (Triangular src1594) 2313 2308 ends1594 := triangleCover (by decide +kernel)

def src1595 : Request := ⟨⟨⟨5682,7886,1750,103007⟩,5597575584940032,108128998877830⟩,145,6,1,771959,4⟩

theorem rank1595 : P3_7_1.BankOK src1595.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5682_7886_1750 103007

theorem width1595 : Lower6960.HelperSource.WidthGuard src1595.bank 179730 2308 src1595.reserve := requestWidth (by decide)

def ends1595 : List ℕ := [2308, 2309, 2313]




theorem cover1595 : Cover (Triangular src1595) 2313 2308 ends1595 := triangleCover (by decide +kernel)

def src1596 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,0,6,1,771959,9⟩

theorem rank1596 : P3_7_1.BankOK src1596.bank := by
  simpa only [src1596, _root_.Research6969.TransitionBanks.bank100] using _root_.Research6969.TransitionBanks.rank100 6858

theorem width1596 : Lower6960.HelperSource.WidthGuard src1596.bank 179730 2308 src1596.reserve := requestWidth (by decide)

def ends1596 : List ℕ := [2313]

theorem inside1596 : Research6966.TerminalBanks.inside src1596.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1596 : Cover (Triangular src1596) 2313 2308 ends1596 := triangleCover (by decide +kernel)

def src1597 : Request := ⟨⟨⟨325,452,98,7713⟩,1045036793856,1166286935⟩,1,6,1,771959,9⟩

theorem rank1597 : P3_7_1.BankOK src1597.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_452_98 7713

theorem width1597 : Lower6960.HelperSource.WidthGuard src1597.bank 179730 2308 src1597.reserve := requestWidth (by decide)

def ends1597 : List ℕ := [2308, 2309, 2313]

theorem inside1597 : Research6966.TerminalBanks.inside src1597.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1597 : Cover (Triangular src1597) 2313 2308 ends1597 := triangleCover (by decide +kernel)

def src1598 : Request := ⟨⟨⟨400,558,123,8679⟩,1971918995456,2734096379⟩,3,6,1,771959,9⟩

theorem rank1598 : P3_7_1.BankOK src1598.bank := by
  simpa only [src1598, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 8679

theorem width1598 : Lower6960.HelperSource.WidthGuard src1598.bank 179730 2308 src1598.reserve := requestWidth (by decide)

def ends1598 : List ℕ := [2313]

theorem inside1598 : Research6966.TerminalBanks.inside src1598.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1598 : Cover (Triangular src1598) 2313 2308 ends1598 := triangleCover (by decide +kernel)

def src1599 : Request := ⟨⟨⟨470,655,144,10983⟩,3184589537280,5168862572⟩,6,6,1,771959,9⟩

theorem rank1599 : P3_7_1.BankOK src1599.bank := by
  simpa only [src1599, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 10983

theorem width1599 : Lower6960.HelperSource.WidthGuard src1599.bank 179730 2308 src1599.reserve := requestWidth (by decide)

def ends1599 : List ℕ := [2313]

theorem inside1599 : Research6966.TerminalBanks.inside src1599.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1599 : Cover (Triangular src1599) 2313 2308 ends1599 := triangleCover (by decide +kernel)

def src16 : Request := ⟨⟨⟨2590,3600,775,62142⟩,519149091553280,4592038728177⟩,249,1,1,128659,513⟩

theorem rank16 : P3_7_1.BankOK src16.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2590_3600_775 62142

theorem width16 : Lower6960.HelperSource.WidthGuard src16.bank 179730 2308 src16.reserve := requestWidth (by decide)

def ends16 : List ℕ := [2308, 2309, 2313]

theorem inside16 : Research6966.TerminalBanks.inside src16.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover16 : Cover (Triangular src16) 2313 2308 ends16 := triangleCover (by decide +kernel)

def src160 : Request := ⟨⟨⟨2589,3611,775,35467⟩,518701050757120,4637334487213⟩,32,2,1,298829,33⟩

theorem rank160 : P3_7_1.BankOK src160.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2589_3611_775 35467

theorem width160 : Lower6960.HelperSource.WidthGuard src160.bank 179730 2308 src160.reserve := requestWidth (by decide)

def ends160 : List ℕ := [2308, 2309, 2313]

theorem inside160 : Research6966.TerminalBanks.inside src160.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover160 : Cover (Triangular src160) 2313 2308 ends160 := triangleCover (by decide +kernel)

def src1600 : Request := ⟨⟨⟨560,781,172,13899⟩,5388141854720,10440670587⟩,10,6,1,771959,9⟩

theorem rank1600 : P3_7_1.BankOK src1600.bank := by
  simpa only [src1600, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 13899

theorem width1600 : Lower6960.HelperSource.WidthGuard src1600.bank 179730 2308 src1600.reserve := requestWidth (by decide)

def ends1600 : List ℕ := [2309, 2313]

theorem inside1600 : Research6966.TerminalBanks.inside src1600.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1600 : Cover (Triangular src1600) 2313 2308 ends1600 := triangleCover (by decide +kernel)

def src1601 : Request := ⟨⟨⟨1000,1395,301,19788⟩,30103476895744,104105680031⟩,20,6,1,771959,9⟩

theorem rank1601 : P3_7_1.BankOK src1601.bank := by
  simpa only [src1601, _root_.Research6969.TransitionBanks.bank221] using _root_.Research6969.TransitionBanks.rank221 19788

theorem width1601 : Lower6960.HelperSource.WidthGuard src1601.bank 179730 2308 src1601.reserve := requestWidth (by decide)

def ends1601 : List ℕ := [2308, 2313]

theorem inside1601 : Research6966.TerminalBanks.inside src1601.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1601 : Cover (Triangular src1601) 2313 2308 ends1601 := triangleCover (by decide +kernel)

def src1602 : Request := ⟨⟨⟨1459,2023,457,31723⟩,96215367155712,476245648464⟩,40,6,1,771959,9⟩

theorem rank1602 : P3_7_1.BankOK src1602.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1459_2023_457 31723

theorem width1602 : Lower6960.HelperSource.WidthGuard src1602.bank 179730 2308 src1602.reserve := requestWidth (by decide)

def ends1602 : List ℕ := [2308, 2309, 2313]

theorem inside1602 : Research6966.TerminalBanks.inside src1602.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1602 : Cover (Triangular src1602) 2313 2308 ends1602 := triangleCover (by decide +kernel)

def src1603 : Request := ⟨⟨⟨1209,1677,378,102753⟩,54707005685760,224698623950⟩,50,6,1,771959,9⟩

theorem rank1603 : P3_7_1.BankOK src1603.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1209_1677_378 102753

theorem width1603 : Lower6960.HelperSource.WidthGuard src1603.bank 179730 2308 src1603.reserve := requestWidth (by decide)

def ends1603 : List ℕ := [2308, 2309, 2313]

theorem inside1603 : Research6966.TerminalBanks.inside src1603.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1603 : Cover (Triangular src1603) 2313 2308 ends1603 := triangleCover (by decide +kernel)

def src1604 : Request := ⟨⟨⟨2265,3143,702,44751⟩,356709130567680,2746433306696⟩,63,6,1,771959,9⟩

theorem rank1604 : P3_7_1.BankOK src1604.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2265_3143_702 44751

theorem width1604 : Lower6960.HelperSource.WidthGuard src1604.bank 179730 2308 src1604.reserve := requestWidth (by decide)

def ends1604 : List ℕ := [2308, 2309, 2313]

theorem inside1604 : Research6966.TerminalBanks.inside src1604.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1604 : Cover (Triangular src1604) 2313 2308 ends1604 := triangleCover (by decide +kernel)

def src1605 : Request := ⟨⟨⟨3170,4399,982,56903⟩,976937316515840,10526816118216⟩,85,6,1,771959,9⟩

theorem rank1605 : P3_7_1.BankOK src1605.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3170_4399_982 56903

theorem width1605 : Lower6960.HelperSource.WidthGuard src1605.bank 179730 2308 src1605.reserve := requestWidth (by decide)

def ends1605 : List ℕ := [2308, 2309, 2313]




theorem cover1605 : Cover (Triangular src1605) 2313 2308 ends1605 := triangleCover (by decide +kernel)

def src1606 : Request := ⟨⟨⟨2588,3608,775,232789⟩,518253213384704,4624951115297⟩,115,6,1,771959,9⟩

theorem rank1606 : P3_7_1.BankOK src1606.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3608_775 232789

theorem width1606 : Lower6960.HelperSource.WidthGuard src1606.bank 179730 2308 src1606.reserve := requestWidth (by decide)

def ends1606 : List ℕ := [2308, 2309, 2313]

theorem inside1606 : Research6966.TerminalBanks.inside src1606.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1606 : Cover (Triangular src1606) 2313 2308 ends1606 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources23

section Pack_R6970Height2313CommonSources24

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1607 : Request := ⟨⟨⟨5733,7950,1796,91586⟩,5824240852664320,113242283843565⟩,145,6,1,771959,9⟩

theorem rank1607 : P3_7_1.BankOK src1607.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5733_7950_1796 91586

theorem width1607 : Lower6960.HelperSource.WidthGuard src1607.bank 179730 2308 src1607.reserve := requestWidth (by decide)

def ends1607 : List ℕ := [2308, 2309, 2313]




theorem cover1607 : Cover (Triangular src1607) 2313 2308 ends1607 := triangleCover (by decide +kernel)

def src1608 : Request := ⟨⟨⟨4846,6722,1512,839849⟩,3507346883215360,57696887074637⟩,245,6,1,771959,9⟩

theorem rank1608 : P3_7_1.BankOK src1608.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4846_6722_1512 839849

theorem width1608 : Lower6960.HelperSource.WidthGuard src1608.bank 179730 2308 src1608.reserve := requestWidth (by decide)

def ends1608 : List ℕ := [2308, 2309, 2313]




theorem cover1608 : Cover (Triangular src1608) 2313 2308 ends1608 := triangleCover (by decide +kernel)

def src1609 : Request := ⟨⟨⟨2619,3633,819,56828⟩,555050351984640,4936552670529⟩,85,6,1,771959,13⟩

theorem rank1609 : P3_7_1.BankOK src1609.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2619_3633_819 56828

theorem width1609 : Lower6960.HelperSource.WidthGuard src1609.bank 179730 2308 src1609.reserve := requestWidth (by decide)

def ends1609 : List ℕ := [2308, 2309, 2313]

theorem inside1609 : Research6966.TerminalBanks.inside src1609.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1609 : Cover (Triangular src1609) 2313 2308 ends1609 := triangleCover (by decide +kernel)

def src161 : Request := ⟨⟨⟨2567,3563,793,26829⟩,517850014416896,4521960393814⟩,32,2,1,298829,33⟩

theorem rank161 : P3_7_1.BankOK src161.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3563_793 26829

theorem width161 : Lower6960.HelperSource.WidthGuard src161.bank 179730 2308 src161.reserve := requestWidth (by decide)

def ends161 : List ℕ := [2308, 2309, 2313]

theorem inside161 : Research6966.TerminalBanks.inside src161.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover161 : Cover (Triangular src161) 2313 2308 ends161 := triangleCover (by decide +kernel)

def src1610 : Request := ⟨⟨⟨2591,3612,754,530820⟩,508801528627200,4542835970406⟩,115,6,1,772547,13⟩

theorem rank1610 : P3_7_1.BankOK src1610.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2591_3612_754 530820

theorem width1610 : Lower6960.HelperSource.WidthGuard src1610.bank 179730 2308 src1610.reserve := requestWidth (by decide)

def ends1610 : List ℕ := [2308, 2309, 2313]

theorem inside1610 : Research6966.TerminalBanks.inside src1610.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1610 : Cover (Triangular src1610) 2313 2308 ends1610 := triangleCover (by decide +kernel)

def src1611 : Request := ⟨⟨⟨326,452,100,5415⟩,1068355026944,1184600066⟩,0,6,1,771959,16⟩

theorem rank1611 : P3_7_1.BankOK src1611.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_452_100 5415

theorem width1611 : Lower6960.HelperSource.WidthGuard src1611.bank 179730 2308 src1611.reserve := requestWidth (by decide)

def ends1611 : List ℕ := [2308, 2309, 2313]

theorem inside1611 : Research6966.TerminalBanks.inside src1611.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1611 : Cover (Triangular src1611) 2313 2308 ends1611 := triangleCover (by decide +kernel)

def src1612 : Request := ⟨⟨⟨401,558,120,6858⟩,1946335576064,2682384904⟩,2,6,1,771959,16⟩

theorem rank1612 : P3_7_1.BankOK src1612.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_401_558_120 6858

theorem width1612 : Lower6960.HelperSource.WidthGuard src1612.bank 179730 2308 src1612.reserve := requestWidth (by decide)

def ends1612 : List ℕ := [2308, 2309, 2313]

theorem inside1612 : Research6966.TerminalBanks.inside src1612.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1612 : Cover (Triangular src1612) 2313 2308 ends1612 := triangleCover (by decide +kernel)

def src1613 : Request := ⟨⟨⟨470,655,144,7715⟩,3184589537280,5168862572⟩,4,6,1,771959,16⟩

theorem rank1613 : P3_7_1.BankOK src1613.bank := by
  simpa only [src1613, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 7715

theorem width1613 : Lower6960.HelperSource.WidthGuard src1613.bank 179730 2308 src1613.reserve := requestWidth (by decide)

def ends1613 : List ℕ := [2313]

theorem inside1613 : Research6966.TerminalBanks.inside src1613.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1613 : Cover (Triangular src1613) 2313 2308 ends1613 := triangleCover (by decide +kernel)

def src1614 : Request := ⟨⟨⟨562,781,172,9763⟩,5431270572032,10440670587⟩,8,6,1,771959,16⟩

theorem rank1614 : P3_7_1.BankOK src1614.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_172 9763

theorem width1614 : Lower6960.HelperSource.WidthGuard src1614.bank 179730 2308 src1614.reserve := requestWidth (by decide)

def ends1614 : List ℕ := [2308, 2309, 2313]

theorem inside1614 : Research6966.TerminalBanks.inside src1614.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1614 : Cover (Triangular src1614) 2313 2308 ends1614 := triangleCover (by decide +kernel)

def src1615 : Request := ⟨⟨⟨826,1150,253,17590⟩,17208151113728,48873782027⟩,20,6,1,771959,16⟩

theorem rank1615 : P3_7_1.BankOK src1615.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1150_253 17590

theorem width1615 : Lower6960.HelperSource.WidthGuard src1615.bank 179730 2308 src1615.reserve := requestWidth (by decide)

def ends1615 : List ℕ := [2308, 2309, 2313]

theorem inside1615 : Research6966.TerminalBanks.inside src1615.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1615 : Cover (Triangular src1615) 2313 2308 ends1615 := triangleCover (by decide +kernel)

def src1616 : Request := ⟨⟨⟨1450,2022,445,28173⟩,92998964346880,465769321795⟩,40,6,1,771959,16⟩

theorem rank1616 : P3_7_1.BankOK src1616.bank := by
  simpa only [src1616, _root_.Research6969.TransitionBanks.bank233] using _root_.Research6969.TransitionBanks.rank233 28173

theorem width1616 : Lower6960.HelperSource.WidthGuard src1616.bank 179730 2308 src1616.reserve := requestWidth (by decide)

def ends1616 : List ℕ := [2308, 2313]

theorem inside1616 : Research6966.TerminalBanks.inside src1616.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1616 : Cover (Triangular src1616) 2313 2308 ends1616 := triangleCover (by decide +kernel)

def src1617 : Request := ⟨⟨⟨1456,2021,449,162963⟩,94501502976000,468272232157⟩,65,6,1,771959,16⟩

theorem rank1617 : P3_7_1.BankOK src1617.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2021_449 162963

theorem width1617 : Lower6960.HelperSource.WidthGuard src1617.bank 179730 2308 src1617.reserve := requestWidth (by decide)

def ends1617 : List ℕ := [2308, 2309, 2313]

theorem inside1617 : Research6966.TerminalBanks.inside src1617.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1617 : Cover (Triangular src1617) 2313 2308 ends1617 := triangleCover (by decide +kernel)

def src1618 : Request := ⟨⟨⟨2585,3591,783,56796⟩,520968959164416,4591813372944⟩,85,6,1,771959,16⟩

theorem rank1618 : P3_7_1.BankOK src1618.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2585_3591_783 56796

theorem width1618 : Lower6960.HelperSource.WidthGuard src1618.bank 179730 2308 src1618.reserve := requestWidth (by decide)

def ends1618 : List ℕ := [2308, 2309, 2313]

theorem inside1618 : Research6966.TerminalBanks.inside src1618.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1618 : Cover (Triangular src1618) 2313 2308 ends1618 := triangleCover (by decide +kernel)

def src1619 : Request := ⟨⟨⟨4832,6706,1493,774635⟩,3451435488116736,56695740716730⟩,245,6,1,771959,16⟩

theorem rank1619 : P3_7_1.BankOK src1619.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4832_6706_1493 774635

theorem width1619 : Lower6960.HelperSource.WidthGuard src1619.bank 179730 2308 src1619.reserve := requestWidth (by decide)

def ends1619 : List ℕ := [2308, 2309, 2313]




theorem cover1619 : Cover (Triangular src1619) 2313 2308 ends1619 := triangleCover (by decide +kernel)

def src162 : Request := ⟨⟨⟨2305,3203,702,28119⟩,370969276579840,2918855628076⟩,63,2,1,300246,47⟩

theorem rank162 : P3_7_1.BankOK src162.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3203_702 28119

theorem width162 : Lower6960.HelperSource.WidthGuard src162.bank 179730 2308 src162.reserve := requestWidth (by decide)

def ends162 : List ℕ := [2308, 2309, 2313]

theorem inside162 : Research6966.TerminalBanks.inside src162.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover162 : Cover (Triangular src162) 2313 2308 ends162 := triangleCover (by decide +kernel)

def src1620 : Request := ⟨⟨⟨6885,9557,2118,145986⟩,9948425779675136,232955158421260⟩,245,6,1,771959,16⟩

theorem rank1620 : P3_7_1.BankOK src1620.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6885_9557_2118 145986

theorem width1620 : Lower6960.HelperSource.WidthGuard src1620.bank 179730 2308 src1620.reserve := requestWidth (by decide)

def ends1620 : List ℕ := [2308, 2309, 2313]




theorem cover1620 : Cover (Triangular src1620) 2313 2308 ends1620 := triangleCover (by decide +kernel)

def src1621 : Request := ⟨⟨⟨8339,11575,2615,130242⟩,17933010479349760,508734991702659⟩,245,6,1,771959,16⟩

theorem rank1621 : P3_7_1.BankOK src1621.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8339_11575_2615 130242

theorem width1621 : Lower6960.HelperSource.WidthGuard src1621.bank 179730 2308 src1621.reserve := requestWidth (by decide)

def ends1621 : List ℕ := [2308, 2313]



theorem cover1621 : Cover (Triangular src1621) 2313 2308 ends1621 := triangleCover (by decide +kernel)

def src1622 : Request := ⟨⟨⟨1763,2451,551,530820⟩,169382909050880,1021582433505⟩,85,6,1,772547,17⟩

theorem rank1622 : P3_7_1.BankOK src1622.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1763_2451_551 530820

theorem width1622 : Lower6960.HelperSource.WidthGuard src1622.bank 179730 2308 src1622.reserve := requestWidth (by decide)

def ends1622 : List ℕ := [2308, 2309, 2313]

theorem inside1622 : Research6966.TerminalBanks.inside src1622.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1622 : Cover (Triangular src1622) 2313 2308 ends1622 := triangleCover (by decide +kernel)

def src1623 : Request := ⟨⟨⟨2767,3841,854,49820⟩,648028618752000,6101300343282⟩,85,6,1,771959,17⟩

theorem rank1623 : P3_7_1.BankOK src1623.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2767_3841_854 49820

theorem width1623 : Lower6960.HelperSource.WidthGuard src1623.bank 179730 2308 src1623.reserve := requestWidth (by decide)

def ends1623 : List ℕ := [2308, 2309, 2313]

theorem inside1623 : Research6966.TerminalBanks.inside src1623.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1623 : Cover (Triangular src1623) 2313 2308 ends1623 := triangleCover (by decide +kernel)

def src1624 : Request := ⟨⟨⟨1764,2447,551,475797⟩,169598300192768,1016222059945⟩,85,6,1,772547,21⟩

theorem rank1624 : P3_7_1.BankOK src1624.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1764_2447_551 475797

theorem width1624 : Lower6960.HelperSource.WidthGuard src1624.bank 179730 2308 src1624.reserve := requestWidth (by decide)

def ends1624 : List ℕ := [2308, 2309, 2313]

theorem inside1624 : Research6966.TerminalBanks.inside src1624.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1624 : Cover (Triangular src1624) 2313 2308 ends1624 := triangleCover (by decide +kernel)

def src1625 : Request := ⟨⟨⟨2816,3905,882,43945⟩,690700839813120,6598128215989⟩,85,6,1,771959,21⟩

theorem rank1625 : P3_7_1.BankOK src1625.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 43945

theorem width1625 : Lower6960.HelperSource.WidthGuard src1625.bank 179730 2308 src1625.reserve := requestWidth (by decide)

def ends1625 : List ℕ := [2308, 2309, 2313]

theorem inside1625 : Research6966.TerminalBanks.inside src1625.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1625 : Cover (Triangular src1625) 2313 2308 ends1625 := triangleCover (by decide +kernel)

def src1626 : Request := ⟨⟨⟨2816,3905,882,39448⟩,690700839813120,6598128215989⟩,85,6,1,771959,25⟩

theorem rank1626 : P3_7_1.BankOK src1626.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 39448

theorem width1626 : Lower6960.HelperSource.WidthGuard src1626.bank 179730 2308 src1626.reserve := requestWidth (by decide)

def ends1626 : List ℕ := [2308, 2309, 2313]

theorem inside1626 : Research6966.TerminalBanks.inside src1626.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1626 : Cover (Triangular src1626) 2313 2308 ends1626 := triangleCover (by decide +kernel)

def src1627 : Request := ⟨⟨⟨2320,3218,724,530820⟩,385309828710400,3035022464818⟩,115,6,1,772547,25⟩

theorem rank1627 : P3_7_1.BankOK src1627.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2320_3218_724 530820

theorem width1627 : Lower6960.HelperSource.WidthGuard src1627.bank 179730 2308 src1627.reserve := requestWidth (by decide)

def ends1627 : List ℕ := [2308, 2309, 2313]

theorem inside1627 : Research6966.TerminalBanks.inside src1627.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1627 : Cover (Triangular src1627) 2313 2308 ends1627 := triangleCover (by decide +kernel)

def src1628 : Request := ⟨⟨⟨274,381,83,4816⟩,630086696960,592977449⟩,0,6,1,771959,26⟩

theorem rank1628 : P3_7_1.BankOK src1628.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_274_381_83 4816

theorem width1628 : Lower6960.HelperSource.WidthGuard src1628.bank 179730 2308 src1628.reserve := requestWidth (by decide)

def ends1628 : List ℕ := [2308, 2309, 2313]

theorem inside1628 : Research6966.TerminalBanks.inside src1628.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1628 : Cover (Triangular src1628) 2313 2308 ends1628 := triangleCover (by decide +kernel)

def src1629 : Request := ⟨⟨⟨326,453,100,4817⟩,1068355026944,1193036697⟩,1,6,1,771959,26⟩

theorem rank1629 : P3_7_1.BankOK src1629.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 4817

theorem width1629 : Lower6960.HelperSource.WidthGuard src1629.bank 179730 2308 src1629.reserve := requestWidth (by decide)

def ends1629 : List ℕ := [2308, 2313]

theorem inside1629 : Research6966.TerminalBanks.inside src1629.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1629 : Cover (Triangular src1629) 2313 2308 ends1629 := triangleCover (by decide +kernel)

def src163 : Request := ⟨⟨⟨2312,3209,722,24369⟩,381538835628032,3001313456975⟩,63,2,1,300246,47⟩

theorem rank163 : P3_7_1.BankOK src163.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3209_722 24369

theorem width163 : Lower6960.HelperSource.WidthGuard src163.bank 179730 2308 src163.reserve := requestWidth (by decide)

def ends163 : List ℕ := [2308, 2309, 2313]

theorem inside163 : Research6966.TerminalBanks.inside src163.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover163 : Cover (Triangular src163) 2313 2308 ends163 := triangleCover (by decide +kernel)

def src1630 : Request := ⟨⟨⟨400,558,120,6858⟩,1935519252480,2682384904⟩,4,6,1,771959,26⟩

theorem rank1630 : P3_7_1.BankOK src1630.bank := by
  simpa only [src1630, _root_.Research6969.TransitionBanks.bank133] using _root_.Research6969.TransitionBanks.rank133 6858

theorem width1630 : Lower6960.HelperSource.WidthGuard src1630.bank 179730 2308 src1630.reserve := requestWidth (by decide)

def ends1630 : List ℕ := [2313]

theorem inside1630 : Research6966.TerminalBanks.inside src1630.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1630 : Cover (Triangular src1630) 2313 2308 ends1630 := triangleCover (by decide +kernel)

def src1631 : Request := ⟨⟨⟨471,655,144,8679⟩,3199755878400,5168862572⟩,8,6,1,771959,26⟩

theorem rank1631 : P3_7_1.BankOK src1631.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 8679

theorem width1631 : Lower6960.HelperSource.WidthGuard src1631.bank 179730 2308 src1631.reserve := requestWidth (by decide)

def ends1631 : List ℕ := [2309, 2313]

theorem inside1631 : Research6966.TerminalBanks.inside src1631.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1631 : Cover (Triangular src1631) 2313 2308 ends1631 := triangleCover (by decide +kernel)

def src1632 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,16,6,1,771959,26⟩

theorem rank1632 : P3_7_1.BankOK src1632.bank := by
  simpa only [src1632, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 12355

theorem width1632 : Lower6960.HelperSource.WidthGuard src1632.bank 179730 2308 src1632.reserve := requestWidth (by decide)

def ends1632 : List ℕ := [2313]

theorem inside1632 : Research6966.TerminalBanks.inside src1632.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1632 : Cover (Triangular src1632) 2313 2308 ends1632 := triangleCover (by decide +kernel)

def src1633 : Request := ⟨⟨⟨1004,1394,308,22420⟩,30907852390400,105738215253⟩,32,6,1,771959,26⟩

theorem rank1633 : P3_7_1.BankOK src1633.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1394_308 22420

theorem width1633 : Lower6960.HelperSource.WidthGuard src1633.bank 179730 2308 src1633.reserve := requestWidth (by decide)

def ends1633 : List ℕ := [2308, 2309, 2313]

theorem inside1633 : Research6966.TerminalBanks.inside src1633.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1633 : Cover (Triangular src1633) 2313 2308 ends1633 := triangleCover (by decide +kernel)

def src1634 : Request := ⟨⟨⟨1746,2424,537,25023⟩,162547070402560,966283133477⟩,50,6,1,771959,26⟩

theorem rank1634 : P3_7_1.BankOK src1634.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1746_2424_537 25023

theorem width1634 : Lower6960.HelperSource.WidthGuard src1634.bank 179730 2308 src1634.reserve := requestWidth (by decide)

def ends1634 : List ℕ := [2308, 2309, 2313]

theorem inside1634 : Research6966.TerminalBanks.inside src1634.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1634 : Cover (Triangular src1634) 2313 2308 ends1634 := triangleCover (by decide +kernel)

def src1635 : Request := ⟨⟨⟨1459,2025,449,116656⟩,94938031718400,471262550407⟩,65,6,1,771959,26⟩

theorem rank1635 : P3_7_1.BankOK src1635.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1459_2025_449 116656

theorem width1635 : Lower6960.HelperSource.WidthGuard src1635.bank 179730 2308 src1635.reserve := requestWidth (by decide)

def ends1635 : List ℕ := [2308, 2309, 2313]

theorem inside1635 : Research6966.TerminalBanks.inside src1635.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1635 : Cover (Triangular src1635) 2313 2308 ends1635 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources24

section Pack_R6970Height2313CommonSources25

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1636 : Request := ⟨⟨⟨2614,3625,819,40179⟩,552677752176640,4901614794409⟩,85,6,1,771959,26⟩

theorem rank1636 : P3_7_1.BankOK src1636.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3625_819 40179

theorem width1636 : Lower6960.HelperSource.WidthGuard src1636.bank 179730 2308 src1636.reserve := requestWidth (by decide)

def ends1636 : List ℕ := [2308, 2309, 2313]

theorem inside1636 : Research6966.TerminalBanks.inside src1636.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1636 : Cover (Triangular src1636) 2313 2308 ends1636 := triangleCover (by decide +kernel)

def src1637 : Request := ⟨⟨⟨4835,6706,1512,528158⟩,3489524589527040,57255532604349⟩,245,6,1,771959,26⟩

theorem rank1637 : P3_7_1.BankOK src1637.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4835_6706_1512 528158

theorem width1637 : Lower6960.HelperSource.WidthGuard src1637.bank 179730 2308 src1637.reserve := requestWidth (by decide)

def ends1637 : List ℕ := [2308, 2309, 2313]




theorem cover1637 : Cover (Triangular src1637) 2313 2308 ends1637 := triangleCover (by decide +kernel)

def src1638 : Request := ⟨⟨⟨6900,9621,2118,115771⟩,9997036108906496,238016971510476⟩,245,6,1,771959,26⟩

theorem rank1638 : P3_7_1.BankOK src1638.bank := by
  simpa only [src1638, _root_.Research6969.TransitionBanks.bank349] using _root_.Research6969.TransitionBanks.rank349 115771

theorem width1638 : Lower6960.HelperSource.WidthGuard src1638.bank 179730 2308 src1638.reserve := requestWidth (by decide)

def ends1638 : List ℕ := [2313]


theorem cover1638 : Cover (Triangular src1638) 2313 2308 ends1638 := triangleCover (by decide +kernel)

def src1639 : Request := ⟨⟨⟨2816,3905,882,35408⟩,690700839813120,6598128215989⟩,85,6,1,771959,29⟩

theorem rank1639 : P3_7_1.BankOK src1639.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 35408

theorem width1639 : Lower6960.HelperSource.WidthGuard src1639.bank 179730 2308 src1639.reserve := requestWidth (by decide)

def ends1639 : List ℕ := [2308, 2309, 2313]

theorem inside1639 : Research6966.TerminalBanks.inside src1639.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1639 : Cover (Triangular src1639) 2313 2308 ends1639 := triangleCover (by decide +kernel)

def src164 : Request := ⟨⟨⟨2415,3369,737,45124⟩,427275292508160,3566970195593⟩,22,2,1,300842,29⟩

theorem rank164 : P3_7_1.BankOK src164.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2415_3369_737 45124

theorem width164 : Lower6960.HelperSource.WidthGuard src164.bank 179730 2308 src164.reserve := requestWidth (by decide)

def ends164 : List ℕ := [2308, 2313]

theorem inside164 : Research6966.TerminalBanks.inside src164.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover164 : Cover (Triangular src164) 2313 2308 ends164 := triangleCover (by decide +kernel)

def src1640 : Request := ⟨⟨⟨2317,3214,724,475797⟩,384194019328000,3022885912618⟩,115,6,1,772547,29⟩

theorem rank1640 : P3_7_1.BankOK src1640.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2317_3214_724 475797

theorem width1640 : Lower6960.HelperSource.WidthGuard src1640.bank 179730 2308 src1640.reserve := requestWidth (by decide)

def ends1640 : List ℕ := [2308, 2309, 2313]

theorem inside1640 : Research6966.TerminalBanks.inside src1640.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1640 : Cover (Triangular src1640) 2313 2308 ends1640 := triangleCover (by decide +kernel)

def src1641 : Request := ⟨⟨⟨2588,3593,793,34090⟩,527385327042560,4645717944219⟩,85,6,1,771959,33⟩

theorem rank1641 : P3_7_1.BankOK src1641.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 34090

theorem width1641 : Lower6960.HelperSource.WidthGuard src1641.bank 179730 2308 src1641.reserve := requestWidth (by decide)

def ends1641 : List ℕ := [2308, 2309, 2313]

theorem inside1641 : Research6966.TerminalBanks.inside src1641.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1641 : Cover (Triangular src1641) 2313 2308 ends1641 := triangleCover (by decide +kernel)

def src1642 : Request := ⟨⟨⟨2302,3190,708,329731⟩,372287251152896,2900018359096⟩,113,6,1,771959,33⟩

theorem rank1642 : P3_7_1.BankOK src1642.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3190_708 329731

theorem width1642 : Lower6960.HelperSource.WidthGuard src1642.bank 179730 2308 src1642.reserve := requestWidth (by decide)

def ends1642 : List ℕ := [2308, 2309, 2313]

theorem inside1642 : Research6966.TerminalBanks.inside src1642.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1642 : Cover (Triangular src1642) 2313 2308 ends1642 := triangleCover (by decide +kernel)

def src1643 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,0,6,1,771959,41⟩

theorem rank1643 : P3_7_1.BankOK src1643.bank := by
  simpa only [src1643, _root_.Research6969.TransitionBanks.bank78] using _root_.Research6969.TransitionBanks.rank78 3384

theorem width1643 : Lower6960.HelperSource.WidthGuard src1643.bank 179730 2308 src1643.reserve := requestWidth (by decide)

def ends1643 : List ℕ := [2313]

theorem inside1643 : Research6966.TerminalBanks.inside src1643.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1643 : Cover (Triangular src1643) 2313 2308 ends1643 := triangleCover (by decide +kernel)

def src1644 : Request := ⟨⟨⟨326,453,98,3384⟩,1052225568768,1174588250⟩,1,6,1,772547,41⟩

theorem rank1644 : P3_7_1.BankOK src1644.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_98 3384

theorem width1644 : Lower6960.HelperSource.WidthGuard src1644.bank 179730 2308 src1644.reserve := requestWidth (by decide)

def ends1644 : List ℕ := [2308, 2309, 2313]

theorem inside1644 : Research6966.TerminalBanks.inside src1644.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1644 : Cover (Triangular src1644) 2313 2308 ends1644 := triangleCover (by decide +kernel)

def src1645 : Request := ⟨⟨⟨325,451,98,3781⟩,1045036793856,1158025616⟩,2,6,1,771959,41⟩

theorem rank1645 : P3_7_1.BankOK src1645.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_451_98 3781

theorem width1645 : Lower6960.HelperSource.WidthGuard src1645.bank 179730 2308 src1645.reserve := requestWidth (by decide)

def ends1645 : List ℕ := [2308, 2309, 2313]

theorem inside1645 : Research6966.TerminalBanks.inside src1645.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1645 : Cover (Triangular src1645) 2313 2308 ends1645 := triangleCover (by decide +kernel)

def src1646 : Request := ⟨⟨⟨325,453,100,4282⟩,1061047500800,1193036697⟩,3,6,1,771959,41⟩

theorem rank1646 : P3_7_1.BankOK src1646.bank := by
  simpa only [src1646, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 4282

theorem width1646 : Lower6960.HelperSource.WidthGuard src1646.bank 179730 2308 src1646.reserve := requestWidth (by decide)

def ends1646 : List ℕ := [2308, 2313]

theorem inside1646 : Research6966.TerminalBanks.inside src1646.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1646 : Cover (Triangular src1646) 2313 2308 ends1646 := triangleCover (by decide +kernel)

def src1647 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,6,6,1,771959,41⟩

theorem rank1647 : P3_7_1.BankOK src1647.bank := by
  simpa only [src1647, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 5419

theorem width1647 : Lower6960.HelperSource.WidthGuard src1647.bank 179730 2308 src1647.reserve := requestWidth (by decide)

def ends1647 : List ℕ := [2313]

theorem inside1647 : Research6966.TerminalBanks.inside src1647.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1647 : Cover (Triangular src1647) 2313 2308 ends1647 := triangleCover (by decide +kernel)

def src1648 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,13,6,1,771959,41⟩

theorem rank1648 : P3_7_1.BankOK src1648.bank := by
  simpa only [src1648, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 7715

theorem width1648 : Lower6960.HelperSource.WidthGuard src1648.bank 179730 2308 src1648.reserve := requestWidth (by decide)

def ends1648 : List ℕ := [2308, 2313]

theorem inside1648 : Research6966.TerminalBanks.inside src1648.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1648 : Cover (Triangular src1648) 2313 2308 ends1648 := triangleCover (by decide +kernel)

def src1649 : Request := ⟨⟨⟨1205,1673,378,15636⟩,54302243291136,222977190790⟩,40,6,1,771959,41⟩

theorem rank1649 : P3_7_1.BankOK src1649.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1673_378 15636

theorem width1649 : Lower6960.HelperSource.WidthGuard src1649.bank 179730 2308 src1649.reserve := requestWidth (by decide)

def ends1649 : List ℕ := [2308, 2309, 2313]

theorem inside1649 : Research6966.TerminalBanks.inside src1649.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1649 : Cover (Triangular src1649) 2313 2308 ends1649 := triangleCover (by decide +kernel)

def src165 : Request := ⟨⟨⟨2567,3564,793,31467⟩,517850014416896,4526049059099⟩,22,2,1,300842,29⟩

theorem rank165 : P3_7_1.BankOK src165.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2567_3564_793 31467

theorem width165 : Lower6960.HelperSource.WidthGuard src165.bank 179730 2308 src165.reserve := requestWidth (by decide)

def ends165 : List ℕ := [2308, 2309, 2313]

theorem inside165 : Research6966.TerminalBanks.inside src165.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover165 : Cover (Triangular src165) 2313 2308 ends165 := triangleCover (by decide +kernel)

def src1650 : Request := ⟨⟨⟨1456,2021,449,56543⟩,94501502976000,468272232157⟩,65,6,1,771959,41⟩

theorem rank1650 : P3_7_1.BankOK src1650.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2021_449 56543

theorem width1650 : Lower6960.HelperSource.WidthGuard src1650.bank 179730 2308 src1650.reserve := requestWidth (by decide)

def ends1650 : List ℕ := [2308, 2309, 2313]

theorem inside1650 : Research6966.TerminalBanks.inside src1650.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1650 : Cover (Triangular src1650) 2313 2308 ends1650 := triangleCover (by decide +kernel)

def src1651 : Request := ⟨⟨⟨1746,2424,537,25030⟩,162547070402560,966283133477⟩,65,6,1,771959,41⟩

theorem rank1651 : P3_7_1.BankOK src1651.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1746_2424_537 25030

theorem width1651 : Lower6960.HelperSource.WidthGuard src1651.bank 179730 2308 src1651.reserve := requestWidth (by decide)

def ends1651 : List ℕ := [2308, 2309, 2313]

theorem inside1651 : Research6966.TerminalBanks.inside src1651.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1651 : Cover (Triangular src1651) 2313 2308 ends1651 := triangleCover (by decide +kernel)

def src1652 : Request := ⟨⟨⟨2309,3206,710,336847⟩,375630078935040,2953586856669⟩,115,6,1,772547,41⟩

theorem rank1652 : P3_7_1.BankOK src1652.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2309_3206_710 336847

theorem width1652 : Lower6960.HelperSource.WidthGuard src1652.bank 179730 2308 src1652.reserve := requestWidth (by decide)

def ends1652 : List ℕ := [2308, 2309, 2313]

theorem inside1652 : Research6966.TerminalBanks.inside src1652.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1652 : Cover (Triangular src1652) 2313 2308 ends1652 := triangleCover (by decide +kernel)

def src1653 : Request := ⟨⟨⟨2814,3905,880,42846⟩,688418147532800,6586515963428⟩,115,6,1,771959,41⟩

theorem rank1653 : P3_7_1.BankOK src1653.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2814_3905_880 42846

theorem width1653 : Lower6960.HelperSource.WidthGuard src1653.bank 179730 2308 src1653.reserve := requestWidth (by decide)

def ends1653 : List ℕ := [2308, 2309, 2313]

theorem inside1653 : Research6966.TerminalBanks.inside src1653.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1653 : Cover (Triangular src1653) 2313 2308 ends1653 := triangleCover (by decide +kernel)

def src1654 : Request := ⟨⟨⟨4812,6692,1474,64247⟩,3386429898752000,55757027345056⟩,190,6,1,771959,41⟩

theorem rank1654 : P3_7_1.BankOK src1654.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4812_6692_1474 64247

theorem width1654 : Lower6960.HelperSource.WidthGuard src1654.bank 179730 2308 src1654.reserve := requestWidth (by decide)

def ends1654 : List ℕ := [2308, 2309, 2313]




theorem cover1654 : Cover (Triangular src1654) 2313 2308 ends1654 := triangleCover (by decide +kernel)

def src1655 : Request := ⟨⟨⟨4846,6722,1512,231347⟩,3507346883215360,57696887074637⟩,245,6,1,771959,41⟩

theorem rank1655 : P3_7_1.BankOK src1655.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4846_6722_1512 231347

theorem width1655 : Lower6960.HelperSource.WidthGuard src1655.bank 179730 2308 src1655.reserve := requestWidth (by decide)

def ends1655 : List ℕ := [2308, 2309, 2313]




theorem cover1655 : Cover (Triangular src1655) 2313 2308 ends1655 := triangleCover (by decide +kernel)

def src1656 : Request := ⟨⟨⟨2307,3206,702,146017⟩,371690023944192,2927665016684⟩,114,6,1,771959,49⟩

theorem rank1656 : P3_7_1.BankOK src1656.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3206_702 146017

theorem width1656 : Lower6960.HelperSource.WidthGuard src1656.bank 179730 2308 src1656.reserve := requestWidth (by decide)

def ends1656 : List ℕ := [2308, 2309, 2313]

theorem inside1656 : Research6966.TerminalBanks.inside src1656.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1656 : Cover (Triangular src1656) 2313 2308 ends1656 := triangleCover (by decide +kernel)

def src1657 : Request := ⟨⟨⟨2766,3839,854,34698⟩,647504147251200,6091074552402⟩,115,6,1,771959,49⟩

theorem rank1657 : P3_7_1.BankOK src1657.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2766_3839_854 34698

theorem width1657 : Lower6960.HelperSource.WidthGuard src1657.bank 179730 2308 src1657.reserve := requestWidth (by decide)

def ends1657 : List ℕ := [2308, 2309, 2313]

theorem inside1657 : Research6966.TerminalBanks.inside src1657.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1657 : Cover (Triangular src1657) 2313 2308 ends1657 := triangleCover (by decide +kernel)

def src1658 : Request := ⟨⟨⟨2312,3206,724,31180⟩,382338138112000,2998712046218⟩,115,6,1,771959,65⟩

theorem rank1658 : P3_7_1.BankOK src1658.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3206_724 31180

theorem width1658 : Lower6960.HelperSource.WidthGuard src1658.bank 179730 2308 src1658.reserve := requestWidth (by decide)

def ends1658 : List ℕ := [2308, 2309, 2313]

theorem inside1658 : Research6966.TerminalBanks.inside src1658.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1658 : Cover (Triangular src1658) 2313 2308 ends1658 := triangleCover (by decide +kernel)

def src1659 : Request := ⟨⟨⟨2810,3902,858,72277⟩,673179779465216,6442222859746⟩,150,6,1,772547,65⟩

theorem rank1659 : P3_7_1.BankOK src1659.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3902_858 72277

theorem width1659 : Lower6960.HelperSource.WidthGuard src1659.bank 179730 2308 src1659.reserve := requestWidth (by decide)

def ends1659 : List ℕ := [2308, 2309, 2313]

theorem inside1659 : Research6966.TerminalBanks.inside src1659.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1659 : Cover (Triangular src1659) 2313 2308 ends1659 := triangleCover (by decide +kernel)

def src166 : Request := ⟨⟨⟨2601,3622,793,49468⟩,533334139076608,4767521972754⟩,15,2,1,302619,25⟩

theorem rank166 : P3_7_1.BankOK src166.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3622_793 49468

theorem width166 : Lower6960.HelperSource.WidthGuard src166.bank 179730 2308 src166.reserve := requestWidth (by decide)

def ends166 : List ℕ := [2308, 2309, 2313]

theorem inside166 : Research6966.TerminalBanks.inside src166.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover166 : Cover (Triangular src166) 2313 2308 ends166 := triangleCover (by decide +kernel)

def src1660 : Request := ⟨⟨⟨1450,2020,442,25043⟩,92522927882240,461852681878⟩,85,6,1,771959,97⟩

theorem rank1660 : P3_7_1.BankOK src1660.bank := by
  simpa only [src1660, _root_.Research6969.TerminalAuxBanks.bank6] using _root_.Research6969.PackedRanks.TerminalRanks4To7.rank6 25043

theorem width1660 : Lower6960.HelperSource.WidthGuard src1660.bank 179730 2308 src1660.reserve := requestWidth (by decide)

def ends1660 : List ℕ := [2308, 2313]

theorem inside1660 : Research6966.TerminalBanks.inside src1660.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1660 : Cover (Triangular src1660) 2313 2308 ends1660 := triangleCover (by decide +kernel)

def src1661 : Request := ⟨⟨⟨2564,3559,793,30871⟩,516495320023040,4505630874684⟩,150,6,1,771959,97⟩

theorem rank1661 : P3_7_1.BankOK src1661.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2564_3559_793 30871

theorem width1661 : Lower6960.HelperSource.WidthGuard src1661.bank 179730 2308 src1661.reserve := requestWidth (by decide)

def ends1661 : List ℕ := [2308, 2309, 2313]

theorem inside1661 : Research6966.TerminalBanks.inside src1661.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1661 : Cover (Triangular src1661) 2313 2308 ends1661 := triangleCover (by decide +kernel)

def src1662 : Request := ⟨⟨⟨2809,3901,853,43705⟩,669661892444160,6407686561801⟩,193,6,1,771959,129⟩

theorem rank1662 : P3_7_1.BankOK src1662.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3901_853 43705

theorem width1662 : Lower6960.HelperSource.WidthGuard src1662.bank 179730 2308 src1662.reserve := requestWidth (by decide)

def ends1662 : List ℕ := [2308, 2309, 2313]

theorem inside1662 : Research6966.TerminalBanks.inside src1662.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1662 : Cover (Triangular src1662) 2313 2308 ends1662 := triangleCover (by decide +kernel)

def src1663 : Request := ⟨⟨⟨2809,3901,854,46591⟩,670258813992960,6413535689982⟩,195,6,1,771959,129⟩

theorem rank1663 : P3_7_1.BankOK src1663.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3901_854 46591

theorem width1663 : Lower6960.HelperSource.WidthGuard src1663.bank 179730 2308 src1663.reserve := requestWidth (by decide)

def ends1663 : List ℕ := [2308, 2309, 2313]

theorem inside1663 : Research6966.TerminalBanks.inside src1663.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1663 : Cover (Triangular src1663) 2313 2308 ends1663 := triangleCover (by decide +kernel)

def src1664 : Request := ⟨⟨⟨1750,2437,551,40111⟩,166595992223744,1002904994165⟩,150,6,1,771959,257⟩

theorem rank1664 : P3_7_1.BankOK src1664.bank := by
  simpa only [src1664, _root_.Research6969.TerminalAuxBanks.bank9] using _root_.Research6969.PackedRanks.TerminalRanks8To11.rank9 40111

theorem width1664 : Lower6960.HelperSource.WidthGuard src1664.bank 179730 2308 src1664.reserve := requestWidth (by decide)

def ends1664 : List ℕ := [2309, 2313]

theorem inside1664 : Research6966.TerminalBanks.inside src1664.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1664 : Cover (Triangular src1664) 2313 2308 ends1664 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources25

section Pack_R6970Height2313CommonSources26

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1665 : Request := ⟨⟨⟨2957,4108,894,52933⟩,778508848332800,7849872303328⟩,250,6,1,771959,257⟩

theorem rank1665 : P3_7_1.BankOK src1665.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2957_4108_894 52933

theorem width1665 : Lower6960.HelperSource.WidthGuard src1665.bank 179730 2308 src1665.reserve := requestWidth (by decide)

def ends1665 : List ℕ := [2308, 2309, 2313]

theorem inside1665 : Research6966.TerminalBanks.inside src1665.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1665 : Cover (Triangular src1665) 2313 2308 ends1665 := triangleCover (by decide +kernel)

def src1666 : Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,6,1,771959,513⟩

theorem rank1666 : P3_7_1.BankOK src1666.bank := by
  simpa only [src1666, _root_.Research6969.TerminalAuxBanks.bank16] using _root_.Research6969.PackedRanks.TerminalRanks16To19.rank16 50419

theorem width1666 : Lower6960.HelperSource.WidthGuard src1666.bank 179730 2308 src1666.reserve := requestWidth (by decide)

def ends1666 : List ℕ := [2308, 2313]

theorem inside1666 : Research6966.TerminalBanks.inside src1666.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1666 : Cover (Triangular src1666) 2313 2308 ends1666 := triangleCover (by decide +kernel)

def src1667 : Request := ⟨⟨⟨2592,3604,775,58511⟩,520045783416832,4608474947497⟩,249,6,1,771959,513⟩

theorem rank1667 : P3_7_1.BankOK src1667.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2592_3604_775 58511

theorem width1667 : Lower6960.HelperSource.WidthGuard src1667.bank 179730 2308 src1667.reserve := requestWidth (by decide)

def ends1667 : List ℕ := [2308, 2309, 2313]

theorem inside1667 : Research6966.TerminalBanks.inside src1667.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1667 : Cover (Triangular src1667) 2313 2308 ends1667 := triangleCover (by decide +kernel)

def src1668 : Request := ⟨⟨⟨2300,3201,702,79852⟩,369170633195520,2912992731804⟩,250,6,1,771959,1025⟩

theorem rank1668 : P3_7_1.BankOK src1668.bank := by
  simpa only [src1668, _root_.Research6969.TerminalAuxBanks.bank23] using _root_.Research6969.PackedRanks.TerminalRanks20To23.rank23 79852

theorem width1668 : Lower6960.HelperSource.WidthGuard src1668.bank 179730 2308 src1668.reserve := requestWidth (by decide)

def ends1668 : List ℕ := [2309, 2313]

theorem inside1668 : Research6966.TerminalBanks.inside src1668.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1668 : Cover (Triangular src1668) 2313 2308 ends1668 := triangleCover (by decide +kernel)

def src1669 : Request := ⟨⟨⟨3006,4178,900,110245⟩,811784174567424,8331876423452⟩,326,6,1,771959,1025⟩

theorem rank1669 : P3_7_1.BankOK src1669.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3006_4178_900 110245

theorem width1669 : Lower6960.HelperSource.WidthGuard src1669.bank 179730 2308 src1669.reserve := requestWidth (by decide)

def ends1669 : List ℕ := [2308, 2309, 2313]

theorem inside1669 : Research6966.TerminalBanks.inside src1669.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1669 : Cover (Triangular src1669) 2313 2308 ends1669 := triangleCover (by decide +kernel)

def src167 : Request := ⟨⟨⟨2958,4120,900,87640⟩,783072706166784,7965324963082⟩,21,2,1,302619,25⟩

theorem rank167 : P3_7_1.BankOK src167.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2958_4120_900 87640

theorem width167 : Lower6960.HelperSource.WidthGuard src167.bank 179730 2308 src167.reserve := requestWidth (by decide)

def ends167 : List ℕ := [2308, 2309, 2313]

theorem inside167 : Research6966.TerminalBanks.inside src167.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover167 : Cover (Triangular src167) 2313 2308 ends167 := triangleCover (by decide +kernel)

def src1670 : Request := ⟨⟨⟨2807,3896,882,134834⟩,685761434222592,6549254417644⟩,325,6,1,771959,1537⟩

theorem rank1670 : P3_7_1.BankOK src1670.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2807_3896_882 134834

theorem width1670 : Lower6960.HelperSource.WidthGuard src1670.bank 179730 2308 src1670.reserve := requestWidth (by decide)

def ends1670 : List ℕ := [2308, 2309, 2313]

theorem inside1670 : Research6966.TerminalBanks.inside src1670.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1670 : Cover (Triangular src1670) 2313 2308 ends1670 := triangleCover (by decide +kernel)

def src1671 : Request := ⟨⟨⟨2948,4103,870,109728⟩,757337177718784,7654838454885⟩,325,6,1,771959,1537⟩

theorem rank1671 : P3_7_1.BankOK src1671.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2948_4103_870 109728

theorem width1671 : Lower6960.HelperSource.WidthGuard src1671.bank 179730 2308 src1671.reserve := requestWidth (by decide)

def ends1671 : List ℕ := [2308, 2309, 2313]

theorem inside1671 : Research6966.TerminalBanks.inside src1671.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1671 : Cover (Triangular src1671) 2313 2308 ends1671 := triangleCover (by decide +kernel)

def src1672 : Request := ⟨⟨⟨1750,2435,522,70068⟩,159899889172480,959076692411⟩,195,6,1,771959,2049⟩

theorem rank1672 : P3_7_1.BankOK src1672.bank := by
  simpa only [src1672, _root_.Research6969.TerminalAuxBanks.bank8] using _root_.Research6969.PackedRanks.TerminalRanks8To11.rank8 70068

theorem width1672 : Lower6960.HelperSource.WidthGuard src1672.bank 179730 2308 src1672.reserve := requestWidth (by decide)

def ends1672 : List ℕ := [2308, 2313]

theorem inside1672 : Research6966.TerminalBanks.inside src1672.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1672 : Cover (Triangular src1672) 2313 2308 ends1672 := triangleCover (by decide +kernel)

def src1673 : Request := ⟨⟨⟨2808,3900,854,112422⟩,669724928901120,6408244632207⟩,325,6,1,771959,2049⟩

theorem rank1673 : P3_7_1.BankOK src1673.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 112422

theorem width1673 : Lower6960.HelperSource.WidthGuard src1673.bank 179730 2308 src1673.reserve := requestWidth (by decide)

def ends1673 : List ℕ := [2308, 2309, 2313]

theorem inside1673 : Research6966.TerminalBanks.inside src1673.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1673 : Cover (Triangular src1673) 2313 2308 ends1673 := triangleCover (by decide +kernel)

def src1674 : Request := ⟨⟨⟨2748,3824,812,150454⟩,614083158081536,5782986158433⟩,325,6,1,771959,4097⟩

theorem rank1674 : P3_7_1.BankOK src1674.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 150454

theorem width1674 : Lower6960.HelperSource.WidthGuard src1674.bank 179730 2308 src1674.reserve := requestWidth (by decide)

def ends1674 : List ℕ := [2308, 2309, 2313]

theorem inside1674 : Research6966.TerminalBanks.inside src1674.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1674 : Cover (Triangular src1674) 2313 2308 ends1674 := triangleCover (by decide +kernel)

def src1675 : Request := ⟨⟨⟨2777,3864,812,157626⟩,628650759421952,5979768862673⟩,325,6,1,771959,4097⟩

theorem rank1675 : P3_7_1.BankOK src1675.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2777_3864_812 157626

theorem width1675 : Lower6960.HelperSource.WidthGuard src1675.bank 179730 2308 src1675.reserve := requestWidth (by decide)

def ends1675 : List ℕ := [2308, 2309, 2313]

theorem inside1675 : Research6966.TerminalBanks.inside src1675.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1675 : Cover (Triangular src1675) 2313 2308 ends1675 := triangleCover (by decide +kernel)

def src1676 : Request := ⟨⟨⟨2003,2782,610,194054⟩,243494574096384,1662397981334⟩,250,6,1,771959,8193⟩

theorem rank1676 : P3_7_1.BankOK src1676.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2003_2782_610 194054

theorem width1676 : Lower6960.HelperSource.WidthGuard src1676.bank 179730 2308 src1676.reserve := requestWidth (by decide)

def ends1676 : List ℕ := [2308, 2309, 2313]

theorem inside1676 : Research6966.TerminalBanks.inside src1676.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1676 : Cover (Triangular src1676) 2313 2308 ends1676 := triangleCover (by decide +kernel)

def src1677 : Request := ⟨⟨⟨2000,2782,596,170440⟩,238428431581184,1632591172707⟩,250,6,1,771959,32769⟩

theorem rank1677 : P3_7_1.BankOK src1677.bank := by
  simpa only [src1677, _root_.Research6969.TerminalAuxBanks.bank14] using _root_.Research6969.PackedRanks.TerminalRanks12To15.rank14 170440

theorem width1677 : Lower6960.HelperSource.WidthGuard src1677.bank 179730 2308 src1677.reserve := requestWidth (by decide)

def ends1677 : List ℕ := [2308, 2309, 2313]

theorem inside1677 : Research6966.TerminalBanks.inside src1677.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1677 : Cover (Triangular src1677) 2313 2308 ends1677 := triangleCover (by decide +kernel)

def src1678 : Request := ⟨⟨⟨556,772,171,7045⟩,5279150768128,10013440706⟩,10,6,2,771958,2⟩

theorem rank1678 : P3_7_1.BankOK src1678.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 7045

theorem width1678 : Lower6960.HelperSource.WidthGuard src1678.bank 179730 2308 src1678.reserve := requestWidth (by decide)

def ends1678 : List ℕ := [2308, 2309, 2313]

theorem inside1678 : Research6966.TerminalBanks.inside src1678.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1678 : Cover (Triangular src1678) 2313 2308 ends1678 := triangleCover (by decide +kernel)

def src1679 : Request := ⟨⟨⟨555,770,170,6977⟩,5234703728640,9885300877⟩,10,6,2,771958,3⟩

theorem rank1679 : P3_7_1.BankOK src1679.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_555_770_170 6977

theorem width1679 : Lower6960.HelperSource.WidthGuard src1679.bank 179730 2308 src1679.reserve := requestWidth (by decide)

def ends1679 : List ℕ := [2308, 2309, 2313]

theorem inside1679 : Research6966.TerminalBanks.inside src1679.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1679 : Cover (Triangular src1679) 2313 2308 ends1679 := triangleCover (by decide +kernel)

def src168 : Request := ⟨⟨⟨2730,3809,832,64247⟩,616450357985280,5819759915577⟩,22,2,1,302619,27⟩

theorem rank168 : P3_7_1.BankOK src168.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2730_3809_832 64247

theorem width168 : Lower6960.HelperSource.WidthGuard src168.bank 179730 2308 src168.reserve := requestWidth (by decide)

def ends168 : List ℕ := [2309, 2313]

theorem inside168 : Research6966.TerminalBanks.inside src168.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover168 : Cover (Triangular src168) 2313 2308 ends168 := triangleCover (by decide +kernel)

def src1680 : Request := ⟨⟨⟨556,772,171,6833⟩,5279150768128,10013440706⟩,10,6,2,771958,5⟩

theorem rank1680 : P3_7_1.BankOK src1680.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6833

theorem width1680 : Lower6960.HelperSource.WidthGuard src1680.bank 179730 2308 src1680.reserve := requestWidth (by decide)

def ends1680 : List ℕ := [2308, 2309, 2313]

theorem inside1680 : Research6966.TerminalBanks.inside src1680.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1680 : Cover (Triangular src1680) 2313 2308 ends1680 := triangleCover (by decide +kernel)

def src1681 : Request := ⟨⟨⟨556,772,171,6490⟩,5279150768128,10013440706⟩,10,6,2,771958,10⟩

theorem rank1681 : P3_7_1.BankOK src1681.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6490

theorem width1681 : Lower6960.HelperSource.WidthGuard src1681.bank 179730 2308 src1681.reserve := requestWidth (by decide)

def ends1681 : List ℕ := [2308, 2309, 2313]

theorem inside1681 : Research6966.TerminalBanks.inside src1681.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1681 : Cover (Triangular src1681) 2313 2308 ends1681 := triangleCover (by decide +kernel)

def src1682 : Request := ⟨⟨⟨550,763,170,6011⟩,5129809428480,9599221867⟩,10,6,2,771958,17⟩

theorem rank1682 : P3_7_1.BankOK src1682.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 6011

theorem width1682 : Lower6960.HelperSource.WidthGuard src1682.bank 179730 2308 src1682.reserve := requestWidth (by decide)

def ends1682 : List ℕ := [2308, 2309, 2313]

theorem inside1682 : Research6966.TerminalBanks.inside src1682.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1682 : Cover (Triangular src1682) 2313 2308 ends1682 := triangleCover (by decide +kernel)

def src1683 : Request := ⟨⟨⟨545,756,170,5396⟩,5026035793920,9318832198⟩,10,6,2,771958,27⟩

theorem rank1683 : P3_7_1.BankOK src1683.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5396

theorem width1683 : Lower6960.HelperSource.WidthGuard src1683.bank 179730 2308 src1683.reserve := requestWidth (by decide)

def ends1683 : List ℕ := [2308, 2309, 2313]

theorem inside1683 : Research6966.TerminalBanks.inside src1683.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1683 : Cover (Triangular src1683) 2313 2308 ends1683 := triangleCover (by decide +kernel)

def src1684 : Request := ⟨⟨⟨550,764,170,4672⟩,5129809428480,9639740602⟩,10,6,2,771958,42⟩

theorem rank1684 : P3_7_1.BankOK src1684.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4672

theorem width1684 : Lower6960.HelperSource.WidthGuard src1684.bank 179730 2308 src1684.reserve := requestWidth (by decide)

def ends1684 : List ℕ := [2308, 2309, 2313]

theorem inside1684 : Research6966.TerminalBanks.inside src1684.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1684 : Cover (Triangular src1684) 2313 2308 ends1684 := triangleCover (by decide +kernel)

def src1685 : Request := ⟨⟨⟨326,453,100,5419⟩,1068355026944,1193036697⟩,0,7,1,900619,1⟩

theorem rank1685 : P3_7_1.BankOK src1685.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_326_453_100 5419

theorem width1685 : Lower6960.HelperSource.WidthGuard src1685.bank 179730 2308 src1685.reserve := requestWidth (by decide)

def ends1685 : List ℕ := [2308, 2313]

theorem inside1685 : Research6966.TerminalBanks.inside src1685.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1685 : Cover (Triangular src1685) 2313 2308 ends1685 := triangleCover (by decide +kernel)

def src1686 : Request := ⟨⟨⟨325,453,100,6096⟩,1061047500800,1193036697⟩,1,7,1,900619,1⟩

theorem rank1686 : P3_7_1.BankOK src1686.bank := by
  simpa only [src1686, _root_.Research6969.TransitionBanks.bank101] using _root_.Research6969.TransitionBanks.rank101 6096

theorem width1686 : Lower6960.HelperSource.WidthGuard src1686.bank 179730 2308 src1686.reserve := requestWidth (by decide)

def ends1686 : List ℕ := [2313]

theorem inside1686 : Research6966.TerminalBanks.inside src1686.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1686 : Cover (Triangular src1686) 2313 2308 ends1686 := triangleCover (by decide +kernel)

def src1687 : Request := ⟨⟨⟨322,449,98,6844⟩,1023626182656,1141622570⟩,2,7,1,900619,1⟩

theorem rank1687 : P3_7_1.BankOK src1687.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_322_449_98 6844

theorem width1687 : Lower6960.HelperSource.WidthGuard src1687.bank 179730 2308 src1687.reserve := requestWidth (by decide)

def ends1687 : List ℕ := [2308, 2309, 2313]

theorem inside1687 : Research6966.TerminalBanks.inside src1687.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1687 : Cover (Triangular src1687) 2313 2308 ends1687 := triangleCover (by decide +kernel)

def src1688 : Request := ⟨⟨⟨400,558,123,7715⟩,1971918995456,2734096379⟩,4,7,1,900619,1⟩

theorem rank1688 : P3_7_1.BankOK src1688.bank := by
  simpa only [src1688, _root_.Research6969.TransitionBanks.bank134] using _root_.Research6969.TransitionBanks.rank134 7715

theorem width1688 : Lower6960.HelperSource.WidthGuard src1688.bank 179730 2308 src1688.reserve := requestWidth (by decide)

def ends1688 : List ℕ := [2308, 2313]

theorem inside1688 : Research6966.TerminalBanks.inside src1688.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1688 : Cover (Triangular src1688) 2313 2308 ends1688 := triangleCover (by decide +kernel)

def src1689 : Request := ⟨⟨⟨560,781,172,9763⟩,5388141854720,10440670587⟩,8,7,1,900619,1⟩

theorem rank1689 : P3_7_1.BankOK src1689.bank := by
  simpa only [src1689, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 9763

theorem width1689 : Lower6960.HelperSource.WidthGuard src1689.bank 179730 2308 src1689.reserve := requestWidth (by decide)

def ends1689 : List ℕ := [2313]

theorem inside1689 : Research6966.TerminalBanks.inside src1689.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1689 : Cover (Triangular src1689) 2313 2308 ends1689 := triangleCover (by decide +kernel)

def src169 : Request := ⟨⟨⟨2805,3904,854,43794⟩,668124618424320,6429426693477⟩,21,2,1,302619,27⟩

theorem rank169 : P3_7_1.BankOK src169.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3904_854 43794

theorem width169 : Lower6960.HelperSource.WidthGuard src169.bank 179730 2308 src169.reserve := requestWidth (by decide)

def ends169 : List ℕ := [2308, 2309, 2313]

theorem inside169 : Research6966.TerminalBanks.inside src169.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover169 : Cover (Triangular src169) 2313 2308 ends169 := triangleCover (by decide +kernel)

def src1690 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,13,7,1,900619,1⟩

theorem rank1690 : P3_7_1.BankOK src1690.bank := by
  simpa only [src1690, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 12355

theorem width1690 : Lower6960.HelperSource.WidthGuard src1690.bank 179730 2308 src1690.reserve := requestWidth (by decide)

def ends1690 : List ℕ := [2308, 2313]

theorem inside1690 : Research6966.TerminalBanks.inside src1690.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1690 : Cover (Triangular src1690) 2313 2308 ends1690 := triangleCover (by decide +kernel)

def src1691 : Request := ⟨⟨⟨1004,1395,315,15636⟩,31437454049280,107844841957⟩,20,7,1,900619,1⟩

theorem rank1691 : P3_7_1.BankOK src1691.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_315 15636

theorem width1691 : Lower6960.HelperSource.WidthGuard src1691.bank 179730 2308 src1691.reserve := requestWidth (by decide)

def ends1691 : List ℕ := [2308, 2309, 2313]

theorem inside1691 : Research6966.TerminalBanks.inside src1691.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1691 : Cover (Triangular src1691) 2313 2308 ends1691 := triangleCover (by decide +kernel)

def src1692 : Request := ⟨⟨⟨1202,1669,368,22229⟩,52915574931456,216711646649⟩,32,7,1,900619,1⟩

theorem rank1692 : P3_7_1.BankOK src1692.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1669_368 22229

theorem width1692 : Lower6960.HelperSource.WidthGuard src1692.bank 179730 2308 src1692.reserve := requestWidth (by decide)

def ends1692 : List ℕ := [2308, 2309, 2313]

theorem inside1692 : Research6966.TerminalBanks.inside src1692.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1692 : Cover (Triangular src1692) 2313 2308 ends1692 := triangleCover (by decide +kernel)

def src1693 : Request := ⟨⟨⟨1754,2440,537,31694⟩,164219163246592,986966790957⟩,50,7,1,900619,1⟩

theorem rank1693 : P3_7_1.BankOK src1693.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2440_537 31694

theorem width1693 : Lower6960.HelperSource.WidthGuard src1693.bank 179730 2308 src1693.reserve := requestWidth (by decide)

def ends1693 : List ℕ := [2308, 2309, 2313]

theorem inside1693 : Research6966.TerminalBanks.inside src1693.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1693 : Cover (Triangular src1693) 2313 2308 ends1693 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources26

section Pack_R6970Height2313CommonSources29

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1751 : Request := ⟨⟨⟨275,383,83,3807⟩,635228389376,603020643⟩,2,7,1,900619,41⟩

theorem rank1751 : P3_7_1.BankOK src1751.bank := by
  simpa only [src1751, _root_.Research6969.TransitionBanks.bank78] using _root_.Research6969.TransitionBanks.rank78 3807

theorem width1751 : Lower6960.HelperSource.WidthGuard src1751.bank 179730 2308 src1751.reserve := requestWidth (by decide)

def ends1751 : List ℕ := [2313]

theorem inside1751 : Research6966.TerminalBanks.inside src1751.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1751 : Cover (Triangular src1751) 2313 2308 ends1751 := triangleCover (by decide +kernel)

def src1752 : Request := ⟨⟨⟨325,452,98,4270⟩,1045036793856,1166286935⟩,4,7,1,900619,41⟩

theorem rank1752 : P3_7_1.BankOK src1752.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_325_452_98 4270

theorem width1752 : Lower6960.HelperSource.WidthGuard src1752.bank 179730 2308 src1752.reserve := requestWidth (by decide)

def ends1752 : List ℕ := [2308, 2309, 2313]

theorem inside1752 : Research6966.TerminalBanks.inside src1752.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1752 : Cover (Triangular src1752) 2313 2308 ends1752 := triangleCover (by decide +kernel)

def src1753 : Request := ⟨⟨⟨402,558,123,5419⟩,1994022977536,2734096379⟩,8,7,1,900619,41⟩

theorem rank1753 : P3_7_1.BankOK src1753.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_402_558_123 5419

theorem width1753 : Lower6960.HelperSource.WidthGuard src1753.bank 179730 2308 src1753.reserve := requestWidth (by decide)

def ends1753 : List ℕ := [2308, 2313]

theorem inside1753 : Research6966.TerminalBanks.inside src1753.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1753 : Cover (Triangular src1753) 2313 2308 ends1753 := triangleCover (by decide +kernel)

def src1754 : Request := ⟨⟨⟨691,962,212,8679⟩,10098434375680,23997864317⟩,20,7,1,900619,41⟩

theorem rank1754 : P3_7_1.BankOK src1754.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 8679

theorem width1754 : Lower6960.HelperSource.WidthGuard src1754.bank 179730 2308 src1754.reserve := requestWidth (by decide)

def ends1754 : List ℕ := [2309, 2313]

theorem inside1754 : Research6966.TerminalBanks.inside src1754.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1754 : Cover (Triangular src1754) 2313 2308 ends1754 := triangleCover (by decide +kernel)

def src1755 : Request := ⟨⟨⟨1203,1673,378,19788⟩,54100458209280,222977190790⟩,50,7,1,900619,41⟩

theorem rank1755 : P3_7_1.BankOK src1755.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1673_378 19788

theorem width1755 : Lower6960.HelperSource.WidthGuard src1755.bank 179730 2308 src1755.reserve := requestWidth (by decide)

def ends1755 : List ℕ := [2308, 2309, 2313]

theorem inside1755 : Research6966.TerminalBanks.inside src1755.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1755 : Cover (Triangular src1755) 2313 2308 ends1755 := triangleCover (by decide +kernel)

def src1756 : Request := ⟨⟨⟨3200,4461,982,50764⟩,997767489781760,11012145571636⟩,145,7,1,900619,41⟩

theorem rank1756 : P3_7_1.BankOK src1756.bank := by
  simpa only [src1756, _root_.Research6969.TransitionBanks.bank295] using _root_.Research6969.TransitionBanks.rank295 50764

theorem width1756 : Lower6960.HelperSource.WidthGuard src1756.bank 179730 2308 src1756.reserve := requestWidth (by decide)

def ends1756 : List ℕ := [2308, 2313]



theorem cover1756 : Cover (Triangular src1756) 2313 2308 ends1756 := triangleCover (by decide +kernel)

def src1757 : Request := ⟨⟨⟨3213,4459,1008,264035⟩,1027012075192320,11221829825062⟩,190,7,1,900619,41⟩

theorem rank1757 : P3_7_1.BankOK src1757.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3213_4459_1008 264035

theorem width1757 : Lower6960.HelperSource.WidthGuard src1757.bank 179730 2308 src1757.reserve := requestWidth (by decide)

def ends1757 : List ℕ := [2308, 2309, 2313]




theorem cover1757 : Cover (Triangular src1757) 2313 2308 ends1757 := triangleCover (by decide +kernel)

def src1758 : Request := ⟨⟨⟨3991,5536,1244,921434⟩,1958113417625600,26529200910168⟩,245,7,1,900619,41⟩

theorem rank1758 : P3_7_1.BankOK src1758.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3991_5536_1244 921434

theorem width1758 : Lower6960.HelperSource.WidthGuard src1758.bank 179730 2308 src1758.reserve := requestWidth (by decide)

def ends1758 : List ℕ := [2308, 2309, 2313]




theorem cover1758 : Cover (Triangular src1758) 2313 2308 ends1758 := triangleCover (by decide +kernel)

def src1759 : Request := ⟨⟨⟨5701,7946,1796,72277⟩,5751590126092288,113058766636997⟩,245,7,1,900619,41⟩

theorem rank1759 : P3_7_1.BankOK src1759.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5701_7946_1796 72277

theorem width1759 : Lower6960.HelperSource.WidthGuard src1759.bank 179730 2308 src1759.reserve := requestWidth (by decide)

def ends1759 : List ℕ := [2308, 2309, 2313]




theorem cover1759 : Cover (Triangular src1759) 2313 2308 ends1759 := triangleCover (by decide +kernel)

def src176 : Request := ⟨⟨⟨471,655,144,4282⟩,3199755878400,5168862572⟩,0,2,1,303684,40⟩

theorem rank176 : P3_7_1.BankOK src176.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_471_655_144 4282

theorem width176 : Lower6960.HelperSource.WidthGuard src176.bank 179730 2308 src176.reserve := requestWidth (by decide)

def ends176 : List ℕ := [2308, 2313]

theorem inside176 : Research6966.TerminalBanks.inside src176.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover176 : Cover (Triangular src176) 2313 2308 ends176 := triangleCover (by decide +kernel)

def src1760 : Request := ⟨⟨⟨545,756,170,6535⟩,5026035793920,9318832198⟩,10,7,2,900618,2⟩

theorem rank1760 : P3_7_1.BankOK src1760.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 6535

theorem width1760 : Lower6960.HelperSource.WidthGuard src1760.bank 179730 2308 src1760.reserve := requestWidth (by decide)

def ends1760 : List ℕ := [2308, 2309, 2313]

theorem inside1760 : Research6966.TerminalBanks.inside src1760.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1760 : Cover (Triangular src1760) 2313 2308 ends1760 := triangleCover (by decide +kernel)

def src1761 : Request := ⟨⟨⟨545,756,170,6474⟩,5026035793920,9318832198⟩,10,7,2,900618,3⟩

theorem rank1761 : P3_7_1.BankOK src1761.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 6474

theorem width1761 : Lower6960.HelperSource.WidthGuard src1761.bank 179730 2308 src1761.reserve := requestWidth (by decide)

def ends1761 : List ℕ := [2308, 2309, 2313]

theorem inside1761 : Research6966.TerminalBanks.inside src1761.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1761 : Cover (Triangular src1761) 2313 2308 ends1761 := triangleCover (by decide +kernel)

def src1762 : Request := ⟨⟨⟨550,763,170,6356⟩,5129809428480,9599221867⟩,10,7,2,900618,5⟩

theorem rank1762 : P3_7_1.BankOK src1762.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_763_170 6356

theorem width1762 : Lower6960.HelperSource.WidthGuard src1762.bank 179730 2308 src1762.reserve := requestWidth (by decide)

def ends1762 : List ℕ := [2308, 2309, 2313]

theorem inside1762 : Research6966.TerminalBanks.inside src1762.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1762 : Cover (Triangular src1762) 2313 2308 ends1762 := triangleCover (by decide +kernel)

def src1763 : Request := ⟨⟨⟨550,764,170,6073⟩,5129809428480,9639740602⟩,10,7,2,900618,10⟩

theorem rank1763 : P3_7_1.BankOK src1763.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 6073

theorem width1763 : Lower6960.HelperSource.WidthGuard src1763.bank 179730 2308 src1763.reserve := requestWidth (by decide)

def ends1763 : List ℕ := [2308, 2309, 2313]

theorem inside1763 : Research6966.TerminalBanks.inside src1763.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1763 : Cover (Triangular src1763) 2313 2308 ends1763 := triangleCover (by decide +kernel)

def src1764 : Request := ⟨⟨⟨545,756,170,5665⟩,5026035793920,9318832198⟩,10,7,2,900618,17⟩

theorem rank1764 : P3_7_1.BankOK src1764.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5665

theorem width1764 : Lower6960.HelperSource.WidthGuard src1764.bank 179730 2308 src1764.reserve := requestWidth (by decide)

def ends1764 : List ℕ := [2308, 2309, 2313]

theorem inside1764 : Research6966.TerminalBanks.inside src1764.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1764 : Cover (Triangular src1764) 2313 2308 ends1764 := triangleCover (by decide +kernel)

def src1765 : Request := ⟨⟨⟨545,756,170,5151⟩,5026035793920,9318832198⟩,10,7,2,900618,27⟩

theorem rank1765 : P3_7_1.BankOK src1765.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5151

theorem width1765 : Lower6960.HelperSource.WidthGuard src1765.bank 179730 2308 src1765.reserve := requestWidth (by decide)

def ends1765 : List ℕ := [2308, 2309, 2313]

theorem inside1765 : Research6966.TerminalBanks.inside src1765.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1765 : Cover (Triangular src1765) 2313 2308 ends1765 := triangleCover (by decide +kernel)

def src1766 : Request := ⟨⟨⟨550,764,170,4547⟩,5129809428480,9639740602⟩,10,7,2,900618,42⟩

theorem rank1766 : P3_7_1.BankOK src1766.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4547

theorem width1766 : Lower6960.HelperSource.WidthGuard src1766.bank 179730 2308 src1766.reserve := requestWidth (by decide)

def ends1766 : List ℕ := [2308, 2309, 2313]

theorem inside1766 : Research6966.TerminalBanks.inside src1766.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1766 : Cover (Triangular src1766) 2313 2308 ends1766 := triangleCover (by decide +kernel)

def src1767 : Request := ⟨⟨⟨545,756,170,6094⟩,5026035793920,9318832198⟩,10,8,2,1029278,2⟩

theorem rank1767 : P3_7_1.BankOK src1767.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 6094

theorem width1767 : Lower6960.HelperSource.WidthGuard src1767.bank 179730 2308 src1767.reserve := requestWidth (by decide)

def ends1767 : List ℕ := [2308, 2309, 2313]

theorem inside1767 : Research6966.TerminalBanks.inside src1767.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1767 : Cover (Triangular src1767) 2313 2308 ends1767 := triangleCover (by decide +kernel)

def src1768 : Request := ⟨⟨⟨544,755,170,6045⟩,5005415546880,9279237547⟩,10,8,2,1029278,3⟩

theorem rank1768 : P3_7_1.BankOK src1768.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_544_755_170 6045

theorem width1768 : Lower6960.HelperSource.WidthGuard src1768.bank 179730 2308 src1768.reserve := requestWidth (by decide)

def ends1768 : List ℕ := [2308, 2309, 2313]

theorem inside1768 : Research6966.TerminalBanks.inside src1768.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1768 : Cover (Triangular src1768) 2313 2308 ends1768 := triangleCover (by decide +kernel)

def src1769 : Request := ⟨⟨⟨545,756,170,5942⟩,5026035793920,9318832198⟩,10,8,2,1029278,5⟩

theorem rank1769 : P3_7_1.BankOK src1769.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5942

theorem width1769 : Lower6960.HelperSource.WidthGuard src1769.bank 179730 2308 src1769.reserve := requestWidth (by decide)

def ends1769 : List ℕ := [2308, 2309, 2313]

theorem inside1769 : Research6966.TerminalBanks.inside src1769.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1769 : Cover (Triangular src1769) 2313 2308 ends1769 := triangleCover (by decide +kernel)

def src177 : Request := ⟨⟨⟨470,653,144,4816⟩,3184589537280,5118308467⟩,1,2,1,303684,40⟩

theorem rank177 : P3_7_1.BankOK src177.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_470_653_144 4816

theorem width177 : Lower6960.HelperSource.WidthGuard src177.bank 179730 2308 src177.reserve := requestWidth (by decide)

def ends177 : List ℕ := [2308, 2309, 2313]

theorem inside177 : Research6966.TerminalBanks.inside src177.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover177 : Cover (Triangular src177) 2313 2308 ends177 := triangleCover (by decide +kernel)

def src1770 : Request := ⟨⟨⟨544,755,170,5698⟩,5005415546880,9279237547⟩,10,8,2,1029278,10⟩

theorem rank1770 : P3_7_1.BankOK src1770.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_544_755_170 5698

theorem width1770 : Lower6960.HelperSource.WidthGuard src1770.bank 179730 2308 src1770.reserve := requestWidth (by decide)

def ends1770 : List ℕ := [2308, 2309, 2313]

theorem inside1770 : Research6966.TerminalBanks.inside src1770.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1770 : Cover (Triangular src1770) 2313 2308 ends1770 := triangleCover (by decide +kernel)

def src1771 : Request := ⟨⟨⟨545,756,170,5368⟩,5026035793920,9318832198⟩,10,8,2,1029278,17⟩

theorem rank1771 : P3_7_1.BankOK src1771.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5368

theorem width1771 : Lower6960.HelperSource.WidthGuard src1771.bank 179730 2308 src1771.reserve := requestWidth (by decide)

def ends1771 : List ℕ := [2308, 2309, 2313]

theorem inside1771 : Research6966.TerminalBanks.inside src1771.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1771 : Cover (Triangular src1771) 2313 2308 ends1771 := triangleCover (by decide +kernel)

def src1772 : Request := ⟨⟨⟨550,764,170,4970⟩,5129809428480,9639740602⟩,10,8,2,1029278,27⟩

theorem rank1772 : P3_7_1.BankOK src1772.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4970

theorem width1772 : Lower6960.HelperSource.WidthGuard src1772.bank 179730 2308 src1772.reserve := requestWidth (by decide)

def ends1772 : List ℕ := [2308, 2309, 2313]

theorem inside1772 : Research6966.TerminalBanks.inside src1772.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1772 : Cover (Triangular src1772) 2313 2308 ends1772 := triangleCover (by decide +kernel)

def src1773 : Request := ⟨⟨⟨550,764,170,4434⟩,5129809428480,9639740602⟩,10,8,2,1029278,42⟩

theorem rank1773 : P3_7_1.BankOK src1773.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_550_764_170 4434

theorem width1773 : Lower6960.HelperSource.WidthGuard src1773.bank 179730 2308 src1773.reserve := requestWidth (by decide)

def ends1773 : List ℕ := [2308, 2309, 2313]

theorem inside1773 : Research6966.TerminalBanks.inside src1773.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1773 : Cover (Triangular src1773) 2313 2308 ends1773 := triangleCover (by decide +kernel)

def src1774 : Request := ⟨⟨⟨2603,3628,819,530820⟩,547476948910080,4914696693929⟩,4,2,1,257319,11⟩

theorem rank1774 : P3_7_1.BankOK src1774.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3628_819 530820

theorem width1774 : Lower6960.HelperSource.WidthGuard src1774.bank 179730 2308 src1774.reserve := requestWidth (by decide)

def ends1774 : List ℕ := [2308, 2309, 2313]

theorem inside1774 : Research6966.TerminalBanks.inside src1774.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1774 : Cover (Rectangle src1774 6653) 2313 2308 ends1774 := rectangleCover (by decide +kernel)

def src1775 : Request := ⟨⟨⟨2603,3628,819,530820⟩,547476948910080,4914696693929⟩,15,2,1,257319,12⟩

theorem rank1775 : P3_7_1.BankOK src1775.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3628_819 530820

theorem width1775 : Lower6960.HelperSource.WidthGuard src1775.bank 179730 2308 src1775.reserve := requestWidth (by decide)

def ends1775 : List ℕ := [2309, 2313]

theorem inside1775 : Research6966.TerminalBanks.inside src1775.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1775 : Cover (Rectangle src1775 6653) 2313 2308 ends1775 := rectangleCover (by decide +kernel)

def src1776 : Request := ⟨⟨⟨2304,3209,724,530820⟩,379378610995200,3007761756493⟩,22,2,1,257319,13⟩

theorem rank1776 : P3_7_1.BankOK src1776.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2304_3209_724 530820

theorem width1776 : Lower6960.HelperSource.WidthGuard src1776.bank 179730 2308 src1776.reserve := requestWidth (by decide)

def ends1776 : List ℕ := [2308, 2309, 2313]

theorem inside1776 : Research6966.TerminalBanks.inside src1776.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1776 : Cover (Rectangle src1776 6142) 2313 2308 ends1776 := rectangleCover (by decide +kernel)

def src1777 : Request := ⟨⟨⟨2600,3627,819,530820⟩,546063062138880,4910333421859⟩,32,2,1,257319,14⟩

theorem rank1777 : P3_7_1.BankOK src1777.bank := by
  simpa only [src1777, _root_.Research6969.TransitionBanks.bank268] using _root_.Research6969.TransitionBanks.rank268 530820

theorem width1777 : Lower6960.HelperSource.WidthGuard src1777.bank 179730 2308 src1777.reserve := requestWidth (by decide)

def ends1777 : List ℕ := [2308, 2313]

theorem inside1777 : Research6966.TerminalBanks.inside src1777.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1777 : Cover (Rectangle src1777 6142) 2313 2308 ends1777 := rectangleCover (by decide +kernel)

def src1778 : Request := ⟨⟨⟨2608,3627,819,530820⟩,549837726023680,4910333421859⟩,45,2,1,257319,15⟩

theorem rank1778 : P3_7_1.BankOK src1778.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3627_819 530820

theorem width1778 : Lower6960.HelperSource.WidthGuard src1778.bank 179730 2308 src1778.reserve := requestWidth (by decide)

def ends1778 : List ℕ := [2308, 2309, 2313]

theorem inside1778 : Research6966.TerminalBanks.inside src1778.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1778 : Cover (Rectangle src1778 7207) 2313 2308 ends1778 := rectangleCover (by decide +kernel)

def src1779 : Request := ⟨⟨⟨2302,3208,724,530820⟩,378640629760000,3004743122568⟩,45,2,1,257319,16⟩

theorem rank1779 : P3_7_1.BankOK src1779.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3208_724 530820

theorem width1779 : Lower6960.HelperSource.WidthGuard src1779.bank 179730 2308 src1779.reserve := requestWidth (by decide)

def ends1779 : List ℕ := [2308, 2309, 2313]

theorem inside1779 : Research6966.TerminalBanks.inside src1779.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1779 : Cover (Rectangle src1779 6142) 2313 2308 ends1779 := rectangleCover (by decide +kernel)

def src178 : Request := ⟨⟨⟨560,781,169,5419⟩,5316921262080,10299257375⟩,2,2,1,303684,40⟩

theorem rank178 : P3_7_1.BankOK src178.bank := by
  simpa only [src178, _root_.Research6969.TransitionBanks.bank155] using _root_.Research6969.TransitionBanks.rank155 5419

theorem width178 : Lower6960.HelperSource.WidthGuard src178.bank 179730 2308 src178.reserve := requestWidth (by decide)

def ends178 : List ℕ := [2308, 2309, 2313]

theorem inside178 : Research6966.TerminalBanks.inside src178.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover178 : Cover (Triangular src178) 2313 2308 ends178 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources29

section Pack_R6970Height2313CommonSources34

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src22 : Request := ⟨⟨⟨2748,3824,812,152023⟩,614083158081536,5782986158433⟩,325,1,1,128659,4097⟩

theorem rank22 : P3_7_1.BankOK src22.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 152023

theorem width22 : Lower6960.HelperSource.WidthGuard src22.bank 179730 2308 src22.reserve := requestWidth (by decide)

def ends22 : List ℕ := [2308, 2309, 2313]

theorem inside22 : Research6966.TerminalBanks.inside src22.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover22 : Cover (Triangular src22) 2313 2308 ends22 := triangleCover (by decide +kernel)

def src220 : Request := ⟨⟨⟨559,777,172,5413⟩,5366645522432,10269709565⟩,1,2,1,304368,37⟩

theorem rank220 : P3_7_1.BankOK src220.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_559_777_172 5413

theorem width220 : Lower6960.HelperSource.WidthGuard src220.bank 179730 2308 src220.reserve := requestWidth (by decide)

def ends220 : List ℕ := [2308, 2309, 2313]

theorem inside220 : Research6966.TerminalBanks.inside src220.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover220 : Cover (Triangular src220) 2313 2308 ends220 := triangleCover (by decide +kernel)

def src221 : Request := ⟨⟨⟨561,781,172,6858⟩,5409683537920,10440670587⟩,2,2,1,304368,37⟩

theorem rank221 : P3_7_1.BankOK src221.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 6858

theorem width221 : Lower6960.HelperSource.WidthGuard src221.bank 179730 2308 src221.reserve := requestWidth (by decide)

def ends221 : List ℕ := [2308, 2313]

theorem inside221 : Research6966.TerminalBanks.inside src221.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover221 : Cover (Triangular src221) 2313 2308 ends221 := triangleCover (by decide +kernel)

def src222 : Request := ⟨⟨⟨690,961,208,6837⟩,9921631092736,23566853761⟩,3,2,1,304368,37⟩

theorem rank222 : P3_7_1.BankOK src222.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_961_208 6837

theorem width222 : Lower6960.HelperSource.WidthGuard src222.bank 179730 2308 src222.reserve := requestWidth (by decide)

def ends222 : List ℕ := [2308, 2309, 2313]

theorem inside222 : Research6966.TerminalBanks.inside src222.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover222 : Cover (Triangular src222) 2313 2308 ends222 := triangleCover (by decide +kernel)

def src223 : Request := ⟨⟨⟨682,946,212,6847⟩,9806464417792,22737372349⟩,4,2,1,304368,37⟩

theorem rank223 : P3_7_1.BankOK src223.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_682_946_212 6847

theorem width223 : Lower6960.HelperSource.WidthGuard src223.bank 179730 2308 src223.reserve := requestWidth (by decide)

def ends223 : List ℕ := [2308, 2309, 2313]

theorem inside223 : Research6966.TerminalBanks.inside src223.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover223 : Cover (Triangular src223) 2313 2308 ends223 := triangleCover (by decide +kernel)

def src224 : Request := ⟨⟨⟨829,1151,255,9697⟩,17451995627520,49310859688⟩,8,2,1,304368,37⟩

theorem rank224 : P3_7_1.BankOK src224.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_829_1151_255 9697

theorem width224 : Lower6960.HelperSource.WidthGuard src224.bank 179730 2308 src224.reserve := requestWidth (by decide)

def ends224 : List ℕ := [2308, 2309, 2313]

theorem inside224 : Research6966.TerminalBanks.inside src224.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover224 : Cover (Triangular src224) 2313 2308 ends224 := triangleCover (by decide +kernel)

def src225 : Request := ⟨⟨⟨1200,1670,368,13865⟩,52718727069696,217129800278⟩,16,2,1,304368,37⟩

theorem rank225 : P3_7_1.BankOK src225.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1670_368 13865

theorem width225 : Lower6960.HelperSource.WidthGuard src225.bank 179730 2308 src225.reserve := requestWidth (by decide)

def ends225 : List ℕ := [2308, 2309, 2313]

theorem inside225 : Research6966.TerminalBanks.inside src225.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover225 : Cover (Triangular src225) 2313 2308 ends225 := triangleCover (by decide +kernel)

def src226 : Request := ⟨⟨⟨2103,2929,662,19788⟩,288937068199936,2090961110089⟩,32,2,1,304368,37⟩

theorem rank226 : P3_7_1.BankOK src226.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2103_2929_662 19788

theorem width226 : Lower6960.HelperSource.WidthGuard src226.bank 179730 2308 src226.reserve := requestWidth (by decide)

def ends226 : List ℕ := [2308, 2309, 2313]

theorem inside226 : Research6966.TerminalBanks.inside src226.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover226 : Cover (Triangular src226) 2313 2308 ends226 := triangleCover (by decide +kernel)

def src227 : Request := ⟨⟨⟨5708,7951,1796,57109⟩,5767441253662720,113288194826317⟩,110,2,1,304368,37⟩

theorem rank227 : P3_7_1.BankOK src227.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5708_7951_1796 57109

theorem width227 : Lower6960.HelperSource.WidthGuard src227.bank 179730 2308 src227.reserve := requestWidth (by decide)

def ends227 : List ℕ := [2308, 2309, 2313]




theorem cover227 : Cover (Triangular src227) 2313 2308 ends227 := triangleCover (by decide +kernel)

def src228 : Request := ⟨⟨⟨6932,9625,2174,81311⟩,10303123652608000,243221551977378⟩,145,2,1,304368,37⟩

theorem rank228 : P3_7_1.BankOK src228.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6932_9625_2174 81311

theorem width228 : Lower6960.HelperSource.WidthGuard src228.bank 179730 2308 src228.reserve := requestWidth (by decide)

def ends228 : List ℕ := [2309, 2313]



theorem cover228 : Cover (Triangular src228) 2313 2308 ends228 := triangleCover (by decide +kernel)

def src229 : Request := ⟨⟨⟨10051,13950,3150,91847⟩,31383663653945344,1072717072025530⟩,190,2,1,304368,37⟩

theorem rank229 : P3_7_1.BankOK src229.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10051_13950_3150 91847

theorem width229 : Lower6960.HelperSource.WidthGuard src229.bank 179730 2308 src229.reserve := requestWidth (by decide)

def ends229 : List ℕ := [2308, 2309, 2313]




theorem cover229 : Cover (Triangular src229) 2313 2308 ends229 := triangleCover (by decide +kernel)

def src23 : Request := ⟨⟨⟨1000,1391,297,57799⟩,29798654279680,102079893052⟩,115,1,1,128659,8193⟩

theorem rank23 : P3_7_1.BankOK src23.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_297 57799

theorem width23 : Lower6960.HelperSource.WidthGuard src23.bank 179730 2308 src23.reserve := requestWidth (by decide)

def ends23 : List ℕ := [2308, 2309, 2313]

theorem inside23 : Research6966.TerminalBanks.inside src23.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover23 : Cover (Triangular src23) 2313 2308 ends23 := triangleCover (by decide +kernel)

def src230 : Request := ⟨⟨⟨2601,3622,793,47836⟩,533334139076608,4767521972754⟩,15,2,1,304553,25⟩

theorem rank230 : P3_7_1.BankOK src230.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3622_793 47836

theorem width230 : Lower6960.HelperSource.WidthGuard src230.bank 179730 2308 src230.reserve := requestWidth (by decide)

def ends230 : List ℕ := [2308, 2309, 2313]

theorem inside230 : Research6966.TerminalBanks.inside src230.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover230 : Cover (Triangular src230) 2313 2308 ends230 := triangleCover (by decide +kernel)

def src231 : Request := ⟨⟨⟨2992,4172,896,92007⟩,800631134617600,8264657754455⟩,21,2,1,304553,25⟩

theorem rank231 : P3_7_1.BankOK src231.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2992_4172_896 92007

theorem width231 : Lower6960.HelperSource.WidthGuard src231.bank 179730 2308 src231.reserve := requestWidth (by decide)

def ends231 : List ℕ := [2308, 2309, 2313]

theorem inside231 : Research6966.TerminalBanks.inside src231.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover231 : Cover (Triangular src231) 2313 2308 ends231 := triangleCover (by decide +kernel)

def src232 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,0,2,1,304585,36⟩

theorem rank232 : P3_7_1.BankOK src232.bank := by
  simpa only [src232, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 5419

theorem width232 : Lower6960.HelperSource.WidthGuard src232.bank 179730 2308 src232.reserve := requestWidth (by decide)

def ends232 : List ℕ := [2308, 2313]

theorem inside232 : Research6966.TerminalBanks.inside src232.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover232 : Cover (Triangular src232) 2313 2308 ends232 := triangleCover (by decide +kernel)

def src233 : Request := ⟨⟨⟨561,781,172,6096⟩,5409683537920,10440670587⟩,1,2,1,304585,36⟩

theorem rank233 : P3_7_1.BankOK src233.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 6096

theorem width233 : Lower6960.HelperSource.WidthGuard src233.bank 179730 2308 src233.reserve := requestWidth (by decide)

def ends233 : List ℕ := [2308, 2309, 2313]

theorem inside233 : Research6966.TerminalBanks.inside src233.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover233 : Cover (Triangular src233) 2313 2308 ends233 := triangleCover (by decide +kernel)

def src234 : Request := ⟨⟨⟨693,962,217,6096⟩,10344420868096,24434817260⟩,2,2,1,304585,36⟩

theorem rank234 : P3_7_1.BankOK src234.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_217 6096

theorem width234 : Lower6960.HelperSource.WidthGuard src234.bank 179730 2308 src234.reserve := requestWidth (by decide)

def ends234 : List ℕ := [2308, 2309, 2313]

theorem inside234 : Research6966.TerminalBanks.inside src234.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover234 : Cover (Triangular src234) 2313 2308 ends234 := triangleCover (by decide +kernel)

def src235 : Request := ⟨⟨⟨692,962,212,6858⟩,10131154665472,23997864317⟩,3,2,1,304585,36⟩

theorem rank235 : P3_7_1.BankOK src235.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_212 6858

theorem width235 : Lower6960.HelperSource.WidthGuard src235.bank 179730 2308 src235.reserve := requestWidth (by decide)

def ends235 : List ℕ := [2308, 2309, 2313]

theorem inside235 : Research6966.TerminalBanks.inside src235.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover235 : Cover (Triangular src235) 2313 2308 ends235 := triangleCover (by decide +kernel)

def src236 : Request := ⟨⟨⟨693,962,213,7781⟩,10200167219200,24085532067⟩,4,2,1,304585,36⟩

theorem rank236 : P3_7_1.BankOK src236.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_693_962_213 7781

theorem width236 : Lower6960.HelperSource.WidthGuard src236.bank 179730 2308 src236.reserve := requestWidth (by decide)

def ends236 : List ℕ := [2308, 2309, 2313]

theorem inside236 : Research6966.TerminalBanks.inside src236.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover236 : Cover (Triangular src236) 2313 2308 ends236 := triangleCover (by decide +kernel)

def src237 : Request := ⟨⟨⟨826,1151,253,8679⟩,17208151113728,49010625289⟩,6,2,1,304585,36⟩

theorem rank237 : P3_7_1.BankOK src237.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_253 8679

theorem width237 : Lower6960.HelperSource.WidthGuard src237.bank 179730 2308 src237.reserve := requestWidth (by decide)

def ends237 : List ℕ := [2308, 2309, 2313]

theorem inside237 : Research6966.TerminalBanks.inside src237.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover237 : Cover (Triangular src237) 2313 2308 ends237 := triangleCover (by decide +kernel)

def src238 : Request := ⟨⟨⟨1002,1395,307,10983⟩,30694534807552,105715278267⟩,10,2,1,304585,36⟩

theorem rank238 : P3_7_1.BankOK src238.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_307 10983

theorem width238 : Lower6960.HelperSource.WidthGuard src238.bank 179730 2308 src238.reserve := requestWidth (by decide)

def ends238 : List ℕ := [2309, 2313]

theorem inside238 : Research6966.TerminalBanks.inside src238.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover238 : Cover (Triangular src238) 2313 2308 ends238 := triangleCover (by decide +kernel)

def src239 : Request := ⟨⟨⟨1758,2441,551,17693⟩,168308123893760,1008217465165⟩,25,2,1,304585,36⟩

theorem rank239 : P3_7_1.BankOK src239.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1758_2441_551 17693

theorem width239 : Lower6960.HelperSource.WidthGuard src239.bank 179730 2308 src239.reserve := requestWidth (by decide)

def ends239 : List ℕ := [2308, 2309, 2313]

theorem inside239 : Research6966.TerminalBanks.inside src239.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover239 : Cover (Triangular src239) 2313 2308 ends239 := triangleCover (by decide +kernel)

def src24 : Request := ⟨⟨⟨720,1001,214,124745⟩,11149381468160,27467889943⟩,85,1,1,128659,32769⟩

theorem rank24 : P3_7_1.BankOK src24.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_720_1001_214 124745

theorem width24 : Lower6960.HelperSource.WidthGuard src24.bank 179730 2308 src24.reserve := requestWidth (by decide)

def ends24 : List ℕ := [2308, 2309, 2313]

theorem inside24 : Research6966.TerminalBanks.inside src24.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover24 : Cover (Triangular src24) 2313 2308 ends24 := triangleCover (by decide +kernel)

def src240 : Request := ⟨⟨⟨2604,3627,819,25043⟩,547948674416640,4910333421859⟩,40,2,1,304585,36⟩

theorem rank240 : P3_7_1.BankOK src240.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3627_819 25043

theorem width240 : Lower6960.HelperSource.WidthGuard src240.bank 179730 2308 src240.reserve := requestWidth (by decide)

def ends240 : List ℕ := [2308, 2309, 2313]

theorem inside240 : Research6966.TerminalBanks.inside src240.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover240 : Cover (Triangular src240) 2313 2308 ends240 := triangleCover (by decide +kernel)

def src241 : Request := ⟨⟨⟨5725,7951,1796,64247⟩,5806032948035584,113288194826317⟩,110,2,1,304585,36⟩

theorem rank241 : P3_7_1.BankOK src241.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5725_7951_1796 64247

theorem width241 : Lower6960.HelperSource.WidthGuard src241.bank 179730 2308 src241.reserve := requestWidth (by decide)

def ends241 : List ℕ := [2309, 2313]



theorem cover241 : Cover (Triangular src241) 2313 2308 ends241 := triangleCover (by decide +kernel)

def src242 : Request := ⟨⟨⟨10047,13950,3078,103900⟩,30810471804174336,1053602214882697⟩,190,2,1,304585,36⟩

theorem rank242 : P3_7_1.BankOK src242.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10047_13950_3078 103900

theorem width242 : Lower6960.HelperSource.WidthGuard src242.bank 179730 2308 src242.reserve := requestWidth (by decide)

def ends242 : List ℕ := [2308, 2309, 2313]




theorem cover242 : Cover (Triangular src242) 2313 2308 ends242 := triangleCover (by decide +kernel)

def src243 : Request := ⟨⟨⟨559,777,169,6096⟩,5295730851840,10130698125⟩,0,2,1,304795,35⟩

theorem rank243 : P3_7_1.BankOK src243.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_559_777_169 6096

theorem width243 : Lower6960.HelperSource.WidthGuard src243.bank 179730 2308 src243.reserve := requestWidth (by decide)

def ends243 : List ℕ := [2308, 2309, 2313]

theorem inside243 : Research6966.TerminalBanks.inside src243.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover243 : Cover (Triangular src243) 2313 2308 ends243 := triangleCover (by decide +kernel)

def src244 : Request := ⟨⟨⟨692,963,217,6096⟩,10311018217472,24516657294⟩,1,2,1,304795,35⟩

theorem rank244 : P3_7_1.BankOK src244.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_963_217 6096

theorem width244 : Lower6960.HelperSource.WidthGuard src244.bank 179730 2308 src244.reserve := requestWidth (by decide)

def ends244 : List ℕ := [2308, 2313]

theorem inside244 : Research6966.TerminalBanks.inside src244.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover244 : Cover (Triangular src244) 2313 2308 ends244 := triangleCover (by decide +kernel)

def src245 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,2,2,1,304795,35⟩

theorem rank245 : P3_7_1.BankOK src245.bank := by
  simpa only [src245, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 6858

theorem width245 : Lower6960.HelperSource.WidthGuard src245.bank 179730 2308 src245.reserve := requestWidth (by decide)

def ends245 : List ℕ := [2308, 2313]

theorem inside245 : Research6966.TerminalBanks.inside src245.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover245 : Cover (Triangular src245) 2313 2308 ends245 := triangleCover (by decide +kernel)

def src246 : Request := ⟨⟨⟨691,962,212,7715⟩,10098434375680,23997864317⟩,3,2,1,304795,35⟩

theorem rank246 : P3_7_1.BankOK src246.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 7715

theorem width246 : Lower6960.HelperSource.WidthGuard src246.bank 179730 2308 src246.reserve := requestWidth (by decide)

def ends246 : List ℕ := [2308, 2309, 2313]

theorem inside246 : Research6966.TerminalBanks.inside src246.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover246 : Cover (Triangular src246) 2313 2308 ends246 := triangleCover (by decide +kernel)

def src247 : Request := ⟨⟨⟨823,1143,253,7685⟩,17068623134720,47923151213⟩,4,2,1,304795,35⟩

theorem rank247 : P3_7_1.BankOK src247.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_823_1143_253 7685

theorem width247 : Lower6960.HelperSource.WidthGuard src247.bank 179730 2308 src247.reserve := requestWidth (by decide)

def ends247 : List ℕ := [2308, 2309, 2313]

theorem inside247 : Research6966.TerminalBanks.inside src247.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover247 : Cover (Triangular src247) 2313 2308 ends247 := triangleCover (by decide +kernel)

def src248 : Request := ⟨⟨⟨823,1143,253,9705⟩,17068623134720,47923151213⟩,6,2,1,304795,35⟩

theorem rank248 : P3_7_1.BankOK src248.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_823_1143_253 9705

theorem width248 : Lower6960.HelperSource.WidthGuard src248.bank 179730 2308 src248.reserve := requestWidth (by decide)

def ends248 : List ℕ := [2308, 2309, 2313]

theorem inside248 : Research6966.TerminalBanks.inside src248.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover248 : Cover (Triangular src248) 2313 2308 ends248 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources34

section Pack_R6970Height2313CommonSources36

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src278 : Request := ⟨⟨⟨685,955,208,7642⟩,9761649852416,23097088014⟩,0,2,1,305390,32⟩

theorem rank278 : P3_7_1.BankOK src278.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_685_955_208 7642

theorem width278 : Lower6960.HelperSource.WidthGuard src278.bank 179730 2308 src278.reserve := requestWidth (by decide)

def ends278 : List ℕ := [2308, 2309, 2313]

theorem inside278 : Research6966.TerminalBanks.inside src278.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover278 : Cover (Triangular src278) 2313 2308 ends278 := triangleCover (by decide +kernel)

def src279 : Request := ⟨⟨⟨827,1151,260,7715⟩,17614256996352,50057971890⟩,1,2,1,305390,32⟩

theorem rank279 : P3_7_1.BankOK src279.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_260 7715

theorem width279 : Lower6960.HelperSource.WidthGuard src279.bank 179730 2308 src279.reserve := requestWidth (by decide)

def ends279 : List ℕ := [2309, 2313]

theorem inside279 : Research6966.TerminalBanks.inside src279.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover279 : Cover (Triangular src279) 2313 2308 ends279 := triangleCover (by decide +kernel)

def src28 : Request := ⟨⟨⟨3004,4178,897,81611⟩,808515669327872,8310192816141⟩,6,2,1,257319,23⟩

theorem rank28 : P3_7_1.BankOK src28.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3004_4178_897 81611

theorem width28 : Lower6960.HelperSource.WidthGuard src28.bank 179730 2308 src28.reserve := requestWidth (by decide)

def ends28 : List ℕ := [2308, 2309, 2313]

theorem inside28 : Research6966.TerminalBanks.inside src28.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover28 : Cover (Triangular src28) 2313 2308 ends28 := triangleCover (by decide +kernel)

def src280 : Request := ⟨⟨⟨826,1151,253,8679⟩,17208151113728,49010625289⟩,2,2,1,305390,32⟩

theorem rank280 : P3_7_1.BankOK src280.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_253 8679

theorem width280 : Lower6960.HelperSource.WidthGuard src280.bank 179730 2308 src280.reserve := requestWidth (by decide)

def ends280 : List ℕ := [2308, 2309, 2313]

theorem inside280 : Research6966.TerminalBanks.inside src280.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover280 : Cover (Triangular src280) 2313 2308 ends280 := triangleCover (by decide +kernel)

def src281 : Request := ⟨⟨⟨825,1147,253,9740⟩,17161575202816,48464812563⟩,3,2,1,305390,32⟩

theorem rank281 : P3_7_1.BankOK src281.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_825_1147_253 9740

theorem width281 : Lower6960.HelperSource.WidthGuard src281.bank 179730 2308 src281.reserve := requestWidth (by decide)

def ends281 : List ℕ := [2308, 2309, 2313]

theorem inside281 : Research6966.TerminalBanks.inside src281.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover281 : Cover (Triangular src281) 2313 2308 ends281 := triangleCover (by decide +kernel)

def src282 : Request := ⟨⟨⟨999,1387,307,9755⟩,30489252462592,103776832835⟩,4,2,1,305390,32⟩

theorem rank282 : P3_7_1.BankOK src282.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_999_1387_307 9755

theorem width282 : Lower6960.HelperSource.WidthGuard src282.bank 179730 2308 src282.reserve := requestWidth (by decide)

def ends282 : List ℕ := [2308, 2309, 2313]

theorem inside282 : Research6966.TerminalBanks.inside src282.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover282 : Cover (Triangular src282) 2313 2308 ends282 := triangleCover (by decide +kernel)

def src283 : Request := ⟨⟨⟨1001,1395,307,12355⟩,30626026618880,105715278267⟩,6,2,1,305390,32⟩

theorem rank283 : P3_7_1.BankOK src283.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1001_1395_307 12355

theorem width283 : Lower6960.HelperSource.WidthGuard src283.bank 179730 2308 src283.reserve := requestWidth (by decide)

def ends283 : List ℕ := [2308, 2309, 2313]

theorem inside283 : Research6966.TerminalBanks.inside src283.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover283 : Cover (Triangular src283) 2313 2308 ends283 := triangleCover (by decide +kernel)

def src284 : Request := ⟨⟨⟨1205,1674,372,15951⟩,53649283481600,220652458042⟩,10,2,1,305390,32⟩

theorem rank284 : P3_7_1.BankOK src284.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_372 15951

theorem width284 : Lower6960.HelperSource.WidthGuard src284.bank 179730 2308 src284.reserve := requestWidth (by decide)

def ends284 : List ℕ := [2308, 2309, 2313]

theorem inside284 : Research6966.TerminalBanks.inside src284.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover284 : Cover (Triangular src284) 2313 2308 ends284 := triangleCover (by decide +kernel)

def src285 : Request := ⟨⟨⟨2105,2930,645,28173⟩,283904392560640,2051392203643⟩,25,2,1,305390,32⟩

theorem rank285 : P3_7_1.BankOK src285.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2930_645 28173

theorem width285 : Lower6960.HelperSource.WidthGuard src285.bank 179730 2308 src285.reserve := requestWidth (by decide)

def ends285 : List ℕ := [2308, 2309, 2313]

theorem inside285 : Research6966.TerminalBanks.inside src285.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover285 : Cover (Triangular src285) 2313 2308 ends285 := triangleCover (by decide +kernel)

def src286 : Request := ⟨⟨⟨4821,6697,1512,50764⟩,3466911079464960,57008284046562⟩,65,2,1,305390,32⟩

theorem rank286 : P3_7_1.BankOK src286.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4821_6697_1512 50764

theorem width286 : Lower6960.HelperSource.WidthGuard src286.bank 179730 2308 src286.reserve := requestWidth (by decide)

def ends286 : List ℕ := [2308, 2309, 2313]




theorem cover286 : Cover (Triangular src286) 2313 2308 ends286 := triangleCover (by decide +kernel)

def src287 : Request := ⟨⟨⟨7244,10107,2223,102908⟩,11565308219228160,289664566465168⟩,110,2,1,305390,32⟩

theorem rank287 : P3_7_1.BankOK src287.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7244_10107_2223 102908

theorem width287 : Lower6960.HelperSource.WidthGuard src287.bank 179730 2308 src287.reserve := requestWidth (by decide)

def ends287 : List ℕ := [2308, 2313]



theorem cover287 : Cover (Triangular src287) 2313 2308 ends287 := triangleCover (by decide +kernel)

def src288 : Request := ⟨⟨⟨10053,13952,3150,103706⟩,31397668750884864,1073212809809009⟩,145,2,1,305390,32⟩

theorem rank288 : P3_7_1.BankOK src288.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10053_13952_3150 103706

theorem width288 : Lower6960.HelperSource.WidthGuard src288.bank 179730 2308 src288.reserve := requestWidth (by decide)

def ends288 : List ℕ := [2308, 2309, 2313]




theorem cover288 : Cover (Triangular src288) 2313 2308 ends288 := triangleCover (by decide +kernel)

def src289 : Request := ⟨⟨⟨690,963,212,8679⟩,10065769922560,24078187611⟩,0,2,1,305576,31⟩

theorem rank289 : P3_7_1.BankOK src289.bank := by
  simpa only [src289, _root_.Research6969.TransitionBanks.bank196] using _root_.Research6969.TransitionBanks.rank196 8679

theorem width289 : Lower6960.HelperSource.WidthGuard src289.bank 179730 2308 src289.reserve := requestWidth (by decide)

def ends289 : List ℕ := [2308, 2309, 2313]

theorem inside289 : Research6966.TerminalBanks.inside src289.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover289 : Cover (Triangular src289) 2313 2308 ends289 := triangleCover (by decide +kernel)

def src29 : Request := ⟨⟨⟨2926,4066,890,91497⟩,757775095824384,7567966147450⟩,7,2,1,257515,23⟩

theorem rank29 : P3_7_1.BankOK src29.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2926_4066_890 91497

theorem width29 : Lower6960.HelperSource.WidthGuard src29.bank 179730 2308 src29.reserve := requestWidth (by decide)

def ends29 : List ℕ := [2308, 2309, 2313]

theorem inside29 : Research6966.TerminalBanks.inside src29.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover29 : Cover (Triangular src29) 2313 2308 ends29 := triangleCover (by decide +kernel)

def src290 : Request := ⟨⟨⟨828,1151,253,8679⟩,17301502689280,49010625289⟩,1,2,1,305576,31⟩

theorem rank290 : P3_7_1.BankOK src290.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_253 8679

theorem width290 : Lower6960.HelperSource.WidthGuard src290.bank 179730 2308 src290.reserve := requestWidth (by decide)

def ends290 : List ℕ := [2308, 2309, 2313]

theorem inside290 : Research6966.TerminalBanks.inside src290.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover290 : Cover (Triangular src290) 2313 2308 ends290 := triangleCover (by decide +kernel)

def src291 : Request := ⟨⟨⟨823,1143,253,9758⟩,17068623134720,47923151213⟩,2,2,1,305576,31⟩

theorem rank291 : P3_7_1.BankOK src291.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_823_1143_253 9758

theorem width291 : Lower6960.HelperSource.WidthGuard src291.bank 179730 2308 src291.reserve := requestWidth (by decide)

def ends291 : List ℕ := [2308, 2309, 2313]

theorem inside291 : Research6966.TerminalBanks.inside src291.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover291 : Cover (Triangular src291) 2313 2308 ends291 := triangleCover (by decide +kernel)

def src292 : Request := ⟨⟨⟨1000,1391,307,10962⟩,30557599170560,104743003887⟩,4,2,1,305576,31⟩

theorem rank292 : P3_7_1.BankOK src292.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_307 10962

theorem width292 : Lower6960.HelperSource.WidthGuard src292.bank 179730 2308 src292.reserve := requestWidth (by decide)

def ends292 : List ℕ := [2308, 2309, 2313]

theorem inside292 : Research6966.TerminalBanks.inside src292.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover292 : Cover (Triangular src292) 2313 2308 ends292 := triangleCover (by decide +kernel)

def src293 : Request := ⟨⟨⟨1201,1670,368,12350⟩,52817102635008,217129800278⟩,6,2,1,305576,31⟩

theorem rank293 : P3_7_1.BankOK src293.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1670_368 12350

theorem width293 : Lower6960.HelperSource.WidthGuard src293.bank 179730 2308 src293.reserve := requestWidth (by decide)

def ends293 : List ℕ := [2308, 2309, 2313]

theorem inside293 : Research6966.TerminalBanks.inside src293.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover293 : Cover (Triangular src293) 2313 2308 ends293 := triangleCover (by decide +kernel)

def src294 : Request := ⟨⟨⟨1200,1674,368,15636⟩,52718727069696,218807905514⟩,8,2,1,305576,31⟩

theorem rank294 : P3_7_1.BankOK src294.bank := by
  simpa only [src294, _root_.Research6969.TransitionBanks.bank228] using _root_.Research6969.TransitionBanks.rank228 15636

theorem width294 : Lower6960.HelperSource.WidthGuard src294.bank 179730 2308 src294.reserve := requestWidth (by decide)

def ends294 : List ℕ := [2308, 2309, 2313]

theorem inside294 : Research6966.TerminalBanks.inside src294.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover294 : Cover (Triangular src294) 2313 2308 ends294 := triangleCover (by decide +kernel)

def src295 : Request := ⟨⟨⟨1452,2023,445,15636⟩,93286344425472,466511127281⟩,10,2,1,305576,31⟩

theorem rank295 : P3_7_1.BankOK src295.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1452_2023_445 15636

theorem width295 : Lower6960.HelperSource.WidthGuard src295.bank 179730 2308 src295.reserve := requestWidth (by decide)

def ends295 : List ℕ := [2308, 2309, 2313]

theorem inside295 : Research6966.TerminalBanks.inside src295.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover295 : Cover (Triangular src295) 2313 2308 ends295 := triangleCover (by decide +kernel)

def src296 : Request := ⟨⟨⟨1757,2441,551,20205⟩,168093600972800,1008217465165⟩,16,2,1,305576,31⟩

theorem rank296 : P3_7_1.BankOK src296.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2441_551 20205

theorem width296 : Lower6960.HelperSource.WidthGuard src296.bank 179730 2308 src296.reserve := requestWidth (by decide)

def ends296 : List ℕ := [2308, 2309, 2313]

theorem inside296 : Research6966.TerminalBanks.inside src296.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover296 : Cover (Triangular src296) 2313 2308 ends296 := triangleCover (by decide +kernel)

def src297 : Request := ⟨⟨⟨3219,4472,1000,40885⟩,1025113218088960,11257719822725⟩,40,2,1,305576,31⟩

theorem rank297 : P3_7_1.BankOK src297.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3219_4472_1000 40885

theorem width297 : Lower6960.HelperSource.WidthGuard src297.bank 179730 2308 src297.reserve := requestWidth (by decide)

def ends297 : List ℕ := [2308, 2309, 2313]




theorem cover297 : Cover (Triangular src297) 2313 2308 ends297 := triangleCover (by decide +kernel)

def src298 : Request := ⟨⟨⟨10000,13920,3070,128598⟩,30428373265940480,1044203862130693⟩,145,2,1,305576,31⟩

theorem rank298 : P3_7_1.BankOK src298.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13920_3070 128598

theorem width298 : Lower6960.HelperSource.WidthGuard src298.bank 179730 2308 src298.reserve := requestWidth (by decide)

def ends298 : List ℕ := [2308, 2309, 2313]




theorem cover298 : Cover (Triangular src298) 2313 2308 ends298 := triangleCover (by decide +kernel)

def src299 : Request := ⟨⟨⟨2887,4021,882,68142⟩,730324645445632,7250467565269⟩,15,2,1,305579,23⟩

theorem rank299 : P3_7_1.BankOK src299.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2887_4021_882 68142

theorem width299 : Lower6960.HelperSource.WidthGuard src299.bank 179730 2308 src299.reserve := requestWidth (by decide)

def ends299 : List ℕ := [2308, 2309, 2313]

theorem inside299 : Research6966.TerminalBanks.inside src299.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover299 : Cover (Triangular src299) 2313 2308 ends299 := triangleCover (by decide +kernel)

def src3 : Request := ⟨⟨⟨2606,3627,793,28173⟩,535631510110208,4788739883894⟩,45,1,1,128659,41⟩

theorem rank3 : P3_7_1.BankOK src3.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3627_793 28173

theorem width3 : Lower6960.HelperSource.WidthGuard src3.bank 179730 2308 src3.reserve := requestWidth (by decide)

def ends3 : List ℕ := [2308, 2309, 2313]

theorem inside3 : Research6966.TerminalBanks.inside src3.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover3 : Cover (Triangular src3) 2313 2308 ends3 := triangleCover (by decide +kernel)

def src30 : Request := ⟨⟨⟨2992,4160,900,122255⟩,803353782648832,8216917752362⟩,8,2,1,257515,23⟩

theorem rank30 : P3_7_1.BankOK src30.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2992_4160_900 122255

theorem width30 : Lower6960.HelperSource.WidthGuard src30.bank 179730 2308 src30.reserve := requestWidth (by decide)

def ends30 : List ℕ := [2308, 2309, 2313]

theorem inside30 : Research6966.TerminalBanks.inside src30.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover30 : Cover (Triangular src30) 2313 2308 ends30 := triangleCover (by decide +kernel)

def src300 : Request := ⟨⟨⟨2997,4180,900,243134⟩,806359322591232,8344716709602⟩,21,2,1,305579,23⟩

theorem rank300 : P3_7_1.BankOK src300.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2997_4180_900 243134

theorem width300 : Lower6960.HelperSource.WidthGuard src300.bank 179730 2308 src300.reserve := requestWidth (by decide)

def ends300 : List ℕ := [2308, 2309, 2313]

theorem inside300 : Research6966.TerminalBanks.inside src300.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover300 : Cover (Triangular src300) 2313 2308 ends300 := triangleCover (by decide +kernel)

def src301 : Request := ⟨⟨⟨705,982,216,10983⟩,10712231706624,26013996872⟩,0,2,1,305757,30⟩

theorem rank301 : P3_7_1.BankOK src301.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_705_982_216 10983

theorem width301 : Lower6960.HelperSource.WidthGuard src301.bank 179730 2308 src301.reserve := requestWidth (by decide)

def ends301 : List ℕ := [2309, 2313]

theorem inside301 : Research6966.TerminalBanks.inside src301.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover301 : Cover (Triangular src301) 2313 2308 ends301 := triangleCover (by decide +kernel)

def src302 : Request := ⟨⟨⟨817,1135,253,9769⟩,16791364960256,46852217617⟩,1,2,1,305757,30⟩

theorem rank302 : P3_7_1.BankOK src302.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_817_1135_253 9769

theorem width302 : Lower6960.HelperSource.WidthGuard src302.bank 179730 2308 src302.reserve := requestWidth (by decide)

def ends302 : List ℕ := [2308, 2309, 2313]

theorem inside302 : Research6966.TerminalBanks.inside src302.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover302 : Cover (Triangular src302) 2313 2308 ends302 := triangleCover (by decide +kernel)

def src303 : Request := ⟨⟨⟨989,1379,301,12151⟩,29368050515968,100313940775⟩,3,2,1,305757,30⟩

theorem rank303 : P3_7_1.BankOK src303.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_989_1379_301 12151

theorem width303 : Lower6960.HelperSource.WidthGuard src303.bank 179730 2308 src303.reserve := requestWidth (by decide)

def ends303 : List ℕ := [2308, 2309, 2313]

theorem inside303 : Research6966.TerminalBanks.inside src303.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover303 : Cover (Triangular src303) 2313 2308 ends303 := triangleCover (by decide +kernel)

def src304 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,4,2,1,305757,30⟩

theorem rank304 : P3_7_1.BankOK src304.bank := by
  simpa only [src304, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 13899

theorem width304 : Lower6960.HelperSource.WidthGuard src304.bank 179730 2308 src304.reserve := requestWidth (by decide)

def ends304 : List ℕ := [2308, 2309, 2313]

theorem inside304 : Research6966.TerminalBanks.inside src304.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover304 : Cover (Triangular src304) 2313 2308 ends304 := triangleCover (by decide +kernel)

def src305 : Request := ⟨⟨⟨1193,1658,368,13881⟩,52032806584320,212148065594⟩,6,2,1,305757,30⟩

theorem rank305 : P3_7_1.BankOK src305.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_368 13881

theorem width305 : Lower6960.HelperSource.WidthGuard src305.bank 179730 2308 src305.reserve := requestWidth (by decide)

def ends305 : List ℕ := [2308, 2309, 2313]

theorem inside305 : Research6966.TerminalBanks.inside src305.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover305 : Cover (Triangular src305) 2313 2308 ends305 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources36

section Pack_R6970Height2313CommonSources37

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src306 : Request := ⟨⟨⟨1453,2021,447,17744⟩,93748415430656,466651512208⟩,10,2,1,305757,30⟩

theorem rank306 : P3_7_1.BankOK src306.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2021_447 17744

theorem width306 : Lower6960.HelperSource.WidthGuard src306.bank 179730 2308 src306.reserve := requestWidth (by decide)

def ends306 : List ℕ := [2308, 2309, 2313]

theorem inside306 : Research6966.TerminalBanks.inside src306.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover306 : Cover (Triangular src306) 2313 2308 ends306 := triangleCover (by decide +kernel)

def src307 : Request := ⟨⟨⟨1754,2441,541,29320⟩,165146013728768,993986736440⟩,16,2,1,305757,30⟩

theorem rank307 : P3_7_1.BankOK src307.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2441_541 29320

theorem width307 : Lower6960.HelperSource.WidthGuard src307.bank 179730 2308 src307.reserve := requestWidth (by decide)

def ends307 : List ℕ := [2308, 2309, 2313]

theorem inside307 : Research6966.TerminalBanks.inside src307.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover307 : Cover (Triangular src307) 2313 2308 ends307 := triangleCover (by decide +kernel)

def src308 : Request := ⟨⟨⟨3200,4449,982,35565⟩,997767489781760,10917047065016⟩,32,2,1,305757,30⟩

theorem rank308 : P3_7_1.BankOK src308.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4449_982 35565

theorem width308 : Lower6960.HelperSource.WidthGuard src308.bank 179730 2308 src308.reserve := requestWidth (by decide)

def ends308 : List ℕ := [2308, 2309, 2313]




theorem cover308 : Cover (Triangular src308) 2313 2308 ends308 := triangleCover (by decide +kernel)

def src309 : Request := ⟨⟨⟨6928,9619,2126,82082⟩,10117055495536640,238556846527736⟩,85,2,1,305757,30⟩

theorem rank309 : P3_7_1.BankOK src309.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6928_9619_2126 82082

theorem width309 : Lower6960.HelperSource.WidthGuard src309.bank 179730 2308 src309.reserve := requestWidth (by decide)

def ends309 : List ℕ := [2308, 2309, 2313]




theorem cover309 : Cover (Triangular src309) 2313 2308 ends309 := triangleCover (by decide +kernel)

def src31 : Request := ⟨⟨⟨2992,4160,900,122255⟩,803353782648832,8216917752362⟩,8,2,1,257515,23⟩

theorem rank31 : P3_7_1.BankOK src31.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2992_4160_900 122255

theorem width31 : Lower6960.HelperSource.WidthGuard src31.bank 179730 2308 src31.reserve := requestWidth (by decide)

def ends31 : List ℕ := [2308, 2309, 2313]

theorem inside31 : Research6966.TerminalBanks.inside src31.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover31 : Cover (Triangular src31) 2313 2308 ends31 := triangleCover (by decide +kernel)

def src310 : Request := ⟨⟨⟨8301,11580,2548,115771⟩,17404404995719168,499263802703202⟩,110,2,1,305757,30⟩

theorem rank310 : P3_7_1.BankOK src310.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8301_11580_2548 115771

theorem width310 : Lower6960.HelperSource.WidthGuard src310.bank 179730 2308 src310.reserve := requestWidth (by decide)

def ends310 : List ℕ := [2308, 2309, 2313]




theorem cover310 : Cover (Triangular src310) 2313 2308 ends310 := triangleCover (by decide +kernel)

def src311 : Request := ⟨⟨⟨10499,14649,3223,185441⟩,35212191177113600,1278297696123811⟩,145,2,1,305757,30⟩

theorem rank311 : P3_7_1.BankOK src311.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10499_14649_3223 185441

theorem width311 : Lower6960.HelperSource.WidthGuard src311.bank 179730 2308 src311.reserve := requestWidth (by decide)

def ends311 : List ℕ := [2308, 2313]



theorem cover311 : Cover (Triangular src311) 2313 2308 ends311 := triangleCover (by decide +kernel)

def src312 : Request := ⟨⟨⟨2887,4021,882,67802⟩,730324645445632,7250467565269⟩,15,2,1,305811,23⟩

theorem rank312 : P3_7_1.BankOK src312.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2887_4021_882 67802

theorem width312 : Lower6960.HelperSource.WidthGuard src312.bank 179730 2308 src312.reserve := requestWidth (by decide)

def ends312 : List ℕ := [2308, 2309, 2313]

theorem inside312 : Research6966.TerminalBanks.inside src312.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover312 : Cover (Triangular src312) 2313 2308 ends312 := triangleCover (by decide +kernel)

def src313 : Request := ⟨⟨⟨2997,4180,898,157220⟩,804993131872256,8330240596276⟩,20,2,1,305811,23⟩

theorem rank313 : P3_7_1.BankOK src313.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2997_4180_898 157220

theorem width313 : Lower6960.HelperSource.WidthGuard src313.bank 179730 2308 src313.reserve := requestWidth (by decide)

def ends313 : List ℕ := [2308, 2309, 2313]

theorem inside313 : Research6966.TerminalBanks.inside src313.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover313 : Cover (Triangular src313) 2313 2308 ends313 := triangleCover (by decide +kernel)

def src314 : Request := ⟨⟨⟨826,1149,255,9848⟩,17310966349824,49035695912⟩,0,2,1,305932,29⟩

theorem rank314 : P3_7_1.BankOK src314.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1149_255 9848

theorem width314 : Lower6960.HelperSource.WidthGuard src314.bank 179730 2308 src314.reserve := requestWidth (by decide)

def ends314 : List ℕ := [2308, 2309, 2313]

theorem inside314 : Research6966.TerminalBanks.inside src314.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover314 : Cover (Triangular src314) 2313 2308 ends314 := triangleCover (by decide +kernel)

def src315 : Request := ⟨⟨⟨1000,1395,307,10983⟩,30557599170560,105715278267⟩,1,2,1,305932,29⟩

theorem rank315 : P3_7_1.BankOK src315.bank := by
  simpa only [src315, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 10983

theorem width315 : Lower6960.HelperSource.WidthGuard src315.bank 179730 2308 src315.reserve := requestWidth (by decide)

def ends315 : List ℕ := [2309, 2313]

theorem inside315 : Research6966.TerminalBanks.inside src315.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover315 : Cover (Triangular src315) 2313 2308 ends315 := triangleCover (by decide +kernel)

def src316 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,2,2,1,305932,29⟩

theorem rank316 : P3_7_1.BankOK src316.bank := by
  simpa only [src316, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 12355

theorem width316 : Lower6960.HelperSource.WidthGuard src316.bank 179730 2308 src316.reserve := requestWidth (by decide)

def ends316 : List ℕ := [2308, 2313]

theorem inside316 : Research6966.TerminalBanks.inside src316.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover316 : Cover (Triangular src316) 2313 2308 ends316 := triangleCover (by decide +kernel)

def src317 : Request := ⟨⟨⟨1000,1391,307,13853⟩,30557599170560,104743003887⟩,3,2,1,305932,29⟩

theorem rank317 : P3_7_1.BankOK src317.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_307 13853

theorem width317 : Lower6960.HelperSource.WidthGuard src317.bank 179730 2308 src317.reserve := requestWidth (by decide)

def ends317 : List ℕ := [2308, 2309, 2313]

theorem inside317 : Research6966.TerminalBanks.inside src317.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover317 : Cover (Triangular src317) 2313 2308 ends317 := triangleCover (by decide +kernel)

def src318 : Request := ⟨⟨⟨1201,1674,368,13899⟩,52817102635008,218807905514⟩,4,2,1,305932,29⟩

theorem rank318 : P3_7_1.BankOK src318.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_368 13899

theorem width318 : Lower6960.HelperSource.WidthGuard src318.bank 179730 2308 src318.reserve := requestWidth (by decide)

def ends318 : List ℕ := [2309, 2313]

theorem inside318 : Research6966.TerminalBanks.inside src318.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover318 : Cover (Triangular src318) 2313 2308 ends318 := triangleCover (by decide +kernel)

def src319 : Request := ⟨⟨⟨1203,1673,369,17761⟩,53123316449280,218848410398⟩,6,2,1,305932,29⟩

theorem rank319 : P3_7_1.BankOK src319.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1673_369 17761

theorem width319 : Lower6960.HelperSource.WidthGuard src319.bank 179730 2308 src319.reserve := requestWidth (by decide)

def ends319 : List ℕ := [2308, 2309, 2313]

theorem inside319 : Research6966.TerminalBanks.inside src319.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover319 : Cover (Triangular src319) 2313 2308 ends319 := triangleCover (by decide +kernel)

def src32 : Request := ⟨⟨⟨2992,4160,900,122255⟩,803353782648832,8216917752362⟩,8,2,1,257515,23⟩

theorem rank32 : P3_7_1.BankOK src32.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2992_4160_900 122255

theorem width32 : Lower6960.HelperSource.WidthGuard src32.bank 179730 2308 src32.reserve := requestWidth (by decide)

def ends32 : List ℕ := [2308, 2309, 2313]

theorem inside32 : Research6966.TerminalBanks.inside src32.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover32 : Cover (Triangular src32) 2313 2308 ends32 := triangleCover (by decide +kernel)

def src320 : Request := ⟨⟨⟨1482,2063,453,23468⟩,98984436432896,503785592781⟩,10,2,1,305932,29⟩

theorem rank320 : P3_7_1.BankOK src320.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1482_2063_453 23468

theorem width320 : Lower6960.HelperSource.WidthGuard src320.bank 179730 2308 src320.reserve := requestWidth (by decide)

def ends320 : List ℕ := [2308, 2309, 2313]

theorem inside320 : Research6966.TerminalBanks.inside src320.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover320 : Cover (Triangular src320) 2313 2308 ends320 := triangleCover (by decide +kernel)

def src321 : Request := ⟨⟨⟨2606,3630,800,37792⟩,539219229671424,4834461033641⟩,25,2,1,305932,29⟩

theorem rank321 : P3_7_1.BankOK src321.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3630_800 37792

theorem width321 : Lower6960.HelperSource.WidthGuard src321.bank 179730 2308 src321.reserve := requestWidth (by decide)

def ends321 : List ℕ := [2308, 2309, 2313]

theorem inside321 : Research6966.TerminalBanks.inside src321.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover321 : Cover (Triangular src321) 2313 2308 ends321 := triangleCover (by decide +kernel)

def src322 : Request := ⟨⟨⟨5727,7969,1766,73729⟩,5736867509043200,112632359565114⟩,65,2,1,305932,29⟩

theorem rank322 : P3_7_1.BankOK src322.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5727_7969_1766 73729

theorem width322 : Lower6960.HelperSource.WidthGuard src322.bank 179730 2308 src322.reserve := requestWidth (by decide)

def ends322 : List ℕ := [2308, 2309, 2313]




theorem cover322 : Cover (Triangular src322) 2313 2308 ends322 := triangleCover (by decide +kernel)

def src323 : Request := ⟨⟨⟨8714,12159,2675,146522⟩,20134330585579520,606766727288477⟩,110,2,1,305932,29⟩

theorem rank323 : P3_7_1.BankOK src323.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8714_12159_2675 146522

theorem width323 : Lower6960.HelperSource.WidthGuard src323.bank 179730 2308 src323.reserve := requestWidth (by decide)

def ends323 : List ℕ := [2308, 2309, 2313]




theorem cover323 : Cover (Triangular src323) 2313 2308 ends323 := triangleCover (by decide +kernel)

def src324 : Request := ⟨⟨⟨10001,13953,3070,115771⟩,30435188770340864,1052197377228338⟩,110,2,1,305932,29⟩

theorem rank324 : P3_7_1.BankOK src324.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10001_13953_3070 115771

theorem width324 : Lower6960.HelperSource.WidthGuard src324.bank 179730 2308 src324.reserve := requestWidth (by decide)

def ends324 : List ℕ := [2308, 2309, 2313]




theorem cover324 : Cover (Triangular src324) 2313 2308 ends324 := triangleCover (by decide +kernel)

def src325 : Request := ⟨⟨⟨828,1152,254,12662⟩,17353252536320,49298382825⟩,0,2,1,306100,28⟩

theorem rank325 : P3_7_1.BankOK src325.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1152_254 12662

theorem width325 : Lower6960.HelperSource.WidthGuard src325.bank 179730 2308 src325.reserve := requestWidth (by decide)

def ends325 : List ℕ := [2308, 2309, 2313]

theorem inside325 : Research6966.TerminalBanks.inside src325.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover325 : Cover (Triangular src325) 2313 2308 ends325 := triangleCover (by decide +kernel)

def src326 : Request := ⟨⟨⟨1003,1395,307,12355⟩,30763123736576,105715278267⟩,1,2,1,306100,28⟩

theorem rank326 : P3_7_1.BankOK src326.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_307 12355

theorem width326 : Lower6960.HelperSource.WidthGuard src326.bank 179730 2308 src326.reserve := requestWidth (by decide)

def ends326 : List ℕ := [2308, 2309, 2313]

theorem inside326 : Research6966.TerminalBanks.inside src326.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover326 : Cover (Triangular src326) 2313 2308 ends326 := triangleCover (by decide +kernel)

def src327 : Request := ⟨⟨⟨1003,1395,307,14637⟩,30763123736576,105715278267⟩,2,2,1,306100,28⟩

theorem rank327 : P3_7_1.BankOK src327.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_307 14637

theorem width327 : Lower6960.HelperSource.WidthGuard src327.bank 179730 2308 src327.reserve := requestWidth (by decide)

def ends327 : List ℕ := [2308, 2309, 2313]

theorem inside327 : Research6966.TerminalBanks.inside src327.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover327 : Cover (Triangular src327) 2313 2308 ends327 := triangleCover (by decide +kernel)

def src328 : Request := ⟨⟨⟨1204,1674,370,14206⟩,53331470581760,219731030846⟩,3,2,1,306100,28⟩

theorem rank328 : P3_7_1.BankOK src328.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1204_1674_370 14206

theorem width328 : Lower6960.HelperSource.WidthGuard src328.bank 179730 2308 src328.reserve := requestWidth (by decide)

def ends328 : List ℕ := [2308, 2309, 2313]

theorem inside328 : Research6966.TerminalBanks.inside src328.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover328 : Cover (Triangular src328) 2313 2308 ends328 := triangleCover (by decide +kernel)

def src329 : Request := ⟨⟨⟨1202,1674,370,16018⟩,53133361283072,219731030846⟩,4,2,1,306100,28⟩

theorem rank329 : P3_7_1.BankOK src329.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_370 16018

theorem width329 : Lower6960.HelperSource.WidthGuard src329.bank 179730 2308 src329.reserve := requestWidth (by decide)

def ends329 : List ℕ := [2308, 2309, 2313]

theorem inside329 : Research6966.TerminalBanks.inside src329.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover329 : Cover (Triangular src329) 2313 2308 ends329 := triangleCover (by decide +kernel)

def src33 : Request := ⟨⟨⟨2965,4120,900,76886⟩,787225901793280,7965324963082⟩,9,2,1,257515,24⟩

theorem rank33 : P3_7_1.BankOK src33.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2965_4120_900 76886

theorem width33 : Lower6960.HelperSource.WidthGuard src33.bank 179730 2308 src33.reserve := requestWidth (by decide)

def ends33 : List ℕ := [2308, 2309, 2313]

theorem inside33 : Research6966.TerminalBanks.inside src33.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover33 : Cover (Triangular src33) 2313 2308 ends33 := triangleCover (by decide +kernel)

def src330 : Request := ⟨⟨⟨1450,2015,445,17536⟩,92998964346880,460599143061⟩,6,2,1,306100,28⟩

theorem rank330 : P3_7_1.BankOK src330.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1450_2015_445 17536

theorem width330 : Lower6960.HelperSource.WidthGuard src330.bank 179730 2308 src330.reserve := requestWidth (by decide)

def ends330 : List ℕ := [2308, 2309, 2313]

theorem inside330 : Research6966.TerminalBanks.inside src330.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover330 : Cover (Triangular src330) 2313 2308 ends330 := triangleCover (by decide +kernel)

def src331 : Request := ⟨⟨⟨1750,2434,537,22144⟩,163381988556800,979175473612⟩,10,2,1,306100,28⟩

theorem rank331 : P3_7_1.BankOK src331.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1750_2434_537 22144

theorem width331 : Lower6960.HelperSource.WidthGuard src331.bank 179730 2308 src331.reserve := requestWidth (by decide)

def ends331 : List ℕ := [2308, 2309, 2313]

theorem inside331 : Research6966.TerminalBanks.inside src331.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover331 : Cover (Triangular src331) 2313 2308 ends331 := triangleCover (by decide +kernel)

def src332 : Request := ⟨⟨⟨2100,2922,645,31544⟩,282396798484480,2033414523647⟩,16,2,1,306100,28⟩

theorem rank332 : P3_7_1.BankOK src332.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2100_2922_645 31544

theorem width332 : Lower6960.HelperSource.WidthGuard src332.bank 179730 2308 src332.reserve := requestWidth (by decide)

def ends332 : List ℕ := [2308, 2309, 2313]

theorem inside332 : Research6966.TerminalBanks.inside src332.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover332 : Cover (Triangular src332) 2313 2308 ends332 := triangleCover (by decide +kernel)

def src333 : Request := ⟨⟨⟨3960,5511,1213,62783⟩,1887720434302976,25637257621145⟩,40,2,1,306100,28⟩

theorem rank333 : P3_7_1.BankOK src333.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3960_5511_1213 62783

theorem width333 : Lower6960.HelperSource.WidthGuard src333.bank 179730 2308 src333.reserve := requestWidth (by decide)

def ends333 : List ℕ := [2308, 2309, 2313]




theorem cover333 : Cover (Triangular src333) 2313 2308 ends333 := triangleCover (by decide +kernel)

def src334 : Request := ⟨⟨⟨5819,8112,1785,103036⟩,5993853912350720,120269873432242⟩,65,2,1,306100,28⟩

theorem rank334 : P3_7_1.BankOK src334.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5819_8112_1785 103036

theorem width334 : Lower6960.HelperSource.WidthGuard src334.bank 179730 2308 src334.reserve := requestWidth (by decide)

def ends334 : List ℕ := [2308, 2309, 2313]




theorem cover334 : Cover (Triangular src334) 2313 2308 ends334 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources37

section Pack_R6970Height2313CommonSources38

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src335 : Request := ⟨⟨⟨10000,13937,3086,133480⟩,30548737977483264,1052567864777801⟩,110,2,1,306100,28⟩

theorem rank335 : P3_7_1.BankOK src335.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13937_3086 133480

theorem width335 : Lower6960.HelperSource.WidthGuard src335.bank 179730 2308 src335.reserve := requestWidth (by decide)

def ends335 : List ℕ := [2308, 2309, 2313]




theorem cover335 : Cover (Triangular src335) 2313 2308 ends335 := triangleCover (by decide +kernel)

def src336 : Request := ⟨⟨⟨1002,1393,309,12654⟩,30845822566400,105759965279⟩,0,2,1,306263,27⟩

theorem rank336 : P3_7_1.BankOK src336.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1393_309 12654

theorem width336 : Lower6960.HelperSource.WidthGuard src336.bank 179730 2308 src336.reserve := requestWidth (by decide)

def ends336 : List ℕ := [2308, 2309, 2313]

theorem inside336 : Research6966.TerminalBanks.inside src336.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover336 : Cover (Triangular src336) 2313 2308 ends336 := triangleCover (by decide +kernel)

def src337 : Request := ⟨⟨⟨1200,1670,368,13875⟩,52718727069696,217129800278⟩,1,2,1,306263,27⟩

theorem rank337 : P3_7_1.BankOK src337.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1670_368 13875

theorem width337 : Lower6960.HelperSource.WidthGuard src337.bank 179730 2308 src337.reserve := requestWidth (by decide)

def ends337 : List ℕ := [2308, 2309, 2313]

theorem inside337 : Research6966.TerminalBanks.inside src337.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover337 : Cover (Triangular src337) 2313 2308 ends337 := triangleCover (by decide +kernel)

def src338 : Request := ⟨⟨⟨1200,1674,368,15636⟩,52718727069696,218807905514⟩,2,2,1,306263,27⟩

theorem rank338 : P3_7_1.BankOK src338.bank := by
  simpa only [src338, _root_.Research6969.TransitionBanks.bank228] using _root_.Research6969.TransitionBanks.rank228 15636

theorem width338 : Lower6960.HelperSource.WidthGuard src338.bank 179730 2308 src338.reserve := requestWidth (by decide)

def ends338 : List ℕ := [2308, 2309, 2313]

theorem inside338 : Research6966.TerminalBanks.inside src338.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover338 : Cover (Triangular src338) 2313 2308 ends338 := triangleCover (by decide +kernel)

def src339 : Request := ⟨⟨⟨1202,1674,368,17590⟩,52915574931456,218807905514⟩,3,2,1,306263,27⟩

theorem rank339 : P3_7_1.BankOK src339.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_368 17590

theorem width339 : Lower6960.HelperSource.WidthGuard src339.bank 179730 2308 src339.reserve := requestWidth (by decide)

def ends339 : List ℕ := [2308, 2309, 2313]

theorem inside339 : Research6966.TerminalBanks.inside src339.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover339 : Cover (Triangular src339) 2313 2308 ends339 := triangleCover (by decide +kernel)

def src34 : Request := ⟨⟨⟨2953,4102,896,79099⟩,777475411148800,7826642207395⟩,9,2,1,257515,24⟩

theorem rank34 : P3_7_1.BankOK src34.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2953_4102_896 79099

theorem width34 : Lower6960.HelperSource.WidthGuard src34.bank 179730 2308 src34.reserve := requestWidth (by decide)

def ends34 : List ℕ := [2308, 2309, 2313]

theorem inside34 : Research6966.TerminalBanks.inside src34.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover34 : Cover (Triangular src34) 2313 2308 ends34 := triangleCover (by decide +kernel)

def src340 : Request := ⟨⟨⟨1203,1675,369,22094⟩,53123316449280,219691504053⟩,4,2,1,306263,27⟩

theorem rank340 : P3_7_1.BankOK src340.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1675_369 22094

theorem width340 : Lower6960.HelperSource.WidthGuard src340.bank 179730 2308 src340.reserve := requestWidth (by decide)

def ends340 : List ℕ := [2308, 2309, 2313]

theorem inside340 : Research6966.TerminalBanks.inside src340.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover340 : Cover (Triangular src340) 2313 2308 ends340 := triangleCover (by decide +kernel)

def src341 : Request := ⟨⟨⟨1451,2023,445,22261⟩,93142595928064,466511127281⟩,6,2,1,306263,27⟩

theorem rank341 : P3_7_1.BankOK src341.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2023_445 22261

theorem width341 : Lower6960.HelperSource.WidthGuard src341.bank 179730 2308 src341.reserve := requestWidth (by decide)

def ends341 : List ℕ := [2308, 2309, 2313]

theorem inside341 : Research6966.TerminalBanks.inside src341.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover341 : Cover (Triangular src341) 2313 2308 ends341 := triangleCover (by decide +kernel)

def src342 : Request := ⟨⟨⟨1754,2442,538,28192⟩,164451141550080,991005884367⟩,10,2,1,306263,27⟩

theorem rank342 : P3_7_1.BankOK src342.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_538 28192

theorem width342 : Lower6960.HelperSource.WidthGuard src342.bank 179730 2308 src342.reserve := requestWidth (by decide)

def ends342 : List ℕ := [2308, 2309, 2313]

theorem inside342 : Research6966.TerminalBanks.inside src342.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover342 : Cover (Triangular src342) 2313 2308 ends342 := triangleCover (by decide +kernel)

def src343 : Request := ⟨⟨⟨2607,3628,798,42334⟩,538657964425216,4816500515660⟩,20,2,1,306263,27⟩

theorem rank343 : P3_7_1.BankOK src343.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3628_798 42334

theorem width343 : Lower6960.HelperSource.WidthGuard src343.bank 179730 2308 src343.reserve := requestWidth (by decide)

def ends343 : List ℕ := [2308, 2309, 2313]

theorem inside343 : Research6966.TerminalBanks.inside src343.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover343 : Cover (Triangular src343) 2313 2308 ends343 := triangleCover (by decide +kernel)

def src344 : Request := ⟨⟨⟨3969,5520,1221,52029⟩,1906836793458688,25904511971665⟩,32,2,1,306263,27⟩

theorem rank344 : P3_7_1.BankOK src344.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3969_5520_1221 52029

theorem width344 : Lower6960.HelperSource.WidthGuard src344.bank 179730 2308 src344.reserve := requestWidth (by decide)

def ends344 : List ℕ := [2308, 2309, 2313]




theorem cover344 : Cover (Triangular src344) 2313 2308 ends344 := triangleCover (by decide +kernel)

def src345 : Request := ⟨⟨⟨6900,9596,2150,93589⟩,10111427995238400,238800000867221⟩,65,2,1,306263,27⟩

theorem rank345 : P3_7_1.BankOK src345.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6900_9596_2150 93589

theorem width345 : Lower6960.HelperSource.WidthGuard src345.bank 179730 2308 src345.reserve := requestWidth (by decide)

def ends345 : List ℕ := [2308, 2309, 2313]




theorem cover345 : Cover (Triangular src345) 2313 2308 ends345 := triangleCover (by decide +kernel)

def src346 : Request := ⟨⟨⟨10000,13921,3070,182411⟩,30428373265940480,1044445480705554⟩,110,2,1,306263,27⟩

theorem rank346 : P3_7_1.BankOK src346.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13921_3070 182411

theorem width346 : Lower6960.HelperSource.WidthGuard src346.bank 179730 2308 src346.reserve := requestWidth (by decide)

def ends346 : List ℕ := [2308, 2309, 2313]




theorem cover346 : Cover (Triangular src346) 2313 2308 ends346 := triangleCover (by decide +kernel)

def src347 : Request := ⟨⟨⟨2887,4021,882,67119⟩,730324645445632,7250467565269⟩,15,2,1,306290,23⟩

theorem rank347 : P3_7_1.BankOK src347.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2887_4021_882 67119

theorem width347 : Lower6960.HelperSource.WidthGuard src347.bank 179730 2308 src347.reserve := requestWidth (by decide)

def ends347 : List ℕ := [2308, 2309, 2313]

theorem inside347 : Research6966.TerminalBanks.inside src347.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover347 : Cover (Triangular src347) 2313 2308 ends347 := triangleCover (by decide +kernel)

def src348 : Request := ⟨⟨⟨2997,4180,900,217515⟩,806359322591232,8344716709602⟩,21,2,1,306290,23⟩

theorem rank348 : P3_7_1.BankOK src348.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2997_4180_900 217515

theorem width348 : Lower6960.HelperSource.WidthGuard src348.bank 179730 2308 src348.reserve := requestWidth (by decide)

def ends348 : List ℕ := [2308, 2309, 2313]

theorem inside348 : Research6966.TerminalBanks.inside src348.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover348 : Cover (Triangular src348) 2313 2308 ends348 := triangleCover (by decide +kernel)

def src349 : Request := ⟨⟨⟨1002,1395,308,15790⟩,30770229149696,105982496027⟩,0,2,1,306420,26⟩

theorem rank349 : P3_7_1.BankOK src349.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_308 15790

theorem width349 : Lower6960.HelperSource.WidthGuard src349.bank 179730 2308 src349.reserve := requestWidth (by decide)

def ends349 : List ℕ := [2308, 2309, 2313]

theorem inside349 : Research6966.TerminalBanks.inside src349.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover349 : Cover (Triangular src349) 2313 2308 ends349 := triangleCover (by decide +kernel)

def src35 : Request := ⟨⟨⟨3004,4178,897,106646⟩,808515669327872,8310192816141⟩,11,2,1,257319,25⟩

theorem rank35 : P3_7_1.BankOK src35.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3004_4178_897 106646

theorem width35 : Lower6960.HelperSource.WidthGuard src35.bank 179730 2308 src35.reserve := requestWidth (by decide)

def ends35 : List ℕ := [2308, 2309, 2313]

theorem inside35 : Research6966.TerminalBanks.inside src35.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover35 : Cover (Triangular src35) 2313 2308 ends35 := triangleCover (by decide +kernel)

def src350 : Request := ⟨⟨⟨1002,1395,307,23814⟩,30694534807552,105715278267⟩,1,2,1,306420,26⟩

theorem rank350 : P3_7_1.BankOK src350.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_307 23814

theorem width350 : Lower6960.HelperSource.WidthGuard src350.bank 179730 2308 src350.reserve := requestWidth (by decide)

def ends350 : List ℕ := [2308, 2309, 2313]

theorem inside350 : Research6966.TerminalBanks.inside src350.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover350 : Cover (Triangular src350) 2313 2308 ends350 := triangleCover (by decide +kernel)

def src351 : Request := ⟨⟨⟨1203,1674,368,16314⟩,53014143959040,218807905514⟩,1,2,1,306420,26⟩

theorem rank351 : P3_7_1.BankOK src351.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_368 16314

theorem width351 : Lower6960.HelperSource.WidthGuard src351.bank 179730 2308 src351.reserve := requestWidth (by decide)

def ends351 : List ℕ := [2308, 2309, 2313]

theorem inside351 : Research6966.TerminalBanks.inside src351.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover351 : Cover (Triangular src351) 2313 2308 ends351 := triangleCover (by decide +kernel)

def src352 : Request := ⟨⟨⟨1202,1674,370,18636⟩,53133361283072,219731030846⟩,2,2,1,306420,26⟩

theorem rank352 : P3_7_1.BankOK src352.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_370 18636

theorem width352 : Lower6960.HelperSource.WidthGuard src352.bank 179730 2308 src352.reserve := requestWidth (by decide)

def ends352 : List ℕ := [2308, 2309, 2313]

theorem inside352 : Research6966.TerminalBanks.inside src352.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover352 : Cover (Triangular src352) 2313 2308 ends352 := triangleCover (by decide +kernel)

def src353 : Request := ⟨⟨⟨1454,2023,445,20970⟩,93574192168960,466511127281⟩,4,2,1,306420,26⟩

theorem rank353 : P3_7_1.BankOK src353.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2023_445 20970

theorem width353 : Lower6960.HelperSource.WidthGuard src353.bank 179730 2308 src353.reserve := requestWidth (by decide)

def ends353 : List ℕ := [2308, 2309, 2313]

theorem inside353 : Research6966.TerminalBanks.inside src353.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover353 : Cover (Triangular src353) 2313 2308 ends353 := triangleCover (by decide +kernel)

def src354 : Request := ⟨⟨⟨1754,2442,538,28170⟩,164451141550080,991005884367⟩,8,2,1,306420,26⟩

theorem rank354 : P3_7_1.BankOK src354.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_538 28170

theorem width354 : Lower6960.HelperSource.WidthGuard src354.bank 179730 2308 src354.reserve := requestWidth (by decide)

def ends354 : List ℕ := [2308, 2309, 2313]

theorem inside354 : Research6966.TerminalBanks.inside src354.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover354 : Cover (Triangular src354) 2313 2308 ends354 := triangleCover (by decide +kernel)

def src355 : Request := ⟨⟨⟨2105,2930,645,40920⟩,283904392560640,2051392203643⟩,13,2,1,306420,26⟩

theorem rank355 : P3_7_1.BankOK src355.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2930_645 40920

theorem width355 : Lower6960.HelperSource.WidthGuard src355.bank 179730 2308 src355.reserve := requestWidth (by decide)

def ends355 : List ℕ := [2308, 2309, 2313]

theorem inside355 : Research6966.TerminalBanks.inside src355.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover355 : Cover (Triangular src355) 2313 2308 ends355 := triangleCover (by decide +kernel)

def src356 : Request := ⟨⟨⟨4801,6682,1474,76352⟩,3369119023104000,55489160567431⟩,40,2,1,306420,26⟩

theorem rank356 : P3_7_1.BankOK src356.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4801_6682_1474 76352

theorem width356 : Lower6960.HelperSource.WidthGuard src356.bank 179730 2308 src356.reserve := requestWidth (by decide)

def ends356 : List ℕ := [2308, 2309, 2313]




theorem cover356 : Cover (Triangular src356) 2313 2308 ends356 := triangleCover (by decide +kernel)

def src357 : Request := ⟨⟨⟨8308,11581,2548,199647⟩,17437292043960320,499402661779949⟩,85,2,1,306420,26⟩

theorem rank357 : P3_7_1.BankOK src357.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8308_11581_2548 199647

theorem width357 : Lower6960.HelperSource.WidthGuard src357.bank 179730 2308 src357.reserve := requestWidth (by decide)

def ends357 : List ℕ := [2308, 2309, 2313]




theorem cover357 : Cover (Triangular src357) 2313 2308 ends357 := triangleCover (by decide +kernel)

def src358 : Request := ⟨⟨⟨10049,13986,3102,132964⟩,31006604324503552,1068827738108783⟩,85,2,1,306420,26⟩

theorem rank358 : P3_7_1.BankOK src358.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10049_13986_3102 132964

theorem width358 : Lower6960.HelperSource.WidthGuard src358.bank 179730 2308 src358.reserve := requestWidth (by decide)

def ends358 : List ℕ := [2308, 2309, 2313]




theorem cover358 : Cover (Triangular src358) 2313 2308 ends358 := triangleCover (by decide +kernel)

def src359 : Request := ⟨⟨⟨10499,14650,3223,264035⟩,35212191177113600,1278578742564135⟩,110,2,1,306420,26⟩

theorem rank359 : P3_7_1.BankOK src359.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10499_14650_3223 264035

theorem width359 : Lower6960.HelperSource.WidthGuard src359.bank 179730 2308 src359.reserve := requestWidth (by decide)

def ends359 : List ℕ := [2308, 2309, 2313]




theorem cover359 : Cover (Triangular src359) 2313 2308 ends359 := triangleCover (by decide +kernel)

def src36 : Request := ⟨⟨⟨2914,4045,897,52406⟩,755316422868992,7488345307134⟩,10,2,1,257319,25⟩

theorem rank36 : P3_7_1.BankOK src36.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2914_4045_897 52406

theorem width36 : Lower6960.HelperSource.WidthGuard src36.bank 179730 2308 src36.reserve := requestWidth (by decide)

def ends36 : List ℕ := [2308, 2309, 2313]

theorem inside36 : Research6966.TerminalBanks.inside src36.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover36 : Cover (Triangular src36) 2313 2308 ends36 := triangleCover (by decide +kernel)

def src360 : Request := ⟨⟨⟨1002,1395,307,22013⟩,30694534807552,105715278267⟩,0,2,1,306571,25⟩

theorem rank360 : P3_7_1.BankOK src360.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_307 22013

theorem width360 : Lower6960.HelperSource.WidthGuard src360.bank 179730 2308 src360.reserve := requestWidth (by decide)

def ends360 : List ℕ := [2308, 2309, 2313]

theorem inside360 : Research6966.TerminalBanks.inside src360.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover360 : Cover (Triangular src360) 2313 2308 ends360 := triangleCover (by decide +kernel)

def src361 : Request := ⟨⟨⟨1203,1675,369,19971⟩,53123316449280,219691504053⟩,1,2,1,306571,25⟩

theorem rank361 : P3_7_1.BankOK src361.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1675_369 19971

theorem width361 : Lower6960.HelperSource.WidthGuard src361.bank 179730 2308 src361.reserve := requestWidth (by decide)

def ends361 : List ℕ := [2308, 2309, 2313]

theorem inside361 : Research6966.TerminalBanks.inside src361.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover361 : Cover (Triangular src361) 2313 2308 ends361 := triangleCover (by decide +kernel)

def src362 : Request := ⟨⟨⟨1454,2023,445,20561⟩,93574192168960,466511127281⟩,2,2,1,306571,25⟩

theorem rank362 : P3_7_1.BankOK src362.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2023_445 20561

theorem width362 : Lower6960.HelperSource.WidthGuard src362.bank 179730 2308 src362.reserve := requestWidth (by decide)

def ends362 : List ℕ := [2308, 2309, 2313]

theorem inside362 : Research6966.TerminalBanks.inside src362.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover362 : Cover (Triangular src362) 2313 2308 ends362 := triangleCover (by decide +kernel)

def src363 : Request := ⟨⟨⟨1454,2023,447,22788⟩,93892925980672,468139690480⟩,3,2,1,306571,25⟩

theorem rank363 : P3_7_1.BankOK src363.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2023_447 22788

theorem width363 : Lower6960.HelperSource.WidthGuard src363.bank 179730 2308 src363.reserve := requestWidth (by decide)

def ends363 : List ℕ := [2308, 2309, 2313]

theorem inside363 : Research6966.TerminalBanks.inside src363.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover363 : Cover (Triangular src363) 2313 2308 ends363 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources38

section Pack_R6970Height2313CommonSources39

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src364 : Request := ⟨⟨⟨1453,2023,445,26731⟩,93430209839104,466511127281⟩,4,2,1,306571,25⟩

theorem rank364 : P3_7_1.BankOK src364.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_445 26731

theorem width364 : Lower6960.HelperSource.WidthGuard src364.bank 179730 2308 src364.reserve := requestWidth (by decide)

def ends364 : List ℕ := [2308, 2309, 2313]

theorem inside364 : Research6966.TerminalBanks.inside src364.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover364 : Cover (Triangular src364) 2313 2308 ends364 := triangleCover (by decide +kernel)

def src365 : Request := ⟨⟨⟨1754,2442,538,28224⟩,164451141550080,991005884367⟩,6,2,1,306571,25⟩

theorem rank365 : P3_7_1.BankOK src365.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_538 28224

theorem width365 : Lower6960.HelperSource.WidthGuard src365.bank 179730 2308 src365.reserve := requestWidth (by decide)

def ends365 : List ℕ := [2308, 2309, 2313]

theorem inside365 : Research6966.TerminalBanks.inside src365.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover365 : Cover (Triangular src365) 2313 2308 ends365 := triangleCover (by decide +kernel)

def src366 : Request := ⟨⟨⟨2105,2930,645,36398⟩,283904392560640,2051392203643⟩,10,2,1,306571,25⟩

theorem rank366 : P3_7_1.BankOK src366.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2930_645 36398

theorem width366 : Lower6960.HelperSource.WidthGuard src366.bank 179730 2308 src366.reserve := requestWidth (by decide)

def ends366 : List ℕ := [2308, 2309, 2313]

theorem inside366 : Research6966.TerminalBanks.inside src366.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover366 : Cover (Triangular src366) 2313 2308 ends366 := triangleCover (by decide +kernel)

def src367 : Request := ⟨⟨⟨3208,4465,982,52843⟩,1003361371160576,11043969901736⟩,20,2,1,306571,25⟩

theorem rank367 : P3_7_1.BankOK src367.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3208_4465_982 52843

theorem width367 : Lower6960.HelperSource.WidthGuard src367.bank 179730 2308 src367.reserve := requestWidth (by decide)

def ends367 : List ℕ := [2308, 2309, 2313]




theorem cover367 : Cover (Triangular src367) 2313 2308 ends367 := triangleCover (by decide +kernel)

def src368 : Request := ⟨⟨⟨4811,6698,1474,105763⟩,3384854249472000,55918169002031⟩,40,2,1,306571,25⟩

theorem rank368 : P3_7_1.BankOK src368.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4811_6698_1474 105763

theorem width368 : Lower6960.HelperSource.WidthGuard src368.bank 179730 2308 src368.reserve := requestWidth (by decide)

def ends368 : List ℕ := [2308, 2309, 2313]




theorem cover368 : Cover (Triangular src368) 2313 2308 ends368 := triangleCover (by decide +kernel)

def src369 : Request := ⟨⟨⟨8710,12147,2622,310020⟩,19809629157457920,595475399274745⟩,85,2,1,306571,25⟩

theorem rank369 : P3_7_1.BankOK src369.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8710_12147_2622 310020

theorem width369 : Lower6960.HelperSource.WidthGuard src369.bank 179730 2308 src369.reserve := requestWidth (by decide)

def ends369 : List ℕ := [2308, 2309, 2313]




theorem cover369 : Cover (Triangular src369) 2313 2308 ends369 := triangleCover (by decide +kernel)

def src37 : Request := ⟨⟨⟨2914,4045,897,44215⟩,755316422868992,7488345307134⟩,16,2,1,257319,27⟩

theorem rank37 : P3_7_1.BankOK src37.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2914_4045_897 44215

theorem width37 : Lower6960.HelperSource.WidthGuard src37.bank 179730 2308 src37.reserve := requestWidth (by decide)

def ends37 : List ℕ := [2308, 2309, 2313]

theorem inside37 : Research6966.TerminalBanks.inside src37.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover37 : Cover (Triangular src37) 2313 2308 ends37 := triangleCover (by decide +kernel)

def src370 : Request := ⟨⟨⟨10000,13922,3070,165231⟩,30428373265940480,1044687137320892⟩,85,2,1,306571,25⟩

theorem rank370 : P3_7_1.BankOK src370.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13922_3070 165231

theorem width370 : Lower6960.HelperSource.WidthGuard src370.bank 179730 2308 src370.reserve := requestWidth (by decide)

def ends370 : List ℕ := [2308, 2309, 2313]




theorem cover370 : Cover (Triangular src370) 2313 2308 ends370 := triangleCover (by decide +kernel)

def src371 : Request := ⟨⟨⟨1203,1674,368,21235⟩,53014143959040,218807905514⟩,0,2,1,306716,24⟩

theorem rank371 : P3_7_1.BankOK src371.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_368 21235

theorem width371 : Lower6960.HelperSource.WidthGuard src371.bank 179730 2308 src371.reserve := requestWidth (by decide)

def ends371 : List ℕ := [2308, 2309, 2313]

theorem inside371 : Research6966.TerminalBanks.inside src371.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover371 : Cover (Triangular src371) 2313 2308 ends371 := triangleCover (by decide +kernel)

def src372 : Request := ⟨⟨⟨1453,2023,445,22261⟩,93430209839104,466511127281⟩,1,2,1,306716,24⟩

theorem rank372 : P3_7_1.BankOK src372.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_445 22261

theorem width372 : Lower6960.HelperSource.WidthGuard src372.bank 179730 2308 src372.reserve := requestWidth (by decide)

def ends372 : List ℕ := [2308, 2309, 2313]

theorem inside372 : Research6966.TerminalBanks.inside src372.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover372 : Cover (Triangular src372) 2313 2308 ends372 := triangleCover (by decide +kernel)

def src373 : Request := ⟨⟨⟨1453,2023,445,25043⟩,93430209839104,466511127281⟩,2,2,1,306716,24⟩

theorem rank373 : P3_7_1.BankOK src373.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_445 25043

theorem width373 : Lower6960.HelperSource.WidthGuard src373.bank 179730 2308 src373.reserve := requestWidth (by decide)

def ends373 : List ℕ := [2308, 2309, 2313]

theorem inside373 : Research6966.TerminalBanks.inside src373.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover373 : Cover (Triangular src373) 2313 2308 ends373 := triangleCover (by decide +kernel)

def src374 : Request := ⟨⟨⟨1754,2442,537,28406⟩,164219163246592,989573241440⟩,4,2,1,306716,24⟩

theorem rank374 : P3_7_1.BankOK src374.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_537 28406

theorem width374 : Lower6960.HelperSource.WidthGuard src374.bank 179730 2308 src374.reserve := requestWidth (by decide)

def ends374 : List ℕ := [2308, 2309, 2313]

theorem inside374 : Research6966.TerminalBanks.inside src374.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover374 : Cover (Triangular src374) 2313 2308 ends374 := triangleCover (by decide +kernel)

def src375 : Request := ⟨⟨⟨2105,2930,645,37524⟩,283904392560640,2051392203643⟩,8,2,1,306716,24⟩

theorem rank375 : P3_7_1.BankOK src375.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2930_645 37524

theorem width375 : Lower6960.HelperSource.WidthGuard src375.bank 179730 2308 src375.reserve := requestWidth (by decide)

def ends375 : List ℕ := [2308, 2309, 2313]

theorem inside375 : Research6966.TerminalBanks.inside src375.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover375 : Cover (Triangular src375) 2313 2308 ends375 := triangleCover (by decide +kernel)

def src376 : Request := ⟨⟨⟨2606,3628,798,48890⟩,538195492077568,4816500515660⟩,13,2,1,306716,24⟩

theorem rank376 : P3_7_1.BankOK src376.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3628_798 48890

theorem width376 : Lower6960.HelperSource.WidthGuard src376.bank 179730 2308 src376.reserve := requestWidth (by decide)

def ends376 : List ℕ := [2308, 2309, 2313]

theorem inside376 : Research6966.TerminalBanks.inside src376.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover376 : Cover (Triangular src376) 2313 2308 ends376 := triangleCover (by decide +kernel)

def src377 : Request := ⟨⟨⟨4809,6698,1474,86620⟩,3381704110899200,55918169002031⟩,32,2,1,306716,24⟩

theorem rank377 : P3_7_1.BankOK src377.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4809_6698_1474 86620

theorem width377 : Lower6960.HelperSource.WidthGuard src377.bank 179730 2308 src377.reserve := requestWidth (by decide)

def ends377 : List ℕ := [2308, 2309, 2313]




theorem cover377 : Cover (Triangular src377) 2313 2308 ends377 := triangleCover (by decide +kernel)

def src378 : Request := ⟨⟨⟨6905,9628,2083,638280⟩,9887111783120896,235495887116840⟩,65,2,1,306716,24⟩

theorem rank378 : P3_7_1.BankOK src378.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6905_9628_2083 638280

theorem width378 : Lower6960.HelperSource.WidthGuard src378.bank 179730 2308 src378.reserve := requestWidth (by decide)

def ends378 : List ℕ := [2308, 2309, 2313]




theorem cover378 : Cover (Triangular src378) 2313 2308 ends378 := triangleCover (by decide +kernel)

def src379 : Request := ⟨⟨⟨8312,11582,2548,158583⟩,17456099343466496,499541547131788⟩,65,2,1,306716,24⟩

theorem rank379 : P3_7_1.BankOK src379.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8312_11582_2548 158583

theorem width379 : Lower6960.HelperSource.WidthGuard src379.bank 179730 2308 src379.reserve := requestWidth (by decide)

def ends379 : List ℕ := [2308, 2309, 2313]




theorem cover379 : Cover (Triangular src379) 2313 2308 ends379 := triangleCover (by decide +kernel)

def src38 : Request := ⟨⟨⟨2791,3875,854,44373⟩,660683174707200,6276931302582⟩,15,2,1,257319,27⟩

theorem rank38 : P3_7_1.BankOK src38.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2791_3875_854 44373

theorem width38 : Lower6960.HelperSource.WidthGuard src38.bank 179730 2308 src38.reserve := requestWidth (by decide)

def ends38 : List ℕ := [2308, 2309, 2313]

theorem inside38 : Research6966.TerminalBanks.inside src38.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover38 : Cover (Triangular src38) 2313 2308 ends38 := triangleCover (by decide +kernel)

def src380 : Request := ⟨⟨⟨8714,12160,2622,1141999⟩,19829986352955392,597528981303932⟩,85,2,1,306716,24⟩

theorem rank380 : P3_7_1.BankOK src380.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8714_12160_2622 1141999

theorem width380 : Lower6960.HelperSource.WidthGuard src380.bank 179730 2308 src380.reserve := requestWidth (by decide)

def ends380 : List ℕ := [2308, 2309, 2313]




theorem cover380 : Cover (Triangular src380) 2313 2308 ends380 := triangleCover (by decide +kernel)

def src381 : Request := ⟨⟨⟨1202,1674,368,27002⟩,52915574931456,218807905514⟩,0,2,1,306855,23⟩

theorem rank381 : P3_7_1.BankOK src381.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_368 27002

theorem width381 : Lower6960.HelperSource.WidthGuard src381.bank 179730 2308 src381.reserve := requestWidth (by decide)

def ends381 : List ℕ := [2308, 2309, 2313]

theorem inside381 : Research6966.TerminalBanks.inside src381.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover381 : Cover (Triangular src381) 2313 2308 ends381 := triangleCover (by decide +kernel)

def src382 : Request := ⟨⟨⟨1453,2023,445,26968⟩,93430209839104,466511127281⟩,1,2,1,306855,23⟩

theorem rank382 : P3_7_1.BankOK src382.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_445 26968

theorem width382 : Lower6960.HelperSource.WidthGuard src382.bank 179730 2308 src382.reserve := requestWidth (by decide)

def ends382 : List ℕ := [2308, 2309, 2313]

theorem inside382 : Research6966.TerminalBanks.inside src382.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover382 : Cover (Triangular src382) 2313 2308 ends382 := triangleCover (by decide +kernel)

def src383 : Request := ⟨⟨⟨1731,2410,527,31724⟩,157179550105600,934671348902⟩,3,2,1,306855,23⟩

theorem rank383 : P3_7_1.BankOK src383.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1731_2410_527 31724

theorem width383 : Lower6960.HelperSource.WidthGuard src383.bank 179730 2308 src383.reserve := requestWidth (by decide)

def ends383 : List ℕ := [2308, 2309, 2313]

theorem inside383 : Research6966.TerminalBanks.inside src383.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover383 : Cover (Triangular src383) 2313 2308 ends383 := triangleCover (by decide +kernel)

def src384 : Request := ⟨⟨⟨1731,2410,527,35635⟩,157179550105600,934671348902⟩,4,2,1,306855,23⟩

theorem rank384 : P3_7_1.BankOK src384.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1731_2410_527 35635

theorem width384 : Lower6960.HelperSource.WidthGuard src384.bank 179730 2308 src384.reserve := requestWidth (by decide)

def ends384 : List ℕ := [2308, 2309, 2313]

theorem inside384 : Research6966.TerminalBanks.inside src384.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover384 : Cover (Triangular src384) 2313 2308 ends384 := triangleCover (by decide +kernel)

def src385 : Request := ⟨⟨⟨2077,2898,632,39882⟩,271293581361152,1949015201860⟩,6,2,1,306855,23⟩

theorem rank385 : P3_7_1.BankOK src385.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2077_2898_632 39882

theorem width385 : Lower6960.HelperSource.WidthGuard src385.bank 179730 2308 src385.reserve := requestWidth (by decide)

def ends385 : List ℕ := [2308, 2309, 2313]

theorem inside385 : Research6966.TerminalBanks.inside src385.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover385 : Cover (Triangular src385) 2313 2308 ends385 := triangleCover (by decide +kernel)

def src386 : Request := ⟨⟨⟨2105,2932,643,47817⟩,283235782230016,2050941744956⟩,8,2,1,306855,23⟩

theorem rank386 : P3_7_1.BankOK src386.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2932_643 47817

theorem width386 : Lower6960.HelperSource.WidthGuard src386.bank 179730 2308 src386.reserve := requestWidth (by decide)

def ends386 : List ℕ := [2308, 2309, 2313]

theorem inside386 : Research6966.TerminalBanks.inside src386.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover386 : Cover (Triangular src386) 2313 2308 ends386 := triangleCover (by decide +kernel)

def src387 : Request := ⟨⟨⟨2605,3628,798,63654⟩,537733229182976,4816500515660⟩,13,2,1,306855,23⟩

theorem rank387 : P3_7_1.BankOK src387.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3628_798 63654

theorem width387 : Lower6960.HelperSource.WidthGuard src387.bank 179730 2308 src387.reserve := requestWidth (by decide)

def ends387 : List ℕ := [2308, 2309, 2313]

theorem inside387 : Research6966.TerminalBanks.inside src387.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover387 : Cover (Triangular src387) 2313 2308 ends387 := triangleCover (by decide +kernel)

def src388 : Request := ⟨⟨⟨4808,6698,1474,110901⟩,3380129621606400,55918169002031⟩,32,2,1,306855,23⟩

theorem rank388 : P3_7_1.BankOK src388.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4808_6698_1474 110901

theorem width388 : Lower6960.HelperSource.WidthGuard src388.bank 179730 2308 src388.reserve := requestWidth (by decide)

def ends388 : List ℕ := [2308, 2309, 2313]




theorem cover388 : Cover (Triangular src388) 2313 2308 ends388 := triangleCover (by decide +kernel)

def src389 : Request := ⟨⟨⟨7246,10109,2180,422931⟩,11401696470892544,285467749372798⟩,65,2,1,306855,23⟩

theorem rank389 : P3_7_1.BankOK src389.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7246_10109_2180 422931

theorem width389 : Lower6960.HelperSource.WidthGuard src389.bank 179730 2308 src389.reserve := requestWidth (by decide)

def ends389 : List ℕ := [2308, 2309, 2313]




theorem cover389 : Cover (Triangular src389) 2313 2308 ends389 := triangleCover (by decide +kernel)

def src39 : Request := ⟨⟨⟨2914,4045,897,41536⟩,755316422868992,7488345307134⟩,23,2,1,257319,29⟩

theorem rank39 : P3_7_1.BankOK src39.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2914_4045_897 41536

theorem width39 : Lower6960.HelperSource.WidthGuard src39.bank 179730 2308 src39.reserve := requestWidth (by decide)

def ends39 : List ℕ := [2308, 2309, 2313]

theorem inside39 : Research6966.TerminalBanks.inside src39.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover39 : Cover (Triangular src39) 2313 2308 ends39 := triangleCover (by decide +kernel)

def src390 : Request := ⟨⟨⟨10011,13955,3070,174408⟩,30503388091777024,1052683166434338⟩,65,2,1,306855,23⟩

theorem rank390 : P3_7_1.BankOK src390.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10011_13955_3070 174408

theorem width390 : Lower6960.HelperSource.WidthGuard src390.bank 179730 2308 src390.reserve := requestWidth (by decide)

def ends390 : List ℕ := [2308, 2309, 2313]




theorem cover390 : Cover (Triangular src390) 2313 2308 ends390 := triangleCover (by decide +kernel)

def src391 : Request := ⟨⟨⟨8714,12160,2622,5253362⟩,19829986352955392,597528981303932⟩,85,2,1,306855,23⟩

theorem rank391 : P3_7_1.BankOK src391.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8714_12160_2622 5253362

theorem width391 : Lower6960.HelperSource.WidthGuard src391.bank 179730 2308 src391.reserve := requestWidth (by decide)

def ends391 : List ℕ := [2308, 2309, 2313]




theorem cover391 : Cover (Triangular src391) 2313 2308 ends391 := triangleCover (by decide +kernel)

def src392 : Request := ⟨⟨⟨1200,1673,362,35385⟩,52065055539200,215613376984⟩,0,2,1,306989,22⟩

theorem rank392 : P3_7_1.BankOK src392.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1673_362 35385

theorem width392 : Lower6960.HelperSource.WidthGuard src392.bank 179730 2308 src392.reserve := requestWidth (by decide)

def ends392 : List ℕ := [2308, 2309, 2313]

theorem inside392 : Research6966.TerminalBanks.inside src392.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover392 : Cover (Triangular src392) 2313 2308 ends392 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources39

section Pack_R6970Height2313CommonSources40

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src393 : Request := ⟨⟨⟨1453,2023,445,33327⟩,93430209839104,466511127281⟩,1,2,1,306989,22⟩

theorem rank393 : P3_7_1.BankOK src393.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_445 33327

theorem width393 : Lower6960.HelperSource.WidthGuard src393.bank 179730 2308 src393.reserve := requestWidth (by decide)

def ends393 : List ℕ := [2308, 2309, 2313]

theorem inside393 : Research6966.TerminalBanks.inside src393.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover393 : Cover (Triangular src393) 2313 2308 ends393 := triangleCover (by decide +kernel)

def src394 : Request := ⟨⟨⟨1458,2031,445,39795⟩,94151290650624,472474533517⟩,2,2,1,306989,22⟩

theorem rank394 : P3_7_1.BankOK src394.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1458_2031_445 39795

theorem width394 : Lower6960.HelperSource.WidthGuard src394.bank 179730 2308 src394.reserve := requestWidth (by decide)

def ends394 : List ℕ := [2308, 2309, 2313]

theorem inside394 : Research6966.TerminalBanks.inside src394.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover394 : Cover (Triangular src394) 2313 2308 ends394 := triangleCover (by decide +kernel)

def src395 : Request := ⟨⟨⟨1754,2442,537,44030⟩,164219163246592,989573241440⟩,4,2,1,306989,22⟩

theorem rank395 : P3_7_1.BankOK src395.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_537 44030

theorem width395 : Lower6960.HelperSource.WidthGuard src395.bank 179730 2308 src395.reserve := requestWidth (by decide)

def ends395 : List ℕ := [2308, 2309, 2313]

theorem inside395 : Research6966.TerminalBanks.inside src395.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover395 : Cover (Triangular src395) 2313 2308 ends395 := triangleCover (by decide +kernel)

def src396 : Request := ⟨⟨⟨2095,2918,636,47775⟩,277912343281664,2002451397973⟩,6,2,1,306989,22⟩

theorem rank396 : P3_7_1.BankOK src396.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2095_2918_636 47775

theorem width396 : Lower6960.HelperSource.WidthGuard src396.bank 179730 2308 src396.reserve := requestWidth (by decide)

def ends396 : List ℕ := [2308, 2309, 2313]

theorem inside396 : Research6966.TerminalBanks.inside src396.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover396 : Cover (Triangular src396) 2313 2308 ends396 := triangleCover (by decide +kernel)

def src397 : Request := ⟨⟨⟨2602,3628,787,60451⟩,530719010455552,4764712808711⟩,10,2,1,306989,22⟩

theorem rank397 : P3_7_1.BankOK src397.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_787 60451

theorem width397 : Lower6960.HelperSource.WidthGuard src397.bank 179730 2308 src397.reserve := requestWidth (by decide)

def ends397 : List ℕ := [2308, 2309, 2313]

theorem inside397 : Research6966.TerminalBanks.inside src397.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover397 : Cover (Triangular src397) 2313 2308 ends397 := triangleCover (by decide +kernel)

def src398 : Request := ⟨⟨⟨3958,5512,1213,86235⟩,1885586297978880,25652240151764⟩,20,2,1,306989,22⟩

theorem rank398 : P3_7_1.BankOK src398.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3958_5512_1213 86235

theorem width398 : Lower6960.HelperSource.WidthGuard src398.bank 179730 2308 src398.reserve := requestWidth (by decide)

def ends398 : List ℕ := [2308, 2309, 2313]




theorem cover398 : Cover (Triangular src398) 2313 2308 ends398 := triangleCover (by decide +kernel)

def src399 : Request := ⟨⟨⟨6902,9628,2081,207149⟩,9870275941498880,235319397536554⟩,50,2,1,306989,22⟩

theorem rank399 : P3_7_1.BankOK src399.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6902_9628_2081 207149

theorem width399 : Lower6960.HelperSource.WidthGuard src399.bank 179730 2308 src399.reserve := requestWidth (by decide)

def ends399 : List ℕ := [2308, 2309, 2313]




theorem cover399 : Cover (Triangular src399) 2313 2308 ends399 := triangleCover (by decide +kernel)

def src4 : Request := ⟨⟨⟨2615,3627,819,24409⟩,553151842222080,4910333421859⟩,45,1,1,128659,41⟩

theorem rank4 : P3_7_1.BankOK src4.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 24409

theorem width4 : Lower6960.HelperSource.WidthGuard src4.bank 179730 2308 src4.reserve := requestWidth (by decide)

def ends4 : List ℕ := [2308, 2313]

theorem inside4 : Research6966.TerminalBanks.inside src4.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover4 : Cover (Triangular src4) 2313 2308 ends4 := triangleCover (by decide +kernel)

def src40 : Request := ⟨⟨⟨2914,4045,897,41536⟩,755316422868992,7488345307134⟩,23,2,1,257319,29⟩

theorem rank40 : P3_7_1.BankOK src40.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2914_4045_897 41536

theorem width40 : Lower6960.HelperSource.WidthGuard src40.bank 179730 2308 src40.reserve := requestWidth (by decide)

def ends40 : List ℕ := [2308, 2309, 2313]

theorem inside40 : Research6966.TerminalBanks.inside src40.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover40 : Cover (Triangular src40) 2313 2308 ends40 := triangleCover (by decide +kernel)

def src400 : Request := ⟨⟨⟨7041,9820,2118,1142156⟩,10460082407211008,254233369236069⟩,65,2,1,306989,22⟩

theorem rank400 : P3_7_1.BankOK src400.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7041_9820_2118 1142156

theorem width400 : Lower6960.HelperSource.WidthGuard src400.bank 179730 2308 src400.reserve := requestWidth (by decide)

def ends400 : List ℕ := [2308, 2309, 2313]




theorem cover400 : Cover (Triangular src400) 2313 2308 ends400 := triangleCover (by decide +kernel)

def src401 : Request := ⟨⟨⟨8315,11582,2547,275619⟩,17465000554659840,499388835538415⟩,65,2,1,306989,22⟩

theorem rank401 : P3_7_1.BankOK src401.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8315_11582_2547 275619

theorem width401 : Lower6960.HelperSource.WidthGuard src401.bank 179730 2308 src401.reserve := requestWidth (by decide)

def ends401 : List ℕ := [2308, 2309, 2313]




theorem cover401 : Cover (Triangular src401) 2313 2308 ends401 := triangleCover (by decide +kernel)

def src402 : Request := ⟨⟨⟨10000,13923,3042,211895⟩,30217110574858240,1037495757100745⟩,65,2,1,306989,22⟩

theorem rank402 : P3_7_1.BankOK src402.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10000_13923_3042 211895

theorem width402 : Lower6960.HelperSource.WidthGuard src402.bank 179730 2308 src402.reserve := requestWidth (by decide)

def ends402 : List ℕ := [2308, 2309, 2313]




theorem cover402 : Cover (Triangular src402) 2313 2308 ends402 := triangleCover (by decide +kernel)

def src403 : Request := ⟨⟨⟨1754,2442,537,33555⟩,164219163246592,989573241440⟩,0,2,1,307116,21⟩

theorem rank403 : P3_7_1.BankOK src403.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_537 33555

theorem width403 : Lower6960.HelperSource.WidthGuard src403.bank 179730 2308 src403.reserve := requestWidth (by decide)

def ends403 : List ℕ := [2308, 2309, 2313]

theorem inside403 : Research6966.TerminalBanks.inside src403.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover403 : Cover (Triangular src403) 2313 2308 ends403 := triangleCover (by decide +kernel)

def src404 : Request := ⟨⟨⟨1749,2438,528,37793⟩,161091549921280,971500521147⟩,1,2,1,307116,21⟩

theorem rank404 : P3_7_1.BankOK src404.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1749_2438_528 37793

theorem width404 : Lower6960.HelperSource.WidthGuard src404.bank 179730 2308 src404.reserve := requestWidth (by decide)

def ends404 : List ℕ := [2308, 2309, 2313]

theorem inside404 : Research6966.TerminalBanks.inside src404.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover404 : Cover (Triangular src404) 2313 2308 ends404 := triangleCover (by decide +kernel)

def src405 : Request := ⟨⟨⟨1752,2442,535,41063⟩,163337078833152,986705217985⟩,2,2,1,307116,21⟩

theorem rank405 : P3_7_1.BankOK src405.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2442_535 41063

theorem width405 : Lower6960.HelperSource.WidthGuard src405.bank 179730 2308 src405.reserve := requestWidth (by decide)

def ends405 : List ℕ := [2308, 2309, 2313]

theorem inside405 : Research6966.TerminalBanks.inside src405.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover405 : Cover (Triangular src405) 2313 2308 ends405 := triangleCover (by decide +kernel)

def src406 : Request := ⟨⟨⟨1752,2442,527,55865⟩,161477036081152,975196209190⟩,4,2,1,307116,21⟩

theorem rank406 : P3_7_1.BankOK src406.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2442_527 55865

theorem width406 : Lower6960.HelperSource.WidthGuard src406.bank 179730 2308 src406.reserve := requestWidth (by decide)

def ends406 : List ℕ := [2308, 2309, 2313]

theorem inside406 : Research6966.TerminalBanks.inside src406.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover406 : Cover (Triangular src406) 2313 2308 ends406 := triangleCover (by decide +kernel)

def src407 : Request := ⟨⟨⟨2096,2922,634,47810⟩,277543655833600,2006369826343⟩,4,2,1,307116,21⟩

theorem rank407 : P3_7_1.BankOK src407.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2096_2922_634 47810

theorem width407 : Lower6960.HelperSource.WidthGuard src407.bank 179730 2308 src407.reserve := requestWidth (by decide)

def ends407 : List ℕ := [2308, 2309, 2313]

theorem inside407 : Research6966.TerminalBanks.inside src407.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover407 : Cover (Triangular src407) 2313 2308 ends407 := triangleCover (by decide +kernel)

def src408 : Request := ⟨⟨⟨2604,3628,796,60516⟩,536248275959808,4807102837758⟩,8,2,1,307116,21⟩

theorem rank408 : P3_7_1.BankOK src408.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3628_796 60516

theorem width408 : Lower6960.HelperSource.WidthGuard src408.bank 179730 2308 src408.reserve := requestWidth (by decide)

def ends408 : List ℕ := [2308, 2309, 2313]

theorem inside408 : Research6966.TerminalBanks.inside src408.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover408 : Cover (Triangular src408) 2313 2308 ends408 := triangleCover (by decide +kernel)

def src409 : Request := ⟨⟨⟨3202,4464,963,102443⟩,984425340338176,10869251283552⟩,16,2,1,307116,21⟩

theorem rank409 : P3_7_1.BankOK src409.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4464_963 102443

theorem width409 : Lower6960.HelperSource.WidthGuard src409.bank 179730 2308 src409.reserve := requestWidth (by decide)

def ends409 : List ℕ := [2308, 2309, 2313]




theorem cover409 : Cover (Triangular src409) 2313 2308 ends409 := triangleCover (by decide +kernel)

def src41 : Request := ⟨⟨⟨2592,3604,775,35655⟩,520045783416832,4608474947497⟩,22,2,1,257515,31⟩

theorem rank41 : P3_7_1.BankOK src41.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2592_3604_775 35655

theorem width41 : Lower6960.HelperSource.WidthGuard src41.bank 179730 2308 src41.reserve := requestWidth (by decide)

def ends41 : List ℕ := [2309, 2313]

theorem inside41 : Research6966.TerminalBanks.inside src41.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover41 : Cover (Triangular src41) 2313 2308 ends41 := triangleCover (by decide +kernel)

def src410 : Request := ⟨⟨⟨5711,7954,1747,142559⟩,5654385624350720,111012270743197⟩,32,2,1,307116,21⟩

theorem rank410 : P3_7_1.BankOK src410.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5711_7954_1747 142559

theorem width410 : Lower6960.HelperSource.WidthGuard src410.bank 179730 2308 src410.reserve := requestWidth (by decide)

def ends410 : List ℕ := [2308, 2309, 2313]




theorem cover410 : Cover (Triangular src410) 2313 2308 ends410 := triangleCover (by decide +kernel)

def src411 : Request := ⟨⟨⟨4803,6698,1448,669591⟩,3326916058152960,55147852767819⟩,40,2,1,307116,21⟩

theorem rank411 : P3_7_1.BankOK src411.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4803_6698_1448 669591

theorem width411 : Lower6960.HelperSource.WidthGuard src411.bank 179730 2308 src411.reserve := requestWidth (by decide)

def ends411 : List ℕ := [2308, 2309, 2313]




theorem cover411 : Cover (Triangular src411) 2313 2308 ends411 := triangleCover (by decide +kernel)

def src412 : Request := ⟨⟨⟨7041,9820,2118,1600806⟩,10460082407211008,254233369236069⟩,65,2,1,307116,21⟩

theorem rank412 : P3_7_1.BankOK src412.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7041_9820_2118 1600806

theorem width412 : Lower6960.HelperSource.WidthGuard src412.bank 179730 2308 src412.reserve := requestWidth (by decide)

def ends412 : List ℕ := [2308, 2309, 2313]




theorem cover412 : Cover (Triangular src412) 2313 2308 ends412 := triangleCover (by decide +kernel)

def src413 : Request := ⟨⟨⟨10016,13954,3070,256451⟩,30537517941653504,1052440252760428⟩,65,2,1,307116,21⟩

theorem rank413 : P3_7_1.BankOK src413.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10016_13954_3070 256451

theorem width413 : Lower6960.HelperSource.WidthGuard src413.bank 179730 2308 src413.reserve := requestWidth (by decide)

def ends413 : List ℕ := [2308, 2309, 2313]




theorem cover413 : Cover (Triangular src413) 2313 2308 ends413 := triangleCover (by decide +kernel)

def src414 : Request := ⟨⟨⟨1450,2022,436,42462⟩,91566841790464,458421718666⟩,0,2,1,307237,20⟩

theorem rank414 : P3_7_1.BankOK src414.bank := by
  simpa only [src414, _root_.Research6969.TransitionBanks.bank232] using _root_.Research6969.TransitionBanks.rank232 42462

theorem width414 : Lower6960.HelperSource.WidthGuard src414.bank 179730 2308 src414.reserve := requestWidth (by decide)

def ends414 : List ℕ := [2308, 2309, 2313]

theorem inside414 : Research6966.TerminalBanks.inside src414.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover414 : Cover (Triangular src414) 2313 2308 ends414 := triangleCover (by decide +kernel)

def src415 : Request := ⟨⟨⟨1451,2023,436,50370⟩,91708090482688,459151377566⟩,1,2,1,307237,20⟩

theorem rank415 : P3_7_1.BankOK src415.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2023_436 50370

theorem width415 : Lower6960.HelperSource.WidthGuard src415.bank 179730 2308 src415.reserve := requestWidth (by decide)

def ends415 : List ℕ := [2308, 2309, 2313]

theorem inside415 : Research6966.TerminalBanks.inside src415.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover415 : Cover (Triangular src415) 2313 2308 ends415 := triangleCover (by decide +kernel)

def src416 : Request := ⟨⟨⟨1753,2442,537,49365⟩,164009658023936,989573241440⟩,2,2,1,307237,20⟩

theorem rank416 : P3_7_1.BankOK src416.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2442_537 49365

theorem width416 : Lower6960.HelperSource.WidthGuard src416.bank 179730 2308 src416.reserve := requestWidth (by decide)

def ends416 : List ℕ := [2308, 2309, 2313]

theorem inside416 : Research6966.TerminalBanks.inside src416.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover416 : Cover (Triangular src416) 2313 2308 ends416 := triangleCover (by decide +kernel)

def src417 : Request := ⟨⟨⟨1741,2426,527,56350⟩,159218359336960,954787561062⟩,3,2,1,307237,20⟩

theorem rank417 : P3_7_1.BankOK src417.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1741_2426_527 56350

theorem width417 : Lower6960.HelperSource.WidthGuard src417.bank 179730 2308 src417.reserve := requestWidth (by decide)

def ends417 : List ℕ := [2308, 2309, 2313]

theorem inside417 : Research6966.TerminalBanks.inside src417.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover417 : Cover (Triangular src417) 2313 2308 ends417 := triangleCover (by decide +kernel)

def src418 : Request := ⟨⟨⟨2102,2930,632,71307⟩,278652894052352,2019119590628⟩,6,2,1,307237,20⟩

theorem rank418 : P3_7_1.BankOK src418.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2102_2930_632 71307

theorem width418 : Lower6960.HelperSource.WidthGuard src418.bank 179730 2308 src418.reserve := requestWidth (by decide)

def ends418 : List ℕ := [2308, 2309, 2313]

theorem inside418 : Research6966.TerminalBanks.inside src418.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover418 : Cover (Triangular src418) 2313 2308 ends418 := triangleCover (by decide +kernel)

def src419 : Request := ⟨⟨⟨2602,3628,783,88716⟩,528664175312896,4745819470168⟩,10,2,1,307237,20⟩

theorem rank419 : P3_7_1.BankOK src419.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 88716

theorem width419 : Lower6960.HelperSource.WidthGuard src419.bank 179730 2308 src419.reserve := requestWidth (by decide)

def ends419 : List ℕ := [2308, 2309, 2313]

theorem inside419 : Research6966.TerminalBanks.inside src419.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover419 : Cover (Triangular src419) 2313 2308 ends419 := triangleCover (by decide +kernel)

def src42 : Request := ⟨⟨⟨2601,3612,793,27685⟩,533334139076608,4725278189299⟩,22,2,1,257319,31⟩

theorem rank42 : P3_7_1.BankOK src42.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3612_793 27685

theorem width42 : Lower6960.HelperSource.WidthGuard src42.bank 179730 2308 src42.reserve := requestWidth (by decide)

def ends42 : List ℕ := [2308, 2309, 2313]

theorem inside42 : Research6966.TerminalBanks.inside src42.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover42 : Cover (Triangular src42) 2313 2308 ends42 := triangleCover (by decide +kernel)

def src420 : Request := ⟨⟨⟨3943,5496,1189,128245⟩,1841424233922560,25020597788251⟩,20,2,1,307237,20⟩

theorem rank420 : P3_7_1.BankOK src420.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3943_5496_1189 128245

theorem width420 : Lower6960.HelperSource.WidthGuard src420.bank 179730 2308 src420.reserve := requestWidth (by decide)

def ends420 : List ℕ := [2308, 2309, 2313]




theorem cover420 : Cover (Triangular src420) 2313 2308 ends420 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources40

section Pack_R6970Height2313CommonSources49

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src652 : Request := ⟨⟨⟨981,1363,296,64008⟩,28475152662528,95368174997⟩,0,3,1,385979,2⟩

theorem rank652 : P3_7_1.BankOK src652.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_981_1363_296 64008

theorem width652 : Lower6960.HelperSource.WidthGuard src652.bank 179730 2308 src652.reserve := requestWidth (by decide)

def ends652 : List ℕ := [2308, 2309, 2313]

theorem inside652 : Research6966.TerminalBanks.inside src652.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover652 : Cover (Triangular src652) 2313 2308 ends652 := triangleCover (by decide +kernel)

def src653 : Request := ⟨⟨⟨1002,1395,301,72736⟩,30238219960320,104105680031⟩,1,3,1,386273,2⟩

theorem rank653 : P3_7_1.BankOK src653.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 72736

theorem width653 : Lower6960.HelperSource.WidthGuard src653.bank 179730 2308 src653.reserve := requestWidth (by decide)

def ends653 : List ℕ := [2308, 2309, 2313]

theorem inside653 : Research6966.TerminalBanks.inside src653.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover653 : Cover (Triangular src653) 2313 2308 ends653 := triangleCover (by decide +kernel)

def src654 : Request := ⟨⟨⟨1002,1395,301,84765⟩,30238219960320,104105680031⟩,2,3,1,386273,2⟩

theorem rank654 : P3_7_1.BankOK src654.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 84765

theorem width654 : Lower6960.HelperSource.WidthGuard src654.bank 179730 2308 src654.reserve := requestWidth (by decide)

def ends654 : List ℕ := [2308, 2309, 2313]

theorem inside654 : Research6966.TerminalBanks.inside src654.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover654 : Cover (Triangular src654) 2313 2308 ends654 := triangleCover (by decide +kernel)

def src655 : Request := ⟨⟨⟨1202,1674,361,95325⟩,52149455421440,215563369662⟩,4,3,1,386273,2⟩

theorem rank655 : P3_7_1.BankOK src655.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_361 95325

theorem width655 : Lower6960.HelperSource.WidthGuard src655.bank 179730 2308 src655.reserve := requestWidth (by decide)

def ends655 : List ℕ := [2308, 2309, 2313]

theorem inside655 : Research6966.TerminalBanks.inside src655.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover655 : Cover (Triangular src655) 2313 2308 ends655 := triangleCover (by decide +kernel)

def src656 : Request := ⟨⟨⟨1455,2023,437,103907⟩,92435285278720,459971681523⟩,6,3,1,385979,2⟩

theorem rank656 : P3_7_1.BankOK src656.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2023_437 103907

theorem width656 : Lower6960.HelperSource.WidthGuard src656.bank 179730 2308 src656.reserve := requestWidth (by decide)

def ends656 : List ℕ := [2308, 2309, 2313]

theorem inside656 : Research6966.TerminalBanks.inside src656.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover656 : Cover (Triangular src656) 2313 2308 ends656 := triangleCover (by decide +kernel)

def src657 : Request := ⟨⟨⟨1754,2442,527,131324⟩,161889503936512,975196209190⟩,10,3,1,386273,2⟩

theorem rank657 : P3_7_1.BankOK src657.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_527 131324

theorem width657 : Lower6960.HelperSource.WidthGuard src657.bank 179730 2308 src657.reserve := requestWidth (by decide)

def ends657 : List ℕ := [2308, 2309, 2313]

theorem inside657 : Research6966.TerminalBanks.inside src657.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover657 : Cover (Triangular src657) 2313 2308 ends657 := triangleCover (by decide +kernel)

def src658 : Request := ⟨⟨⟨2060,2862,622,147719⟩,263139991224320,1849053003955⟩,13,3,1,385979,2⟩

theorem rank658 : P3_7_1.BankOK src658.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2060_2862_622 147719

theorem width658 : Lower6960.HelperSource.WidthGuard src658.bank 179730 2308 src658.reserve := requestWidth (by decide)

def ends658 : List ℕ := [2308, 2309, 2313]

theorem inside658 : Research6966.TerminalBanks.inside src658.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover658 : Cover (Triangular src658) 2313 2308 ends658 := triangleCover (by decide +kernel)

def src659 : Request := ⟨⟨⟨2606,3628,783,195605⟩,530483446284288,4745819470168⟩,20,3,1,386273,2⟩

theorem rank659 : P3_7_1.BankOK src659.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3628_783 195605

theorem width659 : Lower6960.HelperSource.WidthGuard src659.bank 179730 2308 src659.reserve := requestWidth (by decide)

def ends659 : List ℕ := [2308, 2309, 2313]

theorem inside659 : Research6966.TerminalBanks.inside src659.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover659 : Cover (Triangular src659) 2313 2308 ends659 := triangleCover (by decide +kernel)

def src66 : Request := ⟨⟨⟨2789,3873,854,30468⟩,659623697448960,6266506033362⟩,85,2,1,257319,51⟩

theorem rank66 : P3_7_1.BankOK src66.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 30468

theorem width66 : Lower6960.HelperSource.WidthGuard src66.bank 179730 2308 src66.reserve := requestWidth (by decide)

def ends66 : List ℕ := [2308, 2309, 2313]

theorem inside66 : Research6966.TerminalBanks.inside src66.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover66 : Cover (Triangular src66) 2313 2308 ends66 := triangleCover (by decide +kernel)

def src660 : Request := ⟨⟨⟨2998,4178,897,246381⟩,804909730758656,8310192816141⟩,26,3,1,385979,2⟩

theorem rank660 : P3_7_1.BankOK src660.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4178_897 246381

theorem width660 : Lower6960.HelperSource.WidthGuard src660.bank 179730 2308 src660.reserve := requestWidth (by decide)

def ends660 : List ℕ := [2308, 2309, 2313]

theorem inside660 : Research6966.TerminalBanks.inside src660.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover660 : Cover (Triangular src660) 2313 2308 ends660 := triangleCover (by decide +kernel)

def src661 : Request := ⟨⟨⟨3202,4457,963,219892⟩,984425340338176,10814499327412⟩,25,3,1,386273,2⟩

theorem rank661 : P3_7_1.BankOK src661.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4457_963 219892

theorem width661 : Lower6960.HelperSource.WidthGuard src661.bank 179730 2308 src661.reserve := requestWidth (by decide)

def ends661 : List ℕ := [2308, 2309, 2313]




theorem cover661 : Cover (Triangular src661) 2313 2308 ends661 := triangleCover (by decide +kernel)

def src662 : Request := ⟨⟨⟨2995,4178,897,530710⟩,803109939445760,8310192816141⟩,36,3,1,385979,2⟩

theorem rank662 : P3_7_1.BankOK src662.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2995_4178_897 530710

theorem width662 : Lower6960.HelperSource.WidthGuard src662.bank 179730 2308 src662.reserve := requestWidth (by decide)

def ends662 : List ℕ := [2308, 2309, 2313]

theorem inside662 : Research6966.TerminalBanks.inside src662.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover662 : Cover (Triangular src662) 2313 2308 ends662 := triangleCover (by decide +kernel)

def src663 : Request := ⟨⟨⟨4811,6698,1445,306897⟩,3334049849933824,55058665830093⟩,40,3,1,386273,2⟩

theorem rank663 : P3_7_1.BankOK src663.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4811_6698_1445 306897

theorem width663 : Lower6960.HelperSource.WidthGuard src663.bank 179730 2308 src663.reserve := requestWidth (by decide)

def ends663 : List ℕ := [2308, 2309, 2313]




theorem cover663 : Cover (Triangular src663) 2313 2308 ends663 := triangleCover (by decide +kernel)

def src664 : Request := ⟨⟨⟨10008,13953,3010,791401⟩,30028351888687104,1036125345444439⟩,110,3,1,386273,2⟩

theorem rank664 : P3_7_1.BankOK src664.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10008_13953_3010 791401

theorem width664 : Lower6960.HelperSource.WidthGuard src664.bank 179730 2308 src664.reserve := requestWidth (by decide)

def ends664 : List ℕ := [2308, 2309, 2313]




theorem cover664 : Cover (Triangular src664) 2313 2308 ends664 := triangleCover (by decide +kernel)

def src665 : Request := ⟨⟨⟨1002,1395,301,58472⟩,30238219960320,104105680031⟩,0,3,1,386273,4⟩

theorem rank665 : P3_7_1.BankOK src665.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 58472

theorem width665 : Lower6960.HelperSource.WidthGuard src665.bank 179730 2308 src665.reserve := requestWidth (by decide)

def ends665 : List ℕ := [2308, 2309, 2313]

theorem inside665 : Research6966.TerminalBanks.inside src665.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover665 : Cover (Triangular src665) 2313 2308 ends665 := triangleCover (by decide +kernel)

def src666 : Request := ⟨⟨⟨1002,1395,301,66764⟩,30238219960320,104105680031⟩,1,3,1,386273,4⟩

theorem rank666 : P3_7_1.BankOK src666.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 66764

theorem width666 : Lower6960.HelperSource.WidthGuard src666.bank 179730 2308 src666.reserve := requestWidth (by decide)

def ends666 : List ℕ := [2308, 2309, 2313]

theorem inside666 : Research6966.TerminalBanks.inside src666.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover666 : Cover (Triangular src666) 2313 2308 ends666 := triangleCover (by decide +kernel)

def src667 : Request := ⟨⟨⟨1453,2023,436,95488⟩,91990931537920,459151377566⟩,6,3,1,386273,4⟩

theorem rank667 : P3_7_1.BankOK src667.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_436 95488

theorem width667 : Lower6960.HelperSource.WidthGuard src667.bank 179730 2308 src667.reserve := requestWidth (by decide)

def ends667 : List ℕ := [2308, 2309, 2313]

theorem inside667 : Research6966.TerminalBanks.inside src667.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover667 : Cover (Triangular src667) 2313 2308 ends667 := triangleCover (by decide +kernel)

def src668 : Request := ⟨⟨⟨1754,2442,527,120555⟩,161889503936512,975196209190⟩,10,3,1,386273,4⟩

theorem rank668 : P3_7_1.BankOK src668.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_527 120555

theorem width668 : Lower6960.HelperSource.WidthGuard src668.bank 179730 2308 src668.reserve := requestWidth (by decide)

def ends668 : List ℕ := [2308, 2309, 2313]

theorem inside668 : Research6966.TerminalBanks.inside src668.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover668 : Cover (Triangular src668) 2313 2308 ends668 := triangleCover (by decide +kernel)

def src669 : Request := ⟨⟨⟨2555,3552,770,146637⟩,501114315735040,4375777081296⟩,16,3,1,385979,4⟩

theorem rank669 : P3_7_1.BankOK src669.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2555_3552_770 146637

theorem width669 : Lower6960.HelperSource.WidthGuard src669.bank 179730 2308 src669.reserve := requestWidth (by decide)

def ends669 : List ℕ := [2308, 2309, 2313]

theorem inside669 : Research6966.TerminalBanks.inside src669.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover669 : Cover (Triangular src669) 2313 2308 ends669 := triangleCover (by decide +kernel)

def src67 : Request := ⟨⟨⟨2810,3905,854,31694⟩,670792923217920,6434729640882⟩,85,2,1,257319,51⟩

theorem rank67 : P3_7_1.BankOK src67.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3905_854 31694

theorem width67 : Lower6960.HelperSource.WidthGuard src67.bank 179730 2308 src67.reserve := requestWidth (by decide)

def ends67 : List ℕ := [2308, 2309, 2313]

theorem inside67 : Research6966.TerminalBanks.inside src67.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover67 : Cover (Triangular src67) 2313 2308 ends67 := triangleCover (by decide +kernel)

def src670 : Request := ⟨⟨⟨2104,2930,632,246336⟩,279246119370752,2019119590628⟩,20,3,1,386273,4⟩

theorem rank670 : P3_7_1.BankOK src670.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2104_2930_632 246336

theorem width670 : Lower6960.HelperSource.WidthGuard src670.bank 179730 2308 src670.reserve := requestWidth (by decide)

def ends670 : List ℕ := [2308, 2309, 2313]

theorem inside670 : Research6966.TerminalBanks.inside src670.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover670 : Cover (Triangular src670) 2313 2308 ends670 := triangleCover (by decide +kernel)

def src671 : Request := ⟨⟨⟨2998,4178,897,203762⟩,804909730758656,8310192816141⟩,24,3,1,386273,4⟩

theorem rank671 : P3_7_1.BankOK src671.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4178_897 203762

theorem width671 : Lower6960.HelperSource.WidthGuard src671.bank 179730 2308 src671.reserve := requestWidth (by decide)

def ends671 : List ℕ := [2308, 2309, 2313]

theorem inside671 : Research6966.TerminalBanks.inside src671.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover671 : Cover (Triangular src671) 2313 2308 ends671 := triangleCover (by decide +kernel)

def src672 : Request := ⟨⟨⟨3939,5480,1189,193058⟩,1837247829114880,24786918035651⟩,25,3,1,386273,4⟩

theorem rank672 : P3_7_1.BankOK src672.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3939_5480_1189 193058

theorem width672 : Lower6960.HelperSource.WidthGuard src672.bank 179730 2308 src672.reserve := requestWidth (by decide)

def ends672 : List ℕ := [2308, 2309, 2313]




theorem cover672 : Cover (Triangular src672) 2313 2308 ends672 := triangleCover (by decide +kernel)

def src673 : Request := ⟨⟨⟨2652,3699,813,530820⟩,567668370046976,5201448023684⟩,32,3,1,386273,4⟩

theorem rank673 : P3_7_1.BankOK src673.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2652_3699_813 530820

theorem width673 : Lower6960.HelperSource.WidthGuard src673.bank 179730 2308 src673.reserve := requestWidth (by decide)

def ends673 : List ℕ := [2308, 2309, 2313]

theorem inside673 : Research6966.TerminalBanks.inside src673.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover673 : Cover (Triangular src673) 2313 2308 ends673 := triangleCover (by decide +kernel)

def src674 : Request := ⟨⟨⟨5683,7906,1716,274763⟩,5516850487623680,107361107788084⟩,40,3,1,386273,4⟩

theorem rank674 : P3_7_1.BankOK src674.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5683_7906_1716 274763

theorem width674 : Lower6960.HelperSource.WidthGuard src674.bank 179730 2308 src674.reserve := requestWidth (by decide)

def ends674 : List ℕ := [2308, 2309, 2313]




theorem cover674 : Cover (Triangular src674) 2313 2308 ends674 := triangleCover (by decide +kernel)

def src675 : Request := ⟨⟨⟨9981,13889,3010,721710⟩,29847417077366784,1020905604721879⟩,110,3,1,386273,4⟩

theorem rank675 : P3_7_1.BankOK src675.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_9981_13889_3010 721710

theorem width675 : Lower6960.HelperSource.WidthGuard src675.bank 179730 2308 src675.reserve := requestWidth (by decide)

def ends675 : List ℕ := [2308, 2309, 2313]




theorem cover675 : Cover (Triangular src675) 2313 2308 ends675 := triangleCover (by decide +kernel)

def src676 : Request := ⟨⟨⟨992,1379,296,57102⟩,29193692774400,99015216989⟩,0,3,1,385979,5⟩

theorem rank676 : P3_7_1.BankOK src676.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_296 57102

theorem width676 : Lower6960.HelperSource.WidthGuard src676.bank 179730 2308 src676.reserve := requestWidth (by decide)

def ends676 : List ℕ := [2308, 2309, 2313]

theorem inside676 : Research6966.TerminalBanks.inside src676.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover676 : Cover (Triangular src676) 2313 2308 ends676 := triangleCover (by decide +kernel)

def src677 : Request := ⟨⟨⟨981,1363,296,64488⟩,28475152662528,95368174997⟩,1,3,1,385979,5⟩

theorem rank677 : P3_7_1.BankOK src677.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_981_1363_296 64488

theorem width677 : Lower6960.HelperSource.WidthGuard src677.bank 179730 2308 src677.reserve := requestWidth (by decide)

def ends677 : List ℕ := [2308, 2309, 2313]

theorem inside677 : Research6966.TerminalBanks.inside src677.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover677 : Cover (Triangular src677) 2313 2308 ends677 := triangleCover (by decide +kernel)

def src678 : Request := ⟨⟨⟨1203,1674,361,66459⟩,52246486712320,215563369662⟩,2,3,1,386273,5⟩

theorem rank678 : P3_7_1.BankOK src678.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_361 66459

theorem width678 : Lower6960.HelperSource.WidthGuard src678.bank 179730 2308 src678.reserve := requestWidth (by decide)

def ends678 : List ℕ := [2308, 2309, 2313]

theorem inside678 : Research6966.TerminalBanks.inside src678.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover678 : Cover (Triangular src678) 2313 2308 ends678 := triangleCover (by decide +kernel)

def src679 : Request := ⟨⟨⟨1203,1674,361,74056⟩,52246486712320,215563369662⟩,3,3,1,386273,5⟩

theorem rank679 : P3_7_1.BankOK src679.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_361 74056

theorem width679 : Lower6960.HelperSource.WidthGuard src679.bank 179730 2308 src679.reserve := requestWidth (by decide)

def ends679 : List ℕ := [2308, 2309, 2313]

theorem inside679 : Research6966.TerminalBanks.inside src679.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover679 : Cover (Triangular src679) 2313 2308 ends679 := triangleCover (by decide +kernel)

def src68 : Request := ⟨⟨⟨2800,3905,854,31694⟩,665461916958720,6434729640882⟩,85,2,1,257319,52⟩

theorem rank68 : P3_7_1.BankOK src68.bank := by
  simpa only [src68, _root_.Research6969.TerminalAuxBanks.bank66] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank66 31694

theorem width68 : Lower6960.HelperSource.WidthGuard src68.bank 179730 2308 src68.reserve := requestWidth (by decide)

def ends68 : List ℕ := [2313]

theorem inside68 : Research6966.TerminalBanks.inside src68.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover68 : Cover (Triangular src68) 2313 2308 ends68 := triangleCover (by decide +kernel)

def src680 : Request := ⟨⟨⟨1203,1673,362,83332⟩,52356525326336,215613376984⟩,4,3,1,385979,5⟩

theorem rank680 : P3_7_1.BankOK src680.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1673_362 83332

theorem width680 : Lower6960.HelperSource.WidthGuard src680.bank 179730 2308 src680.reserve := requestWidth (by decide)

def ends680 : List ℕ := [2308, 2309, 2313]

theorem inside680 : Research6966.TerminalBanks.inside src680.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover680 : Cover (Triangular src680) 2313 2308 ends680 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources49

section Pack_R6970Height2313CommonSources51

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src71 : Request := ⟨⟨⟨2800,3889,854,27430⟩,665461916958720,6350238846402⟩,85,2,1,257319,53⟩

theorem rank71 : P3_7_1.BankOK src71.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3889_854 27430

theorem width71 : Lower6960.HelperSource.WidthGuard src71.bank 179730 2308 src71.reserve := requestWidth (by decide)

def ends71 : List ℕ := [2308, 2309, 2313]

theorem inside71 : Research6966.TerminalBanks.inside src71.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover71 : Cover (Triangular src71) 2313 2308 ends71 := triangleCover (by decide +kernel)

def src710 : Request := ⟨⟨⟨1202,1674,361,72277⟩,52149455421440,215563369662⟩,4,3,1,385979,8⟩

theorem rank710 : P3_7_1.BankOK src710.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_361 72277

theorem width710 : Lower6960.HelperSource.WidthGuard src710.bank 179730 2308 src710.reserve := requestWidth (by decide)

def ends710 : List ℕ := [2308, 2309, 2313]

theorem inside710 : Research6966.TerminalBanks.inside src710.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover710 : Cover (Triangular src710) 2313 2308 ends710 := triangleCover (by decide +kernel)

def src711 : Request := ⟨⟨⟨2086,2898,632,91798⟩,273930986455040,1949015201860⟩,10,3,1,385979,8⟩

theorem rank711 : P3_7_1.BankOK src711.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2086_2898_632 91798

theorem width711 : Lower6960.HelperSource.WidthGuard src711.bank 179730 2308 src711.reserve := requestWidth (by decide)

def ends711 : List ℕ := [2308, 2309, 2313]

theorem inside711 : Research6966.TerminalBanks.inside src711.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover711 : Cover (Triangular src711) 2313 2308 ends711 := triangleCover (by decide +kernel)

def src712 : Request := ⟨⟨⟨2607,3628,783,120668⟩,530938777829376,4745819470168⟩,16,3,1,386273,8⟩

theorem rank712 : P3_7_1.BankOK src712.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3628_783 120668

theorem width712 : Lower6960.HelperSource.WidthGuard src712.bank 179730 2308 src712.reserve := requestWidth (by decide)

def ends712 : List ℕ := [2308, 2309, 2313]

theorem inside712 : Research6966.TerminalBanks.inside src712.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover712 : Cover (Triangular src712) 2313 2308 ends712 := triangleCover (by decide +kernel)

def src713 : Request := ⟨⟨⟨2607,3627,789,446118⟩,534033714380800,4769913188218⟩,32,3,1,386273,8⟩

theorem rank713 : P3_7_1.BankOK src713.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3627_789 446118

theorem width713 : Lower6960.HelperSource.WidthGuard src713.bank 179730 2308 src713.reserve := requestWidth (by decide)

def ends713 : List ℕ := [2308, 2309, 2313]

theorem inside713 : Research6966.TerminalBanks.inside src713.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover713 : Cover (Triangular src713) 2313 2308 ends713 := triangleCover (by decide +kernel)

def src714 : Request := ⟨⟨⟨3939,5480,1189,195041⟩,1837247829114880,24786918035651⟩,32,3,1,386273,8⟩

theorem rank714 : P3_7_1.BankOK src714.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3939_5480_1189 195041

theorem width714 : Lower6960.HelperSource.WidthGuard src714.bank 179730 2308 src714.reserve := requestWidth (by decide)

def ends714 : List ℕ := [2308, 2309, 2313]




theorem cover714 : Cover (Triangular src714) 2313 2308 ends714 := triangleCover (by decide +kernel)

def src715 : Request := ⟨⟨⟨6908,9616,2077,351308⟩,9874987794825216,234024998385022⟩,65,3,1,386273,8⟩

theorem rank715 : P3_7_1.BankOK src715.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9616_2077 351308

theorem width715 : Lower6960.HelperSource.WidthGuard src715.bank 179730 2308 src715.reserve := requestWidth (by decide)

def ends715 : List ℕ := [2308, 2309, 2313]




theorem cover715 : Cover (Triangular src715) 2313 2308 ends715 := triangleCover (by decide +kernel)

def src716 : Request := ⟨⟨⟨10032,13954,3010,432081⟩,30189665893220352,1036364370066239⟩,85,3,1,386273,8⟩

theorem rank716 : P3_7_1.BankOK src716.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10032_13954_3010 432081

theorem width716 : Lower6960.HelperSource.WidthGuard src716.bank 179730 2308 src716.reserve := requestWidth (by decide)

def ends716 : List ℕ := [2308, 2309, 2313]




theorem cover716 : Cover (Triangular src716) 2313 2308 ends716 := triangleCover (by decide +kernel)

def src717 : Request := ⟨⟨⟨998,1387,301,45302⟩,29969050501120,102197851203⟩,0,3,1,385979,9⟩

theorem rank717 : P3_7_1.BankOK src717.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_998_1387_301 45302

theorem width717 : Lower6960.HelperSource.WidthGuard src717.bank 179730 2308 src717.reserve := requestWidth (by decide)

def ends717 : List ℕ := [2308, 2309, 2313]

theorem inside717 : Research6966.TerminalBanks.inside src717.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover717 : Cover (Triangular src717) 2313 2308 ends717 := triangleCover (by decide +kernel)

def src718 : Request := ⟨⟨⟨1002,1395,301,52012⟩,30238219960320,104105680031⟩,1,3,1,386273,9⟩

theorem rank718 : P3_7_1.BankOK src718.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 52012

theorem width718 : Lower6960.HelperSource.WidthGuard src718.bank 179730 2308 src718.reserve := requestWidth (by decide)

def ends718 : List ℕ := [2308, 2309, 2313]

theorem inside718 : Research6966.TerminalBanks.inside src718.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover718 : Cover (Triangular src718) 2313 2308 ends718 := triangleCover (by decide +kernel)

def src719 : Request := ⟨⟨⟨1004,1395,302,60378⟩,30449958387712,104374703492⟩,2,3,1,385979,9⟩

theorem rank719 : P3_7_1.BankOK src719.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_302 60378

theorem width719 : Lower6960.HelperSource.WidthGuard src719.bank 179730 2308 src719.reserve := requestWidth (by decide)

def ends719 : List ℕ := [2308, 2309, 2313]

theorem inside719 : Research6966.TerminalBanks.inside src719.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover719 : Cover (Triangular src719) 2313 2308 ends719 := triangleCover (by decide +kernel)

def src72 : Request := ⟨⟨⟨2603,3625,793,31694⟩,534252463063040,4780245027563⟩,85,2,1,257319,54⟩

theorem rank72 : P3_7_1.BankOK src72.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3625_793 31694

theorem width72 : Lower6960.HelperSource.WidthGuard src72.bank 179730 2308 src72.reserve := requestWidth (by decide)

def ends72 : List ℕ := [2308, 2309, 2313]

theorem inside72 : Research6966.TerminalBanks.inside src72.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover72 : Cover (Triangular src72) 2313 2308 ends72 := triangleCover (by decide +kernel)

def src720 : Request := ⟨⟨⟨1204,1674,362,67891⟩,52453872238592,216028185312⟩,4,3,1,385979,9⟩

theorem rank720 : P3_7_1.BankOK src720.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1204_1674_362 67891

theorem width720 : Lower6960.HelperSource.WidthGuard src720.bank 179730 2308 src720.reserve := requestWidth (by decide)

def ends720 : List ℕ := [2308, 2309, 2313]

theorem inside720 : Research6966.TerminalBanks.inside src720.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover720 : Cover (Triangular src720) 2313 2308 ends720 := triangleCover (by decide +kernel)

def src721 : Request := ⟨⟨⟨1456,2023,438,73954⟩,92738543157248,460791341260⟩,6,3,1,385979,9⟩

theorem rank721 : P3_7_1.BankOK src721.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_438 73954

theorem width721 : Lower6960.HelperSource.WidthGuard src721.bank 179730 2308 src721.reserve := requestWidth (by decide)

def ends721 : List ℕ := [2308, 2309, 2313]

theorem inside721 : Research6966.TerminalBanks.inside src721.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover721 : Cover (Triangular src721) 2313 2308 ends721 := triangleCover (by decide +kernel)

def src722 : Request := ⟨⟨⟨1756,2442,528,93739⟩,162536950857728,976638095087⟩,10,3,1,385979,9⟩

theorem rank722 : P3_7_1.BankOK src722.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1756_2442_528 93739

theorem width722 : Lower6960.HelperSource.WidthGuard src722.bank 179730 2308 src722.reserve := requestWidth (by decide)

def ends722 : List ℕ := [2308, 2309, 2313]

theorem inside722 : Research6966.TerminalBanks.inside src722.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover722 : Cover (Triangular src722) 2313 2308 ends722 := triangleCover (by decide +kernel)

def src723 : Request := ⟨⟨⟨2550,3558,770,115261⟩,498923410554880,4399607751447⟩,16,3,1,385979,9⟩

theorem rank723 : P3_7_1.BankOK src723.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2550_3558_770 115261

theorem width723 : Lower6960.HelperSource.WidthGuard src723.bank 179730 2308 src723.reserve := requestWidth (by decide)

def ends723 : List ℕ := [2308, 2309, 2313]

theorem inside723 : Research6966.TerminalBanks.inside src723.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover723 : Cover (Triangular src723) 2313 2308 ends723 := triangleCover (by decide +kernel)

def src724 : Request := ⟨⟨⟨3005,4178,900,174746⟩,811180468469760,8331876423452⟩,26,3,1,385979,9⟩

theorem rank724 : P3_7_1.BankOK src724.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3005_4178_900 174746

theorem width724 : Lower6960.HelperSource.WidthGuard src724.bank 179730 2308 src724.reserve := requestWidth (by decide)

def ends724 : List ℕ := [2308, 2309, 2313]

theorem inside724 : Research6966.TerminalBanks.inside src724.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover724 : Cover (Triangular src724) 2313 2308 ends724 := triangleCover (by decide +kernel)

def src725 : Request := ⟨⟨⟨3968,5512,1205,149820⟩,1886752633257984,25520385136463⟩,25,3,1,385979,9⟩

theorem rank725 : P3_7_1.BankOK src725.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3968_5512_1205 149820

theorem width725 : Lower6960.HelperSource.WidthGuard src725.bank 179730 2308 src725.reserve := requestWidth (by decide)

def ends725 : List ℕ := [2308, 2309, 2313]




theorem cover725 : Cover (Triangular src725) 2313 2308 ends725 := triangleCover (by decide +kernel)

def src726 : Request := ⟨⟨⟨2611,3627,791,427142⟩,536901863866368,4779330614481⟩,32,3,1,385979,9⟩

theorem rank726 : P3_7_1.BankOK src726.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2611_3627_791 427142

theorem width726 : Lower6960.HelperSource.WidthGuard src726.bank 179730 2308 src726.reserve := requestWidth (by decide)

def ends726 : List ℕ := [2308, 2309, 2313]

theorem inside726 : Research6966.TerminalBanks.inside src726.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover726 : Cover (Triangular src726) 2313 2308 ends726 := triangleCover (by decide +kernel)

def src727 : Request := ⟨⟨⟨4802,6682,1445,218754⟩,3320115406569472,54636500602517⟩,40,3,1,386273,9⟩

theorem rank727 : P3_7_1.BankOK src727.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4802_6682_1445 218754

theorem width727 : Lower6960.HelperSource.WidthGuard src727.bank 179730 2308 src727.reserve := requestWidth (by decide)

def ends727 : List ℕ := [2308, 2309, 2313]




theorem cover727 : Cover (Triangular src727) 2313 2308 ends727 := triangleCover (by decide +kernel)

def src728 : Request := ⟨⟨⟨4807,6689,1453,613327⟩,3341881529860096,55057550828510⟩,65,3,1,386273,9⟩

theorem rank728 : P3_7_1.BankOK src728.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4807_6689_1453 613327

theorem width728 : Lower6960.HelperSource.WidthGuard src728.bank 179730 2308 src728.reserve := requestWidth (by decide)

def ends728 : List ℕ := [2308, 2309, 2313]




theorem cover728 : Cover (Triangular src728) 2313 2308 ends728 := triangleCover (by decide +kernel)

def src729 : Request := ⟨⟨⟨10031,13953,3010,566374⟩,30182935399235584,1036125345444439⟩,110,3,1,386273,9⟩

theorem rank729 : P3_7_1.BankOK src729.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10031_13953_3010 566374

theorem width729 : Lower6960.HelperSource.WidthGuard src729.bank 179730 2308 src729.reserve := requestWidth (by decide)

def ends729 : List ℕ := [2308, 2309, 2313]




theorem cover729 : Cover (Triangular src729) 2313 2308 ends729 := triangleCover (by decide +kernel)

def src73 : Request := ⟨⟨⟨2614,3625,819,26892⟩,552677752176640,4901614794409⟩,85,2,1,257319,54⟩

theorem rank73 : P3_7_1.BankOK src73.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3625_819 26892

theorem width73 : Lower6960.HelperSource.WidthGuard src73.bank 179730 2308 src73.reserve := requestWidth (by decide)

def ends73 : List ℕ := [2309, 2313]

theorem inside73 : Research6966.TerminalBanks.inside src73.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover73 : Cover (Triangular src73) 2313 2308 ends73 := triangleCover (by decide +kernel)

def src730 : Request := ⟨⟨⟨994,1387,296,45069⟩,29325348569088,100873788737⟩,0,3,1,385979,10⟩

theorem rank730 : P3_7_1.BankOK src730.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_994_1387_296 45069

theorem width730 : Lower6960.HelperSource.WidthGuard src730.bank 179730 2308 src730.reserve := requestWidth (by decide)

def ends730 : List ℕ := [2308, 2309, 2313]

theorem inside730 : Research6966.TerminalBanks.inside src730.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover730 : Cover (Triangular src730) 2313 2308 ends730 := triangleCover (by decide +kernel)

def src731 : Request := ⟨⟨⟨1203,1673,362,46242⟩,52356525326336,215613376984⟩,1,3,1,385979,10⟩

theorem rank731 : P3_7_1.BankOK src731.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1673_362 46242

theorem width731 : Lower6960.HelperSource.WidthGuard src731.bank 179730 2308 src731.reserve := requestWidth (by decide)

def ends731 : List ℕ := [2308, 2309, 2313]

theorem inside731 : Research6966.TerminalBanks.inside src731.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover731 : Cover (Triangular src731) 2313 2308 ends731 := triangleCover (by decide +kernel)

def src732 : Request := ⟨⟨⟨1193,1658,361,50654⟩,51280444129280,209005943830⟩,2,3,1,385979,10⟩

theorem rank732 : P3_7_1.BankOK src732.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 50654

theorem width732 : Lower6960.HelperSource.WidthGuard src732.bank 179730 2308 src732.reserve := requestWidth (by decide)

def ends732 : List ℕ := [2308, 2309, 2313]

theorem inside732 : Research6966.TerminalBanks.inside src732.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover732 : Cover (Triangular src732) 2313 2308 ends732 := triangleCover (by decide +kernel)

def src733 : Request := ⟨⟨⟨1455,2023,438,58523⟩,92596187693056,460791341260⟩,4,3,1,385979,10⟩

theorem rank733 : P3_7_1.BankOK src733.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2023_438 58523

theorem width733 : Lower6960.HelperSource.WidthGuard src733.bank 179730 2308 src733.reserve := requestWidth (by decide)

def ends733 : List ℕ := [2308, 2309, 2313]

theorem inside733 : Research6966.TerminalBanks.inside src733.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover733 : Cover (Triangular src733) 2313 2308 ends733 := triangleCover (by decide +kernel)

def src734 : Request := ⟨⟨⟨1753,2440,527,75933⟩,161683200802816,972629061662⟩,8,3,1,386273,10⟩

theorem rank734 : P3_7_1.BankOK src734.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2440_527 75933

theorem width734 : Lower6960.HelperSource.WidthGuard src734.bank 179730 2308 src734.reserve := requestWidth (by decide)

def ends734 : List ℕ := [2308, 2309, 2313]

theorem inside734 : Research6966.TerminalBanks.inside src734.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover734 : Cover (Triangular src734) 2313 2308 ends734 := triangleCover (by decide +kernel)

def src735 : Request := ⟨⟨⟨2605,3625,783,107755⟩,530028320260096,4733203574232⟩,16,3,1,386273,10⟩

theorem rank735 : P3_7_1.BankOK src735.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3625_783 107755

theorem width735 : Lower6960.HelperSource.WidthGuard src735.bank 179730 2308 src735.reserve := requestWidth (by decide)

def ends735 : List ℕ := [2308, 2309, 2313]

theorem inside735 : Research6966.TerminalBanks.inside src735.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover735 : Cover (Triangular src735) 2313 2308 ends735 := triangleCover (by decide +kernel)

def src736 : Request := ⟨⟨⟨4805,6686,1445,171501⟩,3324756809482240,54741834824859⟩,32,3,1,386273,10⟩

theorem rank736 : P3_7_1.BankOK src736.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4805_6686_1445 171501

theorem width736 : Lower6960.HelperSource.WidthGuard src736.bank 179730 2308 src736.reserve := requestWidth (by decide)

def ends736 : List ℕ := [2308, 2309, 2313]




theorem cover736 : Cover (Triangular src736) 2313 2308 ends736 := triangleCover (by decide +kernel)

def src737 : Request := ⟨⟨⟨6896,9596,2077,312808⟩,9836655866019840,232461959482352⟩,65,3,1,386273,10⟩

theorem rank737 : P3_7_1.BankOK src737.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6896_9596_2077 312808

theorem width737 : Lower6960.HelperSource.WidthGuard src737.bank 179730 2308 src737.reserve := requestWidth (by decide)

def ends737 : List ℕ := [2308, 2309, 2313]




theorem cover737 : Cover (Triangular src737) 2313 2308 ends737 := triangleCover (by decide +kernel)

def src738 : Request := ⟨⟨⟨5715,7952,1728,1063301⟩,5616331038130176,109981062065525⟩,85,3,1,386273,10⟩

theorem rank738 : P3_7_1.BankOK src738.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5715_7952_1728 1063301

theorem width738 : Lower6960.HelperSource.WidthGuard src738.bank 179730 2308 src738.reserve := requestWidth (by decide)

def ends738 : List ℕ := [2308, 2309, 2313]




theorem cover738 : Cover (Triangular src738) 2313 2308 ends738 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources51

section Pack_R6970Height2313CommonSources54

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src797 : Request := ⟨⟨⟨2610,3628,793,102469⟩,537473153499136,4792991160379⟩,22,3,1,386273,15⟩

theorem rank797 : P3_7_1.BankOK src797.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 102469

theorem width797 : Lower6960.HelperSource.WidthGuard src797.bank 179730 2308 src797.reserve := requestWidth (by decide)

def ends797 : List ℕ := [2308, 2309, 2313]

theorem inside797 : Research6966.TerminalBanks.inside src797.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover797 : Cover (Triangular src797) 2313 2308 ends797 := triangleCover (by decide +kernel)

def src798 : Request := ⟨⟨⟨3208,4457,971,103863⟩,994804165509120,10884480876152⟩,25,3,1,385979,15⟩

theorem rank798 : P3_7_1.BankOK src798.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3208_4457_971 103863

theorem width798 : Lower6960.HelperSource.WidthGuard src798.bank 179730 2308 src798.reserve := requestWidth (by decide)

def ends798 : List ℕ := [2308, 2309, 2313]




theorem cover798 : Cover (Triangular src798) 2313 2308 ends798 := triangleCover (by decide +kernel)

def src799 : Request := ⟨⟨⟨2588,3611,767,262699⟩,514166406250496,4599905423586⟩,30,3,1,385979,15⟩

theorem rank799 : P3_7_1.BankOK src799.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3611_767 262699

theorem width799 : Lower6960.HelperSource.WidthGuard src799.bank 179730 2308 src799.reserve := requestWidth (by decide)

def ends799 : List ℕ := [2308, 2309, 2313]

theorem inside799 : Research6966.TerminalBanks.inside src799.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover799 : Cover (Triangular src799) 2313 2308 ends799 := triangleCover (by decide +kernel)

def src8 : Request := ⟨⟨⟨2300,3207,702,25043⟩,369170633195520,2930605494152⟩,85,1,1,128659,65⟩

theorem rank8 : P3_7_1.BankOK src8.bank := by
  simpa only [src8, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 25043

theorem width8 : Lower6960.HelperSource.WidthGuard src8.bank 179730 2308 src8.reserve := requestWidth (by decide)

def ends8 : List ℕ := [2308, 2309, 2313]

theorem inside8 : Research6966.TerminalBanks.inside src8.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover8 : Cover (Triangular src8) 2313 2308 ends8 := triangleCover (by decide +kernel)

def src80 : Request := ⟨⟨⟨2606,3624,775,28163⟩,526345409921024,4691256264577⟩,85,2,1,257319,58⟩

theorem rank80 : P3_7_1.BankOK src80.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3624_775 28163

theorem width80 : Lower6960.HelperSource.WidthGuard src80.bank 179730 2308 src80.reserve := requestWidth (by decide)

def ends80 : List ℕ := [2308, 2309, 2313]

theorem inside80 : Research6966.TerminalBanks.inside src80.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover80 : Cover (Triangular src80) 2313 2308 ends80 := triangleCover (by decide +kernel)

def src800 : Request := ⟨⟨⟨4800,6681,1449,196321⟩,3324016676044800,54728084477665⟩,50,3,1,385979,15⟩

theorem rank800 : P3_7_1.BankOK src800.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4800_6681_1449 196321

theorem width800 : Lower6960.HelperSource.WidthGuard src800.bank 179730 2308 src800.reserve := requestWidth (by decide)

def ends800 : List ℕ := [2308, 2309, 2313]




theorem cover800 : Cover (Triangular src800) 2313 2308 ends800 := triangleCover (by decide +kernel)

def src801 : Request := ⟨⟨⟨5715,7952,1728,736665⟩,5616331038130176,109981062065525⟩,85,3,1,386273,15⟩

theorem rank801 : P3_7_1.BankOK src801.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5715_7952_1728 736665

theorem width801 : Lower6960.HelperSource.WidthGuard src801.bank 179730 2308 src801.reserve := requestWidth (by decide)

def ends801 : List ℕ := [2308, 2309, 2313]




theorem cover801 : Cover (Triangular src801) 2313 2308 ends801 := triangleCover (by decide +kernel)

def src802 : Request := ⟨⟨⟨10044,13954,3070,268328⟩,30729017031393280,1052440252760428⟩,85,3,1,386273,15⟩

theorem rank802 : P3_7_1.BankOK src802.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10044_13954_3070 268328

theorem width802 : Lower6960.HelperSource.WidthGuard src802.bank 179730 2308 src802.reserve := requestWidth (by decide)

def ends802 : List ℕ := [2308, 2309, 2313]




theorem cover802 : Cover (Triangular src802) 2313 2308 ends802 := triangleCover (by decide +kernel)

def src803 : Request := ⟨⟨⟨998,1387,301,28026⟩,29969050501120,102197851203⟩,0,3,1,385979,16⟩

theorem rank803 : P3_7_1.BankOK src803.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_998_1387_301 28026

theorem width803 : Lower6960.HelperSource.WidthGuard src803.bank 179730 2308 src803.reserve := requestWidth (by decide)

def ends803 : List ℕ := [2308, 2309, 2313]

theorem inside803 : Research6966.TerminalBanks.inside src803.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover803 : Cover (Triangular src803) 2313 2308 ends803 := triangleCover (by decide +kernel)

def src804 : Request := ⟨⟨⟨992,1379,301,31606⟩,29567671336960,100313940775⟩,1,3,1,385979,16⟩

theorem rank804 : P3_7_1.BankOK src804.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 31606

theorem width804 : Lower6960.HelperSource.WidthGuard src804.bank 179730 2308 src804.reserve := requestWidth (by decide)

def ends804 : List ℕ := [2308, 2309, 2313]

theorem inside804 : Research6966.TerminalBanks.inside src804.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover804 : Cover (Triangular src804) 2313 2308 ends804 := triangleCover (by decide +kernel)

def src805 : Request := ⟨⟨⟨1205,1674,365,40971⟩,52882002411520,217419999532⟩,4,3,1,385979,16⟩

theorem rank805 : P3_7_1.BankOK src805.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_365 40971

theorem width805 : Lower6960.HelperSource.WidthGuard src805.bank 179730 2308 src805.reserve := requestWidth (by decide)

def ends805 : List ℕ := [2308, 2309, 2313]

theorem inside805 : Research6966.TerminalBanks.inside src805.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover805 : Cover (Triangular src805) 2313 2308 ends805 := triangleCover (by decide +kernel)

def src806 : Request := ⟨⟨⟨1735,2410,527,56963⟩,157993412853760,934671348902⟩,10,3,1,385979,16⟩

theorem rank806 : P3_7_1.BankOK src806.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1735_2410_527 56963

theorem width806 : Lower6960.HelperSource.WidthGuard src806.bank 179730 2308 src806.reserve := requestWidth (by decide)

def ends806 : List ℕ := [2308, 2309, 2313]

theorem inside806 : Research6966.TerminalBanks.inside src806.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover806 : Cover (Triangular src806) 2313 2308 ends806 := triangleCover (by decide +kernel)

def src807 : Request := ⟨⟨⟨2610,3628,793,94096⟩,537473153499136,4792991160379⟩,22,3,1,386273,16⟩

theorem rank807 : P3_7_1.BankOK src807.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 94096

theorem width807 : Lower6960.HelperSource.WidthGuard src807.bank 179730 2308 src807.reserve := requestWidth (by decide)

def ends807 : List ℕ := [2308, 2309, 2313]

theorem inside807 : Research6966.TerminalBanks.inside src807.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover807 : Cover (Triangular src807) 2313 2308 ends807 := triangleCover (by decide +kernel)

def src808 : Request := ⟨⟨⟨3214,4465,982,94689⟩,1007567605071872,11043969901736⟩,25,3,1,386273,16⟩

theorem rank808 : P3_7_1.BankOK src808.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3214_4465_982 94689

theorem width808 : Lower6960.HelperSource.WidthGuard src808.bank 179730 2308 src808.reserve := requestWidth (by decide)

def ends808 : List ℕ := [2308, 2309, 2313]




theorem cover808 : Cover (Triangular src808) 2313 2308 ends808 := triangleCover (by decide +kernel)

def src809 : Request := ⟨⟨⟨2600,3627,783,266702⟩,527755772952576,4741611634368⟩,32,3,1,385979,16⟩

theorem rank809 : P3_7_1.BankOK src809.bank := by
  simpa only [src809, _root_.Research6969.TransitionBanks.bank266] using _root_.Research6969.TransitionBanks.rank266 266702

theorem width809 : Lower6960.HelperSource.WidthGuard src809.bank 179730 2308 src809.reserve := requestWidth (by decide)

def ends809 : List ℕ := [2308, 2309, 2313]

theorem inside809 : Research6966.TerminalBanks.inside src809.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover809 : Cover (Triangular src809) 2313 2308 ends809 := triangleCover (by decide +kernel)

def src81 : Request := ⟨⟨⟨2599,3609,793,24476⟩,532416647659520,4712654891459⟩,85,2,1,257319,58⟩

theorem rank81 : P3_7_1.BankOK src81.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2599_3609_793 24476

theorem width81 : Lower6960.HelperSource.WidthGuard src81.bank 179730 2308 src81.reserve := requestWidth (by decide)

def ends81 : List ℕ := [2308, 2309, 2313]

theorem inside81 : Research6966.TerminalBanks.inside src81.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover81 : Cover (Triangular src81) 2313 2308 ends81 := triangleCover (by decide +kernel)

def src810 : Request := ⟨⟨⟨3217,4472,971,248547⟩,1001058965913600,11002827304772⟩,40,3,1,385979,16⟩

theorem rank810 : P3_7_1.BankOK src810.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3217_4472_971 248547

theorem width810 : Lower6960.HelperSource.WidthGuard src810.bank 179730 2308 src810.reserve := requestWidth (by decide)

def ends810 : List ℕ := [2308, 2309, 2313]




theorem cover810 : Cover (Triangular src810) 2313 2308 ends810 := triangleCover (by decide +kernel)

def src811 : Request := ⟨⟨⟨8328,11573,2506,266642⟩,17310999549050880,491877509700364⟩,85,3,1,385979,16⟩

theorem rank811 : P3_7_1.BankOK src811.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8328_11573_2506 266642

theorem width811 : Lower6960.HelperSource.WidthGuard src811.bank 179730 2308 src811.reserve := requestWidth (by decide)

def ends811 : List ℕ := [2308, 2309, 2313]




theorem cover811 : Cover (Triangular src811) 2313 2308 ends811 := triangleCover (by decide +kernel)

def src812 : Request := ⟨⟨⟨6920,9626,2093,1319556⟩,9971549386571776,236219430732676⟩,110,3,1,386273,16⟩

theorem rank812 : P3_7_1.BankOK src812.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6920_9626_2093 1319556

theorem width812 : Lower6960.HelperSource.WidthGuard src812.bank 179730 2308 src812.reserve := requestWidth (by decide)

def ends812 : List ℕ := [2308, 2309, 2313]




theorem cover812 : Cover (Triangular src812) 2313 2308 ends812 := triangleCover (by decide +kernel)

def src813 : Request := ⟨⟨⟨10044,13953,3042,340008⟩,30515504591142912,1044710637160035⟩,110,3,1,385979,16⟩

theorem rank813 : P3_7_1.BankOK src813.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10044_13953_3042 340008

theorem width813 : Lower6960.HelperSource.WidthGuard src813.bank 179730 2308 src813.reserve := requestWidth (by decide)

def ends813 : List ℕ := [2308, 2309, 2313]




theorem cover813 : Cover (Triangular src813) 2313 2308 ends813 := triangleCover (by decide +kernel)

def src814 : Request := ⟨⟨⟨1004,1395,303,25661⟩,30526532485120,104643421994⟩,0,3,1,385979,17⟩

theorem rank814 : P3_7_1.BankOK src814.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_303 25661

theorem width814 : Lower6960.HelperSource.WidthGuard src814.bank 179730 2308 src814.reserve := requestWidth (by decide)

def ends814 : List ℕ := [2308, 2309, 2313]

theorem inside814 : Research6966.TerminalBanks.inside src814.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover814 : Cover (Triangular src814) 2313 2308 ends814 := triangleCover (by decide +kernel)

def src815 : Request := ⟨⟨⟨1003,1394,305,28666⟩,30611065012224,104937588728⟩,1,3,1,385979,17⟩

theorem rank815 : P3_7_1.BankOK src815.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1394_305 28666

theorem width815 : Lower6960.HelperSource.WidthGuard src815.bank 179730 2308 src815.reserve := requestWidth (by decide)

def ends815 : List ℕ := [2308, 2309, 2313]

theorem inside815 : Research6966.TerminalBanks.inside src815.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover815 : Cover (Triangular src815) 2313 2308 ends815 := triangleCover (by decide +kernel)

def src816 : Request := ⟨⟨⟨1200,1674,361,31694⟩,51955677528064,215563369662⟩,2,3,1,385979,17⟩

theorem rank816 : P3_7_1.BankOK src816.bank := by
  simpa only [src816, _root_.Research6969.TransitionBanks.bank227] using _root_.Research6969.TransitionBanks.rank227 31694

theorem width816 : Lower6960.HelperSource.WidthGuard src816.bank 179730 2308 src816.reserve := requestWidth (by decide)

def ends816 : List ℕ := [2308, 2309, 2313]

theorem inside816 : Research6966.TerminalBanks.inside src816.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover816 : Cover (Triangular src816) 2313 2308 ends816 := triangleCover (by decide +kernel)

def src817 : Request := ⟨⟨⟨1205,1674,368,37201⟩,53211572207616,218807905514⟩,4,3,1,386273,17⟩

theorem rank817 : P3_7_1.BankOK src817.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 37201

theorem width817 : Lower6960.HelperSource.WidthGuard src817.bank 179730 2308 src817.reserve := requestWidth (by decide)

def ends817 : List ℕ := [2308, 2309, 2313]

theorem inside817 : Research6966.TerminalBanks.inside src817.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover817 : Cover (Triangular src817) 2313 2308 ends817 := triangleCover (by decide +kernel)

def src818 : Request := ⟨⟨⟨1456,2023,445,40759⟩,93862507577344,466511127281⟩,6,3,1,386273,17⟩

theorem rank818 : P3_7_1.BankOK src818.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 40759

theorem width818 : Lower6960.HelperSource.WidthGuard src818.bank 179730 2308 src818.reserve := requestWidth (by decide)

def ends818 : List ℕ := [2308, 2309, 2313]

theorem inside818 : Research6966.TerminalBanks.inside src818.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover818 : Cover (Triangular src818) 2313 2308 ends818 := triangleCover (by decide +kernel)

def src819 : Request := ⟨⟨⟨1757,2442,535,51550⟩,164382115889152,986705217985⟩,10,3,1,385979,17⟩

theorem rank819 : P3_7_1.BankOK src819.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2442_535 51550

theorem width819 : Lower6960.HelperSource.WidthGuard src819.bank 179730 2308 src819.reserve := requestWidth (by decide)

def ends819 : List ℕ := [2308, 2309, 2313]

theorem inside819 : Research6966.TerminalBanks.inside src819.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover819 : Cover (Triangular src819) 2313 2308 ends819 := triangleCover (by decide +kernel)

def src82 : Request := ⟨⟨⟨2312,3207,724,26989⟩,382338138112000,3001726552718⟩,85,2,1,257319,59⟩

theorem rank82 : P3_7_1.BankOK src82.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 26989

theorem width82 : Lower6960.HelperSource.WidthGuard src82.bank 179730 2308 src82.reserve := requestWidth (by decide)

def ends82 : List ℕ := [2309, 2313]

theorem inside82 : Research6966.TerminalBanks.inside src82.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover82 : Cover (Triangular src82) 2313 2308 ends82 := triangleCover (by decide +kernel)

def src820 : Request := ⟨⟨⟨2600,3628,783,81311⟩,527755772952576,4745819470168⟩,20,3,1,385979,17⟩

theorem rank820 : P3_7_1.BankOK src820.bank := by
  simpa only [src820, _root_.Research6969.TransitionBanks.bank270] using _root_.Research6969.TransitionBanks.rank270 81311

theorem width820 : Lower6960.HelperSource.WidthGuard src820.bank 179730 2308 src820.reserve := requestWidth (by decide)

def ends820 : List ℕ := [2308, 2309, 2313]

theorem inside820 : Research6966.TerminalBanks.inside src820.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover820 : Cover (Triangular src820) 2313 2308 ends820 := triangleCover (by decide +kernel)

def src821 : Request := ⟨⟨⟨2610,3628,793,85920⟩,537473153499136,4792991160379⟩,22,3,1,386273,17⟩

theorem rank821 : P3_7_1.BankOK src821.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 85920

theorem width821 : Lower6960.HelperSource.WidthGuard src821.bank 179730 2308 src821.reserve := requestWidth (by decide)

def ends821 : List ℕ := [2308, 2309, 2313]

theorem inside821 : Research6966.TerminalBanks.inside src821.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover821 : Cover (Triangular src821) 2313 2308 ends821 := triangleCover (by decide +kernel)

def src822 : Request := ⟨⟨⟨2608,3627,783,239569⟩,531394314895360,4741611634368⟩,32,3,1,385979,17⟩

theorem rank822 : P3_7_1.BankOK src822.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3627_783 239569

theorem width822 : Lower6960.HelperSource.WidthGuard src822.bank 179730 2308 src822.reserve := requestWidth (by decide)

def ends822 : List ℕ := [2308, 2309, 2313]

theorem inside822 : Research6966.TerminalBanks.inside src822.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover822 : Cover (Triangular src822) 2313 2308 ends822 := triangleCover (by decide +kernel)

def src823 : Request := ⟨⟨⟨3967,5511,1213,136350⟩,1895199936086016,25637257621145⟩,40,3,1,386273,17⟩

theorem rank823 : P3_7_1.BankOK src823.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3967_5511_1213 136350

theorem width823 : Lower6960.HelperSource.WidthGuard src823.bank 179730 2308 src823.reserve := requestWidth (by decide)

def ends823 : List ℕ := [2308, 2309, 2313]




theorem cover823 : Cover (Triangular src823) 2313 2308 ends823 := triangleCover (by decide +kernel)

def src824 : Request := ⟨⟨⟨5748,7984,1748,593701⟩,5739223187456000,112416216904324⟩,85,3,1,385979,17⟩

theorem rank824 : P3_7_1.BankOK src824.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5748_7984_1748 593701

theorem width824 : Lower6960.HelperSource.WidthGuard src824.bank 179730 2308 src824.reserve := requestWidth (by decide)

def ends824 : List ℕ := [2308, 2309, 2313]




theorem cover824 : Cover (Triangular src824) 2313 2308 ends824 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources54

section Pack_R6970Height2313CommonSources55

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src825 : Request := ⟨⟨⟨10043,13953,3070,307613⟩,30722166910091264,1052197377228338⟩,110,3,1,386273,17⟩

theorem rank825 : P3_7_1.BankOK src825.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10043_13953_3070 307613

theorem width825 : Lower6960.HelperSource.WidthGuard src825.bank 179730 2308 src825.reserve := requestWidth (by decide)

def ends825 : List ℕ := [2308, 2309, 2313]




theorem cover825 : Cover (Triangular src825) 2313 2308 ends825 := triangleCover (by decide +kernel)

def src826 : Request := ⟨⟨⟨829,1151,253,25591⟩,17348278353920,49010625289⟩,0,3,1,386273,18⟩

theorem rank826 : P3_7_1.BankOK src826.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_829_1151_253 25591

theorem width826 : Lower6960.HelperSource.WidthGuard src826.bank 179730 2308 src826.reserve := requestWidth (by decide)

def ends826 : List ℕ := [2308, 2309, 2313]

theorem inside826 : Research6966.TerminalBanks.inside src826.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover826 : Cover (Triangular src826) 2313 2308 ends826 := triangleCover (by decide +kernel)

def src827 : Request := ⟨⟨⟨1205,1674,368,25043⟩,53211572207616,218807905514⟩,1,3,1,385979,18⟩

theorem rank827 : P3_7_1.BankOK src827.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 25043

theorem width827 : Lower6960.HelperSource.WidthGuard src827.bank 179730 2308 src827.reserve := requestWidth (by decide)

def ends827 : List ℕ := [2308, 2309, 2313]

theorem inside827 : Research6966.TerminalBanks.inside src827.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover827 : Cover (Triangular src827) 2313 2308 ends827 := triangleCover (by decide +kernel)

def src828 : Request := ⟨⟨⟨1199,1666,361,28167⟩,51858930925568,212267437130⟩,2,3,1,385979,18⟩

theorem rank828 : P3_7_1.BankOK src828.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1199_1666_361 28167

theorem width828 : Lower6960.HelperSource.WidthGuard src828.bank 179730 2308 src828.reserve := requestWidth (by decide)

def ends828 : List ℕ := [2308, 2309, 2313]

theorem inside828 : Research6966.TerminalBanks.inside src828.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover828 : Cover (Triangular src828) 2313 2308 ends828 := triangleCover (by decide +kernel)

def src829 : Request := ⟨⟨⟨1201,1674,361,35655⟩,52052519026688,215563369662⟩,4,3,1,385979,18⟩

theorem rank829 : P3_7_1.BankOK src829.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_361 35655

theorem width829 : Lower6960.HelperSource.WidthGuard src829.bank 179730 2308 src829.reserve := requestWidth (by decide)

def ends829 : List ℕ := [2308, 2309, 2313]

theorem inside829 : Research6966.TerminalBanks.inside src829.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover829 : Cover (Triangular src829) 2313 2308 ends829 := triangleCover (by decide +kernel)

def src83 : Request := ⟨⟨⟨2305,3207,724,28173⟩,379747886694400,3001726552718⟩,85,2,1,257319,59⟩

theorem rank83 : P3_7_1.BankOK src83.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3207_724 28173

theorem width83 : Lower6960.HelperSource.WidthGuard src83.bank 179730 2308 src83.reserve := requestWidth (by decide)

def ends83 : List ℕ := [2308, 2309, 2313]

theorem inside83 : Research6966.TerminalBanks.inside src83.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover83 : Cover (Triangular src83) 2313 2308 ends83 := triangleCover (by decide +kernel)

def src830 : Request := ⟨⟨⟨1758,2442,537,46684⟩,165058594471936,989573241440⟩,10,3,1,386273,18⟩

theorem rank830 : P3_7_1.BankOK src830.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1758_2442_537 46684

theorem width830 : Lower6960.HelperSource.WidthGuard src830.bank 179730 2308 src830.reserve := requestWidth (by decide)

def ends830 : List ℕ := [2308, 2309, 2313]

theorem inside830 : Research6966.TerminalBanks.inside src830.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover830 : Cover (Triangular src830) 2313 2308 ends830 := triangleCover (by decide +kernel)

def src831 : Request := ⟨⟨⟨2811,3907,854,74060⟩,671327256576000,6445344460182⟩,22,3,1,386273,18⟩

theorem rank831 : P3_7_1.BankOK src831.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2811_3907_854 74060

theorem width831 : Lower6960.HelperSource.WidthGuard src831.bank 179730 2308 src831.reserve := requestWidth (by decide)

def ends831 : List ℕ := [2308, 2309, 2313]

theorem inside831 : Research6966.TerminalBanks.inside src831.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover831 : Cover (Triangular src831) 2313 2308 ends831 := triangleCover (by decide +kernel)

def src832 : Request := ⟨⟨⟨2579,3595,754,530820⟩,503556286709760,4474462064331⟩,32,3,1,386273,18⟩

theorem rank832 : P3_7_1.BankOK src832.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2579_3595_754 530820

theorem width832 : Lower6960.HelperSource.WidthGuard src832.bank 179730 2308 src832.reserve := requestWidth (by decide)

def ends832 : List ℕ := [2308, 2309, 2313]

theorem inside832 : Research6966.TerminalBanks.inside src832.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover832 : Cover (Triangular src832) 2313 2308 ends832 := triangleCover (by decide +kernel)

def src833 : Request := ⟨⟨⟨3968,5512,1213,93393⟩,1896269709312000,25652240151764⟩,32,3,1,386273,18⟩

theorem rank833 : P3_7_1.BankOK src833.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3968_5512_1213 93393

theorem width833 : Lower6960.HelperSource.WidthGuard src833.bank 179730 2308 src833.reserve := requestWidth (by decide)

def ends833 : List ℕ := [2308, 2309, 2313]




theorem cover833 : Cover (Triangular src833) 2313 2308 ends833 := triangleCover (by decide +kernel)

def src834 : Request := ⟨⟨⟨4823,6701,1470,295598⟩,3396762661289984,55880476263803⟩,65,3,1,385979,18⟩

theorem rank834 : P3_7_1.BankOK src834.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4823_6701_1470 295598

theorem width834 : Lower6960.HelperSource.WidthGuard src834.bank 179730 2308 src834.reserve := requestWidth (by decide)

def ends834 : List ℕ := [2308, 2309, 2313]




theorem cover834 : Cover (Triangular src834) 2313 2308 ends834 := triangleCover (by decide +kernel)

def src835 : Request := ⟨⟨⟨8337,11581,2548,215081⟩,17573887189712896,499402661779949⟩,85,3,1,386273,18⟩

theorem rank835 : P3_7_1.BankOK src835.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8337_11581_2548 215081

theorem width835 : Lower6960.HelperSource.WidthGuard src835.bank 179730 2308 src835.reserve := requestWidth (by decide)

def ends835 : List ℕ := [2308, 2309, 2313]




theorem cover835 : Cover (Triangular src835) 2313 2308 ends835 := triangleCover (by decide +kernel)

def src836 : Request := ⟨⟨⟨6908,9626,2077,1151383⟩,9874987794825216,234809190715807⟩,110,3,1,386273,18⟩

theorem rank836 : P3_7_1.BankOK src836.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9626_2077 1151383

theorem width836 : Lower6960.HelperSource.WidthGuard src836.bank 179730 2308 src836.reserve := requestWidth (by decide)

def ends836 : List ℕ := [2308, 2309, 2313]




theorem cover836 : Cover (Triangular src836) 2313 2308 ends836 := triangleCover (by decide +kernel)

def src837 : Request := ⟨⟨⟨829,1151,253,22984⟩,17348278353920,49010625289⟩,0,3,1,386273,19⟩

theorem rank837 : P3_7_1.BankOK src837.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_829_1151_253 22984

theorem width837 : Lower6960.HelperSource.WidthGuard src837.bank 179730 2308 src837.reserve := requestWidth (by decide)

def ends837 : List ℕ := [2308, 2309, 2313]

theorem inside837 : Research6966.TerminalBanks.inside src837.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover837 : Cover (Triangular src837) 2313 2308 ends837 := triangleCover (by decide +kernel)

def src838 : Request := ⟨⟨⟨1205,1674,368,22791⟩,53211572207616,218807905514⟩,1,3,1,386273,19⟩

theorem rank838 : P3_7_1.BankOK src838.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 22791

theorem width838 : Lower6960.HelperSource.WidthGuard src838.bank 179730 2308 src838.reserve := requestWidth (by decide)

def ends838 : List ℕ := [2308, 2309, 2313]

theorem inside838 : Research6966.TerminalBanks.inside src838.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover838 : Cover (Triangular src838) 2313 2308 ends838 := triangleCover (by decide +kernel)

def src839 : Request := ⟨⟨⟨1182,1642,361,24895⟩,50228757790720,202585533550⟩,2,3,1,385979,19⟩

theorem rank839 : P3_7_1.BankOK src839.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1182_1642_361 24895

theorem width839 : Lower6960.HelperSource.WidthGuard src839.bank 179730 2308 src839.reserve := requestWidth (by decide)

def ends839 : List ℕ := [2308, 2309, 2313]

theorem inside839 : Research6966.TerminalBanks.inside src839.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover839 : Cover (Triangular src839) 2313 2308 ends839 := triangleCover (by decide +kernel)

def src84 : Request := ⟨⟨⟨2300,3207,702,28173⟩,369170633195520,2930605494152⟩,85,2,1,257319,61⟩

theorem rank84 : P3_7_1.BankOK src84.bank := by
  simpa only [src84, _root_.Research6969.TerminalAuxBanks.bank31] using _root_.Research6969.PackedRanks.TerminalRanks28To31.rank31 28173

theorem width84 : Lower6960.HelperSource.WidthGuard src84.bank 179730 2308 src84.reserve := requestWidth (by decide)

def ends84 : List ℕ := [2308, 2313]

theorem inside84 : Research6966.TerminalBanks.inside src84.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover84 : Cover (Triangular src84) 2313 2308 ends84 := triangleCover (by decide +kernel)

def src840 : Request := ⟨⟨⟨1200,1666,361,31655⟩,51955677528064,212267437130⟩,4,3,1,385979,19⟩

theorem rank840 : P3_7_1.BankOK src840.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1666_361 31655

theorem width840 : Lower6960.HelperSource.WidthGuard src840.bank 179730 2308 src840.reserve := requestWidth (by decide)

def ends840 : List ℕ := [2308, 2309, 2313]

theorem inside840 : Research6966.TerminalBanks.inside src840.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover840 : Cover (Triangular src840) 2313 2308 ends840 := triangleCover (by decide +kernel)

def src841 : Request := ⟨⟨⟨1456,2023,445,40561⟩,93862507577344,466511127281⟩,8,3,1,386273,19⟩

theorem rank841 : P3_7_1.BankOK src841.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 40561

theorem width841 : Lower6960.HelperSource.WidthGuard src841.bank 179730 2308 src841.reserve := requestWidth (by decide)

def ends841 : List ℕ := [2308, 2309, 2313]

theorem inside841 : Research6966.TerminalBanks.inside src841.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover841 : Cover (Triangular src841) 2313 2308 ends841 := triangleCover (by decide +kernel)

def src842 : Request := ⟨⟨⟨2106,2926,640,57923⟩,282531366436864,2030060368902⟩,16,3,1,385979,19⟩

theorem rank842 : P3_7_1.BankOK src842.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2106_2926_640 57923

theorem width842 : Lower6960.HelperSource.WidthGuard src842.bank 179730 2308 src842.reserve := requestWidth (by decide)

def ends842 : List ℕ := [2308, 2309, 2313]

theorem inside842 : Research6966.TerminalBanks.inside src842.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover842 : Cover (Triangular src842) 2313 2308 ends842 := triangleCover (by decide +kernel)

def src843 : Request := ⟨⟨⟨2611,3628,793,70369⟩,537934084702208,4792991160379⟩,22,3,1,386273,19⟩

theorem rank843 : P3_7_1.BankOK src843.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2611_3628_793 70369

theorem width843 : Lower6960.HelperSource.WidthGuard src843.bank 179730 2308 src843.reserve := requestWidth (by decide)

def ends843 : List ℕ := [2308, 2309, 2313]

theorem inside843 : Research6966.TerminalBanks.inside src843.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover843 : Cover (Triangular src843) 2313 2308 ends843 := triangleCover (by decide +kernel)

def src844 : Request := ⟨⟨⟨3168,4401,963,72260⟩,961192486502400,10383217925868⟩,25,3,1,385979,19⟩

theorem rank844 : P3_7_1.BankOK src844.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3168_4401_963 72260

theorem width844 : Lower6960.HelperSource.WidthGuard src844.bank 179730 2308 src844.reserve := requestWidth (by decide)

def ends844 : List ℕ := [2308, 2309, 2313]




theorem cover844 : Cover (Triangular src844) 2313 2308 ends844 := triangleCover (by decide +kernel)

def src845 : Request := ⟨⟨⟨2579,3595,754,475797⟩,503556286709760,4474462064331⟩,32,3,1,386273,19⟩

theorem rank845 : P3_7_1.BankOK src845.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2579_3595_754 475797

theorem width845 : Lower6960.HelperSource.WidthGuard src845.bank 179730 2308 src845.reserve := requestWidth (by decide)

def ends845 : List ℕ := [2308, 2309, 2313]

theorem inside845 : Research6966.TerminalBanks.inside src845.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover845 : Cover (Triangular src845) 2313 2308 ends845 := triangleCover (by decide +kernel)

def src846 : Request := ⟨⟨⟨3207,4456,967,184478⟩,990991186132992,10841682323769⟩,40,3,1,385979,19⟩

theorem rank846 : P3_7_1.BankOK src846.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3207_4456_967 184478

theorem width846 : Lower6960.HelperSource.WidthGuard src846.bank 179730 2308 src846.reserve := requestWidth (by decide)

def ends846 : List ℕ := [2308, 2309, 2313]




theorem cover846 : Cover (Triangular src846) 2313 2308 ends846 := triangleCover (by decide +kernel)

def src847 : Request := ⟨⟨⟨6931,9628,2118,151038⟩,10097893515460608,238575106344005⟩,65,3,1,386273,19⟩

theorem rank847 : P3_7_1.BankOK src847.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6931_9628_2118 151038

theorem width847 : Lower6960.HelperSource.WidthGuard src847.bank 179730 2308 src847.reserve := requestWidth (by decide)

def ends847 : List ℕ := [2308, 2309, 2313]




theorem cover847 : Cover (Triangular src847) 2313 2308 ends847 := triangleCover (by decide +kernel)

def src848 : Request := ⟨⟨⟨5748,7984,1748,466587⟩,5739223187456000,112416216904324⟩,85,3,1,385979,19⟩

theorem rank848 : P3_7_1.BankOK src848.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5748_7984_1748 466587

theorem width848 : Lower6960.HelperSource.WidthGuard src848.bank 179730 2308 src848.reserve := requestWidth (by decide)

def ends848 : List ℕ := [2308, 2309, 2313]




theorem cover848 : Cover (Triangular src848) 2313 2308 ends848 := triangleCover (by decide +kernel)

def src849 : Request := ⟨⟨⟨6908,9626,2077,1019855⟩,9874987794825216,234809190715807⟩,110,3,1,386273,19⟩

theorem rank849 : P3_7_1.BankOK src849.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9626_2077 1019855

theorem width849 : Lower6960.HelperSource.WidthGuard src849.bank 179730 2308 src849.reserve := requestWidth (by decide)

def ends849 : List ℕ := [2308, 2309, 2313]




theorem cover849 : Cover (Triangular src849) 2313 2308 ends849 := triangleCover (by decide +kernel)

def src85 : Request := ⟨⟨⟨2312,3207,724,23957⟩,382338138112000,3001726552718⟩,85,2,1,257319,61⟩

theorem rank85 : P3_7_1.BankOK src85.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 23957

theorem width85 : Lower6960.HelperSource.WidthGuard src85.bank 179730 2308 src85.reserve := requestWidth (by decide)

def ends85 : List ℕ := [2309, 2313]

theorem inside85 : Research6966.TerminalBanks.inside src85.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover85 : Cover (Triangular src85) 2313 2308 ends85 := triangleCover (by decide +kernel)

def src850 : Request := ⟨⟨⟨1000,1391,301,19700⟩,30103476895744,103148766153⟩,0,3,1,385979,20⟩

theorem rank850 : P3_7_1.BankOK src850.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_301 19700

theorem width850 : Lower6960.HelperSource.WidthGuard src850.bank 179730 2308 src850.reserve := requestWidth (by decide)

def ends850 : List ℕ := [2308, 2309, 2313]

theorem inside850 : Research6966.TerminalBanks.inside src850.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover850 : Cover (Triangular src850) 2313 2308 ends850 := triangleCover (by decide +kernel)

def src851 : Request := ⟨⟨⟨1002,1393,301,22186⟩,30238219960320,103626472018⟩,1,3,1,385979,20⟩

theorem rank851 : P3_7_1.BankOK src851.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1393_301 22186

theorem width851 : Lower6960.HelperSource.WidthGuard src851.bank 179730 2308 src851.reserve := requestWidth (by decide)

def ends851 : List ℕ := [2308, 2309, 2313]

theorem inside851 : Research6966.TerminalBanks.inside src851.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover851 : Cover (Triangular src851) 2313 2308 ends851 := triangleCover (by decide +kernel)

def src852 : Request := ⟨⟨⟨998,1387,301,24930⟩,29969050501120,102197851203⟩,2,3,1,385979,20⟩

theorem rank852 : P3_7_1.BankOK src852.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_998_1387_301 24930

theorem width852 : Lower6960.HelperSource.WidthGuard src852.bank 179730 2308 src852.reserve := requestWidth (by decide)

def ends852 : List ℕ := [2308, 2309, 2313]

theorem inside852 : Research6966.TerminalBanks.inside src852.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover852 : Cover (Triangular src852) 2313 2308 ends852 := triangleCover (by decide +kernel)

def src853 : Request := ⟨⟨⟨1193,1658,361,27986⟩,51280444129280,209005943830⟩,4,3,1,385979,20⟩

theorem rank853 : P3_7_1.BankOK src853.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 27986

theorem width853 : Lower6960.HelperSource.WidthGuard src853.bank 179730 2308 src853.reserve := requestWidth (by decide)

def ends853 : List ℕ := [2308, 2309, 2313]

theorem inside853 : Research6966.TerminalBanks.inside src853.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover853 : Cover (Triangular src853) 2313 2308 ends853 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources55

section Pack_R6970Height2313CommonSources56

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src854 : Request := ⟨⟨⟨1456,2023,445,36208⟩,93862507577344,466511127281⟩,8,3,1,386273,20⟩

theorem rank854 : P3_7_1.BankOK src854.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 36208

theorem width854 : Lower6960.HelperSource.WidthGuard src854.bank 179730 2308 src854.reserve := requestWidth (by decide)

def ends854 : List ℕ := [2308, 2309, 2313]

theorem inside854 : Research6966.TerminalBanks.inside src854.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover854 : Cover (Triangular src854) 2313 2308 ends854 := triangleCover (by decide +kernel)

def src855 : Request := ⟨⟨⟨2109,2930,645,51317⟩,285113516032000,2051392203643⟩,16,3,1,386273,20⟩

theorem rank855 : P3_7_1.BankOK src855.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2109_2930_645 51317

theorem width855 : Lower6960.HelperSource.WidthGuard src855.bank 179730 2308 src855.reserve := requestWidth (by decide)

def ends855 : List ℕ := [2308, 2309, 2313]

theorem inside855 : Research6966.TerminalBanks.inside src855.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover855 : Cover (Triangular src855) 2313 2308 ends855 := triangleCover (by decide +kernel)

def src856 : Request := ⟨⟨⟨2611,3628,793,63128⟩,537934084702208,4792991160379⟩,22,3,1,386273,20⟩

theorem rank856 : P3_7_1.BankOK src856.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2611_3628_793 63128

theorem width856 : Lower6960.HelperSource.WidthGuard src856.bank 179730 2308 src856.reserve := requestWidth (by decide)

def ends856 : List ℕ := [2308, 2309, 2313]

theorem inside856 : Research6966.TerminalBanks.inside src856.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover856 : Cover (Triangular src856) 2313 2308 ends856 := triangleCover (by decide +kernel)

def src857 : Request := ⟨⟨⟨2612,3628,798,75172⟩,540973467959296,4816500515660⟩,25,3,1,386273,20⟩

theorem rank857 : P3_7_1.BankOK src857.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_798 75172

theorem width857 : Lower6960.HelperSource.WidthGuard src857.bank 179730 2308 src857.reserve := requestWidth (by decide)

def ends857 : List ℕ := [2308, 2309, 2313]

theorem inside857 : Research6966.TerminalBanks.inside src857.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover857 : Cover (Triangular src857) 2313 2308 ends857 := triangleCover (by decide +kernel)

def src858 : Request := ⟨⟨⟨2579,3595,754,422931⟩,503556286709760,4474462064331⟩,32,3,1,386273,20⟩

theorem rank858 : P3_7_1.BankOK src858.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2579_3595_754 422931

theorem width858 : Lower6960.HelperSource.WidthGuard src858.bank 179730 2308 src858.reserve := requestWidth (by decide)

def ends858 : List ℕ := [2308, 2309, 2313]

theorem inside858 : Research6966.TerminalBanks.inside src858.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover858 : Cover (Triangular src858) 2313 2308 ends858 := triangleCover (by decide +kernel)

def src859 : Request := ⟨⟨⟨3220,4472,979,155005⟩,1009432193925120,11073399396491⟩,40,3,1,385979,20⟩

theorem rank859 : P3_7_1.BankOK src859.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3220_4472_979 155005

theorem width859 : Lower6960.HelperSource.WidthGuard src859.bank 179730 2308 src859.reserve := requestWidth (by decide)

def ends859 : List ℕ := [2308, 2309, 2313]




theorem cover859 : Cover (Triangular src859) 2313 2308 ends859 := triangleCover (by decide +kernel)

def src86 : Request := ⟨⟨⟨2777,3855,854,35655⟩,653285661081600,6173208282882⟩,115,2,1,257515,65⟩

theorem rank86 : P3_7_1.BankOK src86.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2777_3855_854 35655

theorem width86 : Lower6960.HelperSource.WidthGuard src86.bank 179730 2308 src86.reserve := requestWidth (by decide)

def ends86 : List ℕ := [2308, 2309, 2313]

theorem inside86 : Research6966.TerminalBanks.inside src86.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover86 : Cover (Triangular src86) 2313 2308 ends86 := triangleCover (by decide +kernel)

def src860 : Request := ⟨⟨⟨5725,7953,1750,153441⟩,5692888494899200,111115710437454⟩,65,3,1,386273,20⟩

theorem rank860 : P3_7_1.BankOK src860.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5725_7953_1750 153441

theorem width860 : Lower6960.HelperSource.WidthGuard src860.bank 179730 2308 src860.reserve := requestWidth (by decide)

def ends860 : List ℕ := [2308, 2309, 2313]




theorem cover860 : Cover (Triangular src860) 2313 2308 ends860 := triangleCover (by decide +kernel)

def src861 : Request := ⟨⟨⟨6908,9626,2077,889811⟩,9874987794825216,234809190715807⟩,110,3,1,386273,20⟩

theorem rank861 : P3_7_1.BankOK src861.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9626_2077 889811

theorem width861 : Lower6960.HelperSource.WidthGuard src861.bank 179730 2308 src861.reserve := requestWidth (by decide)

def ends861 : List ℕ := [2308, 2309, 2313]




theorem cover861 : Cover (Triangular src861) 2313 2308 ends861 := triangleCover (by decide +kernel)

def src862 : Request := ⟨⟨⟨10042,13953,3026,235514⟩,30379594832936960,1040421890790919⟩,110,3,1,385979,20⟩

theorem rank862 : P3_7_1.BankOK src862.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10042_13953_3026 235514

theorem width862 : Lower6960.HelperSource.WidthGuard src862.bank 179730 2308 src862.reserve := requestWidth (by decide)

def ends862 : List ℕ := [2308, 2309, 2313]




theorem cover862 : Cover (Triangular src862) 2313 2308 ends862 := triangleCover (by decide +kernel)

def src863 : Request := ⟨⟨⟨992,1379,301,17311⟩,29567671336960,100313940775⟩,0,3,1,385979,21⟩

theorem rank863 : P3_7_1.BankOK src863.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 17311

theorem width863 : Lower6960.HelperSource.WidthGuard src863.bank 179730 2308 src863.reserve := requestWidth (by decide)

def ends863 : List ℕ := [2308, 2309, 2313]

theorem inside863 : Research6966.TerminalBanks.inside src863.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover863 : Cover (Triangular src863) 2313 2308 ends863 := triangleCover (by decide +kernel)

def src864 : Request := ⟨⟨⟨998,1387,301,19638⟩,29969050501120,102197851203⟩,1,3,1,385979,21⟩

theorem rank864 : P3_7_1.BankOK src864.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_998_1387_301 19638

theorem width864 : Lower6960.HelperSource.WidthGuard src864.bank 179730 2308 src864.reserve := requestWidth (by decide)

def ends864 : List ℕ := [2308, 2309, 2313]

theorem inside864 : Research6966.TerminalBanks.inside src864.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover864 : Cover (Triangular src864) 2313 2308 ends864 := triangleCover (by decide +kernel)

def src865 : Request := ⟨⟨⟨992,1379,301,21928⟩,29567671336960,100313940775⟩,2,3,1,385979,21⟩

theorem rank865 : P3_7_1.BankOK src865.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 21928

theorem width865 : Lower6960.HelperSource.WidthGuard src865.bank 179730 2308 src865.reserve := requestWidth (by decide)

def ends865 : List ℕ := [2308, 2309, 2313]

theorem inside865 : Research6966.TerminalBanks.inside src865.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover865 : Cover (Triangular src865) 2313 2308 ends865 := triangleCover (by decide +kernel)

def src866 : Request := ⟨⟨⟨1203,1674,368,22261⟩,53014143959040,218807905514⟩,3,3,1,385979,21⟩

theorem rank866 : P3_7_1.BankOK src866.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_368 22261

theorem width866 : Lower6960.HelperSource.WidthGuard src866.bank 179730 2308 src866.reserve := requestWidth (by decide)

def ends866 : List ℕ := [2308, 2309, 2313]

theorem inside866 : Research6966.TerminalBanks.inside src866.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover866 : Cover (Triangular src866) 2313 2308 ends866 := triangleCover (by decide +kernel)

def src867 : Request := ⟨⟨⟨1182,1642,361,24611⟩,50228757790720,202585533550⟩,4,3,1,385979,21⟩

theorem rank867 : P3_7_1.BankOK src867.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1182_1642_361 24611

theorem width867 : Lower6960.HelperSource.WidthGuard src867.bank 179730 2308 src867.reserve := requestWidth (by decide)

def ends867 : List ℕ := [2308, 2309, 2313]

theorem inside867 : Research6966.TerminalBanks.inside src867.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover867 : Cover (Triangular src867) 2313 2308 ends867 := triangleCover (by decide +kernel)

def src868 : Request := ⟨⟨⟨1457,2023,445,32147⟩,94006840655872,466511127281⟩,8,3,1,386273,21⟩

theorem rank868 : P3_7_1.BankOK src868.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1457_2023_445 32147

theorem width868 : Lower6960.HelperSource.WidthGuard src868.bank 179730 2308 src868.reserve := requestWidth (by decide)

def ends868 : List ℕ := [2308, 2309, 2313]

theorem inside868 : Research6966.TerminalBanks.inside src868.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover868 : Cover (Triangular src868) 2313 2308 ends868 := triangleCover (by decide +kernel)

def src869 : Request := ⟨⟨⟨2612,3628,801,55467⟩,542517217198080,4830581955242⟩,22,3,1,385979,21⟩

theorem rank869 : P3_7_1.BankOK src869.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_801 55467

theorem width869 : Lower6960.HelperSource.WidthGuard src869.bank 179730 2308 src869.reserve := requestWidth (by decide)

def ends869 : List ℕ := [2308, 2309, 2313]

theorem inside869 : Research6966.TerminalBanks.inside src869.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover869 : Cover (Triangular src869) 2313 2308 ends869 := triangleCover (by decide +kernel)

def src87 : Request := ⟨⟨⟨2814,3903,882,31059⟩,689601573814272,6587245977411⟩,115,2,1,257319,65⟩

theorem rank87 : P3_7_1.BankOK src87.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2814_3903_882 31059

theorem width87 : Lower6960.HelperSource.WidthGuard src87.bank 179730 2308 src87.reserve := requestWidth (by decide)

def ends87 : List ℕ := [2308, 2309, 2313]

theorem inside87 : Research6966.TerminalBanks.inside src87.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover87 : Cover (Triangular src87) 2313 2308 ends87 := triangleCover (by decide +kernel)

def src870 : Request := ⟨⟨⟨2612,3628,798,66247⟩,540973467959296,4816500515660⟩,25,3,1,386273,21⟩

theorem rank870 : P3_7_1.BankOK src870.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_798 66247

theorem width870 : Lower6960.HelperSource.WidthGuard src870.bank 179730 2308 src870.reserve := requestWidth (by decide)

def ends870 : List ℕ := [2308, 2309, 2313]

theorem inside870 : Research6966.TerminalBanks.inside src870.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover870 : Cover (Triangular src870) 2313 2308 ends870 := triangleCover (by decide +kernel)

def src871 : Request := ⟨⟨⟨2425,3369,737,489842⟩,431245138329600,3566970195593⟩,33,3,1,385979,21⟩

theorem rank871 : P3_7_1.BankOK src871.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2425_3369_737 489842

theorem width871 : Lower6960.HelperSource.WidthGuard src871.bank 179730 2308 src871.reserve := requestWidth (by decide)

def ends871 : List ℕ := [2308, 2309, 2313]

theorem inside871 : Research6966.TerminalBanks.inside src871.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover871 : Cover (Triangular src871) 2313 2308 ends871 := triangleCover (by decide +kernel)

def src872 : Request := ⟨⟨⟨5725,7953,1750,135744⟩,5692888494899200,111115710437454⟩,65,3,1,386273,21⟩

theorem rank872 : P3_7_1.BankOK src872.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5725_7953_1750 135744

theorem width872 : Lower6960.HelperSource.WidthGuard src872.bank 179730 2308 src872.reserve := requestWidth (by decide)

def ends872 : List ℕ := [2308, 2309, 2313]




theorem cover872 : Cover (Triangular src872) 2313 2308 ends872 := triangleCover (by decide +kernel)

def src873 : Request := ⟨⟨⟨6919,9626,2085,716382⟩,9939282828984320,235514775615310⟩,110,3,1,386273,21⟩

theorem rank873 : P3_7_1.BankOK src873.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6919_9626_2085 716382

theorem width873 : Lower6960.HelperSource.WidthGuard src873.bank 179730 2308 src873.reserve := requestWidth (by decide)

def ends873 : List ℕ := [2308, 2309, 2313]




theorem cover873 : Cover (Triangular src873) 2313 2308 ends873 := triangleCover (by decide +kernel)

def src874 : Request := ⟨⟨⟨10029,13935,3026,210316⟩,30291674730856448,1036107350026597⟩,110,3,1,385979,21⟩

theorem rank874 : P3_7_1.BankOK src874.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10029_13935_3026 210316

theorem width874 : Lower6960.HelperSource.WidthGuard src874.bank 179730 2308 src874.reserve := requestWidth (by decide)

def ends874 : List ℕ := [2308, 2309, 2313]




theorem cover874 : Cover (Triangular src874) 2313 2308 ends874 := triangleCover (by decide +kernel)

def src875 : Request := ⟨⟨⟨8473,11810,2547,6207588⟩,18216515147923456,531735451845147⟩,145,3,1,386273,21⟩

theorem rank875 : P3_7_1.BankOK src875.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8473_11810_2547 6207588

theorem width875 : Lower6960.HelperSource.WidthGuard src875.bank 179730 2308 src875.reserve := requestWidth (by decide)

def ends875 : List ℕ := [2308, 2309, 2313]




theorem cover875 : Cover (Triangular src875) 2313 2308 ends875 := triangleCover (by decide +kernel)

def src876 : Request := ⟨⟨⟨826,1151,248,17590⟩,16949640429568,48256472894⟩,0,3,1,385979,22⟩

theorem rank876 : P3_7_1.BankOK src876.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_248 17590

theorem width876 : Lower6960.HelperSource.WidthGuard src876.bank 179730 2308 src876.reserve := requestWidth (by decide)

def ends876 : List ℕ := [2308, 2309, 2313]

theorem inside876 : Research6966.TerminalBanks.inside src876.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover876 : Cover (Triangular src876) 2313 2308 ends876 := triangleCover (by decide +kernel)

def src877 : Request := ⟨⟨⟨992,1379,301,17294⟩,29567671336960,100313940775⟩,1,3,1,385979,22⟩

theorem rank877 : P3_7_1.BankOK src877.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 17294

theorem width877 : Lower6960.HelperSource.WidthGuard src877.bank 179730 2308 src877.reserve := requestWidth (by decide)

def ends877 : List ℕ := [2308, 2309, 2313]

theorem inside877 : Research6966.TerminalBanks.inside src877.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover877 : Cover (Triangular src877) 2313 2308 ends877 := triangleCover (by decide +kernel)

def src878 : Request := ⟨⟨⟨992,1379,301,19485⟩,29567671336960,100313940775⟩,2,3,1,385979,22⟩

theorem rank878 : P3_7_1.BankOK src878.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 19485

theorem width878 : Lower6960.HelperSource.WidthGuard src878.bank 179730 2308 src878.reserve := requestWidth (by decide)

def ends878 : List ℕ := [2308, 2309, 2313]

theorem inside878 : Research6966.TerminalBanks.inside src878.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover878 : Cover (Triangular src878) 2313 2308 ends878 := triangleCover (by decide +kernel)

def src879 : Request := ⟨⟨⟨1205,1673,368,19784⟩,53211572207616,218387554859⟩,3,3,1,385979,22⟩

theorem rank879 : P3_7_1.BankOK src879.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1673_368 19784

theorem width879 : Lower6960.HelperSource.WidthGuard src879.bank 179730 2308 src879.reserve := requestWidth (by decide)

def ends879 : List ℕ := [2308, 2309, 2313]

theorem inside879 : Research6966.TerminalBanks.inside src879.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover879 : Cover (Triangular src879) 2313 2308 ends879 := triangleCover (by decide +kernel)

def src88 : Request := ⟨⟨⟨2800,3902,834,40111⟩,653560508579840,6301295063987⟩,150,2,1,257319,97⟩

theorem rank88 : P3_7_1.BankOK src88.bank := by
  simpa only [src88, _root_.Research6969.TerminalAuxBanks.bank61] using _root_.Research6969.PackedRanks.TerminalRanks60To63.rank61 40111

theorem width88 : Lower6960.HelperSource.WidthGuard src88.bank 179730 2308 src88.reserve := requestWidth (by decide)

def ends88 : List ℕ := [2308, 2313]

theorem inside88 : Research6966.TerminalBanks.inside src88.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover88 : Cover (Triangular src88) 2313 2308 ends88 := triangleCover (by decide +kernel)

def src880 : Request := ⟨⟨⟨1201,1674,368,22261⟩,52817102635008,218807905514⟩,4,3,1,385979,22⟩

theorem rank880 : P3_7_1.BankOK src880.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_368 22261

theorem width880 : Lower6960.HelperSource.WidthGuard src880.bank 179730 2308 src880.reserve := requestWidth (by decide)

def ends880 : List ℕ := [2308, 2309, 2313]

theorem inside880 : Research6966.TerminalBanks.inside src880.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover880 : Cover (Triangular src880) 2313 2308 ends880 := triangleCover (by decide +kernel)

def src881 : Request := ⟨⟨⟨1457,2023,445,28439⟩,94006840655872,466511127281⟩,8,3,1,386273,22⟩

theorem rank881 : P3_7_1.BankOK src881.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1457_2023_445 28439

theorem width881 : Lower6960.HelperSource.WidthGuard src881.bank 179730 2308 src881.reserve := requestWidth (by decide)

def ends881 : List ℕ := [2308, 2309, 2313]

theorem inside881 : Research6966.TerminalBanks.inside src881.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover881 : Cover (Triangular src881) 2313 2308 ends881 := triangleCover (by decide +kernel)

def src882 : Request := ⟨⟨⟨2613,3628,801,51641⟩,542982372065280,4830581955242⟩,23,3,1,385979,22⟩

theorem rank882 : P3_7_1.BankOK src882.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2613_3628_801 51641

theorem width882 : Lower6960.HelperSource.WidthGuard src882.bank 179730 2308 src882.reserve := requestWidth (by decide)

def ends882 : List ℕ := [2308, 2309, 2313]

theorem inside882 : Research6966.TerminalBanks.inside src882.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover882 : Cover (Triangular src882) 2313 2308 ends882 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources56

section Pack_R6970Height2313CommonSources57

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src883 : Request := ⟨⟨⟨2612,3628,798,58059⟩,540973467959296,4816500515660⟩,25,3,1,386273,22⟩

theorem rank883 : P3_7_1.BankOK src883.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_798 58059

theorem width883 : Lower6960.HelperSource.WidthGuard src883.bank 179730 2308 src883.reserve := requestWidth (by decide)

def ends883 : List ℕ := [2308, 2309, 2313]

theorem inside883 : Research6966.TerminalBanks.inside src883.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover883 : Cover (Triangular src883) 2313 2308 ends883 := triangleCover (by decide +kernel)

def src884 : Request := ⟨⟨⟨2425,3369,737,393077⟩,431245138329600,3566970195593⟩,33,3,1,385979,22⟩

theorem rank884 : P3_7_1.BankOK src884.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2425_3369_737 393077

theorem width884 : Lower6960.HelperSource.WidthGuard src884.bank 179730 2308 src884.reserve := requestWidth (by decide)

def ends884 : List ℕ := [2308, 2309, 2313]

theorem inside884 : Research6966.TerminalBanks.inside src884.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover884 : Cover (Triangular src884) 2313 2308 ends884 := triangleCover (by decide +kernel)

def src885 : Request := ⟨⟨⟨5726,7953,1750,119540⟩,5695115172511744,111115710437454⟩,65,3,1,386273,22⟩

theorem rank885 : P3_7_1.BankOK src885.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5726_7953_1750 119540

theorem width885 : Lower6960.HelperSource.WidthGuard src885.bank 179730 2308 src885.reserve := requestWidth (by decide)

def ends885 : List ℕ := [2308, 2309, 2313]




theorem cover885 : Cover (Triangular src885) 2313 2308 ends885 := triangleCover (by decide +kernel)

def src886 : Request := ⟨⟨⟨6914,9626,2077,634919⟩,9894183174930432,234809190715807⟩,110,3,1,386273,22⟩

theorem rank886 : P3_7_1.BankOK src886.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6914_9626_2077 634919

theorem width886 : Lower6960.HelperSource.WidthGuard src886.bank 179730 2308 src886.reserve := requestWidth (by decide)

def ends886 : List ℕ := [2308, 2309, 2313]




theorem cover886 : Cover (Triangular src886) 2313 2308 ends886 := triangleCover (by decide +kernel)

def src887 : Request := ⟨⟨⟨10004,13937,3026,189808⟩,30122974528667648,1036586141451239⟩,110,3,1,385979,22⟩

theorem rank887 : P3_7_1.BankOK src887.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10004_13937_3026 189808

theorem width887 : Lower6960.HelperSource.WidthGuard src887.bank 179730 2308 src887.reserve := requestWidth (by decide)

def ends887 : List ℕ := [2308, 2309, 2313]




theorem cover887 : Cover (Triangular src887) 2313 2308 ends887 := triangleCover (by decide +kernel)

def src888 : Request := ⟨⟨⟨8473,11810,2547,5073467⟩,18216515147923456,531735451845147⟩,145,3,1,386273,22⟩

theorem rank888 : P3_7_1.BankOK src888.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8473_11810_2547 5073467

theorem width888 : Lower6960.HelperSource.WidthGuard src888.bank 179730 2308 src888.reserve := requestWidth (by decide)

def ends888 : List ℕ := [2308, 2309, 2313]




theorem cover888 : Cover (Triangular src888) 2313 2308 ends888 := triangleCover (by decide +kernel)

def src889 : Request := ⟨⟨⟨1004,1395,307,13899⟩,30831793405952,105715278267⟩,0,3,1,385979,23⟩

theorem rank889 : P3_7_1.BankOK src889.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_307 13899

theorem width889 : Lower6960.HelperSource.WidthGuard src889.bank 179730 2308 src889.reserve := requestWidth (by decide)

def ends889 : List ℕ := [2308, 2309, 2313]

theorem inside889 : Research6966.TerminalBanks.inside src889.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover889 : Cover (Triangular src889) 2313 2308 ends889 := triangleCover (by decide +kernel)

def src89 : Request := ⟨⟨⟨2765,3838,854,31356⟩,646979899883520,6085966034562⟩,150,2,1,257319,97⟩

theorem rank89 : P3_7_1.BankOK src89.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2765_3838_854 31356

theorem width89 : Lower6960.HelperSource.WidthGuard src89.bank 179730 2308 src89.reserve := requestWidth (by decide)

def ends89 : List ℕ := [2308, 2309, 2313]

theorem inside89 : Research6966.TerminalBanks.inside src89.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover89 : Cover (Triangular src89) 2313 2308 ends89 := triangleCover (by decide +kernel)

def src890 : Request := ⟨⟨⟨1000,1395,307,15636⟩,30557599170560,105715278267⟩,1,3,1,385979,23⟩

theorem rank890 : P3_7_1.BankOK src890.bank := by
  simpa only [src890, _root_.Research6969.TransitionBanks.bank222] using _root_.Research6969.TransitionBanks.rank222 15636

theorem width890 : Lower6960.HelperSource.WidthGuard src890.bank 179730 2308 src890.reserve := requestWidth (by decide)

def ends890 : List ℕ := [2308, 2309, 2313]

theorem inside890 : Research6966.TerminalBanks.inside src890.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover890 : Cover (Triangular src890) 2313 2308 ends890 := triangleCover (by decide +kernel)

def src891 : Request := ⟨⟨⟨992,1379,301,17295⟩,29567671336960,100313940775⟩,2,3,1,385979,23⟩

theorem rank891 : P3_7_1.BankOK src891.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 17295

theorem width891 : Lower6960.HelperSource.WidthGuard src891.bank 179730 2308 src891.reserve := requestWidth (by decide)

def ends891 : List ℕ := [2308, 2309, 2313]

theorem inside891 : Research6966.TerminalBanks.inside src891.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover891 : Cover (Triangular src891) 2313 2308 ends891 := triangleCover (by decide +kernel)

def src892 : Request := ⟨⟨⟨1201,1674,368,19788⟩,52817102635008,218807905514⟩,4,3,1,385979,23⟩

theorem rank892 : P3_7_1.BankOK src892.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1674_368 19788

theorem width892 : Lower6960.HelperSource.WidthGuard src892.bank 179730 2308 src892.reserve := requestWidth (by decide)

def ends892 : List ℕ := [2308, 2309, 2313]

theorem inside892 : Research6966.TerminalBanks.inside src892.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover892 : Cover (Triangular src892) 2313 2308 ends892 := triangleCover (by decide +kernel)

def src893 : Request := ⟨⟨⟨1451,2015,445,25039⟩,93142595928064,460599143061⟩,8,3,1,385979,23⟩

theorem rank893 : P3_7_1.BankOK src893.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2015_445 25039

theorem width893 : Lower6960.HelperSource.WidthGuard src893.bank 179730 2308 src893.reserve := requestWidth (by decide)

def ends893 : List ℕ := [2308, 2309, 2313]

theorem inside893 : Research6966.TerminalBanks.inside src893.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover893 : Cover (Triangular src893) 2313 2308 ends893 := triangleCover (by decide +kernel)

def src894 : Request := ⟨⟨⟨2110,2930,645,47118⟩,285416220262400,2051392203643⟩,20,3,1,386273,23⟩

theorem rank894 : P3_7_1.BankOK src894.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2110_2930_645 47118

theorem width894 : Lower6960.HelperSource.WidthGuard src894.bank 179730 2308 src894.reserve := requestWidth (by decide)

def ends894 : List ℕ := [2308, 2309, 2313]

theorem inside894 : Research6966.TerminalBanks.inside src894.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover894 : Cover (Triangular src894) 2313 2308 ends894 := triangleCover (by decide +kernel)

def src895 : Request := ⟨⟨⟨2612,3628,797,45974⟩,540458353426432,4811802684982⟩,23,3,1,385979,23⟩

theorem rank895 : P3_7_1.BankOK src895.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_797 45974

theorem width895 : Lower6960.HelperSource.WidthGuard src895.bank 179730 2308 src895.reserve := requestWidth (by decide)

def ends895 : List ℕ := [2308, 2309, 2313]

theorem inside895 : Research6966.TerminalBanks.inside src895.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover895 : Cover (Triangular src895) 2313 2308 ends895 := triangleCover (by decide +kernel)

def src896 : Request := ⟨⟨⟨2924,4062,893,59131⟩,758553969950720,7563813743010⟩,30,3,1,386273,23⟩

theorem rank896 : P3_7_1.BankOK src896.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2924_4062_893 59131

theorem width896 : Lower6960.HelperSource.WidthGuard src896.bank 179730 2308 src896.reserve := requestWidth (by decide)

def ends896 : List ℕ := [2308, 2309, 2313]

theorem inside896 : Research6966.TerminalBanks.inside src896.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover896 : Cover (Triangular src896) 2313 2308 ends896 := triangleCover (by decide +kernel)

def src897 : Request := ⟨⟨⟨2347,3273,719,530820⟩,393355355750400,3188049024550⟩,32,3,1,386273,23⟩

theorem rank897 : P3_7_1.BankOK src897.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2347_3273_719 530820

theorem width897 : Lower6960.HelperSource.WidthGuard src897.bank 179730 2308 src897.reserve := requestWidth (by decide)

def ends897 : List ℕ := [2308, 2309, 2313]

theorem inside897 : Research6966.TerminalBanks.inside src897.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover897 : Cover (Triangular src897) 2313 2308 ends897 := triangleCover (by decide +kernel)

def src898 : Request := ⟨⟨⟨2754,3842,830,369020⟩,627492187013120,5972384579105⟩,39,3,1,386273,23⟩

theorem rank898 : P3_7_1.BankOK src898.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2754_3842_830 369020

theorem width898 : Lower6960.HelperSource.WidthGuard src898.bank 179730 2308 src898.reserve := requestWidth (by decide)

def ends898 : List ℕ := [2308, 2309, 2313]

theorem inside898 : Research6966.TerminalBanks.inside src898.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover898 : Cover (Triangular src898) 2313 2308 ends898 := triangleCover (by decide +kernel)

def src899 : Request := ⟨⟨⟨4800,6665,1474,81237⟩,3367547627110400,55035799050931⟩,50,3,1,385979,23⟩

theorem rank899 : P3_7_1.BankOK src899.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4800_6665_1474 81237

theorem width899 : Lower6960.HelperSource.WidthGuard src899.bank 179730 2308 src899.reserve := requestWidth (by decide)

def ends899 : List ℕ := [2308, 2309, 2313]




theorem cover899 : Cover (Triangular src899) 2313 2308 ends899 := triangleCover (by decide +kernel)

def src9 : Request := ⟨⟨⟨2800,3902,854,35655⟩,665461916958720,6418829718882⟩,150,1,1,128659,97⟩

theorem rank9 : P3_7_1.BankOK src9.bank := by
  simpa only [src9, _root_.Research6969.TerminalAuxBanks.bank62] using _root_.Research6969.PackedRanks.TerminalRanks60To63.rank62 35655

theorem width9 : Lower6960.HelperSource.WidthGuard src9.bank 179730 2308 src9.reserve := requestWidth (by decide)

def ends9 : List ℕ := [2313]

theorem inside9 : Research6966.TerminalBanks.inside src9.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover9 : Cover (Triangular src9) 2313 2308 ends9 := triangleCover (by decide +kernel)

def src90 : Request := ⟨⟨⟨2307,3204,702,34830⟩,371690023944192,2921790084349⟩,149,2,1,257319,129⟩

theorem rank90 : P3_7_1.BankOK src90.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3204_702 34830

theorem width90 : Lower6960.HelperSource.WidthGuard src90.bank 179730 2308 src90.reserve := requestWidth (by decide)

def ends90 : List ℕ := [2308, 2309, 2313]

theorem inside90 : Research6966.TerminalBanks.inside src90.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover90 : Cover (Triangular src90) 2313 2308 ends90 := triangleCover (by decide +kernel)

def src900 : Request := ⟨⟨⟨4821,6697,1474,140698⟩,3400628142080000,55891290082931⟩,65,3,1,386273,23⟩

theorem rank900 : P3_7_1.BankOK src900.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4821_6697_1474 140698

theorem width900 : Lower6960.HelperSource.WidthGuard src900.bank 179730 2308 src900.reserve := requestWidth (by decide)

def ends900 : List ℕ := [2308, 2309, 2313]




theorem cover900 : Cover (Triangular src900) 2313 2308 ends900 := triangleCover (by decide +kernel)

def src900000 : Request := ⟨⟨⟨557,773,170,9064⟩,5276975235072,10009662337⟩,10,3,2,385978,2⟩

theorem rank900000 : P3_7_1.BankOK src900000.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_557_773_170 9064

theorem width900000 : Lower6960.HelperSource.WidthGuard src900000.bank 179730 2308 src900000.reserve := requestWidth (by decide)

def ends900000 : List ℕ := [2308, 2309, 2313]

theorem inside900000 : Research6966.TerminalBanks.inside src900000.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover900000 : Cover (Triangular src900000) 2313 2308 ends900000 := triangleCover (by decide +kernel)

def src901 : Request := ⟨⟨⟨6874,9562,2077,507253⟩,9766584394186752,229821110674495⟩,110,3,1,386273,23⟩

theorem rank901 : P3_7_1.BankOK src901.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6874_9562_2077 507253

theorem width901 : Lower6960.HelperSource.WidthGuard src901.bank 179730 2308 src901.reserve := requestWidth (by decide)

def ends901 : List ℕ := [2308, 2309, 2313]




theorem cover901 : Cover (Triangular src901) 2313 2308 ends901 := triangleCover (by decide +kernel)

def src902 : Request := ⟨⟨⟨10005,13953,3070,164837⟩,30462458838384640,1052197377228338⟩,110,3,1,385979,23⟩

theorem rank902 : P3_7_1.BankOK src902.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10005_13953_3070 164837

theorem width902 : Lower6960.HelperSource.WidthGuard src902.bank 179730 2308 src902.reserve := requestWidth (by decide)

def ends902 : List ℕ := [2308, 2309, 2313]




theorem cover902 : Cover (Triangular src902) 2313 2308 ends902 := triangleCover (by decide +kernel)

def src903 : Request := ⟨⟨⟨8473,11810,2547,3948839⟩,18216515147923456,531735451845147⟩,145,3,1,386273,23⟩

theorem rank903 : P3_7_1.BankOK src903.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8473_11810_2547 3948839

theorem width903 : Lower6960.HelperSource.WidthGuard src903.bank 179730 2308 src903.reserve := requestWidth (by decide)

def ends903 : List ℕ := [2308, 2309, 2313]




theorem cover903 : Cover (Triangular src903) 2313 2308 ends903 := triangleCover (by decide +kernel)

def src904 : Request := ⟨⟨⟨827,1151,248,13899⟩,16995527950336,48256472894⟩,0,3,1,385979,24⟩

theorem rank904 : P3_7_1.BankOK src904.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_827_1151_248 13899

theorem width904 : Lower6960.HelperSource.WidthGuard src904.bank 179730 2308 src904.reserve := requestWidth (by decide)

def ends904 : List ℕ := [2308, 2309, 2313]

theorem inside904 : Research6966.TerminalBanks.inside src904.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover904 : Cover (Triangular src904) 2313 2308 ends904 := triangleCover (by decide +kernel)

def src905 : Request := ⟨⟨⟨1001,1395,307,13899⟩,30626026618880,105715278267⟩,1,3,1,385979,24⟩

theorem rank905 : P3_7_1.BankOK src905.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1001_1395_307 13899

theorem width905 : Lower6960.HelperSource.WidthGuard src905.bank 179730 2308 src905.reserve := requestWidth (by decide)

def ends905 : List ℕ := [2308, 2309, 2313]

theorem inside905 : Research6966.TerminalBanks.inside src905.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover905 : Cover (Triangular src905) 2313 2308 ends905 := triangleCover (by decide +kernel)

def src906 : Request := ⟨⟨⟨992,1379,301,15382⟩,29567671336960,100313940775⟩,2,3,1,385979,24⟩

theorem rank906 : P3_7_1.BankOK src906.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 15382

theorem width906 : Lower6960.HelperSource.WidthGuard src906.bank 179730 2308 src906.reserve := requestWidth (by decide)

def ends906 : List ℕ := [2308, 2309, 2313]

theorem inside906 : Research6966.TerminalBanks.inside src906.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover906 : Cover (Triangular src906) 2313 2308 ends906 := triangleCover (by decide +kernel)

def src907 : Request := ⟨⟨⟨1202,1674,368,17590⟩,52915574931456,218807905514⟩,4,3,1,385979,24⟩

theorem rank907 : P3_7_1.BankOK src907.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_368 17590

theorem width907 : Lower6960.HelperSource.WidthGuard src907.bank 179730 2308 src907.reserve := requestWidth (by decide)

def ends907 : List ℕ := [2308, 2309, 2313]

theorem inside907 : Research6966.TerminalBanks.inside src907.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover907 : Cover (Triangular src907) 2313 2308 ends907 := triangleCover (by decide +kernel)

def src908 : Request := ⟨⟨⟨1455,2021,445,22252⟩,93718291415040,465028319332⟩,8,3,1,385979,24⟩

theorem rank908 : P3_7_1.BankOK src908.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2021_445 22252

theorem width908 : Lower6960.HelperSource.WidthGuard src908.bank 179730 2308 src908.reserve := requestWidth (by decide)

def ends908 : List ℕ := [2308, 2309, 2313]

theorem inside908 : Research6966.TerminalBanks.inside src908.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover908 : Cover (Triangular src908) 2313 2308 ends908 := triangleCover (by decide +kernel)

def src909 : Request := ⟨⟨⟨2110,2930,646,40422⟩,285752121360384,2053865446192⟩,20,3,1,385979,24⟩

theorem rank909 : P3_7_1.BankOK src909.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2110_2930_646 40422

theorem width909 : Lower6960.HelperSource.WidthGuard src909.bank 179730 2308 src909.reserve := requestWidth (by decide)

def ends909 : List ℕ := [2308, 2309, 2313]

theorem inside909 : Research6966.TerminalBanks.inside src909.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover909 : Cover (Triangular src909) 2313 2308 ends909 := triangleCover (by decide +kernel)

def src91 : Request := ⟨⟨⟨2307,3204,702,34830⟩,371690023944192,2921790084349⟩,149,2,1,257319,129⟩

theorem rank91 : P3_7_1.BankOK src91.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3204_702 34830

theorem width91 : Lower6960.HelperSource.WidthGuard src91.bank 179730 2308 src91.reserve := requestWidth (by decide)

def ends91 : List ℕ := [2308, 2309, 2313]

theorem inside91 : Research6966.TerminalBanks.inside src91.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover91 : Cover (Triangular src91) 2313 2308 ends91 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources57

import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_ec9790ff7fc8ae2f
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks31
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks38
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks41
import ProximityPrize.SubmissionLower.Bundle6970_6ed322075960e0ab
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks47
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks54
import ProximityPrize.SubmissionLower.R6970Height2313SourceRanks
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Bundle6970_adf41cb1614b9a70
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks50
import ProximityPrize.SubmissionLower.Bundle6970_c51a423b59d0dd6b
import ProximityPrize.SubmissionLower.Bundle6970_fa0707633ba569a9
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks64
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks77
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks27
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks60
import ProximityPrize.SubmissionLower.Bundle6970_ceea66e6500ee0de
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Bundle6970_fa78e5af1890b063
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks65
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks68
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks72
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks73
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks78
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks56
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks63
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks67
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks61
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.R6970Height2313CommonRanks71
import ProximityPrize.SubmissionLower.Z6969Pack0596

section Pack_R6970Height2313CommonSources00

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def ord0 : Request := ⟨⟨⟨2801,3906,882,28173⟩,682478913454080,6603573924229⟩,32,1,1,128659,36⟩

theorem rankOrd0 : P3_7_1.BankOK ord0.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3906_882 28173

theorem widthOrd0 : Lower6960.HelperSource.WidthGuard ord0.bank 179730 2308 ord0.reserve := requestWidth (by decide)

def endsOrd0 : List ℕ := [2308, 2309, 2313]

theorem insideOrd0 : Research6966.TerminalBanks.inside ord0.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd0 : Cover (Triangular ord0) 2313 2308 endsOrd0 := triangleCover (by decide +kernel)

def ord1 : Request := ⟨⟨⟨2600,3626,793,28173⟩,532875289296896,4784491173220⟩,63,1,1,128659,48⟩

theorem rankOrd1 : P3_7_1.BankOK ord1.bank := by
  simpa only [ord1, _root_.Research6969.TerminalAuxBanks.bank48] using _root_.Research6969.PackedRanks.TerminalRanks48To51.rank48 28173

theorem widthOrd1 : Lower6960.HelperSource.WidthGuard ord1.bank 179730 2308 ord1.reserve := requestWidth (by decide)

def endsOrd1 : List ℕ := [2308, 2313]

theorem insideOrd1 : Research6966.TerminalBanks.inside ord1.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd1 : Cover (Triangular ord1) 2313 2308 endsOrd1 := triangleCover (by decide +kernel)

def ord101 : Request := ⟨⟨⟨2300,3208,702,64247⟩,369170633195520,2933547980091⟩,45,5,1,643299,1⟩

theorem rankOrd101 : P3_7_1.BankOK ord101.bank := by
  simpa only [ord101, _root_.Research6969.TerminalAuxBanks.bank33] using _root_.Research6969.PackedRanks.TerminalRanks32To35.rank33 64247

theorem widthOrd101 : Lower6960.HelperSource.WidthGuard ord101.bank 179730 2308 ord101.reserve := requestWidth (by decide)

def endsOrd101 : List ℕ := [2308, 2309, 2313]

theorem insideOrd101 : Research6966.TerminalBanks.inside ord101.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd101 : Cover (Triangular ord101) 2313 2308 endsOrd101 := triangleCover (by decide +kernel)

def ord102 : Request := ⟨⟨⟨2767,3841,854,81398⟩,648028618752000,6101300343282⟩,63,5,1,643299,3⟩

theorem rankOrd102 : P3_7_1.BankOK ord102.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2767_3841_854 81398

theorem widthOrd102 : Lower6960.HelperSource.WidthGuard ord102.bank 179730 2308 ord102.reserve := requestWidth (by decide)

def endsOrd102 : List ℕ := [2308, 2309, 2313]

theorem insideOrd102 : Research6966.TerminalBanks.inside ord102.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd102 : Cover (Triangular ord102) 2313 2308 endsOrd102 := triangleCover (by decide +kernel)

def ord103 : Request := ⟨⟨⟨2300,3208,702,57109⟩,369170633195520,2933547980091⟩,45,5,1,643299,6⟩

theorem rankOrd103 : P3_7_1.BankOK ord103.bank := by
  simpa only [ord103, _root_.Research6969.TerminalAuxBanks.bank33] using _root_.Research6969.PackedRanks.TerminalRanks32To35.rank33 57109

theorem widthOrd103 : Lower6960.HelperSource.WidthGuard ord103.bank 179730 2308 ord103.reserve := requestWidth (by decide)

def endsOrd103 : List ℕ := [2313]

theorem insideOrd103 : Research6966.TerminalBanks.inside ord103.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd103 : Cover (Triangular ord103) 2313 2308 endsOrd103 := triangleCover (by decide +kernel)

def ord104 : Request := ⟨⟨⟨2600,3626,793,72277⟩,532875289296896,4784491173220⟩,63,5,1,643299,10⟩

theorem rankOrd104 : P3_7_1.BankOK ord104.bank := by
  simpa only [ord104, _root_.Research6969.TerminalAuxBanks.bank48] using _root_.Research6969.PackedRanks.TerminalRanks48To51.rank48 72277

theorem widthOrd104 : Lower6960.HelperSource.WidthGuard ord104.bank 179730 2308 ord104.reserve := requestWidth (by decide)

def endsOrd104 : List ℕ := [2308, 2313]

theorem insideOrd104 : Research6966.TerminalBanks.inside ord104.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd104 : Cover (Triangular ord104) 2313 2308 endsOrd104 := triangleCover (by decide +kernel)

def ord105 : Request := ⟨⟨⟨2809,3901,854,57078⟩,670258813992960,6413535689982⟩,63,5,1,643299,15⟩

theorem rankOrd105 : P3_7_1.BankOK ord105.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3901_854 57078

theorem widthOrd105 : Lower6960.HelperSource.WidthGuard ord105.bank 179730 2308 ord105.reserve := requestWidth (by decide)

def endsOrd105 : List ℕ := [2308, 2309, 2313]

theorem insideOrd105 : Research6966.TerminalBanks.inside ord105.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd105 : Cover (Triangular ord105) 2313 2308 endsOrd105 := triangleCover (by decide +kernel)

def ord106 : Request := ⟨⟨⟨2789,3873,854,44903⟩,659623697448960,6266506033362⟩,63,5,1,643299,21⟩

theorem rankOrd106 : P3_7_1.BankOK ord106.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 44903

theorem widthOrd106 : Lower6960.HelperSource.WidthGuard ord106.bank 179730 2308 ord106.reserve := requestWidth (by decide)

def endsOrd106 : List ℕ := [2308, 2309, 2313]

theorem insideOrd106 : Research6966.TerminalBanks.inside ord106.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd106 : Cover (Triangular ord106) 2313 2308 endsOrd106 := triangleCover (by decide +kernel)

def ord107 : Request := ⟨⟨⟨2607,3626,819,35655⟩,549365140684800,4905972788959⟩,63,5,1,643299,27⟩

theorem rankOrd107 : P3_7_1.BankOK ord107.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3626_819 35655

theorem widthOrd107 : Lower6960.HelperSource.WidthGuard ord107.bank 179730 2308 ord107.reserve := requestWidth (by decide)

def endsOrd107 : List ℕ := [2308, 2309, 2313]

theorem insideOrd107 : Research6966.TerminalBanks.inside ord107.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd107 : Cover (Triangular ord107) 2313 2308 endsOrd107 := triangleCover (by decide +kernel)

def ord108 : Request := ⟨⟨⟨2810,3905,882,35655⟩,687405819494400,6598128215989⟩,85,5,1,643299,36⟩

theorem rankOrd108 : P3_7_1.BankOK ord108.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3905_882 35655

theorem widthOrd108 : Lower6960.HelperSource.WidthGuard ord108.bank 179730 2308 ord108.reserve := requestWidth (by decide)

def endsOrd108 : List ℕ := [2308, 2309, 2313]

theorem insideOrd108 : Research6966.TerminalBanks.inside ord108.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd108 : Cover (Triangular ord108) 2313 2308 endsOrd108 := triangleCover (by decide +kernel)

def ord109 : Request := ⟨⟨⟨2303,3207,724,28173⟩,379009525350400,3001726552718⟩,85,5,1,643299,48⟩

theorem rankOrd109 : P3_7_1.BankOK ord109.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3207_724 28173

theorem widthOrd109 : Lower6960.HelperSource.WidthGuard ord109.bank 179730 2308 ord109.reserve := requestWidth (by decide)

def endsOrd109 : List ℕ := [2308, 2309, 2313]

theorem insideOrd109 : Research6966.TerminalBanks.inside ord109.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd109 : Cover (Triangular ord109) 2313 2308 endsOrd109 := triangleCover (by decide +kernel)

def ord110 : Request := ⟨⟨⟨2600,3624,819,28173⟩,546063062138880,4897259437389⟩,115,5,1,643299,65⟩

theorem rankOrd110 : P3_7_1.BankOK ord110.bank := by
  simpa only [ord110, _root_.Research6969.TerminalAuxBanks.bank44] using _root_.Research6969.PackedRanks.TerminalRanks44To47.rank44 28173

theorem widthOrd110 : Lower6960.HelperSource.WidthGuard ord110.bank 179730 2308 ord110.reserve := requestWidth (by decide)

def endsOrd110 : List ℕ := [2308, 2313]

theorem insideOrd110 : Research6966.TerminalBanks.inside ord110.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd110 : Cover (Triangular ord110) 2313 2308 endsOrd110 := triangleCover (by decide +kernel)

def ord111 : Request := ⟨⟨⟨2600,3623,793,35655⟩,532875289296896,4771760428124⟩,150,5,1,643299,97⟩

theorem rankOrd111 : P3_7_1.BankOK ord111.bank := by
  simpa only [ord111, _root_.Research6969.TerminalAuxBanks.bank40] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank40 35655

theorem widthOrd111 : Lower6960.HelperSource.WidthGuard ord111.bank 179730 2308 ord111.reserve := requestWidth (by decide)

def endsOrd111 : List ℕ := [2313]

theorem insideOrd111 : Research6966.TerminalBanks.inside ord111.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd111 : Cover (Triangular ord111) 2313 2308 endsOrd111 := triangleCover (by decide +kernel)

def ord112 : Request := ⟨⟨⟨2800,3901,834,40072⟩,653560508579840,6296101689637⟩,195,5,1,643299,161⟩

theorem rankOrd112 : P3_7_1.BankOK ord112.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3901_834 40072

theorem widthOrd112 : Lower6960.HelperSource.WidthGuard ord112.bank 179730 2308 ord112.reserve := requestWidth (by decide)

def endsOrd112 : List ℕ := [2308, 2313]

theorem insideOrd112 : Research6966.TerminalBanks.inside ord112.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd112 : Cover (Triangular ord112) 2313 2308 endsOrd112 := triangleCover (by decide +kernel)

def ord113 : Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,5,1,643299,257⟩

theorem rankOrd113 : P3_7_1.BankOK ord113.bank := by
  simpa only [ord113, _root_.Research6969.TerminalAuxBanks.bank75] using _root_.Research6969.PackedRanks.TerminalRanks72To75.rank75 57109

theorem widthOrd113 : Lower6960.HelperSource.WidthGuard ord113.bank 179730 2308 ord113.reserve := requestWidth (by decide)

def endsOrd113 : List ℕ := [2308, 2309, 2313]

theorem insideOrd113 : Research6966.TerminalBanks.inside ord113.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd113 : Cover (Triangular ord113) 2313 2308 endsOrd113 := triangleCover (by decide +kernel)

def ord115 : Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,5,1,643299,513⟩

theorem rankOrd115 : P3_7_1.BankOK ord115.bank := by
  simpa only [ord115, _root_.Research6969.TerminalAuxBanks.bank38] using _root_.Research6969.PackedRanks.TerminalRanks36To39.rank38 63811

theorem widthOrd115 : Lower6960.HelperSource.WidthGuard ord115.bank 179730 2308 ord115.reserve := requestWidth (by decide)

def endsOrd115 : List ℕ := [2308, 2313]

theorem insideOrd115 : Research6966.TerminalBanks.inside ord115.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd115 : Cover (Triangular ord115) 2313 2308 endsOrd115 := triangleCover (by decide +kernel)

def ord116 : Request := ⟨⟨⟨3002,4175,897,113694⟩,807312748183552,8291009592869⟩,325,5,1,643789,1025⟩

theorem rankOrd116 : P3_7_1.BankOK ord116.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3002_4175_897 113694

theorem widthOrd116 : Lower6960.HelperSource.WidthGuard ord116.bank 179730 2308 ord116.reserve := requestWidth (by decide)

def endsOrd116 : List ℕ := [2308, 2309, 2313]

theorem insideOrd116 : Research6966.TerminalBanks.inside ord116.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd116 : Cover (Triangular ord116) 2313 2308 endsOrd116 := triangleCover (by decide +kernel)

def ord119 : Request := ⟨⟨⟨2000,2782,598,190194⟩,239038181933056,1636863891369⟩,250,5,1,643299,16385⟩

theorem rankOrd119 : P3_7_1.BankOK ord119.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2000_2782_598 190194

theorem widthOrd119 : Lower6960.HelperSource.WidthGuard ord119.bank 179730 2308 ord119.reserve := requestWidth (by decide)

def endsOrd119 : List ℕ := [2308, 2309, 2313]

theorem insideOrd119 : Research6966.TerminalBanks.inside ord119.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd119 : Cover (Triangular ord119) 2313 2308 endsOrd119 := triangleCover (by decide +kernel)

def ord121 : Request := ⟨⟨⟨2789,3873,854,72161⟩,659623697448960,6266506033362⟩,85,6,1,771959,1⟩

theorem rankOrd121 : P3_7_1.BankOK ord121.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2789_3873_854 72161

theorem widthOrd121 : Lower6960.HelperSource.WidthGuard ord121.bank 179730 2308 ord121.reserve := requestWidth (by decide)

def endsOrd121 : List ℕ := [2308, 2309, 2313]

theorem insideOrd121 : Research6966.TerminalBanks.inside ord121.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd121 : Cover (Triangular ord121) 2313 2308 endsOrd121 := triangleCover (by decide +kernel)

def ord122 : Request := ⟨⟨⟨2306,3207,724,50764⟩,380117352448000,3001726552718⟩,63,6,1,771959,3⟩

theorem rankOrd122 : P3_7_1.BankOK ord122.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2306_3207_724 50764

theorem widthOrd122 : Lower6960.HelperSource.WidthGuard ord122.bank 179730 2308 ord122.reserve := requestWidth (by decide)

def endsOrd122 : List ℕ := [2308, 2309, 2313]

theorem insideOrd122 : Research6966.TerminalBanks.inside ord122.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd122 : Cover (Triangular ord122) 2313 2308 endsOrd122 := triangleCover (by decide +kernel)

def ord123 : Request := ⟨⟨⟨2804,3905,882,64247⟩,684119132209152,6598128215989⟩,85,6,1,771959,6⟩

theorem rankOrd123 : P3_7_1.BankOK ord123.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2804_3905_882 64247

theorem widthOrd123 : Lower6960.HelperSource.WidthGuard ord123.bank 179730 2308 ord123.reserve := requestWidth (by decide)

def endsOrd123 : List ℕ := [2308, 2309, 2313]

theorem insideOrd123 : Research6966.TerminalBanks.inside ord123.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd123 : Cover (Triangular ord123) 2313 2308 endsOrd123 := triangleCover (by decide +kernel)

def ord124 : Request := ⟨⟨⟨2302,3207,702,45124⟩,369889537687552,2930605494152⟩,63,6,1,771959,10⟩

theorem rankOrd124 : P3_7_1.BankOK ord124.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3207_702 45124

theorem widthOrd124 : Lower6960.HelperSource.WidthGuard ord124.bank 179730 2308 ord124.reserve := requestWidth (by decide)

def endsOrd124 : List ℕ := [2308, 2309, 2313]

theorem insideOrd124 : Research6966.TerminalBanks.inside ord124.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd124 : Cover (Triangular ord124) 2313 2308 endsOrd124 := triangleCover (by decide +kernel)

def ord125 : Request := ⟨⟨⟨2303,3207,702,40111⟩,370249266364416,2930605494152⟩,63,6,1,771959,15⟩

theorem rankOrd125 : P3_7_1.BankOK ord125.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3207_702 40111

theorem widthOrd125 : Lower6960.HelperSource.WidthGuard ord125.bank 179730 2308 ord125.reserve := requestWidth (by decide)

def endsOrd125 : List ℕ := [2308, 2309, 2313]

theorem insideOrd125 : Research6966.TerminalBanks.inside ord125.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd125 : Cover (Triangular ord125) 2313 2308 endsOrd125 := triangleCover (by decide +kernel)

def ord126 : Request := ⟨⟨⟨2800,3905,882,45124⟩,681932636815360,6598128215989⟩,85,6,1,771959,21⟩

theorem rankOrd126 : P3_7_1.BankOK ord126.bank := by
  simpa only [ord126, _root_.Research6969.TerminalAuxBanks.bank67] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank67 45124

theorem widthOrd126 : Lower6960.HelperSource.WidthGuard ord126.bank 179730 2308 ord126.reserve := requestWidth (by decide)

def endsOrd126 : List ℕ := [2308, 2309, 2313]

theorem insideOrd126 : Research6966.TerminalBanks.inside ord126.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd126 : Cover (Triangular ord126) 2313 2308 endsOrd126 := triangleCover (by decide +kernel)

def ord127 : Request := ⟨⟨⟨2600,3625,819,40111⟩,546063062138880,4901614794409⟩,85,6,1,771959,27⟩

theorem rankOrd127 : P3_7_1.BankOK ord127.bank := by
  simpa only [ord127, _root_.Research6969.TransitionBanks.bank263] using _root_.Research6969.TransitionBanks.rank263 40111

theorem widthOrd127 : Lower6960.HelperSource.WidthGuard ord127.bank 179730 2308 ord127.reserve := requestWidth (by decide)

def endsOrd127 : List ℕ := [2308, 2309, 2313]

theorem insideOrd127 : Research6966.TerminalBanks.inside ord127.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd127 : Cover (Triangular ord127) 2313 2308 endsOrd127 := triangleCover (by decide +kernel)

def ord128 : Request := ⟨⟨⟨2287,3175,702,35485⟩,364515722002432,2837502581224⟩,85,6,1,771959,36⟩

theorem rankOrd128 : P3_7_1.BankOK ord128.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2287_3175_702 35485

theorem widthOrd128 : Lower6960.HelperSource.WidthGuard ord128.bank 179730 2308 ord128.reserve := requestWidth (by decide)

def endsOrd128 : List ℕ := [2308, 2309, 2313]

theorem insideOrd128 : Research6966.TerminalBanks.inside ord128.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd128 : Cover (Triangular ord128) 2313 2308 endsOrd128 := triangleCover (by decide +kernel)

def ord129 : Request := ⟨⟨⟨2800,3903,882,35655⟩,681932636815360,6587245977411⟩,115,6,1,771959,48⟩

theorem rankOrd129 : P3_7_1.BankOK ord129.bank := by
  simpa only [ord129, _root_.Research6969.TerminalAuxBanks.bank65] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank65 35655

theorem widthOrd129 : Lower6960.HelperSource.WidthGuard ord129.bank 179730 2308 ord129.reserve := requestWidth (by decide)

def endsOrd129 : List ℕ := [2308, 2313]

theorem insideOrd129 : Research6966.TerminalBanks.inside ord129.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd129 : Cover (Triangular ord129) 2313 2308 endsOrd129 := triangleCover (by decide +kernel)

def ord13 : Request := ⟨⟨⟨722,1002,221,67510⟩,11495983022080,28253679740⟩,85,1,1,128659,16385⟩

theorem rankOrd13 : P3_7_1.BankOK ord13.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_722_1002_221 67510

theorem widthOrd13 : Lower6960.HelperSource.WidthGuard ord13.bank 179730 2308 ord13.reserve := requestWidth (by decide)

def endsOrd13 : List ℕ := [2308, 2309, 2313]

theorem insideOrd13 : Research6966.TerminalBanks.inside ord13.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd13 : Cover (Triangular ord13) 2313 2308 endsOrd13 := triangleCover (by decide +kernel)

def ord130 : Request := ⟨⟨⟨2305,3206,724,31694⟩,379747886694400,2998712046218⟩,115,6,1,771959,65⟩

theorem rankOrd130 : P3_7_1.BankOK ord130.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3206_724 31694

theorem widthOrd130 : Lower6960.HelperSource.WidthGuard ord130.bank 179730 2308 ord130.reserve := requestWidth (by decide)

def endsOrd130 : List ℕ := [2308, 2309, 2313]

theorem insideOrd130 : Research6966.TerminalBanks.inside ord130.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd130 : Cover (Triangular ord130) 2313 2308 endsOrd130 := triangleCover (by decide +kernel)

def ord131 : Request := ⟨⟨⟨2601,3623,793,31694⟩,533334139076608,4771760428124⟩,150,6,1,771959,97⟩

theorem rankOrd131 : P3_7_1.BankOK ord131.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3623_793 31694

theorem widthOrd131 : Lower6960.HelperSource.WidthGuard ord131.bank 179730 2308 ord131.reserve := requestWidth (by decide)

def endsOrd131 : List ℕ := [2308, 2309, 2313]

theorem insideOrd131 : Research6966.TerminalBanks.inside ord131.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd131 : Cover (Triangular ord131) 2313 2308 endsOrd131 := triangleCover (by decide +kernel)

def ord132 : Request := ⟨⟨⟨2607,3621,793,45123⟩,536091608743936,4763286079225⟩,195,6,1,771959,161⟩

theorem rankOrd132 : P3_7_1.BankOK ord132.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3621_793 45123

theorem widthOrd132 : Lower6960.HelperSource.WidthGuard ord132.bank 179730 2308 ord132.reserve := requestWidth (by decide)

def endsOrd132 : List ℕ := [2308, 2309, 2313]

theorem insideOrd132 : Research6966.TerminalBanks.inside ord132.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd132 : Cover (Triangular ord132) 2313 2308 endsOrd132 := triangleCover (by decide +kernel)

def ord133 : Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,6,1,771959,257⟩

theorem rankOrd133 : P3_7_1.BankOK ord133.bank := by
  simpa only [ord133, _root_.Research6969.TerminalAuxBanks.bank75] using _root_.Research6969.PackedRanks.TerminalRanks72To75.rank75 57109

theorem widthOrd133 : Lower6960.HelperSource.WidthGuard ord133.bank 179730 2308 ord133.reserve := requestWidth (by decide)

def endsOrd133 : List ℕ := [2313]

theorem insideOrd133 : Research6966.TerminalBanks.inside ord133.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd133 : Cover (Triangular ord133) 2313 2308 endsOrd133 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources00

section Pack_R6970Height2313CommonSources01

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def ord134 : Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,6,1,771959,513⟩

theorem rankOrd134 : P3_7_1.BankOK ord134.bank := by
  simpa only [ord134, _root_.Research6969.TerminalAuxBanks.bank38] using _root_.Research6969.PackedRanks.TerminalRanks36To39.rank38 63811

theorem widthOrd134 : Lower6960.HelperSource.WidthGuard ord134.bank 179730 2308 ord134.reserve := requestWidth (by decide)

def endsOrd134 : List ℕ := [2313]

theorem insideOrd134 : Research6966.TerminalBanks.inside ord134.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd134 : Cover (Triangular ord134) 2313 2308 endsOrd134 := triangleCover (by decide +kernel)

def ord135 : Request := ⟨⟨⟨3000,4175,897,111809⟩,806110768660480,8291009592869⟩,325,6,1,771959,1025⟩

theorem rankOrd135 : P3_7_1.BankOK ord135.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4175_897 111809

theorem widthOrd135 : Lower6960.HelperSource.WidthGuard ord135.bank 179730 2308 ord135.reserve := requestWidth (by decide)

def endsOrd135 : List ℕ := [2308, 2309, 2313]

theorem insideOrd135 : Research6966.TerminalBanks.inside ord135.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd135 : Cover (Triangular ord135) 2313 2308 endsOrd135 := triangleCover (by decide +kernel)

def ord18 : Request := ⟨⟨⟨2816,3906,882,28173⟩,690700839813120,6603573924229⟩,32,2,1,257319,33⟩

theorem rankOrd18 : P3_7_1.BankOK ord18.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3906_882 28173

theorem widthOrd18 : Lower6960.HelperSource.WidthGuard ord18.bank 179730 2308 ord18.reserve := requestWidth (by decide)

def endsOrd18 : List ℕ := [2308, 2313]

theorem insideOrd18 : Research6966.TerminalBanks.inside ord18.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd18 : Cover (Triangular ord18) 2313 2308 endsOrd18 := triangleCover (by decide +kernel)

def ord19 : Request := ⟨⟨⟨2808,3906,882,31694⟩,686309331173376,6603573924229⟩,45,2,1,257319,36⟩

theorem rankOrd19 : P3_7_1.BankOK ord19.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3906_882 31694

theorem widthOrd19 : Lower6960.HelperSource.WidthGuard ord19.bank 179730 2308 ord19.reserve := requestWidth (by decide)

def endsOrd19 : List ℕ := [2308, 2309, 2313]

theorem insideOrd19 : Research6966.TerminalBanks.inside ord19.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd19 : Cover (Triangular ord19) 2313 2308 endsOrd19 := triangleCover (by decide +kernel)

def ord2 : Request := ⟨⟨⟨2600,3626,819,25043⟩,546063062138880,4905972788959⟩,63,1,1,128659,48⟩

theorem rankOrd2 : P3_7_1.BankOK ord2.bank := by
  simpa only [ord2, _root_.Research6969.TransitionBanks.bank265] using _root_.Research6969.TransitionBanks.rank265 25043

theorem widthOrd2 : Lower6960.HelperSource.WidthGuard ord2.bank 179730 2308 ord2.reserve := requestWidth (by decide)

def endsOrd2 : List ℕ := [2308, 2309, 2313]

theorem insideOrd2 : Research6966.TerminalBanks.inside ord2.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd2 : Cover (Triangular ord2) 2313 2308 endsOrd2 := triangleCover (by decide +kernel)

def ord21 : Request := ⟨⟨⟨2305,3208,724,22261⟩,379747886694400,3004743122568⟩,45,2,1,257319,41⟩

theorem rankOrd21 : P3_7_1.BankOK ord21.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3208_724 22261

theorem widthOrd21 : Lower6960.HelperSource.WidthGuard ord21.bank 179730 2308 ord21.reserve := requestWidth (by decide)

def endsOrd21 : List ℕ := [2309, 2313]

theorem insideOrd21 : Research6966.TerminalBanks.inside ord21.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd21 : Cover (Triangular ord21) 2313 2308 endsOrd21 := triangleCover (by decide +kernel)

def ord23 : Request := ⟨⟨⟨2301,3207,724,25043⟩,378271924224000,3001726552718⟩,63,2,1,257319,48⟩

theorem rankOrd23 : P3_7_1.BankOK ord23.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3207_724 25043

theorem widthOrd23 : Lower6960.HelperSource.WidthGuard ord23.bank 179730 2308 ord23.reserve := requestWidth (by decide)

def endsOrd23 : List ℕ := [2308, 2309, 2313]

theorem insideOrd23 : Research6966.TerminalBanks.inside ord23.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd23 : Cover (Triangular ord23) 2313 2308 endsOrd23 := triangleCover (by decide +kernel)

def ord26 : Request := ⟨⟨⟨2600,3625,819,25043⟩,546063062138880,4901614794409⟩,85,2,1,257319,57⟩

theorem rankOrd26 : P3_7_1.BankOK ord26.bank := by
  simpa only [ord26, _root_.Research6969.TransitionBanks.bank263] using _root_.Research6969.TransitionBanks.rank263 25043

theorem widthOrd26 : Lower6960.HelperSource.WidthGuard ord26.bank 179730 2308 ord26.reserve := requestWidth (by decide)

def endsOrd26 : List ℕ := [2313]

theorem insideOrd26 : Research6966.TerminalBanks.inside ord26.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd26 : Cover (Triangular ord26) 2313 2308 endsOrd26 := triangleCover (by decide +kernel)

def ord28 : Request := ⟨⟨⟨2300,3207,724,25043⟩,377903408742400,3001726552718⟩,85,2,1,257319,61⟩

theorem rankOrd28 : P3_7_1.BankOK ord28.bank := by
  simpa only [ord28, _root_.Research6969.TerminalAuxBanks.bank32] using _root_.Research6969.PackedRanks.TerminalRanks32To35.rank32 25043

theorem widthOrd28 : Lower6960.HelperSource.WidthGuard ord28.bank 179730 2308 ord28.reserve := requestWidth (by decide)

def endsOrd28 : List ℕ := [2309, 2313]

theorem insideOrd28 : Research6966.TerminalBanks.inside ord28.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd28 : Cover (Triangular ord28) 2313 2308 endsOrd28 := triangleCover (by decide +kernel)

def ord30 : Request := ⟨⟨⟨2806,3903,882,31694⟩,685213768744960,6587245977411⟩,115,2,1,257319,65⟩

theorem rankOrd30 : P3_7_1.BankOK ord30.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2806_3903_882 31694

theorem widthOrd30 : Lower6960.HelperSource.WidthGuard ord30.bank 179730 2308 ord30.reserve := requestWidth (by decide)

def endsOrd30 : List ℕ := [2308, 2309, 2313]

theorem insideOrd30 : Research6966.TerminalBanks.inside ord30.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd30 : Cover (Triangular ord30) 2313 2308 endsOrd30 := triangleCover (by decide +kernel)

def ord31 : Request := ⟨⟨⟨2308,3206,724,31694⟩,380856854118400,2998712046218⟩,115,2,1,257319,81⟩

theorem rankOrd31 : P3_7_1.BankOK ord31.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2308_3206_724 31694

theorem widthOrd31 : Lower6960.HelperSource.WidthGuard ord31.bank 179730 2308 ord31.reserve := requestWidth (by decide)

def endsOrd31 : List ℕ := [2308, 2309, 2313]

theorem insideOrd31 : Research6966.TerminalBanks.inside ord31.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd31 : Cover (Triangular ord31) 2313 2308 endsOrd31 := triangleCover (by decide +kernel)

def ord33 : Request := ⟨⟨⟨2787,3870,854,31545⟩,658565116723200,6250890231282⟩,150,2,1,257319,97⟩

theorem rankOrd33 : P3_7_1.BankOK ord33.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2787_3870_854 31545

theorem widthOrd33 : Lower6960.HelperSource.WidthGuard ord33.bank 179730 2308 ord33.reserve := requestWidth (by decide)

def endsOrd33 : List ℕ := [2308, 2309, 2313]

theorem insideOrd33 : Research6966.TerminalBanks.inside ord33.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd33 : Cover (Triangular ord33) 2313 2308 endsOrd33 := triangleCover (by decide +kernel)

def ord34 : Request := ⟨⟨⟨1437,1996,432,25043⟩,89114385580032,436582815793⟩,85,2,1,257515,121⟩

theorem rankOrd34 : P3_7_1.BankOK ord34.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1437_1996_432 25043

theorem widthOrd34 : Lower6960.HelperSource.WidthGuard ord34.bank 179730 2308 ord34.reserve := requestWidth (by decide)

def endsOrd34 : List ℕ := [2308, 2309, 2313]

theorem insideOrd34 : Research6966.TerminalBanks.inside ord34.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd34 : Cover (Triangular ord34) 2313 2308 endsOrd34 := triangleCover (by decide +kernel)

def ord35 : Request := ⟨⟨⟨2600,3623,793,28173⟩,532875289296896,4771760428124⟩,150,2,1,257319,121⟩

theorem rankOrd35 : P3_7_1.BankOK ord35.bank := by
  simpa only [ord35, _root_.Research6969.TerminalAuxBanks.bank40] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank40 28173

theorem widthOrd35 : Lower6960.HelperSource.WidthGuard ord35.bank 179730 2308 ord35.reserve := requestWidth (by decide)

def endsOrd35 : List ℕ := [2309, 2313]

theorem insideOrd35 : Research6966.TerminalBanks.inside ord35.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd35 : Cover (Triangular ord35) 2313 2308 endsOrd35 := triangleCover (by decide +kernel)

def ord36 : Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,2,1,257319,161⟩

theorem rankOrd36 : P3_7_1.BankOK ord36.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3901_834 45081

theorem widthOrd36 : Lower6960.HelperSource.WidthGuard ord36.bank 179730 2308 ord36.reserve := requestWidth (by decide)

def endsOrd36 : List ℕ := [2309, 2313]

theorem insideOrd36 : Research6966.TerminalBanks.inside ord36.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd36 : Cover (Triangular ord36) 2313 2308 endsOrd36 := triangleCover (by decide +kernel)

def ord38 : Request := ⟨⟨⟨2972,4130,894,64247⟩,787370403430400,7985976760333⟩,250,2,1,257515,257⟩

theorem rankOrd38 : P3_7_1.BankOK ord38.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2972_4130_894 64247

theorem widthOrd38 : Lower6960.HelperSource.WidthGuard ord38.bank 179730 2308 ord38.reserve := requestWidth (by decide)

def endsOrd38 : List ℕ := [2308, 2309, 2313]

theorem insideOrd38 : Research6966.TerminalBanks.inside ord38.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd38 : Cover (Triangular ord38) 2313 2308 endsOrd38 := triangleCover (by decide +kernel)

def ord39 : Request := ⟨⟨⟨2581,3588,775,63697⟩,515124047642624,4542969264457⟩,250,2,1,257319,513⟩

theorem rankOrd39 : P3_7_1.BankOK ord39.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2581_3588_775 63697

theorem widthOrd39 : Lower6960.HelperSource.WidthGuard ord39.bank 179730 2308 ord39.reserve := requestWidth (by decide)

def endsOrd39 : List ℕ := [2308, 2309, 2313]

theorem insideOrd39 : Research6966.TerminalBanks.inside ord39.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd39 : Cover (Triangular ord39) 2313 2308 endsOrd39 := triangleCover (by decide +kernel)

def ord41 : Request := ⟨⟨⟨3000,4175,898,127905⟩,806795987910656,8298222886581⟩,325,2,1,257515,1025⟩

theorem rankOrd41 : P3_7_1.BankOK ord41.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4175_898 127905

theorem widthOrd41 : Lower6960.HelperSource.WidthGuard ord41.bank 179730 2308 ord41.reserve := requestWidth (by decide)

def endsOrd41 : List ℕ := [2308, 2309, 2313]

theorem insideOrd41 : Research6966.TerminalBanks.inside ord41.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd41 : Cover (Triangular ord41) 2313 2308 endsOrd41 := triangleCover (by decide +kernel)

def ord45 : Request := ⟨⟨⟨1206,1673,378,117195⟩,54403284860928,222977190790⟩,150,2,1,257319,16385⟩

theorem rankOrd45 : P3_7_1.BankOK ord45.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1206_1673_378 117195

theorem widthOrd45 : Lower6960.HelperSource.WidthGuard ord45.bank 179730 2308 ord45.reserve := requestWidth (by decide)

def endsOrd45 : List ℕ := [2308, 2309, 2313]

theorem insideOrd45 : Research6966.TerminalBanks.inside ord45.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd45 : Cover (Triangular ord45) 2313 2308 endsOrd45 := triangleCover (by decide +kernel)

def ord47 : Request := ⟨⟨⟨2899,4045,897,47057⟩,746635263475712,7488345307134⟩,22,2,1,299354,27⟩

theorem rankOrd47 : P3_7_1.BankOK ord47.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2899_4045_897 47057

theorem widthOrd47 : Lower6960.HelperSource.WidthGuard ord47.bank 179730 2308 ord47.reserve := requestWidth (by decide)

def endsOrd47 : List ℕ := [2308, 2309, 2313]

theorem insideOrd47 : Research6966.TerminalBanks.inside ord47.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd47 : Cover (Triangular ord47) 2313 2308 endsOrd47 := triangleCover (by decide +kernel)

def ord48 : Request := ⟨⟨⟨2605,3628,793,49690⟩,535171619618816,4792991160379⟩,15,2,1,302619,25⟩

theorem rankOrd48 : P3_7_1.BankOK ord48.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3628_793 49690

theorem widthOrd48 : Lower6960.HelperSource.WidthGuard ord48.bank 179730 2308 ord48.reserve := requestWidth (by decide)

def endsOrd48 : List ℕ := [2308, 2309, 2313]

theorem insideOrd48 : Research6966.TerminalBanks.inside ord48.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd48 : Cover (Triangular ord48) 2313 2308 endsOrd48 := triangleCover (by decide +kernel)

def ord49 : Request := ⟨⟨⟨2810,3907,854,137354⟩,670792923217920,6445344460182⟩,22,3,1,386273,10⟩

theorem rankOrd49 : P3_7_1.BankOK ord49.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3907_854 137354

theorem widthOrd49 : Lower6960.HelperSource.WidthGuard ord49.bank 179730 2308 ord49.reserve := requestWidth (by decide)

def endsOrd49 : List ℕ := [2308, 2309, 2313]

theorem insideOrd49 : Research6966.TerminalBanks.inside ord49.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd49 : Cover (Triangular ord49) 2313 2308 endsOrd49 := triangleCover (by decide +kernel)

def ord5 : Request := ⟨⟨⟨2754,3837,834,44726⟩,629792749649920,5969742006437⟩,195,1,1,128659,161⟩

theorem rankOrd5 : P3_7_1.BankOK ord5.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2754_3837_834 44726

theorem widthOrd5 : Lower6960.HelperSource.WidthGuard ord5.bank 179730 2308 ord5.reserve := requestWidth (by decide)

def endsOrd5 : List ℕ := [2308, 2309, 2313]

theorem insideOrd5 : Research6966.TerminalBanks.inside ord5.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd5 : Cover (Triangular ord5) 2313 2308 endsOrd5 := triangleCover (by decide +kernel)

def ord50 : Request := ⟨⟨⟨2610,3628,793,119660⟩,537473153499136,4792991160379⟩,22,3,1,386273,13⟩

theorem rankOrd50 : P3_7_1.BankOK ord50.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 119660

theorem widthOrd50 : Lower6960.HelperSource.WidthGuard ord50.bank 179730 2308 ord50.reserve := requestWidth (by decide)

def endsOrd50 : List ℕ := [2308, 2309, 2313]

theorem insideOrd50 : Research6966.TerminalBanks.inside ord50.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd50 : Cover (Triangular ord50) 2313 2308 endsOrd50 := triangleCover (by decide +kernel)

def ord51 : Request := ⟨⟨⟨2608,3628,793,102908⟩,536551915520000,4792991160379⟩,22,3,1,385979,15⟩

theorem rankOrd51 : P3_7_1.BankOK ord51.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3628_793 102908

theorem widthOrd51 : Lower6960.HelperSource.WidthGuard ord51.bank 179730 2308 ord51.reserve := requestWidth (by decide)

def endsOrd51 : List ℕ := [2308, 2309, 2313]

theorem insideOrd51 : Research6966.TerminalBanks.inside ord51.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd51 : Cover (Triangular ord51) 2313 2308 endsOrd51 := triangleCover (by decide +kernel)

def ord52 : Request := ⟨⟨⟨2610,3628,793,85920⟩,537473153499136,4792991160379⟩,22,3,1,386273,17⟩

theorem rankOrd52 : P3_7_1.BankOK ord52.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 85920

theorem widthOrd52 : Lower6960.HelperSource.WidthGuard ord52.bank 179730 2308 ord52.reserve := requestWidth (by decide)

def endsOrd52 : List ℕ := [2308, 2309, 2313]

theorem insideOrd52 : Research6966.TerminalBanks.inside ord52.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd52 : Cover (Triangular ord52) 2313 2308 endsOrd52 := triangleCover (by decide +kernel)

def ord53 : Request := ⟨⟨⟨2811,3907,854,74060⟩,671327256576000,6445344460182⟩,22,3,1,386273,18⟩

theorem rankOrd53 : P3_7_1.BankOK ord53.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2811_3907_854 74060

theorem widthOrd53 : Lower6960.HelperSource.WidthGuard ord53.bank 179730 2308 ord53.reserve := requestWidth (by decide)

def endsOrd53 : List ℕ := [2308, 2309, 2313]

theorem insideOrd53 : Research6966.TerminalBanks.inside ord53.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd53 : Cover (Triangular ord53) 2313 2308 endsOrd53 := triangleCover (by decide +kernel)

def ord54 : Request := ⟨⟨⟨2605,3628,793,57109⟩,535171619618816,4792991160379⟩,22,3,1,385979,21⟩

theorem rankOrd54 : P3_7_1.BankOK ord54.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3628_793 57109

theorem widthOrd54 : Lower6960.HelperSource.WidthGuard ord54.bank 179730 2308 ord54.reserve := requestWidth (by decide)

def endsOrd54 : List ℕ := [2308, 2309, 2313]

theorem insideOrd54 : Research6966.TerminalBanks.inside ord54.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd54 : Cover (Triangular ord54) 2313 2308 endsOrd54 := triangleCover (by decide +kernel)

def ord55 : Request := ⟨⟨⟨2802,3906,854,64247⟩,666526325145600,6440035562832⟩,32,3,1,385979,24⟩

theorem rankOrd55 : P3_7_1.BankOK ord55.bank := 
  _root_.Research6970.Height2313.Physical.bank_2802_3906_854 64247

theorem widthOrd55 : Lower6960.HelperSource.WidthGuard ord55.bank 179730 2308 ord55.reserve := requestWidth (by decide)

def endsOrd55 : List ℕ := [2308, 2309, 2313]

theorem insideOrd55 : Research6966.TerminalBanks.inside ord55.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd55 : Cover (Triangular ord55) 2313 2308 endsOrd55 := triangleCover (by decide +kernel)

def ord56 : Request := ⟨⟨⟨2808,3906,854,40111⟩,669724928901120,6440035562832⟩,32,3,1,385979,27⟩

theorem rankOrd56 : P3_7_1.BankOK ord56.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3906_854 40111

theorem widthOrd56 : Lower6960.HelperSource.WidthGuard ord56.bank 179730 2308 ord56.reserve := requestWidth (by decide)

def endsOrd56 : List ℕ := [2308, 2309, 2313]

theorem insideOrd56 : Research6966.TerminalBanks.inside ord56.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd56 : Cover (Triangular ord56) 2313 2308 endsOrd56 := triangleCover (by decide +kernel)

def ord57 : Request := ⟨⟨⟨2809,3902,854,35568⟩,670258813992960,6418829718882⟩,45,3,1,385979,32⟩

theorem rankOrd57 : P3_7_1.BankOK ord57.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3902_854 35568

theorem widthOrd57 : Lower6960.HelperSource.WidthGuard ord57.bank 179730 2308 ord57.reserve := requestWidth (by decide)

def endsOrd57 : List ℕ := [2308, 2309, 2313]

theorem insideOrd57 : Research6966.TerminalBanks.inside ord57.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd57 : Cover (Triangular ord57) 2313 2308 endsOrd57 := triangleCover (by decide +kernel)

def ord58 : Request := ⟨⟨⟨2301,3208,724,28173⟩,378271924224000,3004743122568⟩,45,3,1,385979,36⟩

theorem rankOrd58 : P3_7_1.BankOK ord58.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3208_724 28173

theorem widthOrd58 : Lower6960.HelperSource.WidthGuard ord58.bank 179730 2308 ord58.reserve := requestWidth (by decide)

def endsOrd58 : List ℕ := [2308, 2309, 2313]

theorem insideOrd58 : Research6966.TerminalBanks.inside ord58.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd58 : Cover (Triangular ord58) 2313 2308 endsOrd58 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources01

section Pack_R6970Height2313CommonSources02

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def ord59 : Request := ⟨⟨⟨2601,3626,793,28173⟩,533334139076608,4784491173220⟩,63,3,1,385979,42⟩

theorem rankOrd59 : P3_7_1.BankOK ord59.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3626_793 28173

theorem widthOrd59 : Lower6960.HelperSource.WidthGuard ord59.bank 179730 2308 ord59.reserve := requestWidth (by decide)

def endsOrd59 : List ℕ := [2308, 2309, 2313]

theorem insideOrd59 : Research6966.TerminalBanks.inside ord59.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd59 : Cover (Triangular ord59) 2313 2308 endsOrd59 := triangleCover (by decide +kernel)

def ord60 : Request := ⟨⟨⟨2808,3905,854,31694⟩,669724928901120,6434729640882⟩,85,3,1,385979,48⟩

theorem rankOrd60 : P3_7_1.BankOK ord60.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3905_854 31694

theorem widthOrd60 : Lower6960.HelperSource.WidthGuard ord60.bank 179730 2308 ord60.reserve := requestWidth (by decide)

def endsOrd60 : List ℕ := [2308, 2309, 2313]

theorem insideOrd60 : Research6966.TerminalBanks.inside ord60.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd60 : Cover (Triangular ord60) 2313 2308 endsOrd60 := triangleCover (by decide +kernel)

def ord62 : Request := ⟨⟨⟨2800,3903,854,31694⟩,665461916958720,6424126719762⟩,115,3,1,385979,65⟩

theorem rankOrd62 : P3_7_1.BankOK ord62.bank := by
  simpa only [ord62, _root_.Research6969.TerminalAuxBanks.bank64] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank64 31694

theorem widthOrd62 : Lower6960.HelperSource.WidthGuard ord62.bank 179730 2308 ord62.reserve := requestWidth (by decide)

def endsOrd62 : List ℕ := [2308, 2313]

theorem insideOrd62 : Research6966.TerminalBanks.inside ord62.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd62 : Cover (Triangular ord62) 2313 2308 endsOrd62 := triangleCover (by decide +kernel)

def ord64 : Request := ⟨⟨⟨2603,3623,819,35655⟩,547476948910080,4892906717079⟩,150,3,1,385979,97⟩

theorem rankOrd64 : P3_7_1.BankOK ord64.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3623_819 35655

theorem widthOrd64 : Lower6960.HelperSource.WidthGuard ord64.bank 179730 2308 ord64.reserve := requestWidth (by decide)

def endsOrd64 : List ℕ := [2309, 2313]

theorem insideOrd64 : Research6966.TerminalBanks.inside ord64.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd64 : Cover (Triangular ord64) 2313 2308 endsOrd64 := triangleCover (by decide +kernel)

def ord65 : Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,3,1,385979,161⟩

theorem rankOrd65 : P3_7_1.BankOK ord65.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3901_834 45081

theorem widthOrd65 : Lower6960.HelperSource.WidthGuard ord65.bank 179730 2308 ord65.reserve := requestWidth (by decide)

def endsOrd65 : List ℕ := [2313]

theorem insideOrd65 : Research6966.TerminalBanks.inside ord65.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd65 : Cover (Triangular ord65) 2313 2308 endsOrd65 := triangleCover (by decide +kernel)

def ord67 : Request := ⟨⟨⟨3000,4178,894,64247⟩,804053213511680,8288484232853⟩,250,3,1,385979,257⟩

theorem rankOrd67 : P3_7_1.BankOK ord67.bank := by
  simpa only [ord67, _root_.Research6969.TerminalAuxBanks.bank75] using _root_.Research6969.PackedRanks.TerminalRanks72To75.rank75 64247

theorem widthOrd67 : Lower6960.HelperSource.WidthGuard ord67.bank 179730 2308 ord67.reserve := requestWidth (by decide)

def endsOrd67 : List ℕ := [2309, 2313]

theorem insideOrd67 : Research6966.TerminalBanks.inside ord67.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd67 : Cover (Triangular ord67) 2313 2308 endsOrd67 := triangleCover (by decide +kernel)

def ord68 : Request := ⟨⟨⟨2604,3620,775,63811⟩,525443022192640,4674619806217⟩,250,3,1,385979,513⟩

theorem rankOrd68 : P3_7_1.BankOK ord68.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3620_775 63811

theorem widthOrd68 : Lower6960.HelperSource.WidthGuard ord68.bank 179730 2308 ord68.reserve := requestWidth (by decide)

def endsOrd68 : List ℕ := [2308, 2309, 2313]

theorem insideOrd68 : Research6966.TerminalBanks.inside ord68.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd68 : Cover (Triangular ord68) 2313 2308 endsOrd68 := triangleCover (by decide +kernel)

def ord70 : Request := ⟨⟨⟨3000,4175,897,127905⟩,806110768660480,8291009592869⟩,325,3,1,386273,1025⟩

theorem rankOrd70 : P3_7_1.BankOK ord70.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4175_897 127905

theorem widthOrd70 : Lower6960.HelperSource.WidthGuard ord70.bank 179730 2308 ord70.reserve := requestWidth (by decide)

def endsOrd70 : List ℕ := [2308, 2309, 2313]

theorem insideOrd70 : Research6966.TerminalBanks.inside ord70.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd70 : Cover (Triangular ord70) 2313 2308 endsOrd70 := triangleCover (by decide +kernel)

def ord74 : Request := ⟨⟨⟨2000,2782,598,190413⟩,239038181933056,1636863891369⟩,250,3,1,385979,16385⟩

theorem rankOrd74 : P3_7_1.BankOK ord74.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2000_2782_598 190413

theorem widthOrd74 : Lower6960.HelperSource.WidthGuard ord74.bank 179730 2308 ord74.reserve := requestWidth (by decide)

def endsOrd74 : List ℕ := [2308, 2309, 2313]

theorem insideOrd74 : Research6966.TerminalBanks.inside ord74.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd74 : Cover (Triangular ord74) 2313 2308 endsOrd74 := triangleCover (by decide +kernel)

def ord76 : Request := ⟨⟨⟨2809,3906,854,133229⟩,670258813992960,6440035562832⟩,45,4,1,515031,1⟩

theorem rankOrd76 : P3_7_1.BankOK ord76.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3906_854 133229

theorem widthOrd76 : Lower6960.HelperSource.WidthGuard ord76.bank 179730 2308 ord76.reserve := requestWidth (by decide)

def endsOrd76 : List ℕ := [2308, 2309, 2313]

theorem insideOrd76 : Research6966.TerminalBanks.inside ord76.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd76 : Cover (Triangular ord76) 2313 2308 endsOrd76 := triangleCover (by decide +kernel)

def ord77 : Request := ⟨⟨⟨2307,3209,702,91474⟩,371690023944192,2936492475204⟩,32,4,1,514639,3⟩

theorem rankOrd77 : P3_7_1.BankOK ord77.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3209_702 91474

theorem widthOrd77 : Lower6960.HelperSource.WidthGuard ord77.bank 179730 2308 ord77.reserve := requestWidth (by decide)

def endsOrd77 : List ℕ := [2308, 2309, 2313]

theorem insideOrd77 : Research6966.TerminalBanks.inside ord77.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd77 : Cover (Triangular ord77) 2313 2308 endsOrd77 := triangleCover (by decide +kernel)

def ord78 : Request := ⟨⟨⟨2309,3208,703,81633⟩,372814653685760,2936800480322⟩,32,4,1,514639,6⟩

theorem rankOrd78 : P3_7_1.BankOK ord78.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2309_3208_703 81633

theorem widthOrd78 : Lower6960.HelperSource.WidthGuard ord78.bank 179730 2308 ord78.reserve := requestWidth (by decide)

def endsOrd78 : List ℕ := [2308, 2309, 2313]

theorem insideOrd78 : Research6966.TerminalBanks.inside ord78.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd78 : Cover (Triangular ord78) 2313 2308 endsOrd78 := triangleCover (by decide +kernel)

def ord79 : Request := ⟨⟨⟨2810,3902,858,93737⟩,673179779465216,6442222859746⟩,45,4,1,514639,10⟩

theorem rankOrd79 : P3_7_1.BankOK ord79.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3902_858 93737

theorem widthOrd79 : Lower6960.HelperSource.WidthGuard ord79.bank 179730 2308 ord79.reserve := requestWidth (by decide)

def endsOrd79 : List ℕ := [2308, 2309, 2313]

theorem insideOrd79 : Research6966.TerminalBanks.inside ord79.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd79 : Cover (Triangular ord79) 2313 2308 endsOrd79 := triangleCover (by decide +kernel)

def ord8 : Request := ⟨⟨⟨2604,3620,777,63706⟩,526477262323712,4684034271577⟩,250,1,1,128659,513⟩

theorem rankOrd8 : P3_7_1.BankOK ord8.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3620_777 63706

theorem widthOrd8 : Lower6960.HelperSource.WidthGuard ord8.bank 179730 2308 ord8.reserve := requestWidth (by decide)

def endsOrd8 : List ℕ := [2308, 2309, 2313]

theorem insideOrd8 : Research6966.TerminalBanks.inside ord8.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd8 : Cover (Triangular ord8) 2313 2308 endsOrd8 := triangleCover (by decide +kernel)

def ord80 : Request := ⟨⟨⟨2813,3906,862,72765⟩,677178014171136,6486944896419⟩,45,4,1,514639,15⟩

theorem rankOrd80 : P3_7_1.BankOK ord80.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2813_3906_862 72765

theorem widthOrd80 : Lower6960.HelperSource.WidthGuard ord80.bank 179730 2308 ord80.reserve := requestWidth (by decide)

def endsOrd80 : List ℕ := [2308, 2309, 2313]

theorem insideOrd80 : Research6966.TerminalBanks.inside ord80.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd80 : Cover (Triangular ord80) 2313 2308 endsOrd80 := triangleCover (by decide +kernel)

def ord81 : Request := ⟨⟨⟨2768,3842,854,50673⟩,648553314385920,6106417618032⟩,45,4,1,514639,21⟩

theorem rankOrd81 : P3_7_1.BankOK ord81.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2768_3842_854 50673

theorem widthOrd81 : Lower6960.HelperSource.WidthGuard ord81.bank 179730 2308 ord81.reserve := requestWidth (by decide)

def endsOrd81 : List ℕ := [2308, 2309, 2313]

theorem insideOrd81 : Research6966.TerminalBanks.inside ord81.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd81 : Cover (Triangular ord81) 2313 2308 endsOrd81 := triangleCover (by decide +kernel)

def ord82 : Request := ⟨⟨⟨2600,3611,793,35602⟩,532875289296896,4721067870510⟩,45,4,1,514639,27⟩

theorem rankOrd82 : P3_7_1.BankOK ord82.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3611_793 35602

theorem widthOrd82 : Lower6960.HelperSource.WidthGuard ord82.bank 179730 2308 ord82.reserve := requestWidth (by decide)

def endsOrd82 : List ℕ := [2308, 2309, 2313]

theorem insideOrd82 : Research6966.TerminalBanks.inside ord82.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd82 : Cover (Triangular ord82) 2313 2308 endsOrd82 := triangleCover (by decide +kernel)

def ord83 : Request := ⟨⟨⟨2588,3594,793,31404⟩,527385327042560,4649882428564⟩,63,4,1,514639,36⟩

theorem rankOrd83 : P3_7_1.BankOK ord83.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3594_793 31404

theorem widthOrd83 : Lower6960.HelperSource.WidthGuard ord83.bank 179730 2308 ord83.reserve := requestWidth (by decide)

def endsOrd83 : List ℕ := [2308, 2309, 2313]

theorem insideOrd83 : Research6966.TerminalBanks.inside ord83.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd83 : Cover (Triangular ord83) 2313 2308 endsOrd83 := triangleCover (by decide +kernel)

def ord84 : Request := ⟨⟨⟨2600,3625,819,28173⟩,546063062138880,4901614794409⟩,85,4,1,514639,48⟩

theorem rankOrd84 : P3_7_1.BankOK ord84.bank := by
  simpa only [ord84, _root_.Research6969.TransitionBanks.bank263] using _root_.Research6969.TransitionBanks.rank263 28173

theorem widthOrd84 : Lower6960.HelperSource.WidthGuard ord84.bank 179730 2308 ord84.reserve := requestWidth (by decide)

def endsOrd84 : List ℕ := [2308, 2309, 2313]

theorem insideOrd84 : Research6966.TerminalBanks.inside ord84.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd84 : Cover (Triangular ord84) 2313 2308 endsOrd84 := triangleCover (by decide +kernel)

def ord85 : Request := ⟨⟨⟨2600,3624,819,31694⟩,546063062138880,4897259437389⟩,115,4,1,514639,65⟩

theorem rankOrd85 : P3_7_1.BankOK ord85.bank := by
  simpa only [ord85, _root_.Research6969.TerminalAuxBanks.bank44] using _root_.Research6969.PackedRanks.TerminalRanks44To47.rank44 31694

theorem widthOrd85 : Lower6960.HelperSource.WidthGuard ord85.bank 179730 2308 ord85.reserve := requestWidth (by decide)

def endsOrd85 : List ℕ := [2313]

theorem insideOrd85 : Research6966.TerminalBanks.inside ord85.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem coverOrd85 : Cover (Triangular ord85) 2313 2308 endsOrd85 := triangleCover (by decide +kernel)

def ord87 : Request := ⟨⟨⟨2604,3623,793,35655⟩,534711937269760,4771760428124⟩,150,4,1,514639,97⟩

theorem rankOrd87 : P3_7_1.BankOK ord87.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3623_793 35655

theorem widthOrd87 : Lower6960.HelperSource.WidthGuard ord87.bank 179730 2308 ord87.reserve := requestWidth (by decide)

def endsOrd87 : List ℕ := [2308, 2309, 2313]

theorem insideOrd87 : Research6966.TerminalBanks.inside ord87.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd87 : Cover (Triangular ord87) 2313 2308 endsOrd87 := triangleCover (by decide +kernel)

def ord88 : Request := ⟨⟨⟨2609,3621,819,45081⟩,550310526320640,4884209183309⟩,195,4,1,514639,161⟩

theorem rankOrd88 : P3_7_1.BankOK ord88.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2609_3621_819 45081

theorem widthOrd88 : Lower6960.HelperSource.WidthGuard ord88.bank 179730 2308 ord88.reserve := requestWidth (by decide)

def endsOrd88 : List ℕ := [2308, 2309, 2313]

theorem insideOrd88 : Research6966.TerminalBanks.inside ord88.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd88 : Cover (Triangular ord88) 2313 2308 endsOrd88 := triangleCover (by decide +kernel)

def ord89 : Request := ⟨⟨⟨2794,3885,834,40042⟩,650434099281920,6213402888837⟩,195,4,1,514639,161⟩

theorem rankOrd89 : P3_7_1.BankOK ord89.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2794_3885_834 40042

theorem widthOrd89 : Lower6960.HelperSource.WidthGuard ord89.bank 179730 2308 ord89.reserve := requestWidth (by decide)

def endsOrd89 : List ℕ := [2308, 2309, 2313]

theorem insideOrd89 : Research6966.TerminalBanks.inside ord89.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd89 : Cover (Triangular ord89) 2313 2308 endsOrd89 := triangleCover (by decide +kernel)

def ord91 : Request := ⟨⟨⟨2983,4146,894,56954⟩,793902427668480,8085963618533⟩,250,4,1,514639,257⟩

theorem rankOrd91 : P3_7_1.BankOK ord91.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2983_4146_894 56954

theorem widthOrd91 : Lower6960.HelperSource.WidthGuard ord91.bank 179730 2308 ord91.reserve := requestWidth (by decide)

def endsOrd91 : List ℕ := [2308, 2309, 2313]

theorem insideOrd91 : Research6966.TerminalBanks.inside ord91.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd91 : Cover (Triangular ord91) 2313 2308 endsOrd91 := triangleCover (by decide +kernel)

def ord93 : Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,4,1,514639,513⟩

theorem rankOrd93 : P3_7_1.BankOK ord93.bank := by
  simpa only [ord93, _root_.Research6969.TerminalAuxBanks.bank38] using _root_.Research6969.PackedRanks.TerminalRanks36To39.rank38 63811

theorem widthOrd93 : Lower6960.HelperSource.WidthGuard ord93.bank 179730 2308 ord93.reserve := requestWidth (by decide)

def endsOrd93 : List ℕ := [2309, 2313]

theorem insideOrd93 : Research6966.TerminalBanks.inside ord93.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem coverOrd93 : Cover (Triangular ord93) 2313 2308 endsOrd93 := triangleCover (by decide +kernel)

def ord95 : Request := ⟨⟨⟨2987,4151,898,112852⟩,798998930128896,8145701898053⟩,325,4,1,514639,1025⟩

theorem rankOrd95 : P3_7_1.BankOK ord95.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2987_4151_898 112852

theorem widthOrd95 : Lower6960.HelperSource.WidthGuard ord95.bank 179730 2308 ord95.reserve := requestWidth (by decide)

def endsOrd95 : List ℕ := [2308, 2309, 2313]

theorem insideOrd95 : Research6966.TerminalBanks.inside ord95.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd95 : Cover (Triangular ord95) 2313 2308 endsOrd95 := triangleCover (by decide +kernel)

def ord99 : Request := ⟨⟨⟨1205,1671,378,121786⟩,54302243291136,222119852616⟩,150,4,1,514639,16385⟩

theorem rankOrd99 : P3_7_1.BankOK ord99.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1671_378 121786

theorem widthOrd99 : Lower6960.HelperSource.WidthGuard ord99.bank 179730 2308 ord99.reserve := requestWidth (by decide)

def endsOrd99 : List ℕ := [2308, 2309, 2313]

theorem insideOrd99 : Research6966.TerminalBanks.inside ord99.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem coverOrd99 : Cover (Triangular ord99) 2313 2308 endsOrd99 := triangleCover (by decide +kernel)

def src0 : Request := ⟨⟨⟨2796,3883,854,31300⟩,663335790182400,6318750403662⟩,4,1,1,128757,29⟩

theorem rank0 : P3_7_1.BankOK src0.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2796_3883_854 31300

theorem width0 : Lower6960.HelperSource.WidthGuard src0.bank 179730 2308 src0.reserve := requestWidth (by decide)

def ends0 : List ℕ := [2308, 2309, 2313]

theorem inside0 : Research6966.TerminalBanks.inside src0.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover0 : Cover (Triangular src0) 2313 2308 ends0 := triangleCover (by decide +kernel)

def src1 : Request := ⟨⟨⟨2307,3205,702,24928⟩,371690023944192,2924726546984⟩,15,1,1,128659,33⟩

theorem rank1 : P3_7_1.BankOK src1.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3205_702 24928

theorem width1 : Lower6960.HelperSource.WidthGuard src1.bank 179730 2308 src1.reserve := requestWidth (by decide)

def ends1 : List ℕ := [2308, 2309, 2313]

theorem inside1 : Research6966.TerminalBanks.inside src1.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1 : Cover (Triangular src1) 2313 2308 ends1 := triangleCover (by decide +kernel)

def src10 : Request := ⟨⟨⟨2814,3902,882,30856⟩,689601573814272,6581809445307⟩,150,1,1,128659,97⟩

theorem rank10 : P3_7_1.BankOK src10.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2814_3902_882 30856

theorem width10 : Lower6960.HelperSource.WidthGuard src10.bank 179730 2308 src10.reserve := requestWidth (by decide)

def ends10 : List ℕ := [2308, 2309, 2313]

theorem inside10 : Research6966.TerminalBanks.inside src10.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover10 : Cover (Triangular src10) 2313 2308 ends10 := triangleCover (by decide +kernel)

def src100 : Request := ⟨⟨⟨1000,1391,304,58257⟩,30330999275520,103947228761⟩,115,2,1,257319,4097⟩

theorem rank100 : P3_7_1.BankOK src100.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_304 58257

theorem width100 : Lower6960.HelperSource.WidthGuard src100.bank 179730 2308 src100.reserve := requestWidth (by decide)

def ends100 : List ℕ := [2308, 2309, 2313]

theorem inside100 : Research6966.TerminalBanks.inside src100.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover100 : Cover (Triangular src100) 2313 2308 ends100 := triangleCover (by decide +kernel)

def src1000 : Request := ⟨⟨⟨828,1151,253,12355⟩,17301502689280,49010625289⟩,6,3,1,385979,31⟩

theorem rank1000 : P3_7_1.BankOK src1000.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_253 12355

theorem width1000 : Lower6960.HelperSource.WidthGuard src1000.bank 179730 2308 src1000.reserve := requestWidth (by decide)

def ends1000 : List ℕ := [2309, 2313]

theorem inside1000 : Research6966.TerminalBanks.inside src1000.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1000 : Cover (Triangular src1000) 2313 2308 ends1000 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources02

section Pack_R6970Height2313CommonSources21

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1520 : Request := ⟨⟨⟨5680,7884,1750,64074⟩,5593163081973760,108040693109459⟩,190,5,1,643299,41⟩

theorem rank1520 : P3_7_1.BankOK src1520.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5680_7884_1750 64074

theorem width1520 : Lower6960.HelperSource.WidthGuard src1520.bank 179730 2308 src1520.reserve := requestWidth (by decide)

def ends1520 : List ℕ := [2308, 2309, 2313]




theorem cover1520 : Cover (Triangular src1520) 2313 2308 ends1520 := triangleCover (by decide +kernel)

def src1521 : Request := ⟨⟨⟨5732,7991,1754,334168⟩,5718400951910400,113035233942686⟩,237,5,1,643789,41⟩

theorem rank1521 : P3_7_1.BankOK src1521.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5732_7991_1754 334168

theorem width1521 : Lower6960.HelperSource.WidthGuard src1521.bank 179730 2308 src1521.reserve := requestWidth (by decide)

def ends1521 : List ℕ := [2313]


theorem cover1521 : Cover (Triangular src1521) 2313 2308 ends1521 := triangleCover (by decide +kernel)

def src1522 : Request := ⟨⟨⟨2287,3175,702,27888⟩,364515722002432,2837502581224⟩,85,5,1,643299,49⟩

theorem rank1522 : P3_7_1.BankOK src1522.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2287_3175_702 27888

theorem width1522 : Lower6960.HelperSource.WidthGuard src1522.bank 179730 2308 src1522.reserve := requestWidth (by decide)

def ends1522 : List ℕ := [2308, 2309, 2313]

theorem inside1522 : Research6966.TerminalBanks.inside src1522.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1522 : Cover (Triangular src1522) 2313 2308 ends1522 := triangleCover (by decide +kernel)

def src1523 : Request := ⟨⟨⟨2807,3899,854,50699⟩,669191267942400,6402956544702⟩,115,5,1,643299,49⟩

theorem rank1523 : P3_7_1.BankOK src1523.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2807_3899_854 50699

theorem width1523 : Lower6960.HelperSource.WidthGuard src1523.bank 179730 2308 src1523.reserve := requestWidth (by decide)

def ends1523 : List ℕ := [2308, 2309, 2313]

theorem inside1523 : Research6966.TerminalBanks.inside src1523.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1523 : Cover (Triangular src1523) 2313 2308 ends1523 := triangleCover (by decide +kernel)

def src1524 : Request := ⟨⟨⟨2600,3624,775,35655⟩,523640687820800,4691256264577⟩,115,5,1,643299,65⟩

theorem rank1524 : P3_7_1.BankOK src1524.bank := by
  simpa only [src1524, _root_.Research6969.TerminalAuxBanks.bank42] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank42 35655

theorem width1524 : Lower6960.HelperSource.WidthGuard src1524.bank 179730 2308 src1524.reserve := requestWidth (by decide)

def ends1524 : List ℕ := [2313]

theorem inside1524 : Research6966.TerminalBanks.inside src1524.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1524 : Cover (Triangular src1524) 2313 2308 ends1524 := triangleCover (by decide +kernel)

def src1525 : Request := ⟨⟨⟨2613,3624,819,27318⟩,552203877089280,4897259437389⟩,115,5,1,643299,65⟩

theorem rank1525 : P3_7_1.BankOK src1525.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2613_3624_819 27318

theorem width1525 : Lower6960.HelperSource.WidthGuard src1525.bank 179730 2308 src1525.reserve := requestWidth (by decide)

def ends1525 : List ℕ := [2308, 2309, 2313]

theorem inside1525 : Research6966.TerminalBanks.inside src1525.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1525 : Cover (Triangular src1525) 2313 2308 ends1525 := triangleCover (by decide +kernel)

def src1526 : Request := ⟨⟨⟨1455,2020,457,25043⟩,95625142599680,473974537987⟩,85,5,1,643299,97⟩

theorem rank1526 : P3_7_1.BankOK src1526.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2020_457 25043

theorem width1526 : Lower6960.HelperSource.WidthGuard src1526.bank 179730 2308 src1526.reserve := requestWidth (by decide)

def ends1526 : List ℕ := [2308, 2309, 2313]

theorem inside1526 : Research6966.TerminalBanks.inside src1526.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1526 : Cover (Triangular src1526) 2313 2308 ends1526 := triangleCover (by decide +kernel)

def src1527 : Request := ⟨⟨⟨2612,3623,818,30506⟩,551220579926016,4888271640312⟩,150,5,1,643299,97⟩

theorem rank1527 : P3_7_1.BankOK src1527.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3623_818 30506

theorem width1527 : Lower6960.HelperSource.WidthGuard src1527.bank 179730 2308 src1527.reserve := requestWidth (by decide)

def ends1527 : List ℕ := [2308, 2309, 2313]

theorem inside1527 : Research6966.TerminalBanks.inside src1527.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1527 : Cover (Triangular src1527) 2313 2308 ends1527 := triangleCover (by decide +kernel)

def src1528 : Request := ⟨⟨⟨2813,3905,878,44104⟩,686686358732800,6574894765364⟩,195,5,1,643299,129⟩

theorem rank1528 : P3_7_1.BankOK src1528.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2813_3905_878 44104

theorem width1528 : Lower6960.HelperSource.WidthGuard src1528.bank 179730 2308 src1528.reserve := requestWidth (by decide)

def ends1528 : List ℕ := [2308, 2309, 2313]

theorem inside1528 : Research6966.TerminalBanks.inside src1528.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1528 : Cover (Triangular src1528) 2313 2308 ends1528 := triangleCover (by decide +kernel)

def src1529 : Request := ⟨⟨⟨2805,3901,882,45210⟩,684666334740480,6576375970149⟩,195,5,1,643299,129⟩

theorem rank1529 : P3_7_1.BankOK src1529.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3901_882 45210

theorem width1529 : Lower6960.HelperSource.WidthGuard src1529.bank 179730 2308 src1529.reserve := requestWidth (by decide)

def ends1529 : List ℕ := [2308, 2309, 2313]

theorem inside1529 : Research6966.TerminalBanks.inside src1529.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1529 : Cover (Triangular src1529) 2313 2308 ends1529 := triangleCover (by decide +kernel)

def src153 : Request := ⟨⟨⟨2100,2913,645,19772⟩,282396798484480,2013318131288⟩,40,2,1,296085,41⟩

theorem rank153 : P3_7_1.BankOK src153.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2100_2913_645 19772

theorem width153 : Lower6960.HelperSource.WidthGuard src153.bank 179730 2308 src153.reserve := requestWidth (by decide)

def ends153 : List ℕ := [2308, 2309, 2313]

theorem inside153 : Research6966.TerminalBanks.inside src153.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover153 : Cover (Triangular src153) 2313 2308 ends153 := triangleCover (by decide +kernel)

def src1530 : Request := ⟨⟨⟨1756,2437,551,40111⟩,167879222755328,1002904994165⟩,150,5,1,643299,257⟩

theorem rank1530 : P3_7_1.BankOK src1530.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1756_2437_551 40111

theorem width1530 : Lower6960.HelperSource.WidthGuard src1530.bank 179730 2308 src1530.reserve := requestWidth (by decide)

def ends1530 : List ℕ := [2308, 2309, 2313]

theorem inside1530 : Research6966.TerminalBanks.inside src1530.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1530 : Cover (Triangular src1530) 2313 2308 ends1530 := triangleCover (by decide +kernel)

def src1531 : Request := ⟨⟨⟨2957,4108,894,54250⟩,778508848332800,7849872303328⟩,250,5,1,643299,257⟩

theorem rank1531 : P3_7_1.BankOK src1531.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2957_4108_894 54250

theorem width1531 : Lower6960.HelperSource.WidthGuard src1531.bank 179730 2308 src1531.reserve := requestWidth (by decide)

def ends1531 : List ℕ := [2308, 2309, 2313]

theorem inside1531 : Research6966.TerminalBanks.inside src1531.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1531 : Cover (Triangular src1531) 2313 2308 ends1531 := triangleCover (by decide +kernel)

def src1532 : Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,5,1,643299,513⟩

theorem rank1532 : P3_7_1.BankOK src1532.bank := by
  simpa only [src1532, _root_.Research6969.TerminalAuxBanks.bank16] using _root_.Research6969.PackedRanks.TerminalRanks16To19.rank16 50419

theorem width1532 : Lower6960.HelperSource.WidthGuard src1532.bank 179730 2308 src1532.reserve := requestWidth (by decide)

def ends1532 : List ℕ := [2309, 2313]

theorem inside1532 : Research6966.TerminalBanks.inside src1532.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1532 : Cover (Triangular src1532) 2313 2308 ends1532 := triangleCover (by decide +kernel)

def src1533 : Request := ⟨⟨⟨2593,3604,775,59113⟩,520494434484224,4608474947497⟩,249,5,1,643299,513⟩

theorem rank1533 : P3_7_1.BankOK src1533.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2593_3604_775 59113

theorem width1533 : Lower6960.HelperSource.WidthGuard src1533.bank 179730 2308 src1533.reserve := requestWidth (by decide)

def ends1533 : List ℕ := [2308, 2309, 2313]

theorem inside1533 : Research6966.TerminalBanks.inside src1533.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1533 : Cover (Triangular src1533) 2313 2308 ends1533 := triangleCover (by decide +kernel)

def src1534 : Request := ⟨⟨⟨2301,3201,702,79852⟩,369529993297920,2912992731804⟩,250,5,1,643299,1025⟩

theorem rank1534 : P3_7_1.BankOK src1534.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3201_702 79852

theorem width1534 : Lower6960.HelperSource.WidthGuard src1534.bank 179730 2308 src1534.reserve := requestWidth (by decide)

def ends1534 : List ℕ := [2308, 2309, 2313]

theorem inside1534 : Research6966.TerminalBanks.inside src1534.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1534 : Cover (Triangular src1534) 2313 2308 ends1534 := triangleCover (by decide +kernel)

def src1535 : Request := ⟨⟨⟨3001,4171,898,109942⟩,807397411258368,8272669034533⟩,325,5,1,643789,1025⟩

theorem rank1535 : P3_7_1.BankOK src1535.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3001_4171_898 109942

theorem width1535 : Lower6960.HelperSource.WidthGuard src1535.bank 179730 2308 src1535.reserve := requestWidth (by decide)

def ends1535 : List ℕ := [2308, 2309, 2313]

theorem inside1535 : Research6966.TerminalBanks.inside src1535.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1535 : Cover (Triangular src1535) 2313 2308 ends1535 := triangleCover (by decide +kernel)

def src1536 : Request := ⟨⟨⟨2810,3897,881,136171⟩,686816268386304,6548907208321⟩,325,5,1,643299,1537⟩

theorem rank1536 : P3_7_1.BankOK src1536.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2810_3897_881 136171

theorem width1536 : Lower6960.HelperSource.WidthGuard src1536.bank 179730 2308 src1536.reserve := requestWidth (by decide)

def ends1536 : List ℕ := [2308, 2309, 2313]

theorem inside1536 : Research6966.TerminalBanks.inside src1536.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1536 : Cover (Triangular src1536) 2313 2308 ends1536 := triangleCover (by decide +kernel)

def src1537 : Request := ⟨⟨⟨2948,4103,870,110296⟩,757337177718784,7654838454885⟩,325,5,1,643299,1537⟩

theorem rank1537 : P3_7_1.BankOK src1537.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2948_4103_870 110296

theorem width1537 : Lower6960.HelperSource.WidthGuard src1537.bank 179730 2308 src1537.reserve := requestWidth (by decide)

def ends1537 : List ℕ := [2308, 2309, 2313]

theorem inside1537 : Research6966.TerminalBanks.inside src1537.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1537 : Cover (Triangular src1537) 2313 2308 ends1537 := triangleCover (by decide +kernel)

def src1538 : Request := ⟨⟨⟨2808,3900,854,112795⟩,669724928901120,6408244632207⟩,325,5,1,643299,2049⟩

theorem rank1538 : P3_7_1.BankOK src1538.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 112795

theorem width1538 : Lower6960.HelperSource.WidthGuard src1538.bank 179730 2308 src1538.reserve := requestWidth (by decide)

def ends1538 : List ℕ := [2308, 2309, 2313]

theorem inside1538 : Research6966.TerminalBanks.inside src1538.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1538 : Cover (Triangular src1538) 2313 2308 ends1538 := triangleCover (by decide +kernel)

def src1539 : Request := ⟨⟨⟨2805,3896,852,116233⟩,666934584279040,6375459527244⟩,325,5,1,643299,2049⟩

theorem rank1539 : P3_7_1.BankOK src1539.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3896_852 116233

theorem width1539 : Lower6960.HelperSource.WidthGuard src1539.bank 179730 2308 src1539.reserve := requestWidth (by decide)

def ends1539 : List ℕ := [2308, 2309, 2313]

theorem inside1539 : Research6966.TerminalBanks.inside src1539.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1539 : Cover (Triangular src1539) 2313 2308 ends1539 := triangleCover (by decide +kernel)

def src154 : Request := ⟨⟨⟨4800,6695,1474,50764⟩,3367547627110400,55837558620681⟩,110,2,1,296085,41⟩

theorem rank154 : P3_7_1.BankOK src154.bank := by
  simpa only [src154, _root_.Research6969.TransitionBanks.bank324] using _root_.Research6969.TransitionBanks.rank324 50764

theorem width154 : Lower6960.HelperSource.WidthGuard src154.bank 179730 2308 src154.reserve := requestWidth (by decide)

def ends154 : List ℕ := [2309, 2313]



theorem cover154 : Cover (Triangular src154) 2313 2308 ends154 := triangleCover (by decide +kernel)

def src1540 : Request := ⟨⟨⟨2748,3824,812,150758⟩,614083158081536,5782986158433⟩,325,5,1,643299,4097⟩

theorem rank1540 : P3_7_1.BankOK src1540.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2748_3824_812 150758

theorem width1540 : Lower6960.HelperSource.WidthGuard src1540.bank 179730 2308 src1540.reserve := requestWidth (by decide)

def ends1540 : List ℕ := [2308, 2309, 2313]

theorem inside1540 : Research6966.TerminalBanks.inside src1540.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1540 : Cover (Triangular src1540) 2313 2308 ends1540 := triangleCover (by decide +kernel)

def src1541 : Request := ⟨⟨⟨2754,3832,812,151666⟩,617082439073792,5821985239441⟩,325,5,1,643299,4097⟩

theorem rank1541 : P3_7_1.BankOK src1541.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2754_3832_812 151666

theorem width1541 : Lower6960.HelperSource.WidthGuard src1541.bank 179730 2308 src1541.reserve := requestWidth (by decide)

def ends1541 : List ℕ := [2308, 2309, 2313]

theorem inside1541 : Research6966.TerminalBanks.inside src1541.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1541 : Cover (Triangular src1541) 2313 2308 ends1541 := triangleCover (by decide +kernel)

def src1542 : Request := ⟨⟨⟨2003,2782,610,195029⟩,243494574096384,1662397981334⟩,250,5,1,643299,8193⟩

theorem rank1542 : P3_7_1.BankOK src1542.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2003_2782_610 195029

theorem width1542 : Lower6960.HelperSource.WidthGuard src1542.bank 179730 2308 src1542.reserve := requestWidth (by decide)

def ends1542 : List ℕ := [2308, 2309, 2313]

theorem inside1542 : Research6966.TerminalBanks.inside src1542.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1542 : Cover (Triangular src1542) 2313 2308 ends1542 := triangleCover (by decide +kernel)

def src1543 : Request := ⟨⟨⟨1202,1670,365,139374⟩,52587979866112,215752938462⟩,150,5,1,643299,32769⟩

theorem rank1543 : P3_7_1.BankOK src1543.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1670_365 139374

theorem width1543 : Lower6960.HelperSource.WidthGuard src1543.bank 179730 2308 src1543.reserve := requestWidth (by decide)

def ends1543 : List ℕ := [2308, 2309, 2313]

theorem inside1543 : Research6966.TerminalBanks.inside src1543.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1543 : Cover (Triangular src1543) 2313 2308 ends1543 := triangleCover (by decide +kernel)

def src1544 : Request := ⟨⟨⟨556,772,170,7618⟩,5255817068544,9968090926⟩,10,5,2,643298,2⟩

theorem rank1544 : P3_7_1.BankOK src1544.bank := by
  simpa only [src1544, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7618

theorem width1544 : Lower6960.HelperSource.WidthGuard src1544.bank 179730 2308 src1544.reserve := requestWidth (by decide)

def ends1544 : List ℕ := [2308, 2309, 2313]

theorem inside1544 : Research6966.TerminalBanks.inside src1544.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1544 : Cover (Triangular src1544) 2313 2308 ends1544 := triangleCover (by decide +kernel)

def src1545 : Request := ⟨⟨⟨556,772,170,7535⟩,5255817068544,9968090926⟩,10,5,2,643298,3⟩

theorem rank1545 : P3_7_1.BankOK src1545.bank := by
  simpa only [src1545, _root_.Research6969.TransitionBanks.bank154] using _root_.Research6969.TransitionBanks.rank154 7535

theorem width1545 : Lower6960.HelperSource.WidthGuard src1545.bank 179730 2308 src1545.reserve := requestWidth (by decide)

def ends1545 : List ℕ := [2308, 2309, 2313]

theorem inside1545 : Research6966.TerminalBanks.inside src1545.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1545 : Cover (Triangular src1545) 2313 2308 ends1545 := triangleCover (by decide +kernel)

def src1546 : Request := ⟨⟨⟨553,767,170,7357⟩,5192611528704,9761995171⟩,10,5,2,643298,5⟩

theorem rank1546 : P3_7_1.BankOK src1546.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_553_767_170 7357

theorem width1546 : Lower6960.HelperSource.WidthGuard src1546.bank 179730 2308 src1546.reserve := requestWidth (by decide)

def ends1546 : List ℕ := [2308, 2309, 2313]

theorem inside1546 : Research6966.TerminalBanks.inside src1546.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1546 : Cover (Triangular src1546) 2313 2308 ends1546 := triangleCover (by decide +kernel)

def src1547 : Request := ⟨⟨⟨556,772,171,6955⟩,5279150768128,10013440706⟩,10,5,2,643298,10⟩

theorem rank1547 : P3_7_1.BankOK src1547.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6955

theorem width1547 : Lower6960.HelperSource.WidthGuard src1547.bank 179730 2308 src1547.reserve := requestWidth (by decide)

def ends1547 : List ℕ := [2308, 2309, 2313]

theorem inside1547 : Research6966.TerminalBanks.inside src1547.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1547 : Cover (Triangular src1547) 2313 2308 ends1547 := triangleCover (by decide +kernel)

def src1548 : Request := ⟨⟨⟨556,772,171,6413⟩,5279150768128,10013440706⟩,10,5,2,643298,17⟩

theorem rank1548 : P3_7_1.BankOK src1548.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_556_772_171 6413

theorem width1548 : Lower6960.HelperSource.WidthGuard src1548.bank 179730 2308 src1548.reserve := requestWidth (by decide)

def ends1548 : List ℕ := [2308, 2309, 2313]

theorem inside1548 : Research6966.TerminalBanks.inside src1548.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1548 : Cover (Triangular src1548) 2313 2308 ends1548 := triangleCover (by decide +kernel)

def src1549 : Request := ⟨⟨⟨545,756,170,5680⟩,5026035793920,9318832198⟩,10,5,2,643298,27⟩

theorem rank1549 : P3_7_1.BankOK src1549.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_545_756_170 5680

theorem width1549 : Lower6960.HelperSource.WidthGuard src1549.bank 179730 2308 src1549.reserve := requestWidth (by decide)

def ends1549 : List ℕ := [2308, 2309, 2313]

theorem inside1549 : Research6966.TerminalBanks.inside src1549.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1549 : Cover (Triangular src1549) 2313 2308 ends1549 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources21

section Pack_R6970Height2313CommonSources30

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1780 : Request := ⟨⟨⟨2800,3905,882,530820⟩,681932636815360,6598128215989⟩,63,2,1,257319,17⟩

theorem rank1780 : P3_7_1.BankOK src1780.bank := by
  simpa only [src1780, _root_.Research6969.TerminalAuxBanks.bank67] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank67 530820

theorem width1780 : Lower6960.HelperSource.WidthGuard src1780.bank 179730 2308 src1780.reserve := requestWidth (by decide)

def ends1780 : List ℕ := [2308, 2313]

theorem inside1780 : Research6966.TerminalBanks.inside src1780.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1780 : Cover (Rectangle src1780 7207) 2313 2308 ends1780 := rectangleCover (by decide +kernel)

def src1781 : Request := ⟨⟨⟨2606,3626,793,530820⟩,535631510110208,4784491173220⟩,63,2,1,257319,18⟩

theorem rank1781 : P3_7_1.BankOK src1781.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3626_793 530820

theorem width1781 : Lower6960.HelperSource.WidthGuard src1781.bank 179730 2308 src1781.reserve := requestWidth (by decide)

def ends1781 : List ℕ := [2308, 2309, 2313]

theorem inside1781 : Research6966.TerminalBanks.inside src1781.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1781 : Cover (Rectangle src1781 6653) 2313 2308 ends1781 := rectangleCover (by decide +kernel)

def src1782 : Request := ⟨⟨⟨2302,3207,724,530820⟩,378640629760000,3001726552718⟩,63,2,1,257319,19⟩

theorem rank1782 : P3_7_1.BankOK src1782.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3207_724 530820

theorem width1782 : Lower6960.HelperSource.WidthGuard src1782.bank 179730 2308 src1782.reserve := requestWidth (by decide)

def ends1782 : List ℕ := [2309, 2313]

theorem inside1782 : Research6966.TerminalBanks.inside src1782.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1782 : Cover (Rectangle src1782 6142) 2313 2308 ends1782 := rectangleCover (by decide +kernel)

def src1783 : Request := ⟨⟨⟨2816,3905,882,530820⟩,690700839813120,6598128215989⟩,85,2,1,257319,20⟩

theorem rank1783 : P3_7_1.BankOK src1783.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 530820

theorem width1783 : Lower6960.HelperSource.WidthGuard src1783.bank 179730 2308 src1783.reserve := requestWidth (by decide)

def ends1783 : List ℕ := [2308, 2313]

theorem inside1783 : Research6966.TerminalBanks.inside src1783.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1783 : Cover (Rectangle src1783 7207) 2313 2308 ends1783 := rectangleCover (by decide +kernel)

def src1784 : Request := ⟨⟨⟨2605,3625,819,530820⟩,548420614881280,4901614794409⟩,85,2,1,257319,21⟩

theorem rank1784 : P3_7_1.BankOK src1784.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3625_819 530820

theorem width1784 : Lower6960.HelperSource.WidthGuard src1784.bank 179730 2308 src1784.reserve := requestWidth (by decide)

def ends1784 : List ℕ := [2308, 2309, 2313]

theorem inside1784 : Research6966.TerminalBanks.inside src1784.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1784 : Cover (Rectangle src1784 7207) 2313 2308 ends1784 := rectangleCover (by decide +kernel)

def src1785 : Request := ⟨⟨⟨2608,3625,793,530820⟩,536551915520000,4780245027563⟩,85,2,1,257319,22⟩

theorem rank1785 : P3_7_1.BankOK src1785.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3625_793 530820

theorem width1785 : Lower6960.HelperSource.WidthGuard src1785.bank 179730 2308 src1785.reserve := requestWidth (by decide)

def ends1785 : List ℕ := [2308, 2309, 2313]

theorem inside1785 : Research6966.TerminalBanks.inside src1785.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1785 : Cover (Rectangle src1785 6653) 2313 2308 ends1785 := rectangleCover (by decide +kernel)

def src1786 : Request := ⟨⟨⟨2601,3625,793,530820⟩,533334139076608,4780245027563⟩,85,2,1,257319,23⟩

theorem rank1786 : P3_7_1.BankOK src1786.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3625_793 530820

theorem width1786 : Lower6960.HelperSource.WidthGuard src1786.bank 179730 2308 src1786.reserve := requestWidth (by decide)

def ends1786 : List ℕ := [2308, 2309, 2313]

theorem inside1786 : Research6966.TerminalBanks.inside src1786.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1786 : Cover (Rectangle src1786 6142) 2313 2308 ends1786 := rectangleCover (by decide +kernel)

def src1787 : Request := ⟨⟨⟨2303,3207,702,530820⟩,370249266364416,2930605494152⟩,85,2,1,257319,24⟩

theorem rank1787 : P3_7_1.BankOK src1787.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3207_702 530820

theorem width1787 : Lower6960.HelperSource.WidthGuard src1787.bank 179730 2308 src1787.reserve := requestWidth (by decide)

def ends1787 : List ℕ := [2308, 2309, 2313]

theorem inside1787 : Research6966.TerminalBanks.inside src1787.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1787 : Cover (Rectangle src1787 6653) 2313 2308 ends1787 := rectangleCover (by decide +kernel)

def src1788 : Request := ⟨⟨⟨2809,3903,882,530820⟩,686857459597312,6587245977411⟩,115,2,1,257319,25⟩

theorem rank1788 : P3_7_1.BankOK src1788.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3903_882 530820

theorem width1788 : Lower6960.HelperSource.WidthGuard src1788.bank 179730 2308 src1788.reserve := requestWidth (by decide)

def ends1788 : List ℕ := [2308, 2309, 2313]

theorem inside1788 : Research6966.TerminalBanks.inside src1788.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1788 : Cover (Rectangle src1788 9161) 2313 2308 ends1788 := rectangleCover (by decide +kernel)

def src1789 : Request := ⟨⟨⟨2803,3903,854,530820⟩,667058865438720,6424126719762⟩,115,2,1,257319,26⟩

theorem rank1789 : P3_7_1.BankOK src1789.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2803_3903_854 530820

theorem width1789 : Lower6960.HelperSource.WidthGuard src1789.bank 179730 2308 src1789.reserve := requestWidth (by decide)

def ends1789 : List ℕ := [2308, 2309, 2313]

theorem inside1789 : Research6966.TerminalBanks.inside src1789.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1789 : Cover (Rectangle src1789 8457) 2313 2308 ends1789 := rectangleCover (by decide +kernel)

def src179 : Request := ⟨⟨⟨562,781,176,5419⟩,5526256353280,10627925923⟩,3,2,1,303684,40⟩

theorem rank179 : P3_7_1.BankOK src179.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_176 5419

theorem width179 : Lower6960.HelperSource.WidthGuard src179.bank 179730 2308 src179.reserve := requestWidth (by decide)

def ends179 : List ℕ := [2308, 2309, 2313]

theorem inside179 : Research6966.TerminalBanks.inside src179.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover179 : Cover (Triangular src179) 2313 2308 ends179 := triangleCover (by decide +kernel)

def src1790 : Request := ⟨⟨⟨2800,3903,854,530820⟩,665461916958720,6424126719762⟩,115,2,1,257319,27⟩

theorem rank1790 : P3_7_1.BankOK src1790.bank := by
  simpa only [src1790, _root_.Research6969.TerminalAuxBanks.bank64] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank64 530820

theorem width1790 : Lower6960.HelperSource.WidthGuard src1790.bank 179730 2308 src1790.reserve := requestWidth (by decide)

def ends1790 : List ℕ := [2313]

theorem inside1790 : Research6966.TerminalBanks.inside src1790.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1790 : Cover (Rectangle src1790 7807) 2313 2308 ends1790 := rectangleCover (by decide +kernel)

def src1791 : Request := ⟨⟨⟨2608,3624,819,530820⟩,549837726023680,4897259437389⟩,115,2,1,257319,28⟩

theorem rank1791 : P3_7_1.BankOK src1791.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2608_3624_819 530820

theorem width1791 : Lower6960.HelperSource.WidthGuard src1791.bank 179730 2308 src1791.reserve := requestWidth (by decide)

def ends1791 : List ℕ := [2308, 2309, 2313]

theorem inside1791 : Research6966.TerminalBanks.inside src1791.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1791 : Cover (Rectangle src1791 7207) 2313 2308 ends1791 := rectangleCover (by decide +kernel)

def src1792 : Request := ⟨⟨⟨2605,3618,793,530820⟩,535171619618816,4750593761744⟩,115,2,1,257515,29⟩

theorem rank1792 : P3_7_1.BankOK src1792.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3618_793 530820

theorem width1792 : Lower6960.HelperSource.WidthGuard src1792.bank 179730 2308 src1792.reserve := requestWidth (by decide)

def ends1792 : List ℕ := [2308, 2309, 2313]

theorem inside1792 : Research6966.TerminalBanks.inside src1792.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1792 : Cover (Rectangle src1792 7207) 2313 2308 ends1792 := rectangleCover (by decide +kernel)

def src1793 : Request := ⟨⟨⟨2600,3618,775,530820⟩,523640687820800,4666316635317⟩,115,2,1,257515,30⟩

theorem rank1793 : P3_7_1.BankOK src1793.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3618_775 530820

theorem width1793 : Lower6960.HelperSource.WidthGuard src1793.bank 179730 2308 src1793.reserve := requestWidth (by decide)

def ends1793 : List ℕ := [2308, 2309, 2313]

theorem inside1793 : Research6966.TerminalBanks.inside src1793.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1793 : Cover (Rectangle src1793 7807) 2313 2308 ends1793 := rectangleCover (by decide +kernel)

def src1794 : Request := ⟨⟨⟨2600,3620,775,530820⟩,523640687820800,4674619806217⟩,115,2,1,257515,31⟩

theorem rank1794 : P3_7_1.BankOK src1794.bank := by
  simpa only [src1794, _root_.Research6969.TerminalAuxBanks.bank38] using _root_.Research6969.PackedRanks.TerminalRanks36To39.rank38 530820

theorem width1794 : Lower6960.HelperSource.WidthGuard src1794.bank 179730 2308 src1794.reserve := requestWidth (by decide)

def ends1794 : List ℕ := [2308, 2309, 2313]

theorem inside1794 : Research6966.TerminalBanks.inside src1794.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1794 : Cover (Rectangle src1794 7207) 2313 2308 ends1794 := rectangleCover (by decide +kernel)

def src1795 : Request := ⟨⟨⟨2302,3206,724,530820⟩,378640629760000,2998712046218⟩,115,2,1,257319,32⟩

theorem rank1795 : P3_7_1.BankOK src1795.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2302_3206_724 530820

theorem width1795 : Lower6960.HelperSource.WidthGuard src1795.bank 179730 2308 src1795.reserve := requestWidth (by decide)

def ends1795 : List ℕ := [2308, 2309, 2313]

theorem inside1795 : Research6966.TerminalBanks.inside src1795.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1795 : Cover (Rectangle src1795 7807) 2313 2308 ends1795 := rectangleCover (by decide +kernel)

def src1796 : Request := ⟨⟨⟨2308,3206,710,503502⟩,375265883848704,2953586856669⟩,116,2,1,257319,33⟩

theorem rank1796 : P3_7_1.BankOK src1796.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2308_3206_710 503502

theorem width1796 : Lower6960.HelperSource.WidthGuard src1796.bank 179730 2308 src1796.reserve := requestWidth (by decide)

def ends1796 : List ℕ := [2308, 2309, 2313]

theorem inside1796 : Research6966.TerminalBanks.inside src1796.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1796 : Cover (Rectangle src1796 7207) 2313 2308 ends1796 := rectangleCover (by decide +kernel)

def src1797 : Request := ⟨⟨⟨2292,3182,702,530820⟩,366302386716672,2857694270952⟩,115,2,1,257515,34⟩

theorem rank1797 : P3_7_1.BankOK src1797.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2292_3182_702 530820

theorem width1797 : Lower6960.HelperSource.WidthGuard src1797.bank 179730 2308 src1797.reserve := requestWidth (by decide)

def ends1797 : List ℕ := [2308, 2309, 2313]

theorem inside1797 : Research6966.TerminalBanks.inside src1797.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1797 : Cover (Rectangle src1797 6653) 2313 2308 ends1797 := rectangleCover (by decide +kernel)

def src1798 : Request := ⟨⟨⟨2800,3902,882,530820⟩,681932636815360,6581809445307⟩,150,2,1,257319,35⟩

theorem rank1798 : P3_7_1.BankOK src1798.bank := by
  simpa only [src1798, _root_.Research6969.TerminalAuxBanks.bank63] using _root_.Research6969.PackedRanks.TerminalRanks60To63.rank63 530820

theorem width1798 : Lower6960.HelperSource.WidthGuard src1798.bank 179730 2308 src1798.reserve := requestWidth (by decide)

def ends1798 : List ℕ := [2309, 2313]

theorem inside1798 : Research6966.TerminalBanks.inside src1798.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1798 : Cover (Rectangle src1798 9161) 2313 2308 ends1798 := rectangleCover (by decide +kernel)

def src1799 : Request := ⟨⟨⟨2802,3902,854,530820⟩,666526325145600,6418829718882⟩,150,2,1,257319,36⟩

theorem rank1799 : P3_7_1.BankOK src1799.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2802_3902_854 530820

theorem width1799 : Lower6960.HelperSource.WidthGuard src1799.bank 179730 2308 src1799.reserve := requestWidth (by decide)

def ends1799 : List ℕ := [2308, 2309, 2313]

theorem inside1799 : Research6966.TerminalBanks.inside src1799.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1799 : Cover (Rectangle src1799 9161) 2313 2308 ends1799 := rectangleCover (by decide +kernel)

def src18 : Request := ⟨⟨⟨2300,3201,702,77987⟩,369170633195520,2912992731804⟩,249,1,1,128659,1025⟩

theorem rank18 : P3_7_1.BankOK src18.bank := by
  simpa only [src18, _root_.Research6969.TerminalAuxBanks.bank23] using _root_.Research6969.PackedRanks.TerminalRanks20To23.rank23 77987

theorem width18 : Lower6960.HelperSource.WidthGuard src18.bank 179730 2308 src18.reserve := requestWidth (by decide)

def ends18 : List ℕ := [2308, 2309, 2313]

theorem inside18 : Research6966.TerminalBanks.inside src18.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover18 : Cover (Triangular src18) 2313 2308 ends18 := triangleCover (by decide +kernel)

def src180 : Request := ⟨⟨⟨562,781,173,6858⟩,5455101034496,10487621483⟩,4,2,1,303684,40⟩

theorem rank180 : P3_7_1.BankOK src180.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_562_781_173 6858

theorem width180 : Lower6960.HelperSource.WidthGuard src180.bank 179730 2308 src180.reserve := requestWidth (by decide)

def ends180 : List ℕ := [2308, 2309, 2313]

theorem inside180 : Research6966.TerminalBanks.inside src180.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover180 : Cover (Triangular src180) 2313 2308 ends180 := triangleCover (by decide +kernel)

def src1800 : Request := ⟨⟨⟨2802,3902,854,530820⟩,666526325145600,6418829718882⟩,150,2,1,257319,37⟩

theorem rank1800 : P3_7_1.BankOK src1800.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2802_3902_854 530820

theorem width1800 : Lower6960.HelperSource.WidthGuard src1800.bank 179730 2308 src1800.reserve := requestWidth (by decide)

def ends1800 : List ℕ := [2308, 2309, 2313]

theorem inside1800 : Research6966.TerminalBanks.inside src1800.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1800 : Cover (Rectangle src1800 8457) 2313 2308 ends1800 := rectangleCover (by decide +kernel)

def src1801 : Request := ⟨⟨⟨2790,3878,834,530820⟩,648354204221440,6177455542647⟩,150,2,1,257515,38⟩

theorem rank1801 : P3_7_1.BankOK src1801.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2790_3878_834 530820

theorem width1801 : Lower6960.HelperSource.WidthGuard src1801.bank 179730 2308 src1801.reserve := requestWidth (by decide)

def ends1801 : List ℕ := [2308, 2309, 2313]

theorem inside1801 : Research6966.TerminalBanks.inside src1801.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1801 : Cover (Rectangle src1801 9161) 2313 2308 ends1801 := rectangleCover (by decide +kernel)

def src1802 : Request := ⟨⟨⟨2602,3623,819,530820⟩,547005438361600,4892906717079⟩,150,2,1,257319,39⟩

theorem rank1802 : P3_7_1.BankOK src1802.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3623_819 530820

theorem width1802 : Lower6960.HelperSource.WidthGuard src1802.bank 179730 2308 src1802.reserve := requestWidth (by decide)

def ends1802 : List ℕ := [2308, 2309, 2313]

theorem inside1802 : Research6966.TerminalBanks.inside src1802.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1802 : Cover (Rectangle src1802 9161) 2313 2308 ends1802 := rectangleCover (by decide +kernel)

def src1803 : Request := ⟨⟨⟨2609,3623,795,530820⟩,538041673318400,4781126977761⟩,150,2,1,257515,40⟩

theorem rank1803 : P3_7_1.BankOK src1803.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2609_3623_795 530820

theorem width1803 : Lower6960.HelperSource.WidthGuard src1803.bank 179730 2308 src1803.reserve := requestWidth (by decide)

def ends1803 : List ℕ := [2309, 2313]

theorem inside1803 : Research6966.TerminalBanks.inside src1803.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1803 : Cover (Rectangle src1803 9161) 2313 2308 ends1803 := rectangleCover (by decide +kernel)

def src1804 : Request := ⟨⟨⟨2604,3617,793,530820⟩,534711937269760,4746368107639⟩,150,2,1,257515,41⟩

theorem rank1804 : P3_7_1.BankOK src1804.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3617_793 530820

theorem width1804 : Lower6960.HelperSource.WidthGuard src1804.bank 179730 2308 src1804.reserve := requestWidth (by decide)

def ends1804 : List ℕ := [2308, 2309, 2313]

theorem inside1804 : Research6966.TerminalBanks.inside src1804.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1804 : Cover (Rectangle src1804 8457) 2313 2308 ends1804 := rectangleCover (by decide +kernel)

def src1805 : Request := ⟨⟨⟨2600,3623,793,530820⟩,532875289296896,4771760428124⟩,150,2,1,257319,42⟩

theorem rank1805 : P3_7_1.BankOK src1805.bank := by
  simpa only [src1805, _root_.Research6969.TerminalAuxBanks.bank40] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank40 530820

theorem width1805 : Lower6960.HelperSource.WidthGuard src1805.bank 179730 2308 src1805.reserve := requestWidth (by decide)

def ends1805 : List ℕ := [2313]

theorem inside1805 : Research6966.TerminalBanks.inside src1805.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1805 : Cover (Rectangle src1805 8457) 2313 2308 ends1805 := rectangleCover (by decide +kernel)

def src1806 : Request := ⟨⟨⟨2602,3623,793,530820⟩,533793196998656,4771760428124⟩,150,2,1,257319,43⟩

theorem rank1806 : P3_7_1.BankOK src1806.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3623_793 530820

theorem width1806 : Lower6960.HelperSource.WidthGuard src1806.bank 179730 2308 src1806.reserve := requestWidth (by decide)

def ends1806 : List ℕ := [2308, 2309, 2313]

theorem inside1806 : Research6966.TerminalBanks.inside src1806.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1806 : Cover (Rectangle src1806 7807) 2313 2308 ends1806 := rectangleCover (by decide +kernel)

def src1807 : Request := ⟨⟨⟨2600,3611,775,530820⟩,523640687820800,4637334487213⟩,150,2,1,257515,44⟩

theorem rank1807 : P3_7_1.BankOK src1807.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3611_775 530820

theorem width1807 : Lower6960.HelperSource.WidthGuard src1807.bank 179730 2308 src1807.reserve := requestWidth (by decide)

def ends1807 : List ℕ := [2308, 2309, 2313]

theorem inside1807 : Research6966.TerminalBanks.inside src1807.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1807 : Cover (Rectangle src1807 8457) 2313 2308 ends1807 := rectangleCover (by decide +kernel)

def src1808 : Request := ⟨⟨⟨2586,3591,793,530820⟩,526473247326208,4637396591180⟩,150,2,1,257515,45⟩

theorem rank1808 : P3_7_1.BankOK src1808.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2586_3591_793 530820

theorem width1808 : Lower6960.HelperSource.WidthGuard src1808.bank 179730 2308 src1808.reserve := requestWidth (by decide)

def ends1808 : List ℕ := [2308, 2309, 2313]

theorem inside1808 : Research6966.TerminalBanks.inside src1808.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1808 : Cover (Rectangle src1808 7207) 2313 2308 ends1808 := rectangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources30

section Pack_R6970Height2313CommonSources31

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1809 : Request := ⟨⟨⟨2595,3607,775,530820⟩,521392346890240,4620828325461⟩,150,2,1,257515,46⟩

theorem rank1809 : P3_7_1.BankOK src1809.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2595_3607_775 530820

theorem width1809 : Lower6960.HelperSource.WidthGuard src1809.bank 179730 2308 src1809.reserve := requestWidth (by decide)

def ends1809 : List ℕ := [2309, 2313]

theorem inside1809 : Research6966.TerminalBanks.inside src1809.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1809 : Cover (Rectangle src1809 7807) 2313 2308 ends1809 := rectangleCover (by decide +kernel)

def src181 : Request := ⟨⟨⟨691,962,212,6858⟩,10098434375680,23997864317⟩,6,2,1,303684,40⟩

theorem rank181 : P3_7_1.BankOK src181.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 6858

theorem width181 : Lower6960.HelperSource.WidthGuard src181.bank 179730 2308 src181.reserve := requestWidth (by decide)

def ends181 : List ℕ := [2308, 2309, 2313]

theorem inside181 : Research6966.TerminalBanks.inside src181.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover181 : Cover (Triangular src181) 2313 2308 ends181 := triangleCover (by decide +kernel)

def src1810 : Request := ⟨⟨⟨2600,3623,775,530820⟩,523640687820800,4687093383477⟩,150,2,1,257319,47⟩

theorem rank1810 : P3_7_1.BankOK src1810.bank := by
  simpa only [src1810, _root_.Research6969.TerminalAuxBanks.bank39] using _root_.Research6969.PackedRanks.TerminalRanks36To39.rank39 530820

theorem width1810 : Lower6960.HelperSource.WidthGuard src1810.bank 179730 2308 src1810.reserve := requestWidth (by decide)

def ends1810 : List ℕ := [2308, 2313]

theorem inside1810 : Research6966.TerminalBanks.inside src1810.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1810 : Cover (Rectangle src1810 7807) 2313 2308 ends1810 := rectangleCover (by decide +kernel)

def src1811 : Request := ⟨⟨⟨1438,1996,442,530820⟩,90817910276096,444422784858⟩,85,2,1,257515,48⟩

theorem rank1811 : P3_7_1.BankOK src1811.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1438_1996_442 530820

theorem width1811 : Lower6960.HelperSource.WidthGuard src1811.bank 179730 2308 src1811.reserve := requestWidth (by decide)

def ends1811 : List ℕ := [2308, 2309, 2313]

theorem inside1811 : Research6966.TerminalBanks.inside src1811.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1811 : Cover (Rectangle src1811 4461) 2313 2308 ends1811 := rectangleCover (by decide +kernel)

def src1812 : Request := ⟨⟨⟨2312,3207,724,530820⟩,382338138112000,3001726552718⟩,150,2,1,257515,49⟩

theorem rank1812 : P3_7_1.BankOK src1812.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 530820

theorem width1812 : Lower6960.HelperSource.WidthGuard src1812.bank 179730 2308 src1812.reserve := requestWidth (by decide)

def ends1812 : List ℕ := [2308, 2309, 2313]

theorem inside1812 : Research6966.TerminalBanks.inside src1812.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1812 : Cover (Rectangle src1812 8457) 2313 2308 ends1812 := rectangleCover (by decide +kernel)

def src1813 : Request := ⟨⟨⟨2304,3204,706,530820⟩,372211941900288,2934736528158⟩,150,2,1,257515,50⟩

theorem rank1813 : P3_7_1.BankOK src1813.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2304_3204_706 530820

theorem width1813 : Lower6960.HelperSource.WidthGuard src1813.bank 179730 2308 src1813.reserve := requestWidth (by decide)

def ends1813 : List ℕ := [2308, 2309, 2313]

theorem inside1813 : Research6966.TerminalBanks.inside src1813.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1813 : Cover (Rectangle src1813 9161) 2313 2308 ends1813 := rectangleCover (by decide +kernel)

def src1814 : Request := ⟨⟨⟨2306,3202,704,530820⟩,372133088460800,2922386046475⟩,150,2,1,257515,51⟩

theorem rank1814 : P3_7_1.BankOK src1814.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2306_3202_704 530820

theorem width1814 : Lower6960.HelperSource.WidthGuard src1814.bank 179730 2308 src1814.reserve := requestWidth (by decide)

def ends1814 : List ℕ := [2308, 2309, 2313]

theorem inside1814 : Research6966.TerminalBanks.inside src1814.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1814 : Cover (Rectangle src1814 8457) 2313 2308 ends1814 := rectangleCover (by decide +kernel)

def src1815 : Request := ⟨⟨⟨2300,3204,702,530820⟩,369170633195520,2921790084349⟩,150,2,1,257319,52⟩

theorem rank1815 : P3_7_1.BankOK src1815.bank := by
  simpa only [src1815, _root_.Research6969.TerminalAuxBanks.bank26] using _root_.Research6969.PackedRanks.TerminalRanks24To27.rank26 530820

theorem width1815 : Lower6960.HelperSource.WidthGuard src1815.bank 179730 2308 src1815.reserve := requestWidth (by decide)

def ends1815 : List ℕ := [2308, 2313]

theorem inside1815 : Research6966.TerminalBanks.inside src1815.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1815 : Cover (Rectangle src1815 8457) 2313 2308 ends1815 := rectangleCover (by decide +kernel)

def src1816 : Request := ⟨⟨⟨2290,3180,702,530820⟩,365587167969280,2851915272809⟩,150,2,1,257515,53⟩

theorem rank1816 : P3_7_1.BankOK src1816.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2290_3180_702 530820

theorem width1816 : Lower6960.HelperSource.WidthGuard src1816.bank 179730 2308 src1816.reserve := requestWidth (by decide)

def ends1816 : List ℕ := [2308, 2309, 2313]

theorem inside1816 : Research6966.TerminalBanks.inside src1816.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1816 : Cover (Rectangle src1816 7807) 2313 2308 ends1816 := rectangleCover (by decide +kernel)

def src1817 : Request := ⟨⟨⟨2998,4168,894,530820⟩,802855484129280,8224830503778⟩,195,2,1,257515,54⟩

theorem rank1817 : P3_7_1.BankOK src1817.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4168_894 530820

theorem width1817 : Lower6960.HelperSource.WidthGuard src1817.bank 179730 2308 src1817.reserve := requestWidth (by decide)

def ends1817 : List ℕ := [2308, 2309, 2313]

theorem inside1817 : Research6966.TerminalBanks.inside src1817.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1817 : Cover (Rectangle src1817 10751) 2313 2308 ends1817 := rectangleCover (by decide +kernel)

def src1818 : Request := ⟨⟨⟨3000,4180,894,530820⟩,804053213511680,8301255031708⟩,195,2,1,257319,55⟩

theorem rank1818 : P3_7_1.BankOK src1818.bank := by
  simpa only [src1818, _root_.Research6969.TerminalAuxBanks.bank76] using _root_.Research6969.PackedRanks.TerminalRanks76To78.rank76 530820

theorem width1818 : Lower6960.HelperSource.WidthGuard src1818.bank 179730 2308 src1818.reserve := requestWidth (by decide)

def ends1818 : List ℕ := [2308, 2313]

theorem inside1818 : Research6966.TerminalBanks.inside src1818.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1818 : Cover (Rectangle src1818 10751) 2313 2308 ends1818 := rectangleCover (by decide +kernel)

def src1819 : Request := ⟨⟨⟨2802,3901,882,530820⟩,683025421565952,6576375970149⟩,195,2,1,257319,56⟩

theorem rank1819 : P3_7_1.BankOK src1819.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2802_3901_882 530820

theorem width1819 : Lower6960.HelperSource.WidthGuard src1819.bank 179730 2308 src1819.reserve := requestWidth (by decide)

def ends1819 : List ℕ := [2308, 2309, 2313]

theorem inside1819 : Research6966.TerminalBanks.inside src1819.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1819 : Cover (Rectangle src1819 10751) 2313 2308 ends1819 := rectangleCover (by decide +kernel)

def src182 : Request := ⟨⟨⟨826,1151,260,8679⟩,17566568546304,50057971890⟩,10,2,1,303684,40⟩

theorem rank182 : P3_7_1.BankOK src182.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_826_1151_260 8679

theorem width182 : Lower6960.HelperSource.WidthGuard src182.bank 179730 2308 src182.reserve := requestWidth (by decide)

def ends182 : List ℕ := [2308, 2309, 2313]

theorem inside182 : Research6966.TerminalBanks.inside src182.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover182 : Cover (Triangular src182) 2313 2308 ends182 := triangleCover (by decide +kernel)

def src1820 : Request := ⟨⟨⟨2809,3901,855,530820⟩,670855447183360,6419382474065⟩,195,2,1,257515,57⟩

theorem rank1820 : P3_7_1.BankOK src1820.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3901_855 530820

theorem width1820 : Lower6960.HelperSource.WidthGuard src1820.bank 179730 2308 src1820.reserve := requestWidth (by decide)

def ends1820 : List ℕ := [2308, 2309, 2313]

theorem inside1820 : Research6966.TerminalBanks.inside src1820.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1820 : Cover (Rectangle src1820 11646) 2313 2308 ends1820 := rectangleCover (by decide +kernel)

def src1821 : Request := ⟨⟨⟨2800,3907,835,521881⟩,654158360739840,6333230515528⟩,21,3,1,385979,0⟩

theorem rank1821 : P3_7_1.BankOK src1821.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3907_835 521881

theorem width1821 : Lower6960.HelperSource.WidthGuard src1821.bank 179730 2308 src1821.reserve := requestWidth (by decide)

def ends1821 : List ℕ := [2308, 2309, 2313]

theorem inside1821 : Research6966.TerminalBanks.inside src1821.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1821 : Cover (Rectangle src1821 62519) 2313 2308 ends1821 := rectangleCover (by decide +kernel)

def src1822 : Request := ⟨⟨⟨2800,3907,835,525046⟩,654158360739840,6333230515528⟩,21,3,1,385979,1⟩

theorem rank1822 : P3_7_1.BankOK src1822.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3907_835 525046

theorem width1822 : Lower6960.HelperSource.WidthGuard src1822.bank 179730 2308 src1822.reserve := requestWidth (by decide)

def ends1822 : List ℕ := [2308, 2309, 2313]

theorem inside1822 : Research6966.TerminalBanks.inside src1822.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1822 : Cover (Rectangle src1822 57710) 2313 2308 ends1822 := rectangleCover (by decide +kernel)

def src1823 : Request := ⟨⟨⟨2623,3644,793,529939⟩,543481494241280,4861361182339⟩,21,3,1,385979,2⟩

theorem rank1823 : P3_7_1.BankOK src1823.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2623_3644_793 529939

theorem width1823 : Lower6960.HelperSource.WidthGuard src1823.bank 179730 2308 src1823.reserve := requestWidth (by decide)

def ends1823 : List ℕ := [2308, 2309, 2313]

theorem inside1823 : Research6966.TerminalBanks.inside src1823.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1823 : Cover (Rectangle src1823 53271) 2313 2308 ends1823 := rectangleCover (by decide +kernel)

def src1824 : Request := ⟨⟨⟨2965,4120,898,455656⟩,785894641238016,7951531802886⟩,21,3,1,386273,3⟩

theorem rank1824 : P3_7_1.BankOK src1824.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2965_4120_898 455656

theorem width1824 : Lower6960.HelperSource.WidthGuard src1824.bank 179730 2308 src1824.reserve := requestWidth (by decide)

def ends1824 : List ℕ := [2308, 2309, 2313]

theorem inside1824 : Research6966.TerminalBanks.inside src1824.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1824 : Cover (Rectangle src1824 45392) 2313 2308 ends1824 := rectangleCover (by decide +kernel)

def src1825 : Request := ⟨⟨⟨2965,4120,900,528770⟩,787225901793280,7965324963082⟩,22,3,1,386273,4⟩

theorem rank1825 : P3_7_1.BankOK src1825.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2965_4120_900 528770

theorem width1825 : Lower6960.HelperSource.WidthGuard src1825.bank 179730 2308 src1825.reserve := requestWidth (by decide)

def ends1825 : List ℕ := [2308, 2309, 2313]

theorem inside1825 : Research6966.TerminalBanks.inside src1825.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1825 : Cover (Rectangle src1825 41901) 2313 2308 ends1825 := rectangleCover (by decide +kernel)

def src1826 : Request := ⟨⟨⟨2612,3628,793,521695⟩,538395224047616,4792991160379⟩,21,3,1,385979,5⟩

theorem rank1826 : P3_7_1.BankOK src1826.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_793 521695

theorem width1826 : Lower6960.HelperSource.WidthGuard src1826.bank 179730 2308 src1826.reserve := requestWidth (by decide)

def ends1826 : List ℕ := [2308, 2309, 2313]

theorem inside1826 : Research6966.TerminalBanks.inside src1826.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1826 : Cover (Rectangle src1826 38678) 2313 2308 ends1826 := rectangleCover (by decide +kernel)

def src1827 : Request := ⟨⟨⟨2941,4102,896,530820⟩,770422526967808,7826642207395⟩,22,3,1,386273,6⟩

theorem rank1827 : P3_7_1.BankOK src1827.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2941_4102_896 530820

theorem width1827 : Lower6960.HelperSource.WidthGuard src1827.bank 179730 2308 src1827.reserve := requestWidth (by decide)

def ends1827 : List ℕ := [2308, 2309, 2313]

theorem inside1827 : Research6966.TerminalBanks.inside src1827.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1827 : Cover (Rectangle src1827 32957) 2313 2308 ends1827 := rectangleCover (by decide +kernel)

def src1828 : Request := ⟨⟨⟨2942,4102,896,530820⟩,771008974028800,7826642207395⟩,22,3,1,386273,7⟩

theorem rank1828 : P3_7_1.BankOK src1828.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2942_4102_896 530820

theorem width1828 : Lower6960.HelperSource.WidthGuard src1828.bank 179730 2308 src1828.reserve := requestWidth (by decide)

def ends1828 : List ℕ := [2308, 2309, 2313]

theorem inside1828 : Research6966.TerminalBanks.inside src1828.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1828 : Cover (Rectangle src1828 28082) 2313 2308 ends1828 := rectangleCover (by decide +kernel)

def src1829 : Request := ⟨⟨⟨2612,3628,793,496556⟩,538395224047616,4792991160379⟩,21,3,1,385979,8⟩

theorem rank1829 : P3_7_1.BankOK src1829.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_793 496556

theorem width1829 : Lower6960.HelperSource.WidthGuard src1829.bank 179730 2308 src1829.reserve := requestWidth (by decide)

def ends1829 : List ℕ := [2308, 2309, 2313]

theorem inside1829 : Research6966.TerminalBanks.inside src1829.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1829 : Cover (Rectangle src1829 23928) 2313 2308 ends1829 := rectangleCover (by decide +kernel)

def src183 : Request := ⟨⟨⟨1194,1658,368,13766⟩,52130505031680,212148065594⟩,20,2,1,303684,40⟩

theorem rank183 : P3_7_1.BankOK src183.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1194_1658_368 13766

theorem width183 : Lower6960.HelperSource.WidthGuard src183.bank 179730 2308 src183.reserve := requestWidth (by decide)

def ends183 : List ℕ := [2308, 2309, 2313]

theorem inside183 : Research6966.TerminalBanks.inside src183.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover183 : Cover (Triangular src183) 2313 2308 ends183 := triangleCover (by decide +kernel)

def src1830 : Request := ⟨⟨⟨2612,3628,793,521863⟩,538395224047616,4792991160379⟩,21,3,1,385979,9⟩

theorem rank1830 : P3_7_1.BankOK src1830.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2612_3628_793 521863

theorem width1830 : Lower6960.HelperSource.WidthGuard src1830.bank 179730 2308 src1830.reserve := requestWidth (by decide)

def ends1830 : List ℕ := [2308, 2309, 2313]

theorem inside1830 : Research6966.TerminalBanks.inside src1830.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1830 : Cover (Rectangle src1830 18821) 2313 2308 ends1830 := rectangleCover (by decide +kernel)

def src1831 : Request := ⟨⟨⟨2800,3891,854,530820⟩,665461916958720,6360758671782⟩,22,3,1,386273,10⟩

theorem rank1831 : P3_7_1.BankOK src1831.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2800_3891_854 530820

theorem width1831 : Lower6960.HelperSource.WidthGuard src1831.bank 179730 2308 src1831.reserve := requestWidth (by decide)

def ends1831 : List ℕ := [2308, 2309, 2313]

theorem inside1831 : Research6966.TerminalBanks.inside src1831.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1831 : Cover (Rectangle src1831 13667) 2313 2308 ends1831 := rectangleCover (by decide +kernel)

def src1832 : Request := ⟨⟨⟨2590,3596,793,530820⟩,528298239328256,4658219016875⟩,22,3,1,386273,11⟩

theorem rank1832 : P3_7_1.BankOK src1832.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2590_3596_793 530820

theorem width1832 : Lower6960.HelperSource.WidthGuard src1832.bank 179730 2308 src1832.reserve := requestWidth (by decide)

def ends1832 : List ℕ := [2308, 2309, 2313]

theorem inside1832 : Research6966.TerminalBanks.inside src1832.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1832 : Cover (Rectangle src1832 9161) 2313 2308 ends1832 := rectangleCover (by decide +kernel)

def src1833 : Request := ⟨⟨⟨2806,3906,882,530820⟩,685213768744960,6603573924229⟩,32,3,1,385979,12⟩

theorem rank1833 : P3_7_1.BankOK src1833.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2806_3906_882 530820

theorem width1833 : Lower6960.HelperSource.WidthGuard src1833.bank 179730 2308 src1833.reserve := requestWidth (by decide)

def ends1833 : List ℕ := [2308, 2309, 2313]

theorem inside1833 : Research6966.TerminalBanks.inside src1833.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1833 : Cover (Rectangle src1833 8457) 2313 2308 ends1833 := rectangleCover (by decide +kernel)

def src1834 : Request := ⟨⟨⟨2304,3209,724,530820⟩,379378610995200,3007761756493⟩,32,3,1,385979,13⟩

theorem rank1834 : P3_7_1.BankOK src1834.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2304_3209_724 530820

theorem width1834 : Lower6960.HelperSource.WidthGuard src1834.bank 179730 2308 src1834.reserve := requestWidth (by decide)

def ends1834 : List ℕ := [2308, 2309, 2313]

theorem inside1834 : Research6966.TerminalBanks.inside src1834.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1834 : Cover (Rectangle src1834 6653) 2313 2308 ends1834 := rectangleCover (by decide +kernel)

def src1835 : Request := ⟨⟨⟨2604,3627,819,530820⟩,547948674416640,4910333421859⟩,45,3,1,385979,14⟩

theorem rank1835 : P3_7_1.BankOK src1835.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3627_819 530820

theorem width1835 : Lower6960.HelperSource.WidthGuard src1835.bank 179730 2308 src1835.reserve := requestWidth (by decide)

def ends1835 : List ℕ := [2309, 2313]

theorem inside1835 : Research6966.TerminalBanks.inside src1835.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1835 : Cover (Rectangle src1835 7207) 2313 2308 ends1835 := rectangleCover (by decide +kernel)

def src1836 : Request := ⟨⟨⟨2303,3208,724,530820⟩,379009525350400,3004743122568⟩,45,3,1,385979,15⟩

theorem rank1836 : P3_7_1.BankOK src1836.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3208_724 530820

theorem width1836 : Lower6960.HelperSource.WidthGuard src1836.bank 179730 2308 src1836.reserve := requestWidth (by decide)

def ends1836 : List ℕ := [2309, 2313]

theorem inside1836 : Research6966.TerminalBanks.inside src1836.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1836 : Cover (Rectangle src1836 6142) 2313 2308 ends1836 := rectangleCover (by decide +kernel)

def src1837 : Request := ⟨⟨⟨2801,3905,882,530820⟩,682478913454080,6598128215989⟩,63,3,1,385979,16⟩

theorem rank1837 : P3_7_1.BankOK src1837.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3905_882 530820

theorem width1837 : Lower6960.HelperSource.WidthGuard src1837.bank 179730 2308 src1837.reserve := requestWidth (by decide)

def ends1837 : List ℕ := [2308, 2309, 2313]

theorem inside1837 : Research6966.TerminalBanks.inside src1837.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1837 : Cover (Rectangle src1837 7207) 2313 2308 ends1837 := rectangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources31

section Pack_R6970Height2313CommonSources32

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src1838 : Request := ⟨⟨⟨2600,3614,793,530820⟩,532875289296896,4733706489374⟩,63,3,1,386273,17⟩

theorem rank1838 : P3_7_1.BankOK src1838.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3614_793 530820

theorem width1838 : Lower6960.HelperSource.WidthGuard src1838.bank 179730 2308 src1838.reserve := requestWidth (by decide)

def ends1838 : List ℕ := [2308, 2309, 2313]

theorem inside1838 : Research6966.TerminalBanks.inside src1838.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1838 : Cover (Rectangle src1838 6653) 2313 2308 ends1838 := rectangleCover (by decide +kernel)

def src1839 : Request := ⟨⟨⟨2303,3207,724,530820⟩,379009525350400,3001726552718⟩,63,3,1,385979,18⟩

theorem rank1839 : P3_7_1.BankOK src1839.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3207_724 530820

theorem width1839 : Lower6960.HelperSource.WidthGuard src1839.bank 179730 2308 src1839.reserve := requestWidth (by decide)

def ends1839 : List ℕ := [2308, 2309, 2313]

theorem inside1839 : Research6966.TerminalBanks.inside src1839.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1839 : Cover (Rectangle src1839 6142) 2313 2308 ends1839 := rectangleCover (by decide +kernel)

def src184 : Request := ⟨⟨⟨2605,3627,798,25043⟩,537733229182976,4812227595495⟩,50,2,1,303684,40⟩

theorem rank184 : P3_7_1.BankOK src184.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3627_798 25043

theorem width184 : Lower6960.HelperSource.WidthGuard src184.bank 179730 2308 src184.reserve := requestWidth (by decide)

def ends184 : List ℕ := [2308, 2309, 2313]

theorem inside184 : Research6966.TerminalBanks.inside src184.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover184 : Cover (Triangular src184) 2313 2308 ends184 := triangleCover (by decide +kernel)

def src1840 : Request := ⟨⟨⟨2800,3905,882,530820⟩,681932636815360,6598128215989⟩,85,3,1,385979,19⟩

theorem rank1840 : P3_7_1.BankOK src1840.bank := by
  simpa only [src1840, _root_.Research6969.TerminalAuxBanks.bank67] using _root_.Research6969.PackedRanks.TerminalRanks64To67.rank67 530820

theorem width1840 : Lower6960.HelperSource.WidthGuard src1840.bank 179730 2308 src1840.reserve := requestWidth (by decide)

def ends1840 : List ℕ := [2309, 2313]

theorem inside1840 : Research6966.TerminalBanks.inside src1840.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1840 : Cover (Rectangle src1840 7807) 2313 2308 ends1840 := rectangleCover (by decide +kernel)

def src1841 : Request := ⟨⟨⟨2607,3625,819,530820⟩,549365140684800,4901614794409⟩,85,3,1,385979,20⟩

theorem rank1841 : P3_7_1.BankOK src1841.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3625_819 530820

theorem width1841 : Lower6960.HelperSource.WidthGuard src1841.bank 179730 2308 src1841.reserve := requestWidth (by decide)

def ends1841 : List ℕ := [2308, 2309, 2313]

theorem inside1841 : Research6966.TerminalBanks.inside src1841.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1841 : Cover (Rectangle src1841 7207) 2313 2308 ends1841 := rectangleCover (by decide +kernel)

def src1842 : Request := ⟨⟨⟨2600,3625,793,530820⟩,532875289296896,4780245027563⟩,85,3,1,385979,21⟩

theorem rank1842 : P3_7_1.BankOK src1842.bank := by
  simpa only [src1842, _root_.Research6969.TerminalAuxBanks.bank46] using _root_.Research6969.PackedRanks.TerminalRanks44To47.rank46 530820

theorem width1842 : Lower6960.HelperSource.WidthGuard src1842.bank 179730 2308 src1842.reserve := requestWidth (by decide)

def ends1842 : List ℕ := [2313]

theorem inside1842 : Research6966.TerminalBanks.inside src1842.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1842 : Cover (Rectangle src1842 7207) 2313 2308 ends1842 := rectangleCover (by decide +kernel)

def src1843 : Request := ⟨⟨⟨2308,3207,724,530820⟩,380856854118400,3001726552718⟩,85,3,1,385979,22⟩

theorem rank1843 : P3_7_1.BankOK src1843.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2308_3207_724 530820

theorem width1843 : Lower6960.HelperSource.WidthGuard src1843.bank 179730 2308 src1843.reserve := requestWidth (by decide)

def ends1843 : List ℕ := [2308, 2309, 2313]

theorem inside1843 : Research6966.TerminalBanks.inside src1843.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1843 : Cover (Rectangle src1843 7207) 2313 2308 ends1843 := rectangleCover (by decide +kernel)

def src1844 : Request := ⟨⟨⟨2305,3207,702,530820⟩,370969276579840,2930605494152⟩,85,3,1,385979,23⟩

theorem rank1844 : P3_7_1.BankOK src1844.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2305_3207_702 530820

theorem width1844 : Lower6960.HelperSource.WidthGuard src1844.bank 179730 2308 src1844.reserve := requestWidth (by decide)

def ends1844 : List ℕ := [2308, 2309, 2313]

theorem inside1844 : Research6966.TerminalBanks.inside src1844.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1844 : Cover (Rectangle src1844 6653) 2313 2308 ends1844 := rectangleCover (by decide +kernel)

def src1845 : Request := ⟨⟨⟨2805,3903,882,530820⟩,684666334740480,6587245977411⟩,115,3,1,385979,24⟩

theorem rank1845 : P3_7_1.BankOK src1845.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3903_882 530820

theorem width1845 : Lower6960.HelperSource.WidthGuard src1845.bank 179730 2308 src1845.reserve := requestWidth (by decide)

def ends1845 : List ℕ := [2308, 2309, 2313]

theorem inside1845 : Research6966.TerminalBanks.inside src1845.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1845 : Cover (Rectangle src1845 9161) 2313 2308 ends1845 := rectangleCover (by decide +kernel)

def src1846 : Request := ⟨⟨⟨2803,3903,854,530820⟩,667058865438720,6424126719762⟩,115,3,1,385979,25⟩

theorem rank1846 : P3_7_1.BankOK src1846.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2803_3903_854 530820

theorem width1846 : Lower6960.HelperSource.WidthGuard src1846.bank 179730 2308 src1846.reserve := requestWidth (by decide)

def ends1846 : List ℕ := [2308, 2309, 2313]

theorem inside1846 : Research6966.TerminalBanks.inside src1846.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1846 : Cover (Rectangle src1846 8457) 2313 2308 ends1846 := rectangleCover (by decide +kernel)

def src1847 : Request := ⟨⟨⟨2613,3624,819,530820⟩,552203877089280,4897259437389⟩,115,3,1,385979,26⟩

theorem rank1847 : P3_7_1.BankOK src1847.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2613_3624_819 530820

theorem width1847 : Lower6960.HelperSource.WidthGuard src1847.bank 179730 2308 src1847.reserve := requestWidth (by decide)

def ends1847 : List ℕ := [2308, 2309, 2313]

theorem inside1847 : Research6966.TerminalBanks.inside src1847.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1847 : Cover (Rectangle src1847 8457) 2313 2308 ends1847 := rectangleCover (by decide +kernel)

def src1848 : Request := ⟨⟨⟨2603,3624,793,530820⟩,534252463063040,4776001446129⟩,115,3,1,385979,27⟩

theorem rank1848 : P3_7_1.BankOK src1848.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3624_793 530820

theorem width1848 : Lower6960.HelperSource.WidthGuard src1848.bank 179730 2308 src1848.reserve := requestWidth (by decide)

def ends1848 : List ℕ := [2308, 2309, 2313]

theorem inside1848 : Research6966.TerminalBanks.inside src1848.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1848 : Cover (Rectangle src1848 8457) 2313 2308 ends1848 := rectangleCover (by decide +kernel)

def src1849 : Request := ⟨⟨⟨2593,3600,793,530820⟩,529669168824320,4674922694213⟩,115,3,1,386273,28⟩

theorem rank1849 : P3_7_1.BankOK src1849.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2593_3600_793 530820

theorem width1849 : Lower6960.HelperSource.WidthGuard src1849.bank 179730 2308 src1849.reserve := requestWidth (by decide)

def ends1849 : List ℕ := [2309, 2313]

theorem inside1849 : Research6966.TerminalBanks.inside src1849.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1849 : Cover (Rectangle src1849 7207) 2313 2308 ends1849 := rectangleCover (by decide +kernel)

def src185 : Request := ⟨⟨⟨4820,6695,1512,50764⟩,3465298803425280,56953438854149⟩,110,2,1,303684,40⟩

theorem rank185 : P3_7_1.BankOK src185.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4820_6695_1512 50764

theorem width185 : Lower6960.HelperSource.WidthGuard src185.bank 179730 2308 src185.reserve := requestWidth (by decide)

def ends185 : List ℕ := [2308, 2313]



theorem cover185 : Cover (Triangular src185) 2313 2308 ends185 := triangleCover (by decide +kernel)

def src1850 : Request := ⟨⟨⟨2600,3624,793,530820⟩,532875289296896,4776001446129⟩,115,3,1,385979,29⟩

theorem rank1850 : P3_7_1.BankOK src1850.bank := by
  simpa only [src1850, _root_.Research6969.TerminalAuxBanks.bank43] using _root_.Research6969.PackedRanks.TerminalRanks40To43.rank43 530820

theorem width1850 : Lower6960.HelperSource.WidthGuard src1850.bank 179730 2308 src1850.reserve := requestWidth (by decide)

def ends1850 : List ℕ := [2313]

theorem inside1850 : Research6966.TerminalBanks.inside src1850.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover1850 : Cover (Rectangle src1850 7207) 2313 2308 ends1850 := rectangleCover (by decide +kernel)

def src1851 : Request := ⟨⟨⟨2600,3616,775,530820⟩,523640687820800,4658023494993⟩,115,3,1,386273,30⟩

theorem rank1851 : P3_7_1.BankOK src1851.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3616_775 530820

theorem width1851 : Lower6960.HelperSource.WidthGuard src1851.bank 179730 2308 src1851.reserve := requestWidth (by decide)

def ends1851 : List ℕ := [2308, 2309, 2313]

theorem inside1851 : Research6966.TerminalBanks.inside src1851.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1851 : Cover (Rectangle src1851 7207) 2313 2308 ends1851 := rectangleCover (by decide +kernel)

def src1852 : Request := ⟨⟨⟨2301,3206,724,530820⟩,378271924224000,2998712046218⟩,115,3,1,385979,31⟩

theorem rank1852 : P3_7_1.BankOK src1852.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3206_724 530820

theorem width1852 : Lower6960.HelperSource.WidthGuard src1852.bank 179730 2308 src1852.reserve := requestWidth (by decide)

def ends1852 : List ℕ := [2309, 2313]

theorem inside1852 : Research6966.TerminalBanks.inside src1852.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1852 : Cover (Rectangle src1852 7807) 2313 2308 ends1852 := rectangleCover (by decide +kernel)

def src1853 : Request := ⟨⟨⟨2308,3206,710,504934⟩,375265883848704,2953586856669⟩,116,3,1,385979,32⟩

theorem rank1853 : P3_7_1.BankOK src1853.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2308_3206_710 504934

theorem width1853 : Lower6960.HelperSource.WidthGuard src1853.bank 179730 2308 src1853.reserve := requestWidth (by decide)

def ends1853 : List ℕ := [2308, 2309, 2313]

theorem inside1853 : Research6966.TerminalBanks.inside src1853.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1853 : Cover (Rectangle src1853 7207) 2313 2308 ends1853 := rectangleCover (by decide +kernel)

def src1854 : Request := ⟨⟨⟨2809,3902,882,530820⟩,686857459597312,6581809445307⟩,150,3,1,385979,33⟩

theorem rank1854 : P3_7_1.BankOK src1854.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3902_882 530820

theorem width1854 : Lower6960.HelperSource.WidthGuard src1854.bank 179730 2308 src1854.reserve := requestWidth (by decide)

def ends1854 : List ℕ := [2308, 2309, 2313]

theorem inside1854 : Research6966.TerminalBanks.inside src1854.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1854 : Cover (Rectangle src1854 9924) 2313 2308 ends1854 := rectangleCover (by decide +kernel)

def src1855 : Request := ⟨⟨⟨2809,3902,857,530820⟩,672047850586112,6436378078562⟩,150,3,1,386273,34⟩

theorem rank1855 : P3_7_1.BankOK src1855.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2809_3902_857 530820

theorem width1855 : Lower6960.HelperSource.WidthGuard src1855.bank 179730 2308 src1855.reserve := requestWidth (by decide)

def ends1855 : List ℕ := [2308, 2309, 2313]

theorem inside1855 : Research6966.TerminalBanks.inside src1855.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1855 : Cover (Rectangle src1855 9924) 2313 2308 ends1855 := rectangleCover (by decide +kernel)

def src1856 : Request := ⟨⟨⟨2801,3902,854,530820⟩,665994008985600,6418829718882⟩,150,3,1,385979,35⟩

theorem rank1856 : P3_7_1.BankOK src1856.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3902_854 530820

theorem width1856 : Lower6960.HelperSource.WidthGuard src1856.bank 179730 2308 src1856.reserve := requestWidth (by decide)

def ends1856 : List ℕ := [2308, 2309, 2313]

theorem inside1856 : Research6966.TerminalBanks.inside src1856.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1856 : Cover (Rectangle src1856 9161) 2313 2308 ends1856 := rectangleCover (by decide +kernel)

def src1857 : Request := ⟨⟨⟨2804,3902,854,530820⟩,667591629864960,6418829718882⟩,150,3,1,385979,36⟩

theorem rank1857 : P3_7_1.BankOK src1857.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2804_3902_854 530820

theorem width1857 : Lower6960.HelperSource.WidthGuard src1857.bank 179730 2308 src1857.reserve := requestWidth (by decide)

def ends1857 : List ℕ := [2308, 2309, 2313]

theorem inside1857 : Research6966.TerminalBanks.inside src1857.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1857 : Cover (Rectangle src1857 8457) 2313 2308 ends1857 := rectangleCover (by decide +kernel)

def src1858 : Request := ⟨⟨⟨2790,3878,834,530820⟩,648354204221440,6177455542647⟩,150,3,1,386273,37⟩

theorem rank1858 : P3_7_1.BankOK src1858.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2790_3878_834 530820

theorem width1858 : Lower6960.HelperSource.WidthGuard src1858.bank 179730 2308 src1858.reserve := requestWidth (by decide)

def ends1858 : List ℕ := [2309, 2313]

theorem inside1858 : Research6966.TerminalBanks.inside src1858.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover1858 : Cover (Rectangle src1858 9161) 2313 2308 ends1858 := rectangleCover (by decide +kernel)

def src1859 : Request := ⟨⟨⟨2601,3623,819,530820⟩,546534142771200,4892906717079⟩,150,3,1,385979,38⟩

theorem rank1859 : P3_7_1.BankOK src1859.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3623_819 530820

theorem width1859 : Lower6960.HelperSource.WidthGuard src1859.bank 179730 2308 src1859.reserve := requestWidth (by decide)

def ends1859 : List ℕ := [2308, 2309, 2313]

theorem inside1859 : Research6966.TerminalBanks.inside src1859.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1859 : Cover (Rectangle src1859 9161) 2313 2308 ends1859 := rectangleCover (by decide +kernel)

def src186 : Request := ⟨⟨⟨10045,13948,3086,117355⟩,30857543399768064,1055246105378606⟩,245,2,1,303684,40⟩

theorem rank186 : P3_7_1.BankOK src186.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10045_13948_3086 117355

theorem width186 : Lower6960.HelperSource.WidthGuard src186.bank 179730 2308 src186.reserve := requestWidth (by decide)

def ends186 : List ℕ := [2308, 2309, 2313]




theorem cover186 : Cover (Triangular src186) 2313 2308 ends186 := triangleCover (by decide +kernel)

def src1860 : Request := ⟨⟨⟨2603,3615,793,530820⟩,534252463063040,4737924472248⟩,150,3,1,386273,39⟩

theorem rank1860 : P3_7_1.BankOK src1860.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3615_793 530820

theorem width1860 : Lower6960.HelperSource.WidthGuard src1860.bank 179730 2308 src1860.reserve := requestWidth (by decide)

def ends1860 : List ℕ := [2308, 2309, 2313]

theorem inside1860 : Research6966.TerminalBanks.inside src1860.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1860 : Cover (Rectangle src1860 9161) 2313 2308 ends1860 := rectangleCover (by decide +kernel)

def src1861 : Request := ⟨⟨⟨2736,3800,830,530327⟩,618353947049984,5764795702526⟩,337,5,1,643299,2048⟩

theorem rank1861 : P3_7_1.BankOK src1861.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2736_3800_830 530327

theorem width1861 : Lower6960.HelperSource.WidthGuard src1861.bank 179730 2308 src1861.reserve := requestWidth (by decide)

def ends1861 : List ℕ := [2308, 2309, 2313]

theorem inside1861 : Research6966.TerminalBanks.inside src1861.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover1861 : Cover (Rectangle src1861 63481) 2313 2308 ends1861 := rectangleCover (by decide +kernel)

def src187 : Request := ⟨⟨⟨2600,3622,775,31595⟩,523640687820800,4682933013901⟩,63,2,1,303874,45⟩

theorem rank187 : P3_7_1.BankOK src187.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3622_775 31595

theorem width187 : Lower6960.HelperSource.WidthGuard src187.bank 179730 2308 src187.reserve := requestWidth (by decide)

def ends187 : List ℕ := [2308, 2309, 2313]

theorem inside187 : Research6966.TerminalBanks.inside src187.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover187 : Cover (Triangular src187) 2313 2308 ends187 := triangleCover (by decide +kernel)

def src188 : Request := ⟨⟨⟨2614,3626,815,24190⟩,550633901916160,4887369630386⟩,63,2,1,303874,45⟩

theorem rank188 : P3_7_1.BankOK src188.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3626_815 24190

theorem width188 : Lower6960.HelperSource.WidthGuard src188.bank 179730 2308 src188.reserve := requestWidth (by decide)

def ends188 : List ℕ := [2308, 2309, 2313]

theorem inside188 : Research6966.TerminalBanks.inside src188.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover188 : Cover (Triangular src188) 2313 2308 ends188 := triangleCover (by decide +kernel)

def src189 : Request := ⟨⟨⟨2303,3207,702,28173⟩,370249266364416,2930605494152⟩,63,2,1,303874,47⟩

theorem rank189 : P3_7_1.BankOK src189.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2303_3207_702 28173

theorem width189 : Lower6960.HelperSource.WidthGuard src189.bank 179730 2308 src189.reserve := requestWidth (by decide)

def ends189 : List ℕ := [2308, 2309, 2313]

theorem inside189 : Research6966.TerminalBanks.inside src189.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover189 : Cover (Triangular src189) 2313 2308 ends189 := triangleCover (by decide +kernel)

def src19 : Request := ⟨⟨⟨2808,3900,854,114389⟩,669724928901120,6408244632207⟩,325,1,1,128659,2049⟩

theorem rank19 : P3_7_1.BankOK src19.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2808_3900_854 114389

theorem width19 : Lower6960.HelperSource.WidthGuard src19.bank 179730 2308 src19.reserve := requestWidth (by decide)

def ends19 : List ℕ := [2308, 2309, 2313]

theorem inside19 : Research6966.TerminalBanks.inside src19.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover19 : Cover (Triangular src19) 2313 2308 ends19 := triangleCover (by decide +kernel)

def src190 : Request := ⟨⟨⟨2311,3207,722,24246⟩,381169062379520,2995291656973⟩,63,2,1,303874,47⟩

theorem rank190 : P3_7_1.BankOK src190.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2311_3207_722 24246

theorem width190 : Lower6960.HelperSource.WidthGuard src190.bank 179730 2308 src190.reserve := requestWidth (by decide)

def ends190 : List ℕ := [2308, 2309, 2313]

theorem inside190 : Research6966.TerminalBanks.inside src190.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover190 : Cover (Triangular src190) 2313 2308 ends190 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources32

section Pack_R6970Height2313CommonSources33

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src191 : Request := ⟨⟨⟨2265,3143,702,23659⟩,356709130567680,2746433306696⟩,63,2,1,303874,48⟩

theorem rank191 : P3_7_1.BankOK src191.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2265_3143_702 23659

theorem width191 : Lower6960.HelperSource.WidthGuard src191.bank 179730 2308 src191.reserve := requestWidth (by decide)

def ends191 : List ℕ := [2308, 2309, 2313]

theorem inside191 : Research6966.TerminalBanks.inside src191.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover191 : Cover (Triangular src191) 2313 2308 ends191 := triangleCover (by decide +kernel)

def src192 : Request := ⟨⟨⟨2301,3207,702,25043⟩,369529993297920,2930605494152⟩,63,2,1,303874,48⟩

theorem rank192 : P3_7_1.BankOK src192.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3207_702 25043

theorem width192 : Lower6960.HelperSource.WidthGuard src192.bank 179730 2308 src192.reserve := requestWidth (by decide)

def ends192 : List ℕ := [2308, 2309, 2313]

theorem inside192 : Research6966.TerminalBanks.inside src192.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover192 : Cover (Triangular src192) 2313 2308 ends192 := triangleCover (by decide +kernel)

def src193 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,2,1,303918,39⟩

theorem rank193 : P3_7_1.BankOK src193.bank := by
  simpa only [src193, _root_.Research6969.TransitionBanks.bank142] using _root_.Research6969.TransitionBanks.rank142 4817

theorem width193 : Lower6960.HelperSource.WidthGuard src193.bank 179730 2308 src193.reserve := requestWidth (by decide)

def ends193 : List ℕ := [2313]

theorem inside193 : Research6966.TerminalBanks.inside src193.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover193 : Cover (Triangular src193) 2313 2308 ends193 := triangleCover (by decide +kernel)

def src194 : Request := ⟨⟨⟨561,781,176,4817⟩,5504262995968,10627925923⟩,1,2,1,303918,39⟩

theorem rank194 : P3_7_1.BankOK src194.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_176 4817

theorem width194 : Lower6960.HelperSource.WidthGuard src194.bank 179730 2308 src194.reserve := requestWidth (by decide)

def ends194 : List ℕ := [2308, 2313]

theorem inside194 : Research6966.TerminalBanks.inside src194.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover194 : Cover (Triangular src194) 2313 2308 ends194 := triangleCover (by decide +kernel)

def src195 : Request := ⟨⟨⟨561,781,172,5419⟩,5409683537920,10440670587⟩,2,2,1,303918,39⟩

theorem rank195 : P3_7_1.BankOK src195.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_561_781_172 5419

theorem width195 : Lower6960.HelperSource.WidthGuard src195.bank 179730 2308 src195.reserve := requestWidth (by decide)

def ends195 : List ℕ := [2308, 2313]

theorem inside195 : Research6966.TerminalBanks.inside src195.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover195 : Cover (Triangular src195) 2313 2308 ends195 := triangleCover (by decide +kernel)

def src196 : Request := ⟨⟨⟨557,773,172,6084⟩,5323788910592,10100663999⟩,3,2,1,303918,39⟩

theorem rank196 : P3_7_1.BankOK src196.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_557_773_172 6084

theorem width196 : Lower6960.HelperSource.WidthGuard src196.bank 179730 2308 src196.reserve := requestWidth (by decide)

def ends196 : List ℕ := [2308, 2309, 2313]

theorem inside196 : Research6966.TerminalBanks.inside src196.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover196 : Cover (Triangular src196) 2313 2308 ends196 := triangleCover (by decide +kernel)

def src197 : Request := ⟨⟨⟨690,958,212,6086⟩,10065769922560,23678394421⟩,4,2,1,303918,39⟩

theorem rank197 : P3_7_1.BankOK src197.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_958_212 6086

theorem width197 : Lower6960.HelperSource.WidthGuard src197.bank 179730 2308 src197.reserve := requestWidth (by decide)

def ends197 : List ℕ := [2308, 2309, 2313]

theorem inside197 : Research6966.TerminalBanks.inside src197.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover197 : Cover (Triangular src197) 2313 2308 ends197 := triangleCover (by decide +kernel)

def src198 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,6,2,1,303918,39⟩

theorem rank198 : P3_7_1.BankOK src198.bank := by
  simpa only [src198, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 7715

theorem width198 : Lower6960.HelperSource.WidthGuard src198.bank 179730 2308 src198.reserve := requestWidth (by decide)

def ends198 : List ℕ := [2309, 2313]

theorem inside198 : Research6966.TerminalBanks.inside src198.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover198 : Cover (Triangular src198) 2313 2308 ends198 := triangleCover (by decide +kernel)

def src199 : Request := ⟨⟨⟨828,1151,260,9763⟩,17662013865984,50057971890⟩,10,2,1,303918,39⟩

theorem rank199 : P3_7_1.BankOK src199.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1151_260 9763

theorem width199 : Lower6960.HelperSource.WidthGuard src199.bank 179730 2308 src199.reserve := requestWidth (by decide)

def ends199 : List ℕ := [2308, 2309, 2313]

theorem inside199 : Research6966.TerminalBanks.inside src199.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover199 : Cover (Triangular src199) 2313 2308 ends199 := triangleCover (by decide +kernel)

def src2 : Request := ⟨⟨⟨2314,3209,724,22209⟩,383079920435200,3007761756493⟩,15,1,1,128659,33⟩

theorem rank2 : P3_7_1.BankOK src2.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2314_3209_724 22209

theorem width2 : Lower6960.HelperSource.WidthGuard src2.bank 179730 2308 src2.reserve := requestWidth (by decide)

def ends2 : List ℕ := [2308, 2313]

theorem inside2 : Research6966.TerminalBanks.inside src2.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover2 : Cover (Triangular src2) 2313 2308 ends2 := triangleCover (by decide +kernel)

def src20 : Request := ⟨⟨⟨2805,3896,852,118148⟩,666934584279040,6375459527244⟩,325,1,1,128659,2049⟩

theorem rank20 : P3_7_1.BankOK src20.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2805_3896_852 118148

theorem width20 : Lower6960.HelperSource.WidthGuard src20.bank 179730 2308 src20.reserve := requestWidth (by decide)

def ends20 : List ℕ := [2308, 2309, 2313]

theorem inside20 : Research6966.TerminalBanks.inside src20.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover20 : Cover (Triangular src20) 2313 2308 ends20 := triangleCover (by decide +kernel)

def src200 : Request := ⟨⟨⟨1454,2022,445,17590⟩,93574192168960,465769321795⟩,25,2,1,303918,39⟩

theorem rank200 : P3_7_1.BankOK src200.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1454_2022_445 17590

theorem width200 : Lower6960.HelperSource.WidthGuard src200.bank 179730 2308 src200.reserve := requestWidth (by decide)

def ends200 : List ℕ := [2308, 2309, 2313]

theorem inside200 : Research6966.TerminalBanks.inside src200.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover200 : Cover (Triangular src200) 2313 2308 ends200 := triangleCover (by decide +kernel)

def src201 : Request := ⟨⟨⟨2105,2929,662,22261⟩,289553542021120,2090961110089⟩,40,2,1,303918,39⟩

theorem rank201 : P3_7_1.BankOK src201.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2929_662 22261

theorem width201 : Lower6960.HelperSource.WidthGuard src201.bank 179730 2308 src201.reserve := requestWidth (by decide)

def ends201 : List ℕ := [2308, 2309, 2313]

theorem inside201 : Research6966.TerminalBanks.inside src201.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover201 : Cover (Triangular src201) 2313 2308 ends201 := triangleCover (by decide +kernel)

def src202 : Request := ⟨⟨⟨3950,5494,1213,44645⟩,1877062482395136,25383464767379⟩,85,2,1,303918,39⟩

theorem rank202 : P3_7_1.BankOK src202.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3950_5494_1213 44645

theorem width202 : Lower6960.HelperSource.WidthGuard src202.bank 179730 2308 src202.reserve := requestWidth (by decide)

def ends202 : List ℕ := [2308, 2309, 2313]




theorem cover202 : Cover (Triangular src202) 2313 2308 ends202 := triangleCover (by decide +kernel)

def src203 : Request := ⟨⟨⟨8338,11577,2564,91769⟩,17662430167695360,501284470461675⟩,190,2,1,303918,39⟩

theorem rank203 : P3_7_1.BankOK src203.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8338_11577_2564 91769

theorem width203 : Lower6960.HelperSource.WidthGuard src203.bank 179730 2308 src203.reserve := requestWidth (by decide)

def ends203 : List ℕ := [2308, 2309, 2313]




theorem cover203 : Cover (Triangular src203) 2313 2308 ends203 := triangleCover (by decide +kernel)

def src204 : Request := ⟨⟨⟨469,651,144,4798⟩,3169461207040,5068091922⟩,0,2,1,304146,38⟩

theorem rank204 : P3_7_1.BankOK src204.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_469_651_144 4798

theorem width204 : Lower6960.HelperSource.WidthGuard src204.bank 179730 2308 src204.reserve := requestWidth (by decide)

def ends204 : List ℕ := [2308, 2309, 2313]

theorem inside204 : Research6966.TerminalBanks.inside src204.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover204 : Cover (Triangular src204) 2313 2308 ends204 := triangleCover (by decide +kernel)

def src205 : Request := ⟨⟨⟨560,779,169,5407⟩,5316921262080,10214741280⟩,1,2,1,304146,38⟩

theorem rank205 : P3_7_1.BankOK src205.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_560_779_169 5407

theorem width205 : Lower6960.HelperSource.WidthGuard src205.bank 179730 2308 src205.reserve := requestWidth (by decide)

def ends205 : List ℕ := [2308, 2309, 2313]

theorem inside205 : Research6966.TerminalBanks.inside src205.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover205 : Cover (Triangular src205) 2313 2308 ends205 := triangleCover (by decide +kernel)

def src206 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,2,2,1,304146,38⟩

theorem rank206 : P3_7_1.BankOK src206.bank := by
  simpa only [src206, _root_.Research6969.TransitionBanks.bank156] using _root_.Research6969.TransitionBanks.rank156 6096

theorem width206 : Lower6960.HelperSource.WidthGuard src206.bank 179730 2308 src206.reserve := requestWidth (by decide)

def ends206 : List ℕ := [2313]

theorem inside206 : Research6966.TerminalBanks.inside src206.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)


theorem cover206 : Cover (Triangular src206) 2313 2308 ends206 := triangleCover (by decide +kernel)

def src207 : Request := ⟨⟨⟨690,962,212,6096⟩,10065769922560,23997864317⟩,3,2,1,304146,38⟩

theorem rank207 : P3_7_1.BankOK src207.bank := by
  simpa only [src207, _root_.Research6969.TransitionBanks.bank193] using _root_.Research6969.TransitionBanks.rank193 6096

theorem width207 : Lower6960.HelperSource.WidthGuard src207.bank 179730 2308 src207.reserve := requestWidth (by decide)

def ends207 : List ℕ := [2308, 2309, 2313]

theorem inside207 : Research6966.TerminalBanks.inside src207.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover207 : Cover (Triangular src207) 2313 2308 ends207 := triangleCover (by decide +kernel)

def src208 : Request := ⟨⟨⟨684,954,208,6845⟩,9729817968640,23019418180⟩,4,2,1,304146,38⟩

theorem rank208 : P3_7_1.BankOK src208.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_684_954_208 6845

theorem width208 : Lower6960.HelperSource.WidthGuard src208.bank 179730 2308 src208.reserve := requestWidth (by decide)

def ends208 : List ℕ := [2308, 2309, 2313]

theorem inside208 : Research6966.TerminalBanks.inside src208.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover208 : Cover (Triangular src208) 2313 2308 ends208 := triangleCover (by decide +kernel)

def src209 : Request := ⟨⟨⟨692,962,214,8755⟩,10203306393600,24173060093⟩,6,2,1,304146,38⟩

theorem rank209 : P3_7_1.BankOK src209.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_692_962_214 8755

theorem width209 : Lower6960.HelperSource.WidthGuard src209.bank 179730 2308 src209.reserve := requestWidth (by decide)

def ends209 : List ℕ := [2308, 2309, 2313]

theorem inside209 : Research6966.TerminalBanks.inside src209.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover209 : Cover (Triangular src209) 2313 2308 ends209 := triangleCover (by decide +kernel)

def src21 : Request := ⟨⟨⟨1000,1391,304,58418⟩,30330999275520,103947228761⟩,115,1,1,128659,4097⟩

theorem rank21 : P3_7_1.BankOK src21.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1000_1391_304 58418

theorem width21 : Lower6960.HelperSource.WidthGuard src21.bank 179730 2308 src21.reserve := requestWidth (by decide)

def ends21 : List ℕ := [2308, 2309, 2313]

theorem inside21 : Research6966.TerminalBanks.inside src21.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover21 : Cover (Triangular src21) 2313 2308 ends21 := triangleCover (by decide +kernel)

def src210 : Request := ⟨⟨⟨828,1150,253,8676⟩,17301502689280,48873782027⟩,8,2,1,304146,38⟩

theorem rank210 : P3_7_1.BankOK src210.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_828_1150_253 8676

theorem width210 : Lower6960.HelperSource.WidthGuard src210.bank 179730 2308 src210.reserve := requestWidth (by decide)

def ends210 : List ℕ := [2308, 2309, 2313]

theorem inside210 : Research6966.TerminalBanks.inside src210.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover210 : Cover (Triangular src210) 2313 2308 ends210 := triangleCover (by decide +kernel)

def src211 : Request := ⟨⟨⟨1203,1674,368,12355⟩,53014143959040,218807905514⟩,16,2,1,304146,38⟩

theorem rank211 : P3_7_1.BankOK src211.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_368 12355

theorem width211 : Lower6960.HelperSource.WidthGuard src211.bank 179730 2308 src211.reserve := requestWidth (by decide)

def ends211 : List ℕ := [2308, 2309, 2313]

theorem inside211 : Research6966.TerminalBanks.inside src211.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover211 : Cover (Triangular src211) 2313 2308 ends211 := triangleCover (by decide +kernel)

def src212 : Request := ⟨⟨⟨1752,2441,551,15636⟩,167023156920320,1008217465165⟩,25,2,1,304146,38⟩

theorem rank212 : P3_7_1.BankOK src212.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2441_551 15636

theorem width212 : Lower6960.HelperSource.WidthGuard src212.bank 179730 2308 src212.reserve := requestWidth (by decide)

def ends212 : List ℕ := [2309, 2313]

theorem inside212 : Research6966.TerminalBanks.inside src212.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover212 : Cover (Triangular src212) 2313 2308 ends212 := triangleCover (by decide +kernel)

def src213 : Request := ⟨⟨⟨2611,3627,819,28173⟩,551256771788800,4910333421859⟩,50,2,1,304146,38⟩

theorem rank213 : P3_7_1.BankOK src213.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2611_3627_819 28173

theorem width213 : Lower6960.HelperSource.WidthGuard src213.bank 179730 2308 src213.reserve := requestWidth (by decide)

def ends213 : List ℕ := [2308, 2309, 2313]

theorem inside213 : Research6966.TerminalBanks.inside src213.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover213 : Cover (Triangular src213) 2313 2308 ends213 := triangleCover (by decide +kernel)

def src214 : Request := ⟨⟨⟨6887,9561,2118,72545⟩,9954899935625216,233269354849936⟩,145,2,1,304146,38⟩

theorem rank214 : P3_7_1.BankOK src214.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6887_9561_2118 72545

theorem width214 : Lower6960.HelperSource.WidthGuard src214.bank 179730 2308 src214.reserve := requestWidth (by decide)

def ends214 : List ℕ := [2308, 2309, 2313]




theorem cover214 : Cover (Triangular src214) 2313 2308 ends214 := triangleCover (by decide +kernel)

def src215 : Request := ⟨⟨⟨2803,3904,854,75039⟩,667058865438720,6429426693477⟩,15,2,1,304158,23⟩

theorem rank215 : P3_7_1.BankOK src215.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2803_3904_854 75039

theorem width215 : Lower6960.HelperSource.WidthGuard src215.bank 179730 2308 src215.reserve := requestWidth (by decide)

def ends215 : List ℕ := [2308, 2309, 2313]

theorem inside215 : Research6966.TerminalBanks.inside src215.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover215 : Cover (Triangular src215) 2313 2308 ends215 := triangleCover (by decide +kernel)

def src216 : Request := ⟨⟨⟨3000,4184,900,176076⟩,808165480857600,8370437628682⟩,20,2,1,304158,23⟩

theorem rank216 : P3_7_1.BankOK src216.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4184_900 176076

theorem width216 : Lower6960.HelperSource.WidthGuard src216.bank 179730 2308 src216.reserve := requestWidth (by decide)

def ends216 : List ℕ := [2308, 2309, 2313]

theorem inside216 : Research6966.TerminalBanks.inside src216.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover216 : Cover (Triangular src216) 2313 2308 ends216 := triangleCover (by decide +kernel)

def src217 : Request := ⟨⟨⟨2685,3739,821,60860⟩,587960807849984,5425909527495⟩,15,2,1,304158,24⟩

theorem rank217 : P3_7_1.BankOK src217.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2685_3739_821 60860

theorem width217 : Lower6960.HelperSource.WidthGuard src217.bank 179730 2308 src217.reserve := requestWidth (by decide)

def ends217 : List ℕ := [2308, 2309, 2313]

theorem inside217 : Research6966.TerminalBanks.inside src217.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover217 : Cover (Triangular src217) 2313 2308 ends217 := triangleCover (by decide +kernel)

def src218 : Request := ⟨⟨⟨2989,4168,900,158252⟩,801553292984320,8267876438282⟩,21,2,1,304158,24⟩

theorem rank218 : P3_7_1.BankOK src218.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2989_4168_900 158252

theorem width218 : Lower6960.HelperSource.WidthGuard src218.bank 179730 2308 src218.reserve := requestWidth (by decide)

def ends218 : List ℕ := [2308, 2309, 2313]

theorem inside218 : Research6966.TerminalBanks.inside src218.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover218 : Cover (Triangular src218) 2313 2308 ends218 := triangleCover (by decide +kernel)

def src219 : Request := ⟨⟨⟨472,655,145,5426⟩,3231793283072,5196592961⟩,0,2,1,304368,37⟩

theorem rank219 : P3_7_1.BankOK src219.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_472_655_145 5426

theorem width219 : Lower6960.HelperSource.WidthGuard src219.bank 179730 2308 src219.reserve := requestWidth (by decide)

def ends219 : List ℕ := [2308, 2309, 2313]

theorem inside219 : Research6966.TerminalBanks.inside src219.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover219 : Cover (Triangular src219) 2313 2308 ends219 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources33

section Pack_R6970Height2313CommonSources41

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src421 : Request := ⟨⟨⟨4811,6710,1445,832876⟩,3334049849933824,55376741286063⟩,40,2,1,307237,20⟩

theorem rank421 : P3_7_1.BankOK src421.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4811_6710_1445 832876

theorem width421 : Lower6960.HelperSource.WidthGuard src421.bank 179730 2308 src421.reserve := requestWidth (by decide)

def ends421 : List ℕ := [2308, 2309, 2313]




theorem cover421 : Cover (Triangular src421) 2313 2308 ends421 := triangleCover (by decide +kernel)

def src422 : Request := ⟨⟨⟨6874,9581,2077,202138⟩,9766584394186752,231294349662262⟩,40,2,1,307237,20⟩

theorem rank422 : P3_7_1.BankOK src422.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6874_9581_2077 202138

theorem width422 : Lower6960.HelperSource.WidthGuard src422.bank 179730 2308 src422.reserve := requestWidth (by decide)

def ends422 : List ℕ := [2308, 2309, 2313]




theorem cover422 : Cover (Triangular src422) 2313 2308 ends422 := triangleCover (by decide +kernel)

def src423 : Request := ⟨⟨⟨7040,9820,2118,2045341⟩,10456759507091456,254233369236069⟩,65,2,1,307237,20⟩

theorem rank423 : P3_7_1.BankOK src423.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7040_9820_2118 2045341

theorem width423 : Lower6960.HelperSource.WidthGuard src423.bank 179730 2308 src423.reserve := requestWidth (by decide)

def ends423 : List ℕ := [2308, 2309, 2313]




theorem cover423 : Cover (Triangular src423) 2313 2308 ends423 := triangleCover (by decide +kernel)

def src424 : Request := ⟨⟨⟨10008,13955,3010,314542⟩,30028351888687104,1036603432174989⟩,65,2,1,307237,20⟩

theorem rank424 : P3_7_1.BankOK src424.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10008_13955_3010 314542

theorem width424 : Lower6960.HelperSource.WidthGuard src424.bank 179730 2308 src424.reserve := requestWidth (by decide)

def ends424 : List ℕ := [2308, 2309, 2313]




theorem cover424 : Cover (Triangular src424) 2313 2308 ends424 := triangleCover (by decide +kernel)

def src425 : Request := ⟨⟨⟨2950,4109,900,70269⟩,778340368384000,7897067162757⟩,16,2,1,307280,23⟩

theorem rank425 : P3_7_1.BankOK src425.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2950_4109_900 70269

theorem width425 : Lower6960.HelperSource.WidthGuard src425.bank 179730 2308 src425.reserve := requestWidth (by decide)

def ends425 : List ℕ := [2308, 2309, 2313]

theorem inside425 : Research6966.TerminalBanks.inside src425.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover425 : Cover (Triangular src425) 2313 2308 ends425 := triangleCover (by decide +kernel)

def src426 : Request := ⟨⟨⟨3000,4184,900,398428⟩,808165480857600,8370437628682⟩,22,2,1,307303,23⟩

theorem rank426 : P3_7_1.BankOK src426.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3000_4184_900 398428

theorem width426 : Lower6960.HelperSource.WidthGuard src426.bank 179730 2308 src426.reserve := requestWidth (by decide)

def ends426 : List ℕ := [2308, 2309, 2313]

theorem inside426 : Research6966.TerminalBanks.inside src426.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover426 : Cover (Triangular src426) 2313 2308 ends426 := triangleCover (by decide +kernel)

def src427 : Request := ⟨⟨⟨2801,3901,854,69273⟩,665994008985600,6413535689982⟩,15,2,1,307321,23⟩

theorem rank427 : P3_7_1.BankOK src427.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3901_854 69273

theorem width427 : Lower6960.HelperSource.WidthGuard src427.bank 179730 2308 src427.reserve := requestWidth (by decide)

def ends427 : List ℕ := [2308, 2309, 2313]

theorem inside427 : Research6966.TerminalBanks.inside src427.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover427 : Cover (Triangular src427) 2313 2308 ends427 := triangleCover (by decide +kernel)

def src428 : Request := ⟨⟨⟨2976,4152,894,143713⟩,789742400307200,8123677052458⟩,20,2,1,307321,23⟩

theorem rank428 : P3_7_1.BankOK src428.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2976_4152_894 143713

theorem width428 : Lower6960.HelperSource.WidthGuard src428.bank 179730 2308 src428.reserve := requestWidth (by decide)

def ends428 : List ℕ := [2308, 2309, 2313]

theorem inside428 : Research6966.TerminalBanks.inside src428.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover428 : Cover (Triangular src428) 2313 2308 ends428 := triangleCover (by decide +kernel)

def src429 : Request := ⟨⟨⟨2801,3901,854,69265⟩,665994008985600,6413535689982⟩,15,2,1,307326,23⟩

theorem rank429 : P3_7_1.BankOK src429.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3901_854 69265

theorem width429 : Lower6960.HelperSource.WidthGuard src429.bank 179730 2308 src429.reserve := requestWidth (by decide)

def ends429 : List ℕ := [2308, 2309, 2313]

theorem inside429 : Research6966.TerminalBanks.inside src429.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover429 : Cover (Triangular src429) 2313 2308 ends429 := triangleCover (by decide +kernel)

def src43 : Request := ⟨⟨⟨2615,3627,819,31694⟩,553151842222080,4910333421859⟩,32,2,1,257319,33⟩

theorem rank43 : P3_7_1.BankOK src43.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 31694

theorem width43 : Lower6960.HelperSource.WidthGuard src43.bank 179730 2308 src43.reserve := requestWidth (by decide)

def ends43 : List ℕ := [2309, 2313]

theorem inside43 : Research6966.TerminalBanks.inside src43.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover43 : Cover (Triangular src43) 2313 2308 ends43 := triangleCover (by decide +kernel)

def src430 : Request := ⟨⟨⟨2976,4152,894,143663⟩,789742400307200,8123677052458⟩,20,2,1,307326,23⟩

theorem rank430 : P3_7_1.BankOK src430.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2976_4152_894 143663

theorem width430 : Lower6960.HelperSource.WidthGuard src430.bank 179730 2308 src430.reserve := requestWidth (by decide)

def ends430 : List ℕ := [2308, 2309, 2313]

theorem inside430 : Research6966.TerminalBanks.inside src430.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover430 : Cover (Triangular src430) 2313 2308 ends430 := triangleCover (by decide +kernel)

def src431 : Request := ⟨⟨⟨2801,3901,854,69249⟩,665994008985600,6413535689982⟩,15,2,1,307336,23⟩

theorem rank431 : P3_7_1.BankOK src431.bank := 
  _root_.Research6970.Height2313.Physical.bank_2801_3901_854 69249

theorem width431 : Lower6960.HelperSource.WidthGuard src431.bank 179730 2308 src431.reserve := requestWidth (by decide)

def ends431 : List ℕ := [2308, 2309, 2313]

theorem inside431 : Research6966.TerminalBanks.inside src431.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover431 : Cover (Triangular src431) 2313 2308 ends431 := triangleCover (by decide +kernel)

def src432 : Request := ⟨⟨⟨2983,4160,894,145236⟩,793902427668480,8174147409158⟩,20,2,1,307336,23⟩

theorem rank432 : P3_7_1.BankOK src432.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2983_4160_894 145236

theorem width432 : Lower6960.HelperSource.WidthGuard src432.bank 179730 2308 src432.reserve := requestWidth (by decide)

def ends432 : List ℕ := [2308, 2309, 2313]

theorem inside432 : Research6966.TerminalBanks.inside src432.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover432 : Cover (Triangular src432) 2313 2308 ends432 := triangleCover (by decide +kernel)

def src433 : Request := ⟨⟨⟨1451,2023,436,49432⟩,91708090482688,459151377566⟩,0,2,1,307353,19⟩

theorem rank433 : P3_7_1.BankOK src433.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2023_436 49432

theorem width433 : Lower6960.HelperSource.WidthGuard src433.bank 179730 2308 src433.reserve := requestWidth (by decide)

def ends433 : List ℕ := [2308, 2309, 2313]

theorem inside433 : Research6966.TerminalBanks.inside src433.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover433 : Cover (Triangular src433) 2313 2308 ends433 := triangleCover (by decide +kernel)

def src434 : Request := ⟨⟨⟨1741,2426,527,50769⟩,159218359336960,954787561062⟩,1,2,1,307353,19⟩

theorem rank434 : P3_7_1.BankOK src434.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1741_2426_527 50769

theorem width434 : Lower6960.HelperSource.WidthGuard src434.bank 179730 2308 src434.reserve := requestWidth (by decide)

def ends434 : List ℕ := [2308, 2309, 2313]

theorem inside434 : Research6966.TerminalBanks.inside src434.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover434 : Cover (Triangular src434) 2313 2308 ends434 := triangleCover (by decide +kernel)

def src435 : Request := ⟨⟨⟨2102,2930,632,60291⟩,278652894052352,2019119590628⟩,3,2,1,307353,19⟩

theorem rank435 : P3_7_1.BankOK src435.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2102_2930_632 60291

theorem width435 : Lower6960.HelperSource.WidthGuard src435.bank 179730 2308 src435.reserve := requestWidth (by decide)

def ends435 : List ℕ := [2308, 2309, 2313]

theorem inside435 : Research6966.TerminalBanks.inside src435.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover435 : Cover (Triangular src435) 2313 2308 ends435 := triangleCover (by decide +kernel)

def src436 : Request := ⟨⟨⟨2101,2929,633,65843⟩,278691788095488,2019390978963⟩,4,2,1,307353,19⟩

theorem rank436 : P3_7_1.BankOK src436.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2101_2929_633 65843

theorem width436 : Lower6960.HelperSource.WidthGuard src436.bank 179730 2308 src436.reserve := requestWidth (by decide)

def ends436 : List ℕ := [2308, 2309, 2313]

theorem inside436 : Research6966.TerminalBanks.inside src436.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover436 : Cover (Triangular src436) 2313 2308 ends436 := triangleCover (by decide +kernel)

def src437 : Request := ⟨⟨⟨2602,3628,783,85750⟩,528664175312896,4745819470168⟩,8,2,1,307353,19⟩

theorem rank437 : P3_7_1.BankOK src437.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 85750

theorem width437 : Lower6960.HelperSource.WidthGuard src437.bank 179730 2308 src437.reserve := requestWidth (by decide)

def ends437 : List ℕ := [2308, 2309, 2313]

theorem inside437 : Research6966.TerminalBanks.inside src437.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover437 : Cover (Triangular src437) 2313 2308 ends437 := triangleCover (by decide +kernel)

def src438 : Request := ⟨⟨⟨3202,4465,963,111578⟩,984425340338176,10877088344236⟩,13,2,1,307353,19⟩

theorem rank438 : P3_7_1.BankOK src438.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4465_963 111578

theorem width438 : Lower6960.HelperSource.WidthGuard src438.bank 179730 2308 src438.reserve := requestWidth (by decide)

def ends438 : List ℕ := [2308, 2309, 2313]




theorem cover438 : Cover (Triangular src438) 2313 2308 ends438 := triangleCover (by decide +kernel)

def src439 : Request := ⟨⟨⟨5705,7954,1716,204012⟩,5564742610714624,109473260530676⟩,32,2,1,307353,19⟩

theorem rank439 : P3_7_1.BankOK src439.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5705_7954_1716 204012

theorem width439 : Lower6960.HelperSource.WidthGuard src439.bank 179730 2308 src439.reserve := requestWidth (by decide)

def ends439 : List ℕ := [2308, 2309, 2313]




theorem cover439 : Cover (Triangular src439) 2313 2308 ends439 := triangleCover (by decide +kernel)

def src44 : Request := ⟨⟨⟨2816,3906,882,28077⟩,690700839813120,6603573924229⟩,32,2,1,257319,33⟩

theorem rank44 : P3_7_1.BankOK src44.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3906_882 28077

theorem width44 : Lower6960.HelperSource.WidthGuard src44.bank 179730 2308 src44.reserve := requestWidth (by decide)

def ends44 : List ℕ := [2308, 2313]

theorem inside44 : Research6966.TerminalBanks.inside src44.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover44 : Cover (Triangular src44) 2313 2308 ends44 := triangleCover (by decide +kernel)

def src440 : Request := ⟨⟨⟨7040,9820,2118,2469358⟩,10456759507091456,254233369236069⟩,65,2,1,307353,19⟩

theorem rank440 : P3_7_1.BankOK src440.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_7040_9820_2118 2469358

theorem width440 : Lower6960.HelperSource.WidthGuard src440.bank 179730 2308 src440.reserve := requestWidth (by decide)

def ends440 : List ℕ := [2308, 2309, 2313]




theorem cover440 : Cover (Triangular src440) 2313 2308 ends440 := triangleCover (by decide +kernel)

def src441 : Request := ⟨⟨⟨8289,11558,2498,517209⟩,17088464500817920,488607506616833⟩,65,2,1,307353,19⟩

theorem rank441 : P3_7_1.BankOK src441.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8289_11558_2498 517209

theorem width441 : Lower6960.HelperSource.WidthGuard src441.bank 179730 2308 src441.reserve := requestWidth (by decide)

def ends441 : List ℕ := [2308, 2309, 2313]




theorem cover441 : Cover (Triangular src441) 2313 2308 ends441 := triangleCover (by decide +kernel)

def src442 : Request := ⟨⟨⟨10008,13955,3010,366775⟩,30028351888687104,1036603432174989⟩,65,2,1,307353,19⟩

theorem rank442 : P3_7_1.BankOK src442.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10008_13955_3010 366775

theorem width442 : Lower6960.HelperSource.WidthGuard src442.bank 179730 2308 src442.reserve := requestWidth (by decide)

def ends442 : List ℕ := [2308, 2309, 2313]




theorem cover442 : Cover (Triangular src442) 2313 2308 ends442 := triangleCover (by decide +kernel)

def src443 : Request := ⟨⟨⟨1449,2020,439,56158⟩,91903628410880,459411585633⟩,0,2,1,307462,18⟩

theorem rank443 : P3_7_1.BankOK src443.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1449_2020_439 56158

theorem width443 : Lower6960.HelperSource.WidthGuard src443.bank 179730 2308 src443.reserve := requestWidth (by decide)

def ends443 : List ℕ := [2308, 2309, 2313]

theorem inside443 : Research6966.TerminalBanks.inside src443.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover443 : Cover (Triangular src443) 2313 2308 ends443 := triangleCover (by decide +kernel)

def src444 : Request := ⟨⟨⟨1751,2441,528,58528⟩,161503828246528,975351973888⟩,1,2,1,307462,18⟩

theorem rank444 : P3_7_1.BankOK src444.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2441_528 58528

theorem width444 : Lower6960.HelperSource.WidthGuard src444.bank 179730 2308 src444.reserve := requestWidth (by decide)

def ends444 : List ℕ := [2308, 2309, 2313]

theorem inside444 : Research6966.TerminalBanks.inside src444.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover444 : Cover (Triangular src444) 2313 2308 ends444 := triangleCover (by decide +kernel)

def src445 : Request := ⟨⟨⟨1752,2442,527,66681⟩,161477036081152,975196209190⟩,2,2,1,307462,18⟩

theorem rank445 : P3_7_1.BankOK src445.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2442_527 66681

theorem width445 : Lower6960.HelperSource.WidthGuard src445.bank 179730 2308 src445.reserve := requestWidth (by decide)

def ends445 : List ℕ := [2308, 2309, 2313]

theorem inside445 : Research6966.TerminalBanks.inside src445.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover445 : Cover (Triangular src445) 2313 2308 ends445 := triangleCover (by decide +kernel)

def src446 : Request := ⟨⟨⟨2101,2930,636,67965⟩,279696251813888,2029073656181⟩,3,2,1,307462,18⟩

theorem rank446 : P3_7_1.BankOK src446.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2101_2930_636 67965

theorem width446 : Lower6960.HelperSource.WidthGuard src446.bank 179730 2308 src446.reserve := requestWidth (by decide)

def ends446 : List ℕ := [2308, 2309, 2313]

theorem inside446 : Research6966.TerminalBanks.inside src446.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover446 : Cover (Triangular src446) 2313 2308 ends446 := triangleCover (by decide +kernel)

def src447 : Request := ⟨⟨⟨1751,2442,527,91853⟩,161271009771520,975196209190⟩,4,2,1,307462,18⟩

theorem rank447 : P3_7_1.BankOK src447.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 91853

theorem width447 : Lower6960.HelperSource.WidthGuard src447.bank 179730 2308 src447.reserve := requestWidth (by decide)

def ends447 : List ℕ := [2308, 2309, 2313]

theorem inside447 : Research6966.TerminalBanks.inside src447.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover447 : Cover (Triangular src447) 2313 2308 ends447 := triangleCover (by decide +kernel)

def src448 : Request := ⟨⟨⟨2102,2930,632,75935⟩,278652894052352,2019119590628⟩,4,2,1,307462,18⟩

theorem rank448 : P3_7_1.BankOK src448.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2102_2930_632 75935

theorem width448 : Lower6960.HelperSource.WidthGuard src448.bank 179730 2308 src448.reserve := requestWidth (by decide)

def ends448 : List ℕ := [2308, 2309, 2313]

theorem inside448 : Research6966.TerminalBanks.inside src448.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover448 : Cover (Triangular src448) 2313 2308 ends448 := triangleCover (by decide +kernel)

def src449 : Request := ⟨⟨⟨2602,3628,783,98401⟩,528664175312896,4745819470168⟩,8,2,1,307462,18⟩

theorem rank449 : P3_7_1.BankOK src449.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 98401

theorem width449 : Lower6960.HelperSource.WidthGuard src449.bank 179730 2308 src449.reserve := requestWidth (by decide)

def ends449 : List ℕ := [2308, 2309, 2313]

theorem inside449 : Research6966.TerminalBanks.inside src449.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover449 : Cover (Triangular src449) 2313 2308 ends449 := triangleCover (by decide +kernel)

def src45 : Request := ⟨⟨⟨2006,2790,630,25043⟩,250358324527104,1720419448636⟩,32,2,1,257319,37⟩

theorem rank45 : P3_7_1.BankOK src45.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2006_2790_630 25043

theorem width45 : Lower6960.HelperSource.WidthGuard src45.bank 179730 2308 src45.reserve := requestWidth (by decide)

def ends45 : List ℕ := [2308, 2309, 2313]

theorem inside45 : Research6966.TerminalBanks.inside src45.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover45 : Cover (Triangular src45) 2313 2308 ends45 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources41

section Pack_R6970Height2313CommonSources42

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src450 : Request := ⟨⟨⟨3179,4433,963,103143⟩,968677030625280,10628202307532⟩,10,2,1,307462,18⟩

theorem rank450 : P3_7_1.BankOK src450.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3179_4433_963 103143

theorem width450 : Lower6960.HelperSource.WidthGuard src450.bank 179730 2308 src450.reserve := requestWidth (by decide)

def ends450 : List ℕ := [2308, 2309, 2313]




theorem cover450 : Cover (Triangular src450) 2313 2308 ends450 := triangleCover (by decide +kernel)

def src451 : Request := ⟨⟨⟨3200,4462,963,127997⟩,983050615259136,10853588681502⟩,13,2,1,307462,18⟩

theorem rank451 : P3_7_1.BankOK src451.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4462_963 127997

theorem width451 : Lower6960.HelperSource.WidthGuard src451.bank 179730 2308 src451.reserve := requestWidth (by decide)

def ends451 : List ℕ := [2308, 2309, 2313]




theorem cover451 : Cover (Triangular src451) 2313 2308 ends451 := triangleCover (by decide +kernel)

def src452 : Request := ⟨⟨⟨4798,6690,1445,312747⟩,3313932176195584,54847307041873⟩,32,2,1,307462,18⟩

theorem rank452 : P3_7_1.BankOK src452.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4798_6690_1445 312747

theorem width452 : Lower6960.HelperSource.WidthGuard src452.bank 179730 2308 src452.reserve := requestWidth (by decide)

def ends452 : List ℕ := [2308, 2309, 2313]




theorem cover452 : Cover (Triangular src452) 2313 2308 ends452 := triangleCover (by decide +kernel)

def src453 : Request := ⟨⟨⟨5672,7906,1716,233236⟩,5492986119454720,107361107788084⟩,32,2,1,307462,18⟩

theorem rank453 : P3_7_1.BankOK src453.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5672_7906_1716 233236

theorem width453 : Lower6960.HelperSource.WidthGuard src453.bank 179730 2308 src453.reserve := requestWidth (by decide)

def ends453 : List ℕ := [2308, 2309, 2313]




theorem cover453 : Cover (Triangular src453) 2313 2308 ends453 := triangleCover (by decide +kernel)

def src454 : Request := ⟨⟨⟨1752,2442,527,59574⟩,161477036081152,975196209190⟩,0,2,1,307566,17⟩

theorem rank454 : P3_7_1.BankOK src454.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2442_527 59574

theorem width454 : Lower6960.HelperSource.WidthGuard src454.bank 179730 2308 src454.reserve := requestWidth (by decide)

def ends454 : List ℕ := [2308, 2309, 2313]

theorem inside454 : Research6966.TerminalBanks.inside src454.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover454 : Cover (Triangular src454) 2313 2308 ends454 := triangleCover (by decide +kernel)

def src455 : Request := ⟨⟨⟨1751,2442,527,66600⟩,161271009771520,975196209190⟩,1,2,1,307566,17⟩

theorem rank455 : P3_7_1.BankOK src455.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 66600

theorem width455 : Lower6960.HelperSource.WidthGuard src455.bank 179730 2308 src455.reserve := requestWidth (by decide)

def ends455 : List ℕ := [2308, 2309, 2313]

theorem inside455 : Research6966.TerminalBanks.inside src455.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover455 : Cover (Triangular src455) 2313 2308 ends455 := triangleCover (by decide +kernel)

def src456 : Request := ⟨⟨⟨1751,2442,527,75654⟩,161271009771520,975196209190⟩,2,2,1,307566,17⟩

theorem rank456 : P3_7_1.BankOK src456.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 75654

theorem width456 : Lower6960.HelperSource.WidthGuard src456.bank 179730 2308 src456.reserve := requestWidth (by decide)

def ends456 : List ℕ := [2308, 2309, 2313]

theorem inside456 : Research6966.TerminalBanks.inside src456.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover456 : Cover (Triangular src456) 2313 2308 ends456 := triangleCover (by decide +kernel)

def src457 : Request := ⟨⟨⟨1751,2442,527,87792⟩,161271009771520,975196209190⟩,3,2,1,307566,17⟩

theorem rank457 : P3_7_1.BankOK src457.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 87792

theorem width457 : Lower6960.HelperSource.WidthGuard src457.bank 179730 2308 src457.reserve := requestWidth (by decide)

def ends457 : List ℕ := [2308, 2309, 2313]

theorem inside457 : Research6966.TerminalBanks.inside src457.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover457 : Cover (Triangular src457) 2313 2308 ends457 := triangleCover (by decide +kernel)

def src458 : Request := ⟨⟨⟨1751,2442,527,104914⟩,161271009771520,975196209190⟩,4,2,1,307566,17⟩

theorem rank458 : P3_7_1.BankOK src458.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 104914

theorem width458 : Lower6960.HelperSource.WidthGuard src458.bank 179730 2308 src458.reserve := requestWidth (by decide)

def ends458 : List ℕ := [2308, 2309, 2313]

theorem inside458 : Research6966.TerminalBanks.inside src458.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover458 : Cover (Triangular src458) 2313 2308 ends458 := triangleCover (by decide +kernel)

def src459 : Request := ⟨⟨⟨2101,2930,632,109903⟩,278356530298880,2019119590628⟩,6,2,1,307566,17⟩

theorem rank459 : P3_7_1.BankOK src459.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 109903

theorem width459 : Lower6960.HelperSource.WidthGuard src459.bank 179730 2308 src459.reserve := requestWidth (by decide)

def ends459 : List ℕ := [2308, 2309, 2313]

theorem inside459 : Research6966.TerminalBanks.inside src459.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover459 : Cover (Triangular src459) 2313 2308 ends459 := triangleCover (by decide +kernel)

def src46 : Request := ⟨⟨⟨2816,3906,882,27046⟩,690700839813120,6603573924229⟩,45,2,1,257319,37⟩

theorem rank46 : P3_7_1.BankOK src46.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3906_882 27046

theorem width46 : Lower6960.HelperSource.WidthGuard src46.bank 179730 2308 src46.reserve := requestWidth (by decide)

def ends46 : List ℕ := [2308, 2313]

theorem inside46 : Research6966.TerminalBanks.inside src46.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover46 : Cover (Triangular src46) 2313 2308 ends46 := triangleCover (by decide +kernel)

def src460 : Request := ⟨⟨⟨2602,3628,783,111602⟩,528664175312896,4745819470168⟩,8,2,1,307566,17⟩

theorem rank460 : P3_7_1.BankOK src460.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 111602

theorem width460 : Lower6960.HelperSource.WidthGuard src460.bank 179730 2308 src460.reserve := requestWidth (by decide)

def ends460 : List ℕ := [2308, 2309, 2313]

theorem inside460 : Research6966.TerminalBanks.inside src460.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover460 : Cover (Triangular src460) 2313 2308 ends460 := triangleCover (by decide +kernel)

def src461 : Request := ⟨⟨⟨3200,4461,967,116809⟩,986158795325440,10880883913449⟩,10,2,1,307566,17⟩

theorem rank461 : P3_7_1.BankOK src461.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4461_967 116809

theorem width461 : Lower6960.HelperSource.WidthGuard src461.bank 179730 2308 src461.reserve := requestWidth (by decide)

def ends461 : List ℕ := [2308, 2309, 2313]




theorem cover461 : Cover (Triangular src461) 2313 2308 ends461 := triangleCover (by decide +kernel)

def src462 : Request := ⟨⟨⟨3186,4441,963,145091⟩,973455842869248,10690056802628⟩,13,2,1,307566,17⟩

theorem rank462 : P3_7_1.BankOK src462.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3186_4441_963 145091

theorem width462 : Lower6960.HelperSource.WidthGuard src462.bank 179730 2308 src462.reserve := requestWidth (by decide)

def ends462 : List ℕ := [2308, 2309, 2313]




theorem cover462 : Cover (Triangular src462) 2313 2308 ends462 := triangleCover (by decide +kernel)

def src463 : Request := ⟨⟨⟨4802,6698,1446,174697⟩,3321866325852160,55088401876903⟩,20,2,1,307566,17⟩

theorem rank463 : P3_7_1.BankOK src463.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4802_6698_1446 174697

theorem width463 : Lower6960.HelperSource.WidthGuard src463.bank 179730 2308 src463.reserve := requestWidth (by decide)

def ends463 : List ℕ := [2308, 2309, 2313]




theorem cover463 : Cover (Triangular src463) 2313 2308 ends463 := triangleCover (by decide +kernel)

def src464 : Request := ⟨⟨⟨5682,7922,1716,265686⟩,5514678749102080,108062050923124⟩,32,2,1,307566,17⟩

theorem rank464 : P3_7_1.BankOK src464.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5682_7922_1716 265686

theorem width464 : Lower6960.HelperSource.WidthGuard src464.bank 179730 2308 src464.reserve := requestWidth (by decide)

def ends464 : List ℕ := [2308, 2309, 2313]




theorem cover464 : Cover (Triangular src464) 2313 2308 ends464 := triangleCover (by decide +kernel)

def src465 : Request := ⟨⟨⟨1450,2021,438,72000⟩,91886136590336,459327400936⟩,0,2,1,307664,16⟩

theorem rank465 : P3_7_1.BankOK src465.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1450_2021_438 72000

theorem width465 : Lower6960.HelperSource.WidthGuard src465.bank 179730 2308 src465.reserve := requestWidth (by decide)

def ends465 : List ℕ := [2308, 2309, 2313]

theorem inside465 : Research6966.TerminalBanks.inside src465.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover465 : Cover (Triangular src465) 2313 2308 ends465 := triangleCover (by decide +kernel)

def src466 : Request := ⟨⟨⟨1751,2442,527,74563⟩,161271009771520,975196209190⟩,1,2,1,307664,16⟩

theorem rank466 : P3_7_1.BankOK src466.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 74563

theorem width466 : Lower6960.HelperSource.WidthGuard src466.bank 179730 2308 src466.reserve := requestWidth (by decide)

def ends466 : List ℕ := [2308, 2309, 2313]

theorem inside466 : Research6966.TerminalBanks.inside src466.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover466 : Cover (Triangular src466) 2313 2308 ends466 := triangleCover (by decide +kernel)

def src467 : Request := ⟨⟨⟨2085,2906,632,78812⟩,273637277696000,1966383525068⟩,2,2,1,307664,16⟩

theorem rank467 : P3_7_1.BankOK src467.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2085_2906_632 78812

theorem width467 : Lower6960.HelperSource.WidthGuard src467.bank 179730 2308 src467.reserve := requestWidth (by decide)

def ends467 : List ℕ := [2308, 2309, 2313]

theorem inside467 : Research6966.TerminalBanks.inside src467.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover467 : Cover (Triangular src467) 2313 2308 ends467 := triangleCover (by decide +kernel)

def src468 : Request := ⟨⟨⟨2101,2930,632,86929⟩,278356530298880,2019119590628⟩,3,2,1,307664,16⟩

theorem rank468 : P3_7_1.BankOK src468.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 86929

theorem width468 : Lower6960.HelperSource.WidthGuard src468.bank 179730 2308 src468.reserve := requestWidth (by decide)

def ends468 : List ℕ := [2308, 2309, 2313]

theorem inside468 : Research6966.TerminalBanks.inside src468.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover468 : Cover (Triangular src468) 2313 2308 ends468 := triangleCover (by decide +kernel)

def src469 : Request := ⟨⟨⟨1751,2442,527,118235⟩,161271009771520,975196209190⟩,4,2,1,307664,16⟩

theorem rank469 : P3_7_1.BankOK src469.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 118235

theorem width469 : Lower6960.HelperSource.WidthGuard src469.bank 179730 2308 src469.reserve := requestWidth (by decide)

def ends469 : List ℕ := [2308, 2309, 2313]

theorem inside469 : Research6966.TerminalBanks.inside src469.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover469 : Cover (Triangular src469) 2313 2308 ends469 := triangleCover (by decide +kernel)

def src47 : Request := ⟨⟨⟨2600,3611,775,31694⟩,523640687820800,4637334487213⟩,45,2,1,257515,39⟩

theorem rank47 : P3_7_1.BankOK src47.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3611_775 31694

theorem width47 : Lower6960.HelperSource.WidthGuard src47.bank 179730 2308 src47.reserve := requestWidth (by decide)

def ends47 : List ℕ := [2308, 2309, 2313]

theorem inside47 : Research6966.TerminalBanks.inside src47.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover47 : Cover (Triangular src47) 2313 2308 ends47 := triangleCover (by decide +kernel)

def src470 : Request := ⟨⟨⟨2101,2930,632,96364⟩,278356530298880,2019119590628⟩,4,2,1,307664,16⟩

theorem rank470 : P3_7_1.BankOK src470.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 96364

theorem width470 : Lower6960.HelperSource.WidthGuard src470.bank 179730 2308 src470.reserve := requestWidth (by decide)

def ends470 : List ℕ := [2308, 2309, 2313]

theorem inside470 : Research6966.TerminalBanks.inside src470.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover470 : Cover (Triangular src470) 2313 2308 ends470 := triangleCover (by decide +kernel)

def src471 : Request := ⟨⟨⟨2602,3628,783,125198⟩,528664175312896,4745819470168⟩,8,2,1,307664,16⟩

theorem rank471 : P3_7_1.BankOK src471.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 125198

theorem width471 : Lower6960.HelperSource.WidthGuard src471.bank 179730 2308 src471.reserve := requestWidth (by decide)

def ends471 : List ℕ := [2308, 2309, 2313]

theorem inside471 : Research6966.TerminalBanks.inside src471.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover471 : Cover (Triangular src471) 2313 2308 ends471 := triangleCover (by decide +kernel)

def src472 : Request := ⟨⟨⟨3191,4453,963,131796⟩,976876861390848,10783296850152⟩,10,2,1,307664,16⟩

theorem rank472 : P3_7_1.BankOK src472.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3191_4453_963 131796

theorem width472 : Lower6960.HelperSource.WidthGuard src472.bank 179730 2308 src472.reserve := requestWidth (by decide)

def ends472 : List ℕ := [2308, 2309, 2313]




theorem cover472 : Cover (Triangular src472) 2313 2308 ends472 := triangleCover (by decide +kernel)

def src473 : Request := ⟨⟨⟨3191,4449,963,163078⟩,976876861390848,10752155644732⟩,13,2,1,307664,16⟩

theorem rank473 : P3_7_1.BankOK src473.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3191_4449_963 163078

theorem width473 : Lower6960.HelperSource.WidthGuard src473.bank 179730 2308 src473.reserve := requestWidth (by decide)

def ends473 : List ℕ := [2308, 2309, 2313]




theorem cover473 : Cover (Triangular src473) 2313 2308 ends473 := triangleCover (by decide +kernel)

def src474 : Request := ⟨⟨⟨4803,6698,1445,195569⟩,3321662161813504,55058665830093⟩,20,2,1,307664,16⟩

theorem rank474 : P3_7_1.BankOK src474.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4803_6698_1445 195569

theorem width474 : Lower6960.HelperSource.WidthGuard src474.bank 179730 2308 src474.reserve := requestWidth (by decide)

def ends474 : List ℕ := [2308, 2309, 2313]




theorem cover474 : Cover (Triangular src474) 2313 2308 ends474 := triangleCover (by decide +kernel)

def src475 : Request := ⟨⟨⟨5682,7922,1716,299038⟩,5514678749102080,108062050923124⟩,32,2,1,307664,16⟩

theorem rank475 : P3_7_1.BankOK src475.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5682_7922_1716 299038

theorem width475 : Lower6960.HelperSource.WidthGuard src475.bank 179730 2308 src475.reserve := requestWidth (by decide)

def ends475 : List ℕ := [2308, 2309, 2313]




theorem cover475 : Cover (Triangular src475) 2313 2308 ends475 := triangleCover (by decide +kernel)

def src476 : Request := ⟨⟨⟨1450,2022,436,80235⟩,91566841790464,458421718666⟩,0,2,1,307754,15⟩

theorem rank476 : P3_7_1.BankOK src476.bank := by
  simpa only [src476, _root_.Research6969.TransitionBanks.bank232] using _root_.Research6969.TransitionBanks.rank232 80235

theorem width476 : Lower6960.HelperSource.WidthGuard src476.bank 179730 2308 src476.reserve := requestWidth (by decide)

def ends476 : List ℕ := [2308, 2309, 2313]

theorem inside476 : Research6966.TerminalBanks.inside src476.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover476 : Cover (Triangular src476) 2313 2308 ends476 := triangleCover (by decide +kernel)

def src477 : Request := ⟨⟨⟨1748,2439,526,82991⟩,160421722193920,969910301864⟩,1,2,1,307754,15⟩

theorem rank477 : P3_7_1.BankOK src477.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1748_2439_526 82991

theorem width477 : Lower6960.HelperSource.WidthGuard src477.bank 179730 2308 src477.reserve := requestWidth (by decide)

def ends477 : List ℕ := [2308, 2309, 2313]

theorem inside477 : Research6966.TerminalBanks.inside src477.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover477 : Cover (Triangular src477) 2313 2308 ends477 := triangleCover (by decide +kernel)

def src478 : Request := ⟨⟨⟨1751,2442,527,109852⟩,161271009771520,975196209190⟩,3,2,1,307754,15⟩

theorem rank478 : P3_7_1.BankOK src478.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 109852

theorem width478 : Lower6960.HelperSource.WidthGuard src478.bank 179730 2308 src478.reserve := requestWidth (by decide)

def ends478 : List ℕ := [2308, 2309, 2313]

theorem inside478 : Research6966.TerminalBanks.inside src478.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover478 : Cover (Triangular src478) 2313 2308 ends478 := triangleCover (by decide +kernel)

def src479 : Request := ⟨⟨⟨2101,2930,632,96375⟩,278356530298880,2019119590628⟩,3,2,1,307754,15⟩

theorem rank479 : P3_7_1.BankOK src479.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 96375

theorem width479 : Lower6960.HelperSource.WidthGuard src479.bank 179730 2308 src479.reserve := requestWidth (by decide)

def ends479 : List ℕ := [2308, 2309, 2313]

theorem inside479 : Research6966.TerminalBanks.inside src479.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover479 : Cover (Triangular src479) 2313 2308 ends479 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources42

section Pack_R6970Height2313CommonSources43

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src48 : Request := ⟨⟨⟨2615,3627,819,23874⟩,553151842222080,4910333421859⟩,45,2,1,257319,39⟩

theorem rank48 : P3_7_1.BankOK src48.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2615_3627_819 23874

theorem width48 : Lower6960.HelperSource.WidthGuard src48.bank 179730 2308 src48.reserve := requestWidth (by decide)

def ends48 : List ℕ := [2308, 2313]

theorem inside48 : Research6966.TerminalBanks.inside src48.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover48 : Cover (Triangular src48) 2313 2308 ends48 := triangleCover (by decide +kernel)

def src480 : Request := ⟨⟨⟨1751,2442,527,131739⟩,161271009771520,975196209190⟩,4,2,1,307754,15⟩

theorem rank480 : P3_7_1.BankOK src480.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 131739

theorem width480 : Lower6960.HelperSource.WidthGuard src480.bank 179730 2308 src480.reserve := requestWidth (by decide)

def ends480 : List ℕ := [2308, 2309, 2313]

theorem inside480 : Research6966.TerminalBanks.inside src480.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover480 : Cover (Triangular src480) 2313 2308 ends480 := triangleCover (by decide +kernel)

def src481 : Request := ⟨⟨⟨2091,2918,626,108977⟩,273408925892608,1977865107915⟩,4,2,1,307754,15⟩

theorem rank481 : P3_7_1.BankOK src481.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2091_2918_626 108977

theorem width481 : Lower6960.HelperSource.WidthGuard src481.bank 179730 2308 src481.reserve := requestWidth (by decide)

def ends481 : List ℕ := [2308, 2309, 2313]

theorem inside481 : Research6966.TerminalBanks.inside src481.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover481 : Cover (Triangular src481) 2313 2308 ends481 := triangleCover (by decide +kernel)

def src482 : Request := ⟨⟨⟨2602,3628,783,139083⟩,528664175312896,4745819470168⟩,8,2,1,307754,15⟩

theorem rank482 : P3_7_1.BankOK src482.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 139083

theorem width482 : Lower6960.HelperSource.WidthGuard src482.bank 179730 2308 src482.reserve := requestWidth (by decide)

def ends482 : List ℕ := [2308, 2309, 2313]

theorem inside482 : Research6966.TerminalBanks.inside src482.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover482 : Cover (Triangular src482) 2313 2308 ends482 := triangleCover (by decide +kernel)

def src483 : Request := ⟨⟨⟨3154,4401,947,147855⟩,939653185667072,10248469804329⟩,10,2,1,307754,15⟩

theorem rank483 : P3_7_1.BankOK src483.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3154_4401_947 147855

theorem width483 : Lower6960.HelperSource.WidthGuard src483.bank 179730 2308 src483.reserve := requestWidth (by decide)

def ends483 : List ℕ := [2308, 2309, 2313]




theorem cover483 : Cover (Triangular src483) 2313 2308 ends483 := triangleCover (by decide +kernel)

def src484 : Request := ⟨⟨⟨3202,4465,963,181448⟩,984425340338176,10877088344236⟩,13,2,1,307754,15⟩

theorem rank484 : P3_7_1.BankOK src484.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4465_963 181448

theorem width484 : Lower6960.HelperSource.WidthGuard src484.bank 179730 2308 src484.reserve := requestWidth (by decide)

def ends484 : List ℕ := [2308, 2309, 2313]




theorem cover484 : Cover (Triangular src484) 2313 2308 ends484 := triangleCover (by decide +kernel)

def src485 : Request := ⟨⟨⟨4803,6698,1445,216737⟩,3321662161813504,55058665830093⟩,20,2,1,307754,15⟩

theorem rank485 : P3_7_1.BankOK src485.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4803_6698_1445 216737

theorem width485 : Lower6960.HelperSource.WidthGuard src485.bank 179730 2308 src485.reserve := requestWidth (by decide)

def ends485 : List ℕ := [2308, 2309, 2313]




theorem cover485 : Cover (Triangular src485) 2313 2308 ends485 := triangleCover (by decide +kernel)

def src486 : Request := ⟨⟨⟨5693,7938,1716,332426⟩,5538592628408320,108766099493044⟩,32,2,1,307754,15⟩

theorem rank486 : P3_7_1.BankOK src486.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5693_7938_1716 332426

theorem width486 : Lower6960.HelperSource.WidthGuard src486.bank 179730 2308 src486.reserve := requestWidth (by decide)

def ends486 : List ℕ := [2308, 2309, 2313]




theorem cover486 : Cover (Triangular src486) 2313 2308 ends486 := triangleCover (by decide +kernel)

def src487 : Request := ⟨⟨⟨1451,2023,436,88410⟩,91708090482688,459151377566⟩,0,2,1,307836,14⟩

theorem rank487 : P3_7_1.BankOK src487.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2023_436 88410

theorem width487 : Lower6960.HelperSource.WidthGuard src487.bank 179730 2308 src487.reserve := requestWidth (by decide)

def ends487 : List ℕ := [2308, 2309, 2313]

theorem inside487 : Research6966.TerminalBanks.inside src487.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover487 : Cover (Triangular src487) 2313 2308 ends487 := triangleCover (by decide +kernel)

def src488 : Request := ⟨⟨⟨2091,2915,632,88168⟩,275402019307520,1986048372698⟩,1,2,1,307836,14⟩

theorem rank488 : P3_7_1.BankOK src488.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2091_2915_632 88168

theorem width488 : Lower6960.HelperSource.WidthGuard src488.bank 179730 2308 src488.reserve := requestWidth (by decide)

def ends488 : List ℕ := [2308, 2309, 2313]

theorem inside488 : Research6966.TerminalBanks.inside src488.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover488 : Cover (Triangular src488) 2313 2308 ends488 := triangleCover (by decide +kernel)

def src489 : Request := ⟨⟨⟨2101,2930,632,96426⟩,278356530298880,2019119590628⟩,2,2,1,307836,14⟩

theorem rank489 : P3_7_1.BankOK src489.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 96426

theorem width489 : Lower6960.HelperSource.WidthGuard src489.bank 179730 2308 src489.reserve := requestWidth (by decide)

def ends489 : List ℕ := [2308, 2309, 2313]

theorem inside489 : Research6966.TerminalBanks.inside src489.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover489 : Cover (Triangular src489) 2313 2308 ends489 := triangleCover (by decide +kernel)

def src49 : Request := ⟨⟨⟨2300,3208,702,25043⟩,369170633195520,2933547980091⟩,45,2,1,257319,41⟩

theorem rank49 : P3_7_1.BankOK src49.bank := by
  simpa only [src49, _root_.Research6969.TerminalAuxBanks.bank33] using _root_.Research6969.PackedRanks.TerminalRanks32To35.rank33 25043

theorem width49 : Lower6960.HelperSource.WidthGuard src49.bank 179730 2308 src49.reserve := requestWidth (by decide)

def ends49 : List ℕ := [2308, 2313]

theorem inside49 : Research6966.TerminalBanks.inside src49.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover49 : Cover (Triangular src49) 2313 2308 ends49 := triangleCover (by decide +kernel)

def src490 : Request := ⟨⟨⟨1748,2439,526,121571⟩,160421722193920,969910301864⟩,3,2,1,307836,14⟩

theorem rank490 : P3_7_1.BankOK src490.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1748_2439_526 121571

theorem width490 : Lower6960.HelperSource.WidthGuard src490.bank 179730 2308 src490.reserve := requestWidth (by decide)

def ends490 : List ℕ := [2308, 2309, 2313]

theorem inside490 : Research6966.TerminalBanks.inside src490.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover490 : Cover (Triangular src490) 2313 2308 ends490 := triangleCover (by decide +kernel)

def src491 : Request := ⟨⟨⟨2095,2924,626,108411⟩,274579528351744,1990976970162⟩,3,2,1,307836,14⟩

theorem rank491 : P3_7_1.BankOK src491.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2095_2924_626 108411

theorem width491 : Lower6960.HelperSource.WidthGuard src491.bank 179730 2308 src491.reserve := requestWidth (by decide)

def ends491 : List ℕ := [2308, 2309, 2313]

theorem inside491 : Research6966.TerminalBanks.inside src491.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover491 : Cover (Triangular src491) 2313 2308 ends491 := triangleCover (by decide +kernel)

def src492 : Request := ⟨⟨⟨2554,3564,770,129860⟩,500675730472960,4423526519142⟩,6,2,1,307836,14⟩

theorem rank492 : P3_7_1.BankOK src492.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2554_3564_770 129860

theorem width492 : Lower6960.HelperSource.WidthGuard src492.bank 179730 2308 src492.reserve := requestWidth (by decide)

def ends492 : List ℕ := [2308, 2309, 2313]

theorem inside492 : Research6966.TerminalBanks.inside src492.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover492 : Cover (Triangular src492) 2313 2308 ends492 := triangleCover (by decide +kernel)

def src493 : Request := ⟨⟨⟨2603,3630,783,189056⟩,529118684774400,4754242757152⟩,10,2,1,307836,14⟩

theorem rank493 : P3_7_1.BankOK src493.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2603_3630_783 189056

theorem width493 : Lower6960.HelperSource.WidthGuard src493.bank 179730 2308 src493.reserve := requestWidth (by decide)

def ends493 : List ℕ := [2308, 2309, 2313]

theorem inside493 : Research6966.TerminalBanks.inside src493.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover493 : Cover (Triangular src493) 2313 2308 ends493 := triangleCover (by decide +kernel)

def src494 : Request := ⟨⟨⟨3191,4449,963,160462⟩,976876861390848,10752155644732⟩,10,2,1,307836,14⟩

theorem rank494 : P3_7_1.BankOK src494.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3191_4449_963 160462

theorem width494 : Lower6960.HelperSource.WidthGuard src494.bank 179730 2308 src494.reserve := requestWidth (by decide)

def ends494 : List ℕ := [2308, 2309, 2313]




theorem cover494 : Cover (Triangular src494) 2313 2308 ends494 := triangleCover (by decide +kernel)

def src495 : Request := ⟨⟨⟨3936,5488,1189,180646⟩,1834118800998400,24903571529391⟩,13,2,1,307836,14⟩

theorem rank495 : P3_7_1.BankOK src495.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3936_5488_1189 180646

theorem width495 : Lower6960.HelperSource.WidthGuard src495.bank 179730 2308 src495.reserve := requestWidth (by decide)

def ends495 : List ℕ := [2308, 2309, 2313]




theorem cover495 : Cover (Triangular src495) 2313 2308 ends495 := triangleCover (by decide +kernel)

def src496 : Request := ⟨⟨⟨5704,7954,1716,275808⟩,5562560969965568,109473260530676⟩,25,2,1,307836,14⟩

theorem rank496 : P3_7_1.BankOK src496.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5704_7954_1716 275808

theorem width496 : Lower6960.HelperSource.WidthGuard src496.bank 179730 2308 src496.reserve := requestWidth (by decide)

def ends496 : List ℕ := [2308, 2309, 2313]




theorem cover496 : Cover (Triangular src496) 2313 2308 ends496 := triangleCover (by decide +kernel)

def src497 : Request := ⟨⟨⟨5703,7954,1716,366299⟩,5560379779317760,109473260530676⟩,32,2,1,307836,14⟩

theorem rank497 : P3_7_1.BankOK src497.bank := 
  _root_.Research6970.Height2313.Physical.bank_5703_7954_1716 366299

theorem width497 : Lower6960.HelperSource.WidthGuard src497.bank 179730 2308 src497.reserve := requestWidth (by decide)

def ends497 : List ℕ := [2308, 2309, 2313]




theorem cover497 : Cover (Triangular src497) 2313 2308 ends497 := triangleCover (by decide +kernel)

def src498 : Request := ⟨⟨⟨1751,2441,528,88417⟩,161503828246528,975351973888⟩,0,2,1,307912,13⟩

theorem rank498 : P3_7_1.BankOK src498.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2441_528 88417

theorem width498 : Lower6960.HelperSource.WidthGuard src498.bank 179730 2308 src498.reserve := requestWidth (by decide)

def ends498 : List ℕ := [2308, 2309, 2313]

theorem inside498 : Research6966.TerminalBanks.inside src498.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover498 : Cover (Triangular src498) 2313 2308 ends498 := triangleCover (by decide +kernel)

def src499 : Request := ⟨⟨⟨1751,2442,527,99437⟩,161271009771520,975196209190⟩,1,2,1,307912,13⟩

theorem rank499 : P3_7_1.BankOK src499.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 99437

theorem width499 : Lower6960.HelperSource.WidthGuard src499.bank 179730 2308 src499.reserve := requestWidth (by decide)

def ends499 : List ℕ := [2308, 2309, 2313]

theorem inside499 : Research6966.TerminalBanks.inside src499.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover499 : Cover (Triangular src499) 2313 2308 ends499 := triangleCover (by decide +kernel)

def src5 : Request := ⟨⟨⟨2600,3610,775,31694⟩,523640687820800,4633204195397⟩,63,1,1,128757,49⟩

theorem rank5 : P3_7_1.BankOK src5.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2600_3610_775 31694

theorem width5 : Lower6960.HelperSource.WidthGuard src5.bank 179730 2308 src5.reserve := requestWidth (by decide)

def ends5 : List ℕ := [2308, 2309, 2313]

theorem inside5 : Research6966.TerminalBanks.inside src5.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover5 : Cover (Triangular src5) 2313 2308 ends5 := triangleCover (by decide +kernel)

def src50 : Request := ⟨⟨⟨2313,3208,724,21939⟩,382708934246400,3004743122568⟩,45,2,1,257319,41⟩

theorem rank50 : P3_7_1.BankOK src50.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2313_3208_724 21939

theorem width50 : Lower6960.HelperSource.WidthGuard src50.bank 179730 2308 src50.reserve := requestWidth (by decide)

def ends50 : List ℕ := [2308, 2313]

theorem inside50 : Research6966.TerminalBanks.inside src50.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover50 : Cover (Triangular src50) 2313 2308 ends50 := triangleCover (by decide +kernel)

def src500 : Request := ⟨⟨⟨1751,2442,527,113567⟩,161271009771520,975196209190⟩,2,2,1,307912,13⟩

theorem rank500 : P3_7_1.BankOK src500.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 113567

theorem width500 : Lower6960.HelperSource.WidthGuard src500.bank 179730 2308 src500.reserve := requestWidth (by decide)

def ends500 : List ℕ := [2308, 2309, 2313]

theorem inside500 : Research6966.TerminalBanks.inside src500.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover500 : Cover (Triangular src500) 2313 2308 ends500 := triangleCover (by decide +kernel)

def src501 : Request := ⟨⟨⟨2101,2930,633,128558⟩,278691788095488,2021610130172⟩,4,2,1,307912,13⟩

theorem rank501 : P3_7_1.BankOK src501.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2101_2930_633 128558

theorem width501 : Lower6960.HelperSource.WidthGuard src501.bank 179730 2308 src501.reserve := requestWidth (by decide)

def ends501 : List ℕ := [2308, 2309, 2313]

theorem inside501 : Research6966.TerminalBanks.inside src501.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover501 : Cover (Triangular src501) 2313 2308 ends501 := triangleCover (by decide +kernel)

def src502 : Request := ⟨⟨⟨2101,2930,632,165857⟩,278356530298880,2019119590628⟩,6,2,1,307912,13⟩

theorem rank502 : P3_7_1.BankOK src502.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 165857

theorem width502 : Lower6960.HelperSource.WidthGuard src502.bank 179730 2308 src502.reserve := requestWidth (by decide)

def ends502 : List ℕ := [2308, 2309, 2313]

theorem inside502 : Research6966.TerminalBanks.inside src502.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover502 : Cover (Triangular src502) 2313 2308 ends502 := triangleCover (by decide +kernel)

def src503 : Request := ⟨⟨⟨3202,4465,963,175468⟩,984425340338176,10877088344236⟩,10,2,1,307912,13⟩

theorem rank503 : P3_7_1.BankOK src503.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4465_963 175468

theorem width503 : Lower6960.HelperSource.WidthGuard src503.bank 179730 2308 src503.reserve := requestWidth (by decide)

def ends503 : List ℕ := [2308, 2309, 2313]




theorem cover503 : Cover (Triangular src503) 2313 2308 ends503 := triangleCover (by decide +kernel)

def src504 : Request := ⟨⟨⟨2610,3640,783,318691⟩,532306005590016,4796511703592⟩,13,2,1,307912,13⟩

theorem rank504 : P3_7_1.BankOK src504.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3640_783 318691

theorem width504 : Lower6960.HelperSource.WidthGuard src504.bank 179730 2308 src504.reserve := requestWidth (by decide)

def ends504 : List ℕ := [2308, 2309, 2313]

theorem inside504 : Research6966.TerminalBanks.inside src504.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover504 : Cover (Triangular src504) 2313 2308 ends504 := triangleCover (by decide +kernel)

def src505 : Request := ⟨⟨⟨3944,5500,1189,231071⟩,1842469115002880,25079250895001⟩,16,2,1,307912,13⟩

theorem rank505 : P3_7_1.BankOK src505.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3944_5500_1189 231071

theorem width505 : Lower6960.HelperSource.WidthGuard src505.bank 179730 2308 src505.reserve := requestWidth (by decide)

def ends505 : List ℕ := [2308, 2309, 2313]




theorem cover505 : Cover (Triangular src505) 2313 2308 ends505 := triangleCover (by decide +kernel)

def src506 : Request := ⟨⟨⟨4792,6682,1445,259944⟩,3304668702441472,54636500602517⟩,20,2,1,307912,13⟩

theorem rank506 : P3_7_1.BankOK src506.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4792_6682_1445 259944

theorem width506 : Lower6960.HelperSource.WidthGuard src506.bank 179730 2308 src506.reserve := requestWidth (by decide)

def ends506 : List ℕ := [2308, 2309, 2313]




theorem cover506 : Cover (Triangular src506) 2313 2308 ends506 := triangleCover (by decide +kernel)

def src507 : Request := ⟨⟨⟨3926,5479,1169,511708⟩,1800277308211200,24446475358504⟩,25,2,1,307912,13⟩

theorem rank507 : P3_7_1.BankOK src507.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3926_5479_1169 511708

theorem width507 : Lower6960.HelperSource.WidthGuard src507.bank 179730 2308 src507.reserve := requestWidth (by decide)

def ends507 : List ℕ := [2308, 2309, 2313]




theorem cover507 : Cover (Triangular src507) 2313 2308 ends507 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources43

section Pack_R6970Height2313CommonSources44

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src508 : Request := ⟨⟨⟨1751,2442,527,95994⟩,161271009771520,975196209190⟩,0,2,1,307983,12⟩

theorem rank508 : P3_7_1.BankOK src508.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 95994

theorem width508 : Lower6960.HelperSource.WidthGuard src508.bank 179730 2308 src508.reserve := requestWidth (by decide)

def ends508 : List ℕ := [2308, 2309, 2313]

theorem inside508 : Research6966.TerminalBanks.inside src508.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover508 : Cover (Triangular src508) 2313 2308 ends508 := triangleCover (by decide +kernel)

def src509 : Request := ⟨⟨⟨1751,2442,527,107928⟩,161271009771520,975196209190⟩,1,2,1,307983,12⟩

theorem rank509 : P3_7_1.BankOK src509.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 107928

theorem width509 : Lower6960.HelperSource.WidthGuard src509.bank 179730 2308 src509.reserve := requestWidth (by decide)

def ends509 : List ℕ := [2308, 2309, 2313]

theorem inside509 : Research6966.TerminalBanks.inside src509.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover509 : Cover (Triangular src509) 2313 2308 ends509 := triangleCover (by decide +kernel)

def src51 : Request := ⟨⟨⟨2007,2789,630,22261⟩,250638203092992,1718433691636⟩,45,2,1,257319,43⟩

theorem rank51 : P3_7_1.BankOK src51.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2007_2789_630 22261

theorem width51 : Lower6960.HelperSource.WidthGuard src51.bank 179730 2308 src51.reserve := requestWidth (by decide)

def ends51 : List ℕ := [2308, 2309, 2313]

theorem inside51 : Research6966.TerminalBanks.inside src51.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover51 : Cover (Triangular src51) 2313 2308 ends51 := triangleCover (by decide +kernel)

def src510 : Request := ⟨⟨⟨1751,2442,527,123322⟩,161271009771520,975196209190⟩,2,2,1,307983,12⟩

theorem rank510 : P3_7_1.BankOK src510.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 123322

theorem width510 : Lower6960.HelperSource.WidthGuard src510.bank 179730 2308 src510.reserve := requestWidth (by decide)

def ends510 : List ℕ := [2308, 2309, 2313]

theorem inside510 : Research6966.TerminalBanks.inside src510.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover510 : Cover (Triangular src510) 2313 2308 ends510 := triangleCover (by decide +kernel)

def src511 : Request := ⟨⟨⟨1751,2442,527,143924⟩,161271009771520,975196209190⟩,3,2,1,307983,12⟩

theorem rank511 : P3_7_1.BankOK src511.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 143924

theorem width511 : Lower6960.HelperSource.WidthGuard src511.bank 179730 2308 src511.reserve := requestWidth (by decide)

def ends511 : List ℕ := [2308, 2309, 2313]

theorem inside511 : Research6966.TerminalBanks.inside src511.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover511 : Cover (Triangular src511) 2313 2308 ends511 := triangleCover (by decide +kernel)

def src512 : Request := ⟨⟨⟨1785,2490,537,166911⟩,170783777751040,1053541809432⟩,4,2,1,307983,12⟩

theorem rank512 : P3_7_1.BankOK src512.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1785_2490_537 166911

theorem width512 : Lower6960.HelperSource.WidthGuard src512.bank 179730 2308 src512.reserve := requestWidth (by decide)

def ends512 : List ℕ := [2308, 2309, 2313]

theorem inside512 : Research6966.TerminalBanks.inside src512.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover512 : Cover (Triangular src512) 2313 2308 ends512 := triangleCover (by decide +kernel)

def src513 : Request := ⟨⟨⟨2101,2930,632,180155⟩,278356530298880,2019119590628⟩,6,2,1,307983,12⟩

theorem rank513 : P3_7_1.BankOK src513.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 180155

theorem width513 : Lower6960.HelperSource.WidthGuard src513.bank 179730 2308 src513.reserve := requestWidth (by decide)

def ends513 : List ℕ := [2308, 2309, 2313]

theorem inside513 : Research6966.TerminalBanks.inside src513.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover513 : Cover (Triangular src513) 2313 2308 ends513 := triangleCover (by decide +kernel)

def src514 : Request := ⟨⟨⟨2602,3628,783,181807⟩,528664175312896,4745819470168⟩,8,2,1,307983,12⟩

theorem rank514 : P3_7_1.BankOK src514.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 181807

theorem width514 : Lower6960.HelperSource.WidthGuard src514.bank 179730 2308 src514.reserve := requestWidth (by decide)

def ends514 : List ℕ := [2308, 2309, 2313]

theorem inside514 : Research6966.TerminalBanks.inside src514.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover514 : Cover (Triangular src514) 2313 2308 ends514 := triangleCover (by decide +kernel)

def src515 : Request := ⟨⟨⟨3197,4461,955,193767⟩,974772100923392,10775370705171⟩,10,2,1,307983,12⟩

theorem rank515 : P3_7_1.BankOK src515.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3197_4461_955 193767

theorem width515 : Lower6960.HelperSource.WidthGuard src515.bank 179730 2308 src515.reserve := requestWidth (by decide)

def ends515 : List ℕ := [2308, 2309, 2313]




theorem cover515 : Cover (Triangular src515) 2313 2308 ends515 := triangleCover (by decide +kernel)

def src516 : Request := ⟨⟨⟨3203,4467,963,237105⟩,985113081937920,10892773989742⟩,13,2,1,307983,12⟩

theorem rank516 : P3_7_1.BankOK src516.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3203_4467_963 237105

theorem width516 : Lower6960.HelperSource.WidthGuard src516.bank 179730 2308 src516.reserve := requestWidth (by decide)

def ends516 : List ℕ := [2308, 2309, 2313]




theorem cover516 : Cover (Triangular src516) 2313 2308 ends516 := triangleCover (by decide +kernel)

def src517 : Request := ⟨⟨⟨3952,5512,1189,324805⟩,1850839393894400,25255771038451⟩,20,2,1,307983,12⟩

theorem rank517 : P3_7_1.BankOK src517.bank := 
  _root_.Research6970.Height2313.Physical.bank_3952_5512_1189 324805

theorem width517 : Lower6960.HelperSource.WidthGuard src517.bank 179730 2308 src517.reserve := requestWidth (by decide)

def ends517 : List ℕ := [2308, 2309, 2313]




theorem cover517 : Cover (Triangular src517) 2313 2308 ends517 := triangleCover (by decide +kernel)

def src518 : Request := ⟨⟨⟨5692,7938,1716,326422⟩,5536416388874240,108766099493044⟩,25,2,1,307983,12⟩

theorem rank518 : P3_7_1.BankOK src518.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5692_7938_1716 326422

theorem width518 : Lower6960.HelperSource.WidthGuard src518.bank 179730 2308 src518.reserve := requestWidth (by decide)

def ends518 : List ℕ := [2308, 2309, 2313]




theorem cover518 : Cover (Triangular src518) 2313 2308 ends518 := triangleCover (by decide +kernel)

def src519 : Request := ⟨⟨⟨1451,2023,436,113229⟩,91708090482688,459151377566⟩,0,2,1,308048,11⟩

theorem rank519 : P3_7_1.BankOK src519.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2023_436 113229

theorem width519 : Lower6960.HelperSource.WidthGuard src519.bank 179730 2308 src519.reserve := requestWidth (by decide)

def ends519 : List ℕ := [2308, 2309, 2313]

theorem inside519 : Research6966.TerminalBanks.inside src519.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover519 : Cover (Triangular src519) 2313 2308 ends519 := triangleCover (by decide +kernel)

def src52 : Request := ⟨⟨⟨2816,3905,882,26837⟩,690700839813120,6598128215989⟩,63,2,1,257319,43⟩

theorem rank52 : P3_7_1.BankOK src52.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 26837

theorem width52 : Lower6960.HelperSource.WidthGuard src52.bank 179730 2308 src52.reserve := requestWidth (by decide)

def ends52 : List ℕ := [2308, 2313]

theorem inside52 : Research6966.TerminalBanks.inside src52.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover52 : Cover (Triangular src52) 2313 2308 ends52 := triangleCover (by decide +kernel)

def src520 : Request := ⟨⟨⟨1747,2438,522,118200⟩,159287868915712,962882398143⟩,1,2,1,308048,11⟩

theorem rank520 : P3_7_1.BankOK src520.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1747_2438_522 118200

theorem width520 : Lower6960.HelperSource.WidthGuard src520.bank 179730 2308 src520.reserve := requestWidth (by decide)

def ends520 : List ℕ := [2308, 2309, 2313]

theorem inside520 : Research6966.TerminalBanks.inside src520.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover520 : Cover (Triangular src520) 2313 2308 ends520 := triangleCover (by decide +kernel)

def src521 : Request := ⟨⟨⟨1748,2439,519,163386⟩,158792317665280,959825484853⟩,3,2,1,308048,11⟩

theorem rank521 : P3_7_1.BankOK src521.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1748_2439_519 163386

theorem width521 : Lower6960.HelperSource.WidthGuard src521.bank 179730 2308 src521.reserve := requestWidth (by decide)

def ends521 : List ℕ := [2308, 2309, 2313]

theorem inside521 : Research6966.TerminalBanks.inside src521.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover521 : Cover (Triangular src521) 2313 2308 ends521 := triangleCover (by decide +kernel)

def src522 : Request := ⟨⟨⟨2098,2927,626,138004⟩,275459206021120,1997555002095⟩,3,2,1,308048,11⟩

theorem rank522 : P3_7_1.BankOK src522.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2098_2927_626 138004

theorem width522 : Lower6960.HelperSource.WidthGuard src522.bank 179730 2308 src522.reserve := requestWidth (by decide)

def ends522 : List ℕ := [2308, 2309, 2313]

theorem inside522 : Research6966.TerminalBanks.inside src522.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover522 : Cover (Triangular src522) 2313 2308 ends522 := triangleCover (by decide +kernel)

def src523 : Request := ⟨⟨⟨1751,2442,527,186669⟩,161271009771520,975196209190⟩,4,2,1,308048,11⟩

theorem rank523 : P3_7_1.BankOK src523.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 186669

theorem width523 : Lower6960.HelperSource.WidthGuard src523.bank 179730 2308 src523.reserve := requestWidth (by decide)

def ends523 : List ℕ := [2308, 2309, 2313]

theorem inside523 : Research6966.TerminalBanks.inside src523.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover523 : Cover (Triangular src523) 2313 2308 ends523 := triangleCover (by decide +kernel)

def src524 : Request := ⟨⟨⟨2653,3700,798,236272⟩,560158111170560,5130982725704⟩,10,2,1,308048,11⟩

theorem rank524 : P3_7_1.BankOK src524.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2653_3700_798 236272

theorem width524 : Lower6960.HelperSource.WidthGuard src524.bank 179730 2308 src524.reserve := requestWidth (by decide)

def ends524 : List ℕ := [2308, 2309, 2313]

theorem inside524 : Research6966.TerminalBanks.inside src524.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover524 : Cover (Triangular src524) 2313 2308 ends524 := triangleCover (by decide +kernel)

def src525 : Request := ⟨⟨⟨3199,4461,963,205372⟩,982363631779840,10845763138208⟩,10,2,1,308048,11⟩

theorem rank525 : P3_7_1.BankOK src525.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3199_4461_963 205372

theorem width525 : Lower6960.HelperSource.WidthGuard src525.bank 179730 2308 src525.reserve := requestWidth (by decide)

def ends525 : List ℕ := [2308, 2309, 2313]




theorem cover525 : Cover (Triangular src525) 2313 2308 ends525 := triangleCover (by decide +kernel)

def src526 : Request := ⟨⟨⟨3201,4465,963,340025⟩,983737851445248,10877088344236⟩,16,2,1,308048,11⟩

theorem rank526 : P3_7_1.BankOK src526.bank := 
  _root_.Research6970.Height2313.Physical.bank_3201_4465_963 340025

theorem width526 : Lower6960.HelperSource.WidthGuard src526.bank 179730 2308 src526.reserve := requestWidth (by decide)

def ends526 : List ℕ := [2308, 2309, 2313]




theorem cover526 : Cover (Triangular src526) 2313 2308 ends526 := triangleCover (by decide +kernel)

def src527 : Request := ⟨⟨⟨3950,5512,1177,278054⟩,1834497685585920,25056506437126⟩,16,2,1,308048,11⟩

theorem rank527 : P3_7_1.BankOK src527.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3950_5512_1177 278054

theorem width527 : Lower6960.HelperSource.WidthGuard src527.bank 179730 2308 src527.reserve := requestWidth (by decide)

def ends527 : List ℕ := [2308, 2309, 2313]




theorem cover527 : Cover (Triangular src527) 2313 2308 ends527 := triangleCover (by decide +kernel)

def src528 : Request := ⟨⟨⟨4823,6729,1453,304200⟩,3366818370027520,56124300799930⟩,20,2,1,308048,11⟩

theorem rank528 : P3_7_1.BankOK src528.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4823_6729_1453 304200

theorem width528 : Lower6960.HelperSource.WidthGuard src528.bank 179730 2308 src528.reserve := requestWidth (by decide)

def ends528 : List ℕ := [2308, 2309, 2313]




theorem cover528 : Cover (Triangular src528) 2313 2308 ends528 := triangleCover (by decide +kernel)

def src529 : Request := ⟨⟨⟨5703,7954,1716,352297⟩,5560379779317760,109473260530676⟩,25,2,1,308048,11⟩

theorem rank529 : P3_7_1.BankOK src529.bank := 
  _root_.Research6970.Height2313.Physical.bank_5703_7954_1716 352297

theorem width529 : Lower6960.HelperSource.WidthGuard src529.bank 179730 2308 src529.reserve := requestWidth (by decide)

def ends529 : List ℕ := [2308, 2309, 2313]




theorem cover529 : Cover (Triangular src529) 2313 2308 ends529 := triangleCover (by decide +kernel)

def src53 : Request := ⟨⟨⟨2588,3594,793,26442⟩,527385327042560,4649882428564⟩,63,2,1,257319,45⟩

theorem rank53 : P3_7_1.BankOK src53.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3594_793 26442

theorem width53 : Lower6960.HelperSource.WidthGuard src53.bank 179730 2308 src53.reserve := requestWidth (by decide)

def ends53 : List ℕ := [2308, 2309, 2313]

theorem inside53 : Research6966.TerminalBanks.inside src53.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover53 : Cover (Triangular src53) 2313 2308 ends53 := triangleCover (by decide +kernel)

def src530 : Request := ⟨⟨⟨1751,2442,527,111192⟩,161271009771520,975196209190⟩,0,2,1,308107,10⟩

theorem rank530 : P3_7_1.BankOK src530.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 111192

theorem width530 : Lower6960.HelperSource.WidthGuard src530.bank 179730 2308 src530.reserve := requestWidth (by decide)

def ends530 : List ℕ := [2308, 2309, 2313]

theorem inside530 : Research6966.TerminalBanks.inside src530.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover530 : Cover (Triangular src530) 2313 2308 ends530 := triangleCover (by decide +kernel)

def src531 : Request := ⟨⟨⟨1751,2442,527,125150⟩,161271009771520,975196209190⟩,1,2,1,308107,10⟩

theorem rank531 : P3_7_1.BankOK src531.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 125150

theorem width531 : Lower6960.HelperSource.WidthGuard src531.bank 179730 2308 src531.reserve := requestWidth (by decide)

def ends531 : List ℕ := [2308, 2309, 2313]

theorem inside531 : Research6966.TerminalBanks.inside src531.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover531 : Cover (Triangular src531) 2313 2308 ends531 := triangleCover (by decide +kernel)

def src532 : Request := ⟨⟨⟨1751,2442,527,143067⟩,161271009771520,975196209190⟩,2,2,1,308107,10⟩

theorem rank532 : P3_7_1.BankOK src532.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 143067

theorem width532 : Lower6960.HelperSource.WidthGuard src532.bank 179730 2308 src532.reserve := requestWidth (by decide)

def ends532 : List ℕ := [2308, 2309, 2313]

theorem inside532 : Research6966.TerminalBanks.inside src532.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover532 : Cover (Triangular src532) 2313 2308 ends532 := triangleCover (by decide +kernel)

def src533 : Request := ⟨⟨⟨2103,2932,632,161843⟩,278949423742976,2023557179736⟩,4,2,1,308107,10⟩

theorem rank533 : P3_7_1.BankOK src533.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2103_2932_632 161843

theorem width533 : Lower6960.HelperSource.WidthGuard src533.bank 179730 2308 src533.reserve := requestWidth (by decide)

def ends533 : List ℕ := [2308, 2309, 2313]

theorem inside533 : Research6966.TerminalBanks.inside src533.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover533 : Cover (Triangular src533) 2313 2308 ends533 := triangleCover (by decide +kernel)

def src534 : Request := ⟨⟨⟨2101,2930,632,208787⟩,278356530298880,2019119590628⟩,6,2,1,308107,10⟩

theorem rank534 : P3_7_1.BankOK src534.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 208787

theorem width534 : Lower6960.HelperSource.WidthGuard src534.bank 179730 2308 src534.reserve := requestWidth (by decide)

def ends534 : List ℕ := [2308, 2309, 2313]

theorem inside534 : Research6966.TerminalBanks.inside src534.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover534 : Cover (Triangular src534) 2313 2308 ends534 := triangleCover (by decide +kernel)

def src535 : Request := ⟨⟨⟨2602,3628,783,176970⟩,528664175312896,4745819470168⟩,6,2,1,308107,10⟩

theorem rank535 : P3_7_1.BankOK src535.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2602_3628_783 176970

theorem width535 : Lower6960.HelperSource.WidthGuard src535.bank 179730 2308 src535.reserve := requestWidth (by decide)

def ends535 : List ℕ := [2308, 2309, 2313]

theorem inside535 : Research6966.TerminalBanks.inside src535.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover535 : Cover (Triangular src535) 2313 2308 ends535 := triangleCover (by decide +kernel)

def src536 : Request := ⟨⟨⟨3201,4465,963,220508⟩,983737851445248,10877088344236⟩,10,2,1,308107,10⟩

theorem rank536 : P3_7_1.BankOK src536.bank := 
  _root_.Research6970.Height2313.Physical.bank_3201_4465_963 220508

theorem width536 : Lower6960.HelperSource.WidthGuard src536.bank 179730 2308 src536.reserve := requestWidth (by decide)

def ends536 : List ℕ := [2308, 2309, 2313]




theorem cover536 : Cover (Triangular src536) 2313 2308 ends536 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources44

section Pack_R6970Height2313CommonSources45

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src537 : Request := ⟨⟨⟨2604,3632,783,402656⟩,529573399756800,4762676203208⟩,13,2,1,308107,10⟩

theorem rank537 : P3_7_1.BankOK src537.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3632_783 402656

theorem width537 : Lower6960.HelperSource.WidthGuard src537.bank 179730 2308 src537.reserve := requestWidth (by decide)

def ends537 : List ℕ := [2308, 2309, 2313]

theorem inside537 : Research6966.TerminalBanks.inside src537.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover537 : Cover (Triangular src537) 2313 2308 ends537 := triangleCover (by decide +kernel)

def src538 : Request := ⟨⟨⟨3952,5512,1189,248182⟩,1850839393894400,25255771038451⟩,13,2,1,308107,10⟩

theorem rank538 : P3_7_1.BankOK src538.bank := 
  _root_.Research6970.Height2313.Physical.bank_3952_5512_1189 248182

theorem width538 : Lower6960.HelperSource.WidthGuard src538.bank 179730 2308 src538.reserve := requestWidth (by decide)

def ends538 : List ℕ := [2308, 2309, 2313]




theorem cover538 : Cover (Triangular src538) 2313 2308 ends538 := triangleCover (by decide +kernel)

def src539 : Request := ⟨⟨⟨3953,5513,1189,290549⟩,1851887082536960,25270519066641⟩,16,2,1,308107,10⟩

theorem rank539 : P3_7_1.BankOK src539.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3953_5513_1189 290549

theorem width539 : Lower6960.HelperSource.WidthGuard src539.bank 179730 2308 src539.reserve := requestWidth (by decide)

def ends539 : List ℕ := [2308, 2309, 2313]




theorem cover539 : Cover (Triangular src539) 2313 2308 ends539 := triangleCover (by decide +kernel)

def src54 : Request := ⟨⟨⟨2602,3626,793,28173⟩,533793196998656,4784491173220⟩,63,2,1,257319,45⟩

theorem rank54 : P3_7_1.BankOK src54.bank := 
  _root_.Research6970.Height2313.Physical.bank_2602_3626_793 28173

theorem width54 : Lower6960.HelperSource.WidthGuard src54.bank 179730 2308 src54.reserve := requestWidth (by decide)

def ends54 : List ℕ := [2308, 2309, 2313]

theorem inside54 : Research6966.TerminalBanks.inside src54.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover54 : Cover (Triangular src54) 2313 2308 ends54 := triangleCover (by decide +kernel)

def src540 : Request := ⟨⟨⟨4800,6694,1445,326939⟩,3317023033262080,54952917346103⟩,20,2,1,308107,10⟩

theorem rank540 : P3_7_1.BankOK src540.bank := by
  simpa only [src540, _root_.Research6969.TransitionBanks.bank321] using _root_.Research6969.TransitionBanks.rank321 326939

theorem width540 : Lower6960.HelperSource.WidthGuard src540.bank 179730 2308 src540.reserve := requestWidth (by decide)

def ends540 : List ℕ := [2308, 2309, 2313]




theorem cover540 : Cover (Triangular src540) 2313 2308 ends540 := triangleCover (by decide +kernel)

def src541 : Request := ⟨⟨⟨1451,2024,436,129947⟩,91708090482688,459881825688⟩,0,2,1,308161,9⟩

theorem rank541 : P3_7_1.BankOK src541.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1451_2024_436 129947

theorem width541 : Lower6960.HelperSource.WidthGuard src541.bank 179730 2308 src541.reserve := requestWidth (by decide)

def ends541 : List ℕ := [2308, 2309, 2313]

theorem inside541 : Research6966.TerminalBanks.inside src541.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover541 : Cover (Triangular src541) 2313 2308 ends541 := triangleCover (by decide +kernel)

def src542 : Request := ⟨⟨⟨1749,2440,520,137644⟩,159229006315520,962537056707⟩,1,2,1,308161,9⟩

theorem rank542 : P3_7_1.BankOK src542.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1749_2440_520 137644

theorem width542 : Lower6960.HelperSource.WidthGuard src542.bank 179730 2308 src542.reserve := requestWidth (by decide)

def ends542 : List ℕ := [2308, 2309, 2313]

theorem inside542 : Research6966.TerminalBanks.inside src542.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover542 : Cover (Triangular src542) 2313 2308 ends542 := triangleCover (by decide +kernel)

def src543 : Request := ⟨⟨⟨2100,2929,632,141299⟩,278060332482560,2016903279333⟩,2,2,1,308161,9⟩

theorem rank543 : P3_7_1.BankOK src543.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2100_2929_632 141299

theorem width543 : Lower6960.HelperSource.WidthGuard src543.bank 179730 2308 src543.reserve := requestWidth (by decide)

def ends543 : List ℕ := [2308, 2309, 2313]

theorem inside543 : Research6966.TerminalBanks.inside src543.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover543 : Cover (Triangular src543) 2313 2308 ends543 := triangleCover (by decide +kernel)

def src544 : Request := ⟨⟨⟨2101,2930,632,155558⟩,278356530298880,2019119590628⟩,3,2,1,308161,9⟩

theorem rank544 : P3_7_1.BankOK src544.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 155558

theorem width544 : Lower6960.HelperSource.WidthGuard src544.bank 179730 2308 src544.reserve := requestWidth (by decide)

def ends544 : List ℕ := [2308, 2309, 2313]

theorem inside544 : Research6966.TerminalBanks.inside src544.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover544 : Cover (Triangular src544) 2313 2308 ends544 := triangleCover (by decide +kernel)

def src545 : Request := ⟨⟨⟨1753,2445,527,213730⟩,161683200802816,979055562622⟩,4,2,1,308161,9⟩

theorem rank545 : P3_7_1.BankOK src545.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2445_527 213730

theorem width545 : Lower6960.HelperSource.WidthGuard src545.bank 179730 2308 src545.reserve := requestWidth (by decide)

def ends545 : List ℕ := [2308, 2309, 2313]

theorem inside545 : Research6966.TerminalBanks.inside src545.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover545 : Cover (Triangular src545) 2313 2308 ends545 := triangleCover (by decide +kernel)

def src546 : Request := ⟨⟨⟨2099,2929,630,173456⟩,277094667386880,2011923818496⟩,4,2,1,308161,9⟩

theorem rank546 : P3_7_1.BankOK src546.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2099_2929_630 173456

theorem width546 : Lower6960.HelperSource.WidthGuard src546.bank 179730 2308 src546.reserve := requestWidth (by decide)

def ends546 : List ℕ := [2308, 2309, 2313]

theorem inside546 : Research6966.TerminalBanks.inside src546.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover546 : Cover (Triangular src546) 2313 2308 ends546 := triangleCover (by decide +kernel)

def src547 : Request := ⟨⟨⟨2601,3628,783,225366⟩,528209871372288,4745819470168⟩,8,2,1,308161,9⟩

theorem rank547 : P3_7_1.BankOK src547.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3628_783 225366

theorem width547 : Lower6960.HelperSource.WidthGuard src547.bank 179730 2308 src547.reserve := requestWidth (by decide)

def ends547 : List ℕ := [2308, 2309, 2313]

theorem inside547 : Research6966.TerminalBanks.inside src547.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover547 : Cover (Triangular src547) 2313 2308 ends547 := triangleCover (by decide +kernel)

def src548 : Request := ⟨⟨⟨3200,4465,955,239317⟩,976818203525120,10806484661095⟩,10,2,1,308161,9⟩

theorem rank548 : P3_7_1.BankOK src548.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3200_4465_955 239317

theorem width548 : Lower6960.HelperSource.WidthGuard src548.bank 179730 2308 src548.reserve := requestWidth (by decide)

def ends548 : List ℕ := [2308, 2309, 2313]




theorem cover548 : Cover (Triangular src548) 2313 2308 ends548 := triangleCover (by decide +kernel)

def src549 : Request := ⟨⟨⟨3201,4465,963,293853⟩,983737851445248,10877088344236⟩,13,2,1,308161,9⟩

theorem rank549 : P3_7_1.BankOK src549.bank := 
  _root_.Research6970.Height2313.Physical.bank_3201_4465_963 293853

theorem width549 : Lower6960.HelperSource.WidthGuard src549.bank 179730 2308 src549.reserve := requestWidth (by decide)

def ends549 : List ℕ := [2308, 2309, 2313]




theorem cover549 : Cover (Triangular src549) 2313 2308 ends549 := triangleCover (by decide +kernel)

def src55 : Request := ⟨⟨⟨2713,3764,846,31417⟩,615629136855040,5674388321050⟩,70,2,1,257515,45⟩

theorem rank55 : P3_7_1.BankOK src55.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2713_3764_846 31417

theorem width55 : Lower6960.HelperSource.WidthGuard src55.bank 179730 2308 src55.reserve := requestWidth (by decide)

def ends55 : List ℕ := [2308, 2313]

theorem inside55 : Research6966.TerminalBanks.inside src55.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover55 : Cover (Triangular src55) 2313 2308 ends55 := triangleCover (by decide +kernel)

def src550 : Request := ⟨⟨⟨3207,4473,963,389117⟩,987866575405056,10939923188772⟩,16,2,1,308161,9⟩

theorem rank550 : P3_7_1.BankOK src550.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3207_4473_963 389117

theorem width550 : Lower6960.HelperSource.WidthGuard src550.bank 179730 2308 src550.reserve := requestWidth (by decide)

def ends550 : List ℕ := [2308, 2309, 2313]




theorem cover550 : Cover (Triangular src550) 2313 2308 ends550 := triangleCover (by decide +kernel)

def src551 : Request := ⟨⟨⟨5502,7674,1657,443278⟩,4996490915479552,94920001073870⟩,27,2,1,308161,9⟩

theorem rank551 : P3_7_1.BankOK src551.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5502_7674_1657 443278

theorem width551 : Lower6960.HelperSource.WidthGuard src551.bank 179730 2308 src551.reserve := requestWidth (by decide)

def ends551 : List ℕ := [2308, 2309, 2313]




theorem cover551 : Cover (Triangular src551) 2313 2308 ends551 := triangleCover (by decide +kernel)

def src552 : Request := ⟨⟨⟨1751,2442,527,126605⟩,161271009771520,975196209190⟩,0,2,1,308209,8⟩

theorem rank552 : P3_7_1.BankOK src552.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 126605

theorem width552 : Lower6960.HelperSource.WidthGuard src552.bank 179730 2308 src552.reserve := requestWidth (by decide)

def ends552 : List ℕ := [2308, 2309, 2313]

theorem inside552 : Research6966.TerminalBanks.inside src552.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover552 : Cover (Triangular src552) 2313 2308 ends552 := triangleCover (by decide +kernel)

def src553 : Request := ⟨⟨⟨1751,2442,527,142460⟩,161271009771520,975196209190⟩,1,2,1,308209,8⟩

theorem rank553 : P3_7_1.BankOK src553.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_527 142460

theorem width553 : Lower6960.HelperSource.WidthGuard src553.bank 179730 2308 src553.reserve := requestWidth (by decide)

def ends553 : List ℕ := [2308, 2309, 2313]

theorem inside553 : Research6966.TerminalBanks.inside src553.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover553 : Cover (Triangular src553) 2313 2308 ends553 := triangleCover (by decide +kernel)

def src554 : Request := ⟨⟨⟨1753,2445,527,162619⟩,161683200802816,979055562622⟩,2,2,1,308209,8⟩

theorem rank554 : P3_7_1.BankOK src554.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2445_527 162619

theorem width554 : Lower6960.HelperSource.WidthGuard src554.bank 179730 2308 src554.reserve := requestWidth (by decide)

def ends554 : List ℕ := [2308, 2309, 2313]

theorem inside554 : Research6966.TerminalBanks.inside src554.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover554 : Cover (Triangular src554) 2313 2308 ends554 := triangleCover (by decide +kernel)

def src555 : Request := ⟨⟨⟨2102,2932,632,184183⟩,278652894052352,2023557179736⟩,4,2,1,308209,8⟩

theorem rank555 : P3_7_1.BankOK src555.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2102_2932_632 184183

theorem width555 : Lower6960.HelperSource.WidthGuard src555.bank 179730 2308 src555.reserve := requestWidth (by decide)

def ends555 : List ℕ := [2308, 2309, 2313]

theorem inside555 : Research6966.TerminalBanks.inside src555.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover555 : Cover (Triangular src555) 2313 2308 ends555 := triangleCover (by decide +kernel)

def src556 : Request := ⟨⟨⟨2105,2936,632,237104⟩,279542980935680,2032452241748⟩,6,2,1,308209,8⟩

theorem rank556 : P3_7_1.BankOK src556.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2936_632 237104

theorem width556 : Lower6960.HelperSource.WidthGuard src556.bank 179730 2308 src556.reserve := requestWidth (by decide)

def ends556 : List ℕ := [2308, 2309, 2313]

theorem inside556 : Research6966.TerminalBanks.inside src556.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover556 : Cover (Triangular src556) 2313 2308 ends556 := triangleCover (by decide +kernel)

def src557 : Request := ⟨⟨⟨2601,3628,783,201477⟩,528209871372288,4745819470168⟩,6,2,1,308209,8⟩

theorem rank557 : P3_7_1.BankOK src557.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2601_3628_783 201477

theorem width557 : Lower6960.HelperSource.WidthGuard src557.bank 179730 2308 src557.reserve := requestWidth (by decide)

def ends557 : List ℕ := [2308, 2309, 2313]

theorem inside557 : Research6966.TerminalBanks.inside src557.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover557 : Cover (Triangular src557) 2313 2308 ends557 := triangleCover (by decide +kernel)

def src558 : Request := ⟨⟨⟨2607,3636,783,295705⟩,530938777829376,4779573597624⟩,10,2,1,308209,8⟩

theorem rank558 : P3_7_1.BankOK src558.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2607_3636_783 295705

theorem width558 : Lower6960.HelperSource.WidthGuard src558.bank 179730 2308 src558.reserve := requestWidth (by decide)

def ends558 : List ℕ := [2308, 2309, 2313]

theorem inside558 : Research6966.TerminalBanks.inside src558.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover558 : Cover (Triangular src558) 2313 2308 ends558 := triangleCover (by decide +kernel)

def src559 : Request := ⟨⟨⟨3201,4465,963,250967⟩,983737851445248,10877088344236⟩,10,2,1,308209,8⟩

theorem rank559 : P3_7_1.BankOK src559.bank := 
  _root_.Research6970.Height2313.Physical.bank_3201_4465_963 250967

theorem width559 : Lower6960.HelperSource.WidthGuard src559.bank 179730 2308 src559.reserve := requestWidth (by decide)

def ends559 : List ℕ := [2308, 2309, 2313]




theorem cover559 : Cover (Triangular src559) 2313 2308 ends559 := triangleCover (by decide +kernel)

def src56 : Request := ⟨⟨⟨2821,3913,876,28703⟩,689878117122048,6606676994431⟩,71,2,1,257319,45⟩

theorem rank56 : P3_7_1.BankOK src56.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2821_3913_876 28703

theorem width56 : Lower6960.HelperSource.WidthGuard src56.bank 179730 2308 src56.reserve := requestWidth (by decide)

def ends56 : List ℕ := [2308, 2309, 2313]

theorem inside56 : Research6966.TerminalBanks.inside src56.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover56 : Cover (Triangular src56) 2313 2308 ends56 := triangleCover (by decide +kernel)

def src560 : Request := ⟨⟨⟨3952,5512,1189,282426⟩,1850839393894400,25255771038451⟩,13,2,1,308209,8⟩

theorem rank560 : P3_7_1.BankOK src560.bank := 
  _root_.Research6970.Height2313.Physical.bank_3952_5512_1189 282426

theorem width560 : Lower6960.HelperSource.WidthGuard src560.bank 179730 2308 src560.reserve := requestWidth (by decide)

def ends560 : List ℕ := [2308, 2309, 2313]




theorem cover560 : Cover (Triangular src560) 2313 2308 ends560 := triangleCover (by decide +kernel)

def src561 : Request := ⟨⟨⟨3956,5518,1189,330621⟩,1855032020172800,25344347044466⟩,16,2,1,308209,8⟩

theorem rank561 : P3_7_1.BankOK src561.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3956_5518_1189 330621

theorem width561 : Lower6960.HelperSource.WidthGuard src561.bank 179730 2308 src561.reserve := requestWidth (by decide)

def ends561 : List ℕ := [2308, 2309, 2313]




theorem cover561 : Cover (Triangular src561) 2313 2308 ends561 := triangleCover (by decide +kernel)

def src562 : Request := ⟨⟨⟨4805,6702,1445,372019⟩,3324756809482240,55164552586387⟩,20,2,1,308209,8⟩

theorem rank562 : P3_7_1.BankOK src562.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4805_6702_1445 372019

theorem width562 : Lower6960.HelperSource.WidthGuard src562.bank 179730 2308 src562.reserve := requestWidth (by decide)

def ends562 : List ℕ := [2308, 2309, 2313]




theorem cover562 : Cover (Triangular src562) 2313 2308 ends562 := triangleCover (by decide +kernel)

def src563 : Request := ⟨⟨⟨1479,2063,444,144506⟩,97045462384640,495976619495⟩,0,2,1,308251,7⟩

theorem rank563 : P3_7_1.BankOK src563.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1479_2063_444 144506

theorem width563 : Lower6960.HelperSource.WidthGuard src563.bank 179730 2308 src563.reserve := requestWidth (by decide)

def ends563 : List ℕ := [2308, 2309, 2313]

theorem inside563 : Research6966.TerminalBanks.inside src563.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover563 : Cover (Triangular src563) 2313 2308 ends563 := triangleCover (by decide +kernel)

def src564 : Request := ⟨⟨⟨1749,2440,520,154960⟩,159229006315520,962537056707⟩,1,2,1,308251,7⟩

theorem rank564 : P3_7_1.BankOK src564.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1749_2440_520 154960

theorem width564 : Lower6960.HelperSource.WidthGuard src564.bank 179730 2308 src564.reserve := requestWidth (by decide)

def ends564 : List ℕ := [2308, 2309, 2313]

theorem inside564 : Research6966.TerminalBanks.inside src564.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover564 : Cover (Triangular src564) 2313 2308 ends564 := triangleCover (by decide +kernel)

def src565 : Request := ⟨⟨⟨2101,2930,632,159627⟩,278356530298880,2019119590628⟩,2,2,1,308251,7⟩

theorem rank565 : P3_7_1.BankOK src565.bank := 
  _root_.Research6970.Height2313.Physical.bank_2101_2930_632 159627

theorem width565 : Lower6960.HelperSource.WidthGuard src565.bank 179730 2308 src565.reserve := requestWidth (by decide)

def ends565 : List ℕ := [2308, 2309, 2313]

theorem inside565 : Research6966.TerminalBanks.inside src565.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover565 : Cover (Triangular src565) 2313 2308 ends565 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources45

section Pack_R6970Height2313CommonSources47

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src595 : Request := ⟨⟨⟨6473,9030,1946,621116⟩,8124203203297280,181672708620125⟩,32,2,1,308319,5⟩

theorem rank595 : P3_7_1.BankOK src595.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6473_9030_1946 621116

theorem width595 : Lower6960.HelperSource.WidthGuard src595.bank 179730 2308 src595.reserve := requestWidth (by decide)

def ends595 : List ℕ := [2308, 2309, 2313]




theorem cover595 : Cover (Triangular src595) 2313 2308 ends595 := triangleCover (by decide +kernel)

def src596 : Request := ⟨⟨⟨1778,2480,534,157253⟩,168569368739840,1035458553608⟩,0,2,1,308344,4⟩

theorem rank596 : P3_7_1.BankOK src596.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1778_2480_534 157253

theorem width596 : Lower6960.HelperSource.WidthGuard src596.bank 179730 2308 src596.reserve := requestWidth (by decide)

def ends596 : List ℕ := [2308, 2309, 2313]

theorem inside596 : Research6966.TerminalBanks.inside src596.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover596 : Cover (Triangular src596) 2313 2308 ends596 := triangleCover (by decide +kernel)

def src597 : Request := ⟨⟨⟨1751,2442,526,177334⟩,161038008844288,973753382962⟩,1,2,1,308344,4⟩

theorem rank597 : P3_7_1.BankOK src597.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1751_2442_526 177334

theorem width597 : Lower6960.HelperSource.WidthGuard src597.bank 179730 2308 src597.reserve := requestWidth (by decide)

def ends597 : List ℕ := [2308, 2309, 2313]

theorem inside597 : Research6966.TerminalBanks.inside src597.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover597 : Cover (Triangular src597) 2313 2308 ends597 := triangleCover (by decide +kernel)

def src598 : Request := ⟨⟨⟨1755,2448,527,202236⟩,162095945482240,982925287294⟩,2,2,1,308344,4⟩

theorem rank598 : P3_7_1.BankOK src598.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 202236

theorem width598 : Lower6960.HelperSource.WidthGuard src598.bank 179730 2308 src598.reserve := requestWidth (by decide)

def ends598 : List ℕ := [2308, 2309, 2313]

theorem inside598 : Research6966.TerminalBanks.inside src598.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover598 : Cover (Triangular src598) 2313 2308 ends598 := triangleCover (by decide +kernel)

def src599 : Request := ⟨⟨⟨2105,2936,632,229103⟩,279542980935680,2032452241748⟩,4,2,1,308344,4⟩

theorem rank599 : P3_7_1.BankOK src599.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2936_632 229103

theorem width599 : Lower6960.HelperSource.WidthGuard src599.bank 179730 2308 src599.reserve := requestWidth (by decide)

def ends599 : List ℕ := [2308, 2309, 2313]

theorem inside599 : Research6966.TerminalBanks.inside src599.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover599 : Cover (Triangular src599) 2313 2308 ends599 := triangleCover (by decide +kernel)

def src6 : Request := ⟨⟨⟨2599,3610,793,24142⟩,532416647659520,4716860104828⟩,63,1,1,128659,49⟩

theorem rank6 : P3_7_1.BankOK src6.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2599_3610_793 24142

theorem width6 : Lower6960.HelperSource.WidthGuard src6.bank 179730 2308 src6.reserve := requestWidth (by decide)

def ends6 : List ℕ := [2308, 2309, 2313]

theorem inside6 : Research6966.TerminalBanks.inside src6.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover6 : Cover (Triangular src6) 2313 2308 ends6 := triangleCover (by decide +kernel)

def src60 : Request := ⟨⟨⟨2307,3207,702,28173⟩,371690023944192,2930605494152⟩,63,2,1,257319,48⟩

theorem rank60 : P3_7_1.BankOK src60.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2307_3207_702 28173

theorem width60 : Lower6960.HelperSource.WidthGuard src60.bank 179730 2308 src60.reserve := requestWidth (by decide)

def ends60 : List ℕ := [2308, 2309, 2313]

theorem inside60 : Research6966.TerminalBanks.inside src60.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover60 : Cover (Triangular src60) 2313 2308 ends60 := triangleCover (by decide +kernel)

def src600 : Request := ⟨⟨⟨2142,2988,644,288468⟩,294843626291200,2182334193151⟩,6,2,1,308344,4⟩

theorem rank600 : P3_7_1.BankOK src600.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 288468

theorem width600 : Lower6960.HelperSource.WidthGuard src600.bank 179730 2308 src600.reserve := requestWidth (by decide)

def ends600 : List ℕ := [2308, 2309, 2313]

theorem inside600 : Research6966.TerminalBanks.inside src600.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover600 : Cover (Triangular src600) 2313 2308 ends600 := triangleCover (by decide +kernel)

def src601 : Request := ⟨⟨⟨2604,3632,783,250768⟩,529573399756800,4762676203208⟩,6,2,1,308344,4⟩

theorem rank601 : P3_7_1.BankOK src601.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3632_783 250768

theorem width601 : Lower6960.HelperSource.WidthGuard src601.bank 179730 2308 src601.reserve := requestWidth (by decide)

def ends601 : List ℕ := [2308, 2309, 2313]

theorem inside601 : Research6966.TerminalBanks.inside src601.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover601 : Cover (Triangular src601) 2313 2308 ends601 := triangleCover (by decide +kernel)

def src602 : Request := ⟨⟨⟨3204,4469,963,312366⟩,985801076244480,10908475007192⟩,10,2,1,308344,4⟩

theorem rank602 : P3_7_1.BankOK src602.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3204_4469_963 312366

theorem width602 : Lower6960.HelperSource.WidthGuard src602.bank 179730 2308 src602.reserve := requestWidth (by decide)

def ends602 : List ℕ := [2308, 2309, 2313]




theorem cover602 : Cover (Triangular src602) 2313 2308 ends602 := triangleCover (by decide +kernel)

def src603 : Request := ⟨⟨⟨2653,3700,797,537785⟩,559623274233856,5125966017010⟩,13,2,1,308344,4⟩

theorem rank603 : P3_7_1.BankOK src603.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2653_3700_797 537785

theorem width603 : Lower6960.HelperSource.WidthGuard src603.bank 179730 2308 src603.reserve := requestWidth (by decide)

def ends603 : List ℕ := [2308, 2309, 2313]




theorem cover603 : Cover (Triangular src603) 2313 2308 ends603 := triangleCover (by decide +kernel)

def src604 : Request := ⟨⟨⟨3952,5513,1188,351669⟩,1849652950859776,25253930148456⟩,13,2,1,308344,4⟩

theorem rank604 : P3_7_1.BankOK src604.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3952_5513_1188 351669

theorem width604 : Lower6960.HelperSource.WidthGuard src604.bank 179730 2308 src604.reserve := requestWidth (by decide)

def ends604 : List ℕ := [2308, 2309, 2313]




theorem cover604 : Cover (Triangular src604) 2313 2308 ends604 := triangleCover (by decide +kernel)

def src605 : Request := ⟨⟨⟨3960,5524,1189,411383⟩,1859229637672960,25433134016061⟩,16,2,1,308344,4⟩

theorem rank605 : P3_7_1.BankOK src605.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3960_5524_1189 411383

theorem width605 : Lower6960.HelperSource.WidthGuard src605.bank 179730 2308 src605.reserve := requestWidth (by decide)

def ends605 : List ℕ := [2308, 2309, 2313]




theorem cover605 : Cover (Triangular src605) 2313 2308 ends605 := triangleCover (by decide +kernel)

def src606 : Request := ⟨⟨⟨5575,7776,1675,583343⟩,5188554299801600,99879364782516⟩,27,2,1,308344,4⟩

theorem rank606 : P3_7_1.BankOK src606.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5575_7776_1675 583343

theorem width606 : Lower6960.HelperSource.WidthGuard src606.bank 179730 2308 src606.reserve := requestWidth (by decide)

def ends606 : List ℕ := [2308, 2309, 2313]




theorem cover606 : Cover (Triangular src606) 2313 2308 ends606 := triangleCover (by decide +kernel)

def src607 : Request := ⟨⟨⟨1795,2504,539,164861⟩,173420665896960,1075830269751⟩,0,2,1,308364,3⟩

theorem rank607 : P3_7_1.BankOK src607.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1795_2504_539 164861

theorem width607 : Lower6960.HelperSource.WidthGuard src607.bank 179730 2308 src607.reserve := requestWidth (by decide)

def ends607 : List ℕ := [2308, 2309, 2313]

theorem inside607 : Research6966.TerminalBanks.inside src607.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover607 : Cover (Triangular src607) 2313 2308 ends607 := triangleCover (by decide +kernel)

def src608 : Request := ⟨⟨⟨1755,2448,527,185895⟩,162095945482240,982925287294⟩,1,2,1,308364,3⟩

theorem rank608 : P3_7_1.BankOK src608.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 185895

theorem width608 : Lower6960.HelperSource.WidthGuard src608.bank 179730 2308 src608.reserve := requestWidth (by decide)

def ends608 : List ℕ := [2308, 2309, 2313]

theorem inside608 : Research6966.TerminalBanks.inside src608.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover608 : Cover (Triangular src608) 2313 2308 ends608 := triangleCover (by decide +kernel)

def src609 : Request := ⟨⟨⟨1755,2448,527,212252⟩,162095945482240,982925287294⟩,2,2,1,308364,3⟩

theorem rank609 : P3_7_1.BankOK src609.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 212252

theorem width609 : Lower6960.HelperSource.WidthGuard src609.bank 179730 2308 src609.reserve := requestWidth (by decide)

def ends609 : List ℕ := [2308, 2309, 2313]

theorem inside609 : Research6966.TerminalBanks.inside src609.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover609 : Cover (Triangular src609) 2313 2308 ends609 := triangleCover (by decide +kernel)

def src61 : Request := ⟨⟨⟨2312,3207,724,23869⟩,382338138112000,3001726552718⟩,63,2,1,257319,48⟩

theorem rank61 : P3_7_1.BankOK src61.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2312_3207_724 23869

theorem width61 : Lower6960.HelperSource.WidthGuard src61.bank 179730 2308 src61.reserve := requestWidth (by decide)

def ends61 : List ℕ := [2309, 2313]

theorem inside61 : Research6966.TerminalBanks.inside src61.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover61 : Cover (Triangular src61) 2313 2308 ends61 := triangleCover (by decide +kernel)

def src610 : Request := ⟨⟨⟨2105,2936,632,240448⟩,279542980935680,2032452241748⟩,4,2,1,308364,3⟩

theorem rank610 : P3_7_1.BankOK src610.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2936_632 240448

theorem width610 : Lower6960.HelperSource.WidthGuard src610.bank 179730 2308 src610.reserve := requestWidth (by decide)

def ends610 : List ℕ := [2308, 2309, 2313]

theorem inside610 : Research6966.TerminalBanks.inside src610.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover610 : Cover (Triangular src610) 2313 2308 ends610 := triangleCover (by decide +kernel)

def src611 : Request := ⟨⟨⟨2142,2988,644,302767⟩,294843626291200,2182334193151⟩,6,2,1,308364,3⟩

theorem rank611 : P3_7_1.BankOK src611.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 302767

theorem width611 : Lower6960.HelperSource.WidthGuard src611.bank 179730 2308 src611.reserve := requestWidth (by decide)

def ends611 : List ℕ := [2308, 2309, 2313]

theorem inside611 : Research6966.TerminalBanks.inside src611.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover611 : Cover (Triangular src611) 2313 2308 ends611 := triangleCover (by decide +kernel)

def src612 : Request := ⟨⟨⟨2601,3628,781,263232⟩,527181781925888,4736360367482⟩,6,2,1,308364,3⟩

theorem rank612 : P3_7_1.BankOK src612.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3628_781 263232

theorem width612 : Lower6960.HelperSource.WidthGuard src612.bank 179730 2308 src612.reserve := requestWidth (by decide)

def ends612 : List ℕ := [2308, 2309, 2313]

theorem inside612 : Research6966.TerminalBanks.inside src612.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover612 : Cover (Triangular src612) 2313 2308 ends612 := triangleCover (by decide +kernel)

def src613 : Request := ⟨⟨⟨2653,3700,797,377345⟩,559623274233856,5125966017010⟩,10,2,1,308364,3⟩

theorem rank613 : P3_7_1.BankOK src613.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2653_3700_797 377345

theorem width613 : Lower6960.HelperSource.WidthGuard src613.bank 179730 2308 src613.reserve := requestWidth (by decide)

def ends613 : List ℕ := [2308, 2309, 2313]

theorem inside613 : Research6966.TerminalBanks.inside src613.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover613 : Cover (Triangular src613) 2313 2308 ends613 := triangleCover (by decide +kernel)

def src614 : Request := ⟨⟨⟨3204,4469,963,327861⟩,985801076244480,10908475007192⟩,10,2,1,308364,3⟩

theorem rank614 : P3_7_1.BankOK src614.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3204_4469_963 327861

theorem width614 : Lower6960.HelperSource.WidthGuard src614.bank 179730 2308 src614.reserve := requestWidth (by decide)

def ends614 : List ℕ := [2308, 2309, 2313]




theorem cover614 : Cover (Triangular src614) 2313 2308 ends614 := triangleCover (by decide +kernel)

def src615 : Request := ⟨⟨⟨3953,5514,1187,369091⟩,1849512334196736,25252070181474⟩,13,2,1,308364,3⟩

theorem rank615 : P3_7_1.BankOK src615.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3953_5514_1187 369091

theorem width615 : Lower6960.HelperSource.WidthGuard src615.bank 179730 2308 src615.reserve := requestWidth (by decide)

def ends615 : List ℕ := [2308, 2309, 2313]




theorem cover615 : Cover (Triangular src615) 2313 2308 ends615 := triangleCover (by decide +kernel)

def src616 : Request := ⟨⟨⟨3960,5524,1189,431728⟩,1859229637672960,25433134016061⟩,16,2,1,308364,3⟩

theorem rank616 : P3_7_1.BankOK src616.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3960_5524_1189 431728

theorem width616 : Lower6960.HelperSource.WidthGuard src616.bank 179730 2308 src616.reserve := requestWidth (by decide)

def ends616 : List ℕ := [2308, 2309, 2313]




theorem cover616 : Cover (Triangular src616) 2313 2308 ends616 := triangleCover (by decide +kernel)

def src617 : Request := ⟨⟨⟨5574,7775,1674,612285⟩,5184111810969600,99791494771586⟩,27,2,1,308364,3⟩

theorem rank617 : P3_7_1.BankOK src617.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5574_7775_1674 612285

theorem width617 : Lower6960.HelperSource.WidthGuard src617.bank 179730 2308 src617.reserve := requestWidth (by decide)

def ends617 : List ℕ := [2308, 2309, 2313]




theorem cover617 : Cover (Triangular src617) 2313 2308 ends617 := triangleCover (by decide +kernel)

def src618 : Request := ⟨⟨⟨1796,2505,539,172662⟩,173636753817600,1077212992491⟩,0,2,1,308378,2⟩

theorem rank618 : P3_7_1.BankOK src618.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1796_2505_539 172662

theorem width618 : Lower6960.HelperSource.WidthGuard src618.bank 179730 2308 src618.reserve := requestWidth (by decide)

def ends618 : List ℕ := [2308, 2309, 2313]

theorem inside618 : Research6966.TerminalBanks.inside src618.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover618 : Cover (Triangular src618) 2313 2308 ends618 := triangleCover (by decide +kernel)

def src619 : Request := ⟨⟨⟨1755,2448,527,194704⟩,162095945482240,982925287294⟩,1,2,1,308378,2⟩

theorem rank619 : P3_7_1.BankOK src619.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2448_527 194704

theorem width619 : Lower6960.HelperSource.WidthGuard src619.bank 179730 2308 src619.reserve := requestWidth (by decide)

def ends619 : List ℕ := [2308, 2309, 2313]

theorem inside619 : Research6966.TerminalBanks.inside src619.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover619 : Cover (Triangular src619) 2313 2308 ends619 := triangleCover (by decide +kernel)

def src62 : Request := ⟨⟨⟨2287,3175,702,23574⟩,364515722002432,2837502581224⟩,63,2,1,257319,49⟩

theorem rank62 : P3_7_1.BankOK src62.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2287_3175_702 23574

theorem width62 : Lower6960.HelperSource.WidthGuard src62.bank 179730 2308 src62.reserve := requestWidth (by decide)

def ends62 : List ℕ := [2308, 2309, 2313]

theorem inside62 : Research6966.TerminalBanks.inside src62.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover62 : Cover (Triangular src62) 2313 2308 ends62 := triangleCover (by decide +kernel)

def src620 : Request := ⟨⟨⟨1785,2490,537,219841⟩,170783777751040,1053541809432⟩,2,2,1,308378,2⟩

theorem rank620 : P3_7_1.BankOK src620.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1785_2490_537 219841

theorem width620 : Lower6960.HelperSource.WidthGuard src620.bank 179730 2308 src620.reserve := requestWidth (by decide)

def ends620 : List ℕ := [2308, 2309, 2313]

theorem inside620 : Research6966.TerminalBanks.inside src620.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover620 : Cover (Triangular src620) 2313 2308 ends620 := triangleCover (by decide +kernel)

def src621 : Request := ⟨⟨⟨2105,2936,632,251833⟩,279542980935680,2032452241748⟩,4,2,1,308378,2⟩

theorem rank621 : P3_7_1.BankOK src621.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2936_632 251833

theorem width621 : Lower6960.HelperSource.WidthGuard src621.bank 179730 2308 src621.reserve := requestWidth (by decide)

def ends621 : List ℕ := [2308, 2309, 2313]

theorem inside621 : Research6966.TerminalBanks.inside src621.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover621 : Cover (Triangular src621) 2313 2308 ends621 := triangleCover (by decide +kernel)

def src622 : Request := ⟨⟨⟨2142,2988,644,317124⟩,294843626291200,2182334193151⟩,6,2,1,308378,2⟩

theorem rank622 : P3_7_1.BankOK src622.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 317124

theorem width622 : Lower6960.HelperSource.WidthGuard src622.bank 179730 2308 src622.reserve := requestWidth (by decide)

def ends622 : List ℕ := [2308, 2309, 2313]

theorem inside622 : Research6966.TerminalBanks.inside src622.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover622 : Cover (Triangular src622) 2313 2308 ends622 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources47

section Pack_R6970Height2313CommonSources48

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src623 : Request := ⟨⟨⟨2605,3634,782,275557⟩,529512502394880,4766365110730⟩,6,2,1,308378,2⟩

theorem rank623 : P3_7_1.BankOK src623.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2605_3634_782 275557

theorem width623 : Lower6960.HelperSource.WidthGuard src623.bank 179730 2308 src623.reserve := requestWidth (by decide)

def ends623 : List ℕ := [2308, 2309, 2313]

theorem inside623 : Research6966.TerminalBanks.inside src623.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover623 : Cover (Triangular src623) 2313 2308 ends623 := triangleCover (by decide +kernel)

def src624 : Request := ⟨⟨⟨2653,3700,797,395215⟩,559623274233856,5125966017010⟩,10,2,1,308378,2⟩

theorem rank624 : P3_7_1.BankOK src624.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2653_3700_797 395215

theorem width624 : Lower6960.HelperSource.WidthGuard src624.bank 179730 2308 src624.reserve := requestWidth (by decide)

def ends624 : List ℕ := [2308, 2309, 2313]

theorem inside624 : Research6966.TerminalBanks.inside src624.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover624 : Cover (Triangular src624) 2313 2308 ends624 := triangleCover (by decide +kernel)

def src625 : Request := ⟨⟨⟨3204,4469,963,343413⟩,985801076244480,10908475007192⟩,10,2,1,308378,2⟩

theorem rank625 : P3_7_1.BankOK src625.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3204_4469_963 343413

theorem width625 : Lower6960.HelperSource.WidthGuard src625.bank 179730 2308 src625.reserve := requestWidth (by decide)

def ends625 : List ℕ := [2308, 2309, 2313]




theorem cover625 : Cover (Triangular src625) 2313 2308 ends625 := triangleCover (by decide +kernel)

def src626 : Request := ⟨⟨⟨3953,5514,1187,386560⟩,1849512334196736,25252070181474⟩,13,2,1,308378,2⟩

theorem rank626 : P3_7_1.BankOK src626.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3953_5514_1187 386560

theorem width626 : Lower6960.HelperSource.WidthGuard src626.bank 179730 2308 src626.reserve := requestWidth (by decide)

def ends626 : List ℕ := [2308, 2309, 2313]




theorem cover626 : Cover (Triangular src626) 2313 2308 ends626 := triangleCover (by decide +kernel)

def src627 : Request := ⟨⟨⟨3960,5524,1189,452148⟩,1859229637672960,25433134016061⟩,16,2,1,308378,2⟩

theorem rank627 : P3_7_1.BankOK src627.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3960_5524_1189 452148

theorem width627 : Lower6960.HelperSource.WidthGuard src627.bank 179730 2308 src627.reserve := requestWidth (by decide)

def ends627 : List ℕ := [2308, 2309, 2313]




theorem cover627 : Cover (Triangular src627) 2313 2308 ends627 := triangleCover (by decide +kernel)

def src628 : Request := ⟨⟨⟨5574,7775,1674,641254⟩,5184111810969600,99791494771586⟩,27,2,1,308378,2⟩

theorem rank628 : P3_7_1.BankOK src628.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5574_7775_1674 641254

theorem width628 : Lower6960.HelperSource.WidthGuard src628.bank 179730 2308 src628.reserve := requestWidth (by decide)

def ends628 : List ℕ := [2308, 2309, 2313]




theorem cover628 : Cover (Triangular src628) 2313 2308 ends628 := triangleCover (by decide +kernel)

def src629 : Request := ⟨⟨⟨1800,2511,540,180454⟩,174749067509760,1087105140167⟩,0,2,1,308385,1⟩

theorem rank629 : P3_7_1.BankOK src629.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1800_2511_540 180454

theorem width629 : Lower6960.HelperSource.WidthGuard src629.bank 179730 2308 src629.reserve := requestWidth (by decide)

def ends629 : List ℕ := [2308, 2309, 2313]

theorem inside629 : Research6966.TerminalBanks.inside src629.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover629 : Cover (Triangular src629) 2313 2308 ends629 := triangleCover (by decide +kernel)

def src63 : Request := ⟨⟨⟨2301,3207,702,25043⟩,369529993297920,2930605494152⟩,63,2,1,257319,49⟩

theorem rank63 : P3_7_1.BankOK src63.bank := 
  _root_.Research6970.Height2313.Physical.bank_2301_3207_702 25043

theorem width63 : Lower6960.HelperSource.WidthGuard src63.bank 179730 2308 src63.reserve := requestWidth (by decide)

def ends63 : List ℕ := [2308, 2309, 2313]

theorem inside63 : Research6966.TerminalBanks.inside src63.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover63 : Cover (Triangular src63) 2313 2308 ends63 := triangleCover (by decide +kernel)

def src630 : Request := ⟨⟨⟨1752,2444,525,203747⟩,161010208735232,974873455884⟩,1,2,1,308385,1⟩

theorem rank630 : P3_7_1.BankOK src630.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1752_2444_525 203747

theorem width630 : Lower6960.HelperSource.WidthGuard src630.bank 179730 2308 src630.reserve := requestWidth (by decide)

def ends630 : List ℕ := [2308, 2309, 2313]

theorem inside630 : Research6966.TerminalBanks.inside src630.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover630 : Cover (Triangular src630) 2313 2308 ends630 := triangleCover (by decide +kernel)

def src631 : Request := ⟨⟨⟨1785,2490,537,229860⟩,170783777751040,1053541809432⟩,2,2,1,308385,1⟩

theorem rank631 : P3_7_1.BankOK src631.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1785_2490_537 229860

theorem width631 : Lower6960.HelperSource.WidthGuard src631.bank 179730 2308 src631.reserve := requestWidth (by decide)

def ends631 : List ℕ := [2308, 2309, 2313]

theorem inside631 : Research6966.TerminalBanks.inside src631.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover631 : Cover (Triangular src631) 2313 2308 ends631 := triangleCover (by decide +kernel)

def src632 : Request := ⟨⟨⟨2088,2914,622,240534⟩,271204194451456,1959329457697⟩,3,2,1,308385,1⟩

theorem rank632 : P3_7_1.BankOK src632.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2088_2914_622 240534

theorem width632 : Lower6960.HelperSource.WidthGuard src632.bank 179730 2308 src632.reserve := requestWidth (by decide)

def ends632 : List ℕ := [2308, 2309, 2313]

theorem inside632 : Research6966.TerminalBanks.inside src632.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover632 : Cover (Triangular src632) 2313 2308 ends632 := triangleCover (by decide +kernel)

def src633 : Request := ⟨⟨⟨2109,2942,632,263053⟩,280732086566912,2045844620216⟩,4,2,1,308385,1⟩

theorem rank633 : P3_7_1.BankOK src633.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2109_2942_632 263053

theorem width633 : Lower6960.HelperSource.WidthGuard src633.bank 179730 2308 src633.reserve := requestWidth (by decide)

def ends633 : List ℕ := [2308, 2309, 2313]

theorem inside633 : Research6966.TerminalBanks.inside src633.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover633 : Cover (Triangular src633) 2313 2308 ends633 := triangleCover (by decide +kernel)

def src634 : Request := ⟨⟨⟨2142,2988,644,331546⟩,294843626291200,2182334193151⟩,6,2,1,308385,1⟩

theorem rank634 : P3_7_1.BankOK src634.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2142_2988_644 331546

theorem width634 : Lower6960.HelperSource.WidthGuard src634.bank 179730 2308 src634.reserve := requestWidth (by decide)

def ends634 : List ℕ := [2308, 2309, 2313]

theorem inside634 : Research6966.TerminalBanks.inside src634.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover634 : Cover (Triangular src634) 2313 2308 ends634 := triangleCover (by decide +kernel)

def src635 : Request := ⟨⟨⟨2653,3700,797,413169⟩,559623274233856,5125966017010⟩,10,2,1,308385,1⟩

theorem rank635 : P3_7_1.BankOK src635.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2653_3700_797 413169

theorem width635 : Lower6960.HelperSource.WidthGuard src635.bank 179730 2308 src635.reserve := requestWidth (by decide)

def ends635 : List ℕ := [2308, 2309, 2313]

theorem inside635 : Research6966.TerminalBanks.inside src635.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover635 : Cover (Triangular src635) 2313 2308 ends635 := triangleCover (by decide +kernel)

def src636 : Request := ⟨⟨⟨3202,4467,961,359019⟩,982866902384640,10875115635131⟩,10,2,1,308385,1⟩

theorem rank636 : P3_7_1.BankOK src636.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3202_4467_961 359019

theorem width636 : Lower6960.HelperSource.WidthGuard src636.bank 179730 2308 src636.reserve := requestWidth (by decide)

def ends636 : List ℕ := [2308, 2309, 2313]




theorem cover636 : Cover (Triangular src636) 2313 2308 ends636 := triangleCover (by decide +kernel)

def src637 : Request := ⟨⟨⟨3176,4432,947,456586⟩,954371090677760,10482540453677⟩,13,2,1,308385,1⟩

theorem rank637 : P3_7_1.BankOK src637.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3176_4432_947 456586

theorem width637 : Lower6960.HelperSource.WidthGuard src637.bank 179730 2308 src637.reserve := requestWidth (by decide)

def ends637 : List ℕ := [2308, 2309, 2313]




theorem cover637 : Cover (Triangular src637) 2313 2308 ends637 := triangleCover (by decide +kernel)

def src638 : Request := ⟨⟨⟨3953,5514,1187,404101⟩,1849512334196736,25252070181474⟩,13,2,1,308385,1⟩

theorem rank638 : P3_7_1.BankOK src638.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3953_5514_1187 404101

theorem width638 : Lower6960.HelperSource.WidthGuard src638.bank 179730 2308 src638.reserve := requestWidth (by decide)

def ends638 : List ℕ := [2308, 2309, 2313]




theorem cover638 : Cover (Triangular src638) 2313 2308 ends638 := triangleCover (by decide +kernel)

def src639 : Request := ⟨⟨⟨4730,6599,1420,588021⟩,3167380985610240,51772293031740⟩,22,2,1,308385,1⟩

theorem rank639 : P3_7_1.BankOK src639.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4730_6599_1420 588021

theorem width639 : Lower6960.HelperSource.WidthGuard src639.bank 179730 2308 src639.reserve := requestWidth (by decide)

def ends639 : List ℕ := [2308, 2309, 2313]




theorem cover639 : Cover (Triangular src639) 2313 2308 ends639 := triangleCover (by decide +kernel)

def src64 : Request := ⟨⟨⟨2816,3905,882,30467⟩,690700839813120,6598128215989⟩,85,2,1,257319,50⟩

theorem rank64 : P3_7_1.BankOK src64.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 30467

theorem width64 : Lower6960.HelperSource.WidthGuard src64.bank 179730 2308 src64.reserve := requestWidth (by decide)

def ends64 : List ℕ := [2308, 2313]

theorem inside64 : Research6966.TerminalBanks.inside src64.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover64 : Cover (Triangular src64) 2313 2308 ends64 := triangleCover (by decide +kernel)

def src640 : Request := ⟨⟨⟨1002,1395,301,66320⟩,30238219960320,104105680031⟩,0,3,1,386273,1⟩

theorem rank640 : P3_7_1.BankOK src640.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 66320

theorem width640 : Lower6960.HelperSource.WidthGuard src640.bank 179730 2308 src640.reserve := requestWidth (by decide)

def ends640 : List ℕ := [2308, 2309, 2313]

theorem inside640 : Research6966.TerminalBanks.inside src640.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover640 : Cover (Triangular src640) 2313 2308 ends640 := triangleCover (by decide +kernel)

def src641 : Request := ⟨⟨⟨1002,1395,301,75732⟩,30238219960320,104105680031⟩,1,3,1,386273,1⟩

theorem rank641 : P3_7_1.BankOK src641.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 75732

theorem width641 : Lower6960.HelperSource.WidthGuard src641.bank 179730 2308 src641.reserve := requestWidth (by decide)

def ends641 : List ℕ := [2308, 2309, 2313]

theorem inside641 : Research6966.TerminalBanks.inside src641.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover641 : Cover (Triangular src641) 2313 2308 ends641 := triangleCover (by decide +kernel)

def src642 : Request := ⟨⟨⟨989,1379,296,91143⟩,28996793008128,99015216989⟩,2,3,1,385979,1⟩

theorem rank642 : P3_7_1.BankOK src642.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_989_1379_296 91143

theorem width642 : Lower6960.HelperSource.WidthGuard src642.bank 179730 2308 src642.reserve := requestWidth (by decide)

def ends642 : List ℕ := [2308, 2309, 2313]

theorem inside642 : Research6966.TerminalBanks.inside src642.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover642 : Cover (Triangular src642) 2313 2308 ends642 := triangleCover (by decide +kernel)

def src643 : Request := ⟨⟨⟨1188,1658,355,102818⟩,50157848100864,206296069946⟩,4,3,1,385979,1⟩

theorem rank643 : P3_7_1.BankOK src643.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1188_1658_355 102818

theorem width643 : Lower6960.HelperSource.WidthGuard src643.bank 179730 2308 src643.reserve := requestWidth (by decide)

def ends643 : List ℕ := [2308, 2309, 2313]

theorem inside643 : Research6966.TerminalBanks.inside src643.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover643 : Cover (Triangular src643) 2313 2308 ends643 := triangleCover (by decide +kernel)

def src644 : Request := ⟨⟨⟨1453,2023,436,108268⟩,91990931537920,459151377566⟩,6,3,1,386273,1⟩

theorem rank644 : P3_7_1.BankOK src644.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1453_2023_436 108268

theorem width644 : Lower6960.HelperSource.WidthGuard src644.bank 179730 2308 src644.reserve := requestWidth (by decide)

def ends644 : List ℕ := [2308, 2309, 2313]

theorem inside644 : Research6966.TerminalBanks.inside src644.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover644 : Cover (Triangular src644) 2313 2308 ends644 := triangleCover (by decide +kernel)

def src645 : Request := ⟨⟨⟨1757,2442,529,116922⟩,162978555494400,978079044011⟩,8,3,1,385979,1⟩

theorem rank645 : P3_7_1.BankOK src645.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2442_529 116922

theorem width645 : Lower6960.HelperSource.WidthGuard src645.bank 179730 2308 src645.reserve := requestWidth (by decide)

def ends645 : List ℕ := [2308, 2309, 2313]

theorem inside645 : Research6966.TerminalBanks.inside src645.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover645 : Cover (Triangular src645) 2313 2308 ends645 := triangleCover (by decide +kernel)

def src646 : Request := ⟨⟨⟨1754,2442,527,136727⟩,161889503936512,975196209190⟩,10,3,1,386273,1⟩

theorem rank646 : P3_7_1.BankOK src646.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1754_2442_527 136727

theorem width646 : Lower6960.HelperSource.WidthGuard src646.bank 179730 2308 src646.reserve := requestWidth (by decide)

def ends646 : List ℕ := [2308, 2309, 2313]

theorem inside646 : Research6966.TerminalBanks.inside src646.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover646 : Cover (Triangular src646) 2313 2308 ends646 := triangleCover (by decide +kernel)

def src647 : Request := ⟨⟨⟨2104,2930,632,152563⟩,279246119370752,2019119590628⟩,13,3,1,386273,1⟩

theorem rank647 : P3_7_1.BankOK src647.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2104_2930_632 152563

theorem width647 : Lower6960.HelperSource.WidthGuard src647.bank 179730 2308 src647.reserve := requestWidth (by decide)

def ends647 : List ℕ := [2308, 2309, 2313]

theorem inside647 : Research6966.TerminalBanks.inside src647.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover647 : Cover (Triangular src647) 2313 2308 ends647 := triangleCover (by decide +kernel)

def src648 : Request := ⟨⟨⟨3207,4465,963,189662⟩,987866575405056,10877088344236⟩,20,3,1,386273,1⟩

theorem rank648 : P3_7_1.BankOK src648.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3207_4465_963 189662

theorem width648 : Lower6960.HelperSource.WidthGuard src648.bank 179730 2308 src648.reserve := requestWidth (by decide)

def ends648 : List ℕ := [2308, 2309, 2313]




theorem cover648 : Cover (Triangular src648) 2313 2308 ends648 := triangleCover (by decide +kernel)

def src649 : Request := ⟨⟨⟨2998,4178,897,230760⟩,804909730758656,8310192816141⟩,24,3,1,386273,1⟩

theorem rank649 : P3_7_1.BankOK src649.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2998_4178_897 230760

theorem width649 : Lower6960.HelperSource.WidthGuard src649.bank 179730 2308 src649.reserve := requestWidth (by decide)

def ends649 : List ℕ := [2308, 2309, 2313]

theorem inside649 : Research6966.TerminalBanks.inside src649.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover649 : Cover (Triangular src649) 2313 2308 ends649 := triangleCover (by decide +kernel)

def src65 : Request := ⟨⟨⟨2804,3905,882,31694⟩,684119132209152,6598128215989⟩,85,2,1,257319,50⟩

theorem rank65 : P3_7_1.BankOK src65.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2804_3905_882 31694

theorem width65 : Lower6960.HelperSource.WidthGuard src65.bank 179730 2308 src65.reserve := requestWidth (by decide)

def ends65 : List ℕ := [2308, 2309, 2313]

theorem inside65 : Research6966.TerminalBanks.inside src65.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover65 : Cover (Triangular src65) 2313 2308 ends65 := triangleCover (by decide +kernel)

def src650 : Request := ⟨⟨⟨2729,3808,832,530820⟩,615945059172352,5814843148904⟩,32,3,1,386273,1⟩

theorem rank650 : P3_7_1.BankOK src650.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2729_3808_832 530820

theorem width650 : Lower6960.HelperSource.WidthGuard src650.bank 179730 2308 src650.reserve := requestWidth (by decide)

def ends650 : List ℕ := [2308, 2313]

theorem inside650 : Research6966.TerminalBanks.inside src650.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover650 : Cover (Triangular src650) 2313 2308 ends650 := triangleCover (by decide +kernel)

def src651 : Request := ⟨⟨⟨5714,7953,1716,383816⟩,5584397632012288,109428971647179⟩,50,3,1,386273,1⟩

theorem rank651 : P3_7_1.BankOK src651.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5714_7953_1716 383816

theorem width651 : Lower6960.HelperSource.WidthGuard src651.bank 179730 2308 src651.reserve := requestWidth (by decide)

def ends651 : List ℕ := [2308, 2309, 2313]




theorem cover651 : Cover (Triangular src651) 2313 2308 ends651 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources48

section Pack_R6970Height2313CommonSources50

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src681 : Request := ⟨⟨⟨1203,1674,362,111892⟩,52356525326336,216028185312⟩,6,3,1,386273,5⟩

theorem rank681 : P3_7_1.BankOK src681.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_362 111892

theorem width681 : Lower6960.HelperSource.WidthGuard src681.bank 179730 2308 src681.reserve := requestWidth (by decide)

def ends681 : List ℕ := [2308, 2309, 2313]

theorem inside681 : Research6966.TerminalBanks.inside src681.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover681 : Cover (Triangular src681) 2313 2308 ends681 := triangleCover (by decide +kernel)

def src682 : Request := ⟨⟨⟨1739,2426,518,102704⟩,156740461527040,942050892054⟩,8,3,1,385979,5⟩

theorem rank682 : P3_7_1.BankOK src682.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1739_2426_518 102704

theorem width682 : Lower6960.HelperSource.WidthGuard src682.bank 179730 2308 src682.reserve := requestWidth (by decide)

def ends682 : List ℕ := [2308, 2309, 2313]

theorem inside682 : Research6966.TerminalBanks.inside src682.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover682 : Cover (Triangular src682) 2313 2308 ends682 := triangleCover (by decide +kernel)

def src683 : Request := ⟨⟨⟨1749,2436,522,118471⟩,159695745318912,960344122766⟩,10,3,1,385979,5⟩

theorem rank683 : P3_7_1.BankOK src683.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1749_2436_522 118471

theorem width683 : Lower6960.HelperSource.WidthGuard src683.bank 179730 2308 src683.reserve := requestWidth (by decide)

def ends683 : List ℕ := [2308, 2309, 2313]

theorem inside683 : Research6966.TerminalBanks.inside src683.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover683 : Cover (Triangular src683) 2313 2308 ends683 := triangleCover (by decide +kernel)

def src684 : Request := ⟨⟨⟨2105,2930,632,107648⟩,279542980935680,2019119590628⟩,10,3,1,386273,5⟩

theorem rank684 : P3_7_1.BankOK src684.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2105_2930_632 107648

theorem width684 : Lower6960.HelperSource.WidthGuard src684.bank 179730 2308 src684.reserve := requestWidth (by decide)

def ends684 : List ℕ := [2308, 2309, 2313]

theorem inside684 : Research6966.TerminalBanks.inside src684.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover684 : Cover (Triangular src684) 2313 2308 ends684 := triangleCover (by decide +kernel)

def src685 : Request := ⟨⟨⟨3207,4465,963,193465⟩,987866575405056,10877088344236⟩,25,3,1,386273,5⟩

theorem rank685 : P3_7_1.BankOK src685.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3207_4465_963 193465

theorem width685 : Lower6960.HelperSource.WidthGuard src685.bank 179730 2308 src685.reserve := requestWidth (by decide)

def ends685 : List ℕ := [2308, 2309, 2313]




theorem cover685 : Cover (Triangular src685) 2313 2308 ends685 := triangleCover (by decide +kernel)

def src686 : Request := ⟨⟨⟨9988,13890,3010,496995⟩,29894270850433024,1021142236441759⟩,85,3,1,386273,5⟩

theorem rank686 : P3_7_1.BankOK src686.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_9988_13890_3010 496995

theorem width686 : Lower6960.HelperSource.WidthGuard src686.bank 179730 2308 src686.reserve := requestWidth (by decide)

def ends686 : List ℕ := [2308, 2309, 2313]




theorem cover686 : Cover (Triangular src686) 2313 2308 ends686 := triangleCover (by decide +kernel)

def src687 : Request := ⟨⟨⟨1002,1395,301,53282⟩,30238219960320,104105680031⟩,0,3,1,386273,6⟩

theorem rank687 : P3_7_1.BankOK src687.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 53282

theorem width687 : Lower6960.HelperSource.WidthGuard src687.bank 179730 2308 src687.reserve := requestWidth (by decide)

def ends687 : List ℕ := [2308, 2309, 2313]

theorem inside687 : Research6966.TerminalBanks.inside src687.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover687 : Cover (Triangular src687) 2313 2308 ends687 := triangleCover (by decide +kernel)

def src688 : Request := ⟨⟨⟨1193,1658,361,57031⟩,51280444129280,209005943830⟩,1,3,1,385979,6⟩

theorem rank688 : P3_7_1.BankOK src688.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 57031

theorem width688 : Lower6960.HelperSource.WidthGuard src688.bank 179730 2308 src688.reserve := requestWidth (by decide)

def ends688 : List ℕ := [2308, 2309, 2313]

theorem inside688 : Research6966.TerminalBanks.inside src688.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover688 : Cover (Triangular src688) 2313 2308 ends688 := triangleCover (by decide +kernel)

def src689 : Request := ⟨⟨⟨1177,1642,355,64022⟩,49125646139392,199962033930⟩,2,3,1,385979,6⟩

theorem rank689 : P3_7_1.BankOK src689.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1177_1642_355 64022

theorem width689 : Lower6960.HelperSource.WidthGuard src689.bank 179730 2308 src689.reserve := requestWidth (by decide)

def ends689 : List ℕ := [2308, 2309, 2313]

theorem inside689 : Research6966.TerminalBanks.inside src689.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover689 : Cover (Triangular src689) 2313 2308 ends689 := triangleCover (by decide +kernel)

def src69 : Request := ⟨⟨⟨2816,3905,882,27027⟩,690700839813120,6598128215989⟩,85,2,1,257319,52⟩

theorem rank69 : P3_7_1.BankOK src69.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2816_3905_882 27027

theorem width69 : Lower6960.HelperSource.WidthGuard src69.bank 179730 2308 src69.reserve := requestWidth (by decide)

def ends69 : List ℕ := [2308, 2313]

theorem inside69 : Research6966.TerminalBanks.inside src69.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover69 : Cover (Triangular src69) 2313 2308 ends69 := triangleCover (by decide +kernel)

def src690 : Request := ⟨⟨⟨1177,1642,355,71727⟩,49125646139392,199962033930⟩,3,3,1,385979,6⟩

theorem rank690 : P3_7_1.BankOK src690.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1177_1642_355 71727

theorem width690 : Lower6960.HelperSource.WidthGuard src690.bank 179730 2308 src690.reserve := requestWidth (by decide)

def ends690 : List ℕ := [2308, 2309, 2313]

theorem inside690 : Research6966.TerminalBanks.inside src690.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover690 : Cover (Triangular src690) 2313 2308 ends690 := triangleCover (by decide +kernel)

def src691 : Request := ⟨⟨⟨1181,1642,355,80973⟩,49499685781504,199962033930⟩,4,3,1,385979,6⟩

theorem rank691 : P3_7_1.BankOK src691.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1181_1642_355 80973

theorem width691 : Lower6960.HelperSource.WidthGuard src691.bank 179730 2308 src691.reserve := requestWidth (by decide)

def ends691 : List ℕ := [2308, 2309, 2313]

theorem inside691 : Research6966.TerminalBanks.inside src691.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover691 : Cover (Triangular src691) 2313 2308 ends691 := triangleCover (by decide +kernel)

def src692 : Request := ⟨⟨⟨1744,2426,527,109230⟩,159832701140992,954787561062⟩,10,3,1,386273,6⟩

theorem rank692 : P3_7_1.BankOK src692.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1744_2426_527 109230

theorem width692 : Lower6960.HelperSource.WidthGuard src692.bank 179730 2308 src692.reserve := requestWidth (by decide)

def ends692 : List ℕ := [2308, 2309, 2313]

theorem inside692 : Research6966.TerminalBanks.inside src692.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover692 : Cover (Triangular src692) 2313 2308 ends692 := triangleCover (by decide +kernel)

def src693 : Request := ⟨⟨⟨3208,4465,963,152535⟩,988555580538880,10877088344236⟩,20,3,1,386273,6⟩

theorem rank693 : P3_7_1.BankOK src693.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3208_4465_963 152535

theorem width693 : Lower6960.HelperSource.WidthGuard src693.bank 179730 2308 src693.reserve := requestWidth (by decide)

def ends693 : List ℕ := [2308, 2309, 2313]




theorem cover693 : Cover (Triangular src693) 2313 2308 ends693 := triangleCover (by decide +kernel)

def src694 : Request := ⟨⟨⟨3959,5512,1189,217915⟩,1858179765370880,25255771038451⟩,32,3,1,386273,6⟩

theorem rank694 : P3_7_1.BankOK src694.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3959_5512_1189 217915

theorem width694 : Lower6960.HelperSource.WidthGuard src694.bank 179730 2308 src694.reserve := requestWidth (by decide)

def ends694 : List ℕ := [2308, 2309, 2313]




theorem cover694 : Cover (Triangular src694) 2313 2308 ends694 := triangleCover (by decide +kernel)

def src695 : Request := ⟨⟨⟨3205,4460,967,490796⟩,989609234268160,10873035897009⟩,40,3,1,386273,6⟩

theorem rank695 : P3_7_1.BankOK src695.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3205_4460_967 490796

theorem width695 : Lower6960.HelperSource.WidthGuard src695.bank 179730 2308 src695.reserve := requestWidth (by decide)

def ends695 : List ℕ := [2308, 2309, 2313]




theorem cover695 : Cover (Triangular src695) 2313 2308 ends695 := triangleCover (by decide +kernel)

def src696 : Request := ⟨⟨⟨5714,7953,1716,308552⟩,5584397632012288,109428971647179⟩,50,3,1,386273,6⟩

theorem rank696 : P3_7_1.BankOK src696.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5714_7953_1716 308552

theorem width696 : Lower6960.HelperSource.WidthGuard src696.bank 179730 2308 src696.reserve := requestWidth (by decide)

def ends696 : List ℕ := [2308, 2309, 2313]




theorem cover696 : Cover (Triangular src696) 2313 2308 ends696 := triangleCover (by decide +kernel)

def src697 : Request := ⟨⟨⟨8281,11517,2498,502855⟩,17051587732307968,483050333667183⟩,85,3,1,386273,6⟩

theorem rank697 : P3_7_1.BankOK src697.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8281_11517_2498 502855

theorem width697 : Lower6960.HelperSource.WidthGuard src697.bank 179730 2308 src697.reserve := requestWidth (by decide)

def ends697 : List ℕ := [2308, 2309, 2313]




theorem cover697 : Cover (Triangular src697) 2313 2308 ends697 := triangleCover (by decide +kernel)

def src698 : Request := ⟨⟨⟨1002,1395,301,50764⟩,30238219960320,104105680031⟩,0,3,1,386273,7⟩

theorem rank698 : P3_7_1.BankOK src698.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 50764

theorem width698 : Lower6960.HelperSource.WidthGuard src698.bank 179730 2308 src698.reserve := requestWidth (by decide)

def ends698 : List ℕ := [2308, 2309, 2313]

theorem inside698 : Research6966.TerminalBanks.inside src698.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover698 : Cover (Triangular src698) 2313 2308 ends698 := triangleCover (by decide +kernel)

def src699 : Request := ⟨⟨⟨1200,1670,361,60066⟩,51955677528064,213911086908⟩,2,3,1,386273,7⟩

theorem rank699 : P3_7_1.BankOK src699.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1200_1670_361 60066

theorem width699 : Lower6960.HelperSource.WidthGuard src699.bank 179730 2308 src699.reserve := requestWidth (by decide)

def ends699 : List ℕ := [2308, 2309, 2313]

theorem inside699 : Research6966.TerminalBanks.inside src699.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover699 : Cover (Triangular src699) 2313 2308 ends699 := triangleCover (by decide +kernel)

def src7 : Request := ⟨⟨⟨2287,3175,702,23764⟩,364515722002432,2837502581224⟩,85,1,1,128659,65⟩

theorem rank7 : P3_7_1.BankOK src7.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2287_3175_702 23764

theorem width7 : Lower6960.HelperSource.WidthGuard src7.bank 179730 2308 src7.reserve := requestWidth (by decide)

def ends7 : List ℕ := [2308, 2309, 2313]

theorem inside7 : Research6966.TerminalBanks.inside src7.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover7 : Cover (Triangular src7) 2313 2308 ends7 := triangleCover (by decide +kernel)

def src70 : Request := ⟨⟨⟨2601,3625,819,31694⟩,546534142771200,4901614794409⟩,85,2,1,257319,53⟩

theorem rank70 : P3_7_1.BankOK src70.bank := 
  _root_.Research6970.Height2313.Physical.bank_2601_3625_819 31694

theorem width70 : Lower6960.HelperSource.WidthGuard src70.bank 179730 2308 src70.reserve := requestWidth (by decide)

def ends70 : List ℕ := [2308, 2309, 2313]

theorem inside70 : Research6966.TerminalBanks.inside src70.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover70 : Cover (Triangular src70) 2313 2308 ends70 := triangleCover (by decide +kernel)

def src700 : Request := ⟨⟨⟨1203,1674,361,75859⟩,52246486712320,215563369662⟩,4,3,1,386273,7⟩

theorem rank700 : P3_7_1.BankOK src700.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_361 75859

theorem width700 : Lower6960.HelperSource.WidthGuard src700.bank 179730 2308 src700.reserve := requestWidth (by decide)

def ends700 : List ℕ := [2308, 2309, 2313]

theorem inside700 : Research6966.TerminalBanks.inside src700.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover700 : Cover (Triangular src700) 2313 2308 ends700 := triangleCover (by decide +kernel)

def src701 : Request := ⟨⟨⟨1755,2440,529,103927⟩,162563969515520,975504013836⟩,10,3,1,385979,7⟩

theorem rank701 : P3_7_1.BankOK src701.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1755_2440_529 103927

theorem width701 : Lower6960.HelperSource.WidthGuard src701.bank 179730 2308 src701.reserve := requestWidth (by decide)

def ends701 : List ℕ := [2308, 2309, 2313]

theorem inside701 : Research6966.TerminalBanks.inside src701.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover701 : Cover (Triangular src701) 2313 2308 ends701 := triangleCover (by decide +kernel)

def src702 : Request := ⟨⟨⟨2554,3564,770,128447⟩,500675730472960,4423526519142⟩,16,3,1,385979,7⟩

theorem rank702 : P3_7_1.BankOK src702.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2554_3564_770 128447

theorem width702 : Lower6960.HelperSource.WidthGuard src702.bank 179730 2308 src702.reserve := requestWidth (by decide)

def ends702 : List ℕ := [2308, 2309, 2313]

theorem inside702 : Research6966.TerminalBanks.inside src702.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover702 : Cover (Triangular src702) 2313 2308 ends702 := triangleCover (by decide +kernel)

def src703 : Request := ⟨⟨⟨3176,4417,963,173949⟩,966632758837248,10505224384092⟩,25,3,1,386273,7⟩

theorem rank703 : P3_7_1.BankOK src703.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3176_4417_963 173949

theorem width703 : Lower6960.HelperSource.WidthGuard src703.bank 179730 2308 src703.reserve := requestWidth (by decide)

def ends703 : List ℕ := [2308, 2309, 2313]




theorem cover703 : Cover (Triangular src703) 2313 2308 ends703 := triangleCover (by decide +kernel)

def src704 : Request := ⟨⟨⟨3212,4464,967,471331⟩,994450506514432,10904451073769⟩,40,3,1,385979,7⟩

theorem rank704 : P3_7_1.BankOK src704.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3212_4464_967 471331

theorem width704 : Lower6960.HelperSource.WidthGuard src704.bank 179730 2308 src704.reserve := requestWidth (by decide)

def ends704 : List ℕ := [2308, 2309, 2313]




theorem cover704 : Cover (Triangular src704) 2313 2308 ends704 := triangleCover (by decide +kernel)

def src705 : Request := ⟨⟨⟨6871,9588,2058,379665⟩,9688932169023488,230181280555220⟩,65,3,1,385979,7⟩

theorem rank705 : P3_7_1.BankOK src705.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6871_9588_2058 379665

theorem width705 : Lower6960.HelperSource.WidthGuard src705.bank 179730 2308 src705.reserve := requestWidth (by decide)

def ends705 : List ℕ := [2308, 2309, 2313]




theorem cover705 : Cover (Triangular src705) 2313 2308 ends705 := triangleCover (by decide +kernel)

def src706 : Request := ⟨⟨⟨10031,13953,3010,630139⟩,30182935399235584,1036125345444439⟩,110,3,1,386273,7⟩

theorem rank706 : P3_7_1.BankOK src706.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10031_13953_3010 630139

theorem width706 : Lower6960.HelperSource.WidthGuard src706.bank 179730 2308 src706.reserve := requestWidth (by decide)

def ends706 : List ℕ := [2308, 2309, 2313]




theorem cover706 : Cover (Triangular src706) 2313 2308 ends706 := triangleCover (by decide +kernel)

def src707 : Request := ⟨⟨⟨994,1387,296,50233⟩,29325348569088,100873788737⟩,0,3,1,385979,8⟩

theorem rank707 : P3_7_1.BankOK src707.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_994_1387_296 50233

theorem width707 : Lower6960.HelperSource.WidthGuard src707.bank 179730 2308 src707.reserve := requestWidth (by decide)

def ends707 : List ℕ := [2308, 2309, 2313]

theorem inside707 : Research6966.TerminalBanks.inside src707.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover707 : Cover (Triangular src707) 2313 2308 ends707 := triangleCover (by decide +kernel)

def src708 : Request := ⟨⟨⟨1203,1674,361,51961⟩,52246486712320,215563369662⟩,1,3,1,386273,8⟩

theorem rank708 : P3_7_1.BankOK src708.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1203_1674_361 51961

theorem width708 : Lower6960.HelperSource.WidthGuard src708.bank 179730 2308 src708.reserve := requestWidth (by decide)

def ends708 : List ℕ := [2308, 2309, 2313]

theorem inside708 : Research6966.TerminalBanks.inside src708.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover708 : Cover (Triangular src708) 2313 2308 ends708 := triangleCover (by decide +kernel)

def src709 : Request := ⟨⟨⟨1199,1666,361,57003⟩,51858930925568,212267437130⟩,2,3,1,385979,8⟩

theorem rank709 : P3_7_1.BankOK src709.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1199_1666_361 57003

theorem width709 : Lower6960.HelperSource.WidthGuard src709.bank 179730 2308 src709.reserve := requestWidth (by decide)

def ends709 : List ℕ := [2308, 2309, 2313]

theorem inside709 : Research6966.TerminalBanks.inside src709.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover709 : Cover (Triangular src709) 2313 2308 ends709 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources50

section Pack_R6970Height2313CommonSources52

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src739 : Request := ⟨⟨⟨10041,13954,3018,385246⟩,30311585010679808,1038514136880293⟩,85,3,1,385979,10⟩

theorem rank739 : P3_7_1.BankOK src739.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10041_13954_3018 385246

theorem width739 : Lower6960.HelperSource.WidthGuard src739.bank 179730 2308 src739.reserve := requestWidth (by decide)

def ends739 : List ℕ := [2308, 2309, 2313]




theorem cover739 : Cover (Triangular src739) 2313 2308 ends739 := triangleCover (by decide +kernel)

def src74 : Request := ⟨⟨⟨2588,3593,793,27186⟩,527385327042560,4645717944219⟩,85,2,1,257319,55⟩

theorem rank74 : P3_7_1.BankOK src74.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2588_3593_793 27186

theorem width74 : Lower6960.HelperSource.WidthGuard src74.bank 179730 2308 src74.reserve := requestWidth (by decide)

def ends74 : List ℕ := [2308, 2309, 2313]

theorem inside74 : Research6966.TerminalBanks.inside src74.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover74 : Cover (Triangular src74) 2313 2308 ends74 := triangleCover (by decide +kernel)

def src740 : Request := ⟨⟨⟨992,1379,301,40093⟩,29567671336960,100313940775⟩,0,3,1,385979,11⟩

theorem rank740 : P3_7_1.BankOK src740.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 40093

theorem width740 : Lower6960.HelperSource.WidthGuard src740.bank 179730 2308 src740.reserve := requestWidth (by decide)

def ends740 : List ℕ := [2308, 2309, 2313]

theorem inside740 : Research6966.TerminalBanks.inside src740.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover740 : Cover (Triangular src740) 2313 2308 ends740 := triangleCover (by decide +kernel)

def src741 : Request := ⟨⟨⟨1002,1395,301,46222⟩,30238219960320,104105680031⟩,1,3,1,386273,11⟩

theorem rank741 : P3_7_1.BankOK src741.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 46222

theorem width741 : Lower6960.HelperSource.WidthGuard src741.bank 179730 2308 src741.reserve := requestWidth (by decide)

def ends741 : List ℕ := [2308, 2309, 2313]

theorem inside741 : Research6966.TerminalBanks.inside src741.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover741 : Cover (Triangular src741) 2313 2308 ends741 := triangleCover (by decide +kernel)

def src742 : Request := ⟨⟨⟨1002,1395,301,53780⟩,30238219960320,104105680031⟩,2,3,1,386273,11⟩

theorem rank742 : P3_7_1.BankOK src742.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1002_1395_301 53780

theorem width742 : Lower6960.HelperSource.WidthGuard src742.bank 179730 2308 src742.reserve := requestWidth (by decide)

def ends742 : List ℕ := [2308, 2309, 2313]

theorem inside742 : Research6966.TerminalBanks.inside src742.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover742 : Cover (Triangular src742) 2313 2308 ends742 := triangleCover (by decide +kernel)

def src743 : Request := ⟨⟨⟨1204,1674,362,60253⟩,52453872238592,216028185312⟩,4,3,1,385979,11⟩

theorem rank743 : P3_7_1.BankOK src743.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1204_1674_362 60253

theorem width743 : Lower6960.HelperSource.WidthGuard src743.bank 179730 2308 src743.reserve := requestWidth (by decide)

def ends743 : List ℕ := [2308, 2309, 2313]

theorem inside743 : Research6966.TerminalBanks.inside src743.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover743 : Cover (Triangular src743) 2313 2308 ends743 := triangleCover (by decide +kernel)

def src744 : Request := ⟨⟨⟨1757,2442,528,83328⟩,162743991402496,976638095087⟩,10,3,1,385979,11⟩

theorem rank744 : P3_7_1.BankOK src744.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1757_2442_528 83328

theorem width744 : Lower6960.HelperSource.WidthGuard src744.bank 179730 2308 src744.reserve := requestWidth (by decide)

def ends744 : List ℕ := [2308, 2309, 2313]

theorem inside744 : Research6966.TerminalBanks.inside src744.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover744 : Cover (Triangular src744) 2313 2308 ends744 := triangleCover (by decide +kernel)

def src745 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,16,3,1,385979,11⟩

theorem rank745 : P3_7_1.BankOK src745.bank := by
  simpa only [src745, _root_.Research6969.TransitionBanks.bank270] using _root_.Research6969.TransitionBanks.rank270 102908

theorem width745 : Lower6960.HelperSource.WidthGuard src745.bank 179730 2308 src745.reserve := requestWidth (by decide)

def ends745 : List ℕ := [2308, 2309, 2313]

theorem inside745 : Research6966.TerminalBanks.inside src745.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover745 : Cover (Triangular src745) 2313 2308 ends745 := triangleCover (by decide +kernel)

def src746 : Request := ⟨⟨⟨3961,5504,1197,133477⟩,1869808724869120,25269814668608⟩,25,3,1,385979,11⟩

theorem rank746 : P3_7_1.BankOK src746.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3961_5504_1197 133477

theorem width746 : Lower6960.HelperSource.WidthGuard src746.bank 179730 2308 src746.reserve := requestWidth (by decide)

def ends746 : List ℕ := [2308, 2309, 2313]




theorem cover746 : Cover (Triangular src746) 2313 2308 ends746 := triangleCover (by decide +kernel)

def src747 : Request := ⟨⟨⟨4802,6682,1445,194495⟩,3320115406569472,54636500602517⟩,40,3,1,386273,11⟩

theorem rank747 : P3_7_1.BankOK src747.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4802_6682_1445 194495

theorem width747 : Lower6960.HelperSource.WidthGuard src747.bank 179730 2308 src747.reserve := requestWidth (by decide)

def ends747 : List ℕ := [2308, 2309, 2313]




theorem cover747 : Cover (Triangular src747) 2313 2308 ends747 := triangleCover (by decide +kernel)

def src748 : Request := ⟨⟨⟨5708,7952,1716,1036553⟩,5571290233569280,109384694947514⟩,85,3,1,386273,11⟩

theorem rank748 : P3_7_1.BankOK src748.bank := 
  _root_.Research6970.Height2313.Physical.bank_5708_7952_1716 1036553

theorem width748 : Lower6960.HelperSource.WidthGuard src748.bank 179730 2308 src748.reserve := requestWidth (by decide)

def ends748 : List ℕ := [2308, 2309, 2313]




theorem cover748 : Cover (Triangular src748) 2313 2308 ends748 := triangleCover (by decide +kernel)

def src749 : Request := ⟨⟨⟨6908,9626,2077,2090426⟩,9874987794825216,234809190715807⟩,110,3,1,386273,11⟩

theorem rank749 : P3_7_1.BankOK src749.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6908_9626_2077 2090426

theorem width749 : Lower6960.HelperSource.WidthGuard src749.bank 179730 2308 src749.reserve := requestWidth (by decide)

def ends749 : List ℕ := [2308, 2309, 2313]




theorem cover749 : Cover (Triangular src749) 2313 2308 ends749 := triangleCover (by decide +kernel)

def src75 : Request := ⟨⟨⟨2606,3625,793,28173⟩,535631510110208,4780245027563⟩,85,2,1,257319,55⟩

theorem rank75 : P3_7_1.BankOK src75.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2606_3625_793 28173

theorem width75 : Lower6960.HelperSource.WidthGuard src75.bank 179730 2308 src75.reserve := requestWidth (by decide)

def ends75 : List ℕ := [2308, 2309, 2313]

theorem inside75 : Research6966.TerminalBanks.inside src75.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover75 : Cover (Triangular src75) 2313 2308 ends75 := triangleCover (by decide +kernel)

def src750 : Request := ⟨⟨⟨10031,13953,3010,503328⟩,30182935399235584,1036125345444439⟩,110,3,1,386273,11⟩

theorem rank750 : P3_7_1.BankOK src750.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10031_13953_3010 503328

theorem width750 : Lower6960.HelperSource.WidthGuard src750.bank 179730 2308 src750.reserve := requestWidth (by decide)

def ends750 : List ℕ := [2308, 2309, 2313]




theorem cover750 : Cover (Triangular src750) 2313 2308 ends750 := triangleCover (by decide +kernel)

def src751 : Request := ⟨⟨⟨994,1387,296,39985⟩,29325348569088,100873788737⟩,0,3,1,385979,12⟩

theorem rank751 : P3_7_1.BankOK src751.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_994_1387_296 39985

theorem width751 : Lower6960.HelperSource.WidthGuard src751.bank 179730 2308 src751.reserve := requestWidth (by decide)

def ends751 : List ℕ := [2308, 2309, 2313]

theorem inside751 : Research6966.TerminalBanks.inside src751.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover751 : Cover (Triangular src751) 2313 2308 ends751 := triangleCover (by decide +kernel)

def src752 : Request := ⟨⟨⟨1193,1658,361,40476⟩,51280444129280,209005943830⟩,1,3,1,385979,12⟩

theorem rank752 : P3_7_1.BankOK src752.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 40476

theorem width752 : Lower6960.HelperSource.WidthGuard src752.bank 179730 2308 src752.reserve := requestWidth (by decide)

def ends752 : List ℕ := [2308, 2309, 2313]

theorem inside752 : Research6966.TerminalBanks.inside src752.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover752 : Cover (Triangular src752) 2313 2308 ends752 := triangleCover (by decide +kernel)

def src753 : Request := ⟨⟨⟨1201,1670,361,45113⟩,52052519026688,213911086908⟩,2,3,1,385979,12⟩

theorem rank753 : P3_7_1.BankOK src753.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1201_1670_361 45113

theorem width753 : Lower6960.HelperSource.WidthGuard src753.bank 179730 2308 src753.reserve := requestWidth (by decide)

def ends753 : List ℕ := [2308, 2309, 2313]

theorem inside753 : Research6966.TerminalBanks.inside src753.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover753 : Cover (Triangular src753) 2313 2308 ends753 := triangleCover (by decide +kernel)

def src754 : Request := ⟨⟨⟨1202,1674,361,57109⟩,52149455421440,215563369662⟩,4,3,1,385979,12⟩

theorem rank754 : P3_7_1.BankOK src754.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1202_1674_361 57109

theorem width754 : Lower6960.HelperSource.WidthGuard src754.bank 179730 2308 src754.reserve := requestWidth (by decide)

def ends754 : List ℕ := [2308, 2309, 2313]

theorem inside754 : Research6966.TerminalBanks.inside src754.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover754 : Cover (Triangular src754) 2313 2308 ends754 := triangleCover (by decide +kernel)

def src755 : Request := ⟨⟨⟨1455,2023,437,76426⟩,92435285278720,459971681523⟩,8,3,1,385979,12⟩

theorem rank755 : P3_7_1.BankOK src755.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1455_2023_437 76426

theorem width755 : Lower6960.HelperSource.WidthGuard src755.bank 179730 2308 src755.reserve := requestWidth (by decide)

def ends755 : List ℕ := [2308, 2309, 2313]

theorem inside755 : Research6966.TerminalBanks.inside src755.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover755 : Cover (Triangular src755) 2313 2308 ends755 := triangleCover (by decide +kernel)

def src756 : Request := ⟨⟨⟨2086,2898,632,72186⟩,273930986455040,1949015201860⟩,10,3,1,385979,12⟩

theorem rank756 : P3_7_1.BankOK src756.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2086_2898_632 72186

theorem width756 : Lower6960.HelperSource.WidthGuard src756.bank 179730 2308 src756.reserve := requestWidth (by decide)

def ends756 : List ℕ := [2308, 2309, 2313]

theorem inside756 : Research6966.TerminalBanks.inside src756.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover756 : Cover (Triangular src756) 2313 2308 ends756 := triangleCover (by decide +kernel)

def src757 : Request := ⟨⟨⟨2610,3628,791,93755⟩,536441886081024,4783573219221⟩,16,3,1,385979,12⟩

theorem rank757 : P3_7_1.BankOK src757.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_791 93755

theorem width757 : Lower6960.HelperSource.WidthGuard src757.bank 179730 2308 src757.reserve := requestWidth (by decide)

def ends757 : List ℕ := [2308, 2309, 2313]

theorem inside757 : Research6966.TerminalBanks.inside src757.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover757 : Cover (Triangular src757) 2313 2308 ends757 := triangleCover (by decide +kernel)

def src758 : Request := ⟨⟨⟨3967,5512,1213,152623⟩,1895199936086016,25652240151764⟩,32,3,1,386273,12⟩

theorem rank758 : P3_7_1.BankOK src758.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3967_5512_1213 152623

theorem width758 : Lower6960.HelperSource.WidthGuard src758.bank 179730 2308 src758.reserve := requestWidth (by decide)

def ends758 : List ℕ := [2308, 2309, 2313]




theorem cover758 : Cover (Triangular src758) 2313 2308 ends758 := triangleCover (by decide +kernel)

def src759 : Request := ⟨⟨⟨6907,9612,2077,277325⟩,9871790471380992,233711820700520⟩,65,3,1,386273,12⟩

theorem rank759 : P3_7_1.BankOK src759.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_6907_9612_2077 277325

theorem width759 : Lower6960.HelperSource.WidthGuard src759.bank 179730 2308 src759.reserve := requestWidth (by decide)

def ends759 : List ℕ := [2308, 2309, 2313]




theorem cover759 : Cover (Triangular src759) 2313 2308 ends759 := triangleCover (by decide +kernel)

def src76 : Request := ⟨⟨⟨2590,3601,775,31694⟩,519149091553280,4596144040553⟩,85,2,1,257515,56⟩

theorem rank76 : P3_7_1.BankOK src76.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2590_3601_775 31694

theorem width76 : Lower6960.HelperSource.WidthGuard src76.bank 179730 2308 src76.reserve := requestWidth (by decide)

def ends76 : List ℕ := [2309, 2313]

theorem inside76 : Research6966.TerminalBanks.inside src76.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover76 : Cover (Triangular src76) 2313 2308 ends76 := triangleCover (by decide +kernel)

def src760 : Request := ⟨⟨⟨5717,7952,1732,929481⟩,5630634927849472,110179534728296⟩,85,3,1,386273,12⟩

theorem rank760 : P3_7_1.BankOK src760.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5717_7952_1732 929481

theorem width760 : Lower6960.HelperSource.WidthGuard src760.bank 179730 2308 src760.reserve := requestWidth (by decide)

def ends760 : List ℕ := [2308, 2309, 2313]




theorem cover760 : Cover (Triangular src760) 2313 2308 ends760 := triangleCover (by decide +kernel)

def src761 : Request := ⟨⟨⟨10032,13954,3010,342400⟩,30189665893220352,1036364370066239⟩,85,3,1,386273,12⟩

theorem rank761 : P3_7_1.BankOK src761.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10032_13954_3010 342400

theorem width761 : Lower6960.HelperSource.WidthGuard src761.bank 179730 2308 src761.reserve := requestWidth (by decide)

def ends761 : List ℕ := [2308, 2309, 2313]




theorem cover761 : Cover (Triangular src761) 2313 2308 ends761 := triangleCover (by decide +kernel)

def src762 : Request := ⟨⟨⟨1003,1395,301,35655⟩,30305710243840,104105680031⟩,0,3,1,385979,13⟩

theorem rank762 : P3_7_1.BankOK src762.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_301 35655

theorem width762 : Lower6960.HelperSource.WidthGuard src762.bank 179730 2308 src762.reserve := requestWidth (by decide)

def ends762 : List ℕ := [2308, 2309, 2313]

theorem inside762 : Research6966.TerminalBanks.inside src762.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover762 : Cover (Triangular src762) 2313 2308 ends762 := triangleCover (by decide +kernel)

def src763 : Request := ⟨⟨⟨992,1379,301,40050⟩,29567671336960,100313940775⟩,1,3,1,385979,13⟩

theorem rank763 : P3_7_1.BankOK src763.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_992_1379_301 40050

theorem width763 : Lower6960.HelperSource.WidthGuard src763.bank 179730 2308 src763.reserve := requestWidth (by decide)

def ends763 : List ℕ := [2308, 2309, 2313]

theorem inside763 : Research6966.TerminalBanks.inside src763.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover763 : Cover (Triangular src763) 2313 2308 ends763 := triangleCover (by decide +kernel)

def src764 : Request := ⟨⟨⟨1205,1674,368,41487⟩,53211572207616,218807905514⟩,2,3,1,386273,13⟩

theorem rank764 : P3_7_1.BankOK src764.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 41487

theorem width764 : Lower6960.HelperSource.WidthGuard src764.bank 179730 2308 src764.reserve := requestWidth (by decide)

def ends764 : List ℕ := [2308, 2309, 2313]

theorem inside764 : Research6966.TerminalBanks.inside src764.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover764 : Cover (Triangular src764) 2313 2308 ends764 := triangleCover (by decide +kernel)

def src765 : Request := ⟨⟨⟨1205,1674,365,46147⟩,52882002411520,217419999532⟩,3,3,1,385979,13⟩

theorem rank765 : P3_7_1.BankOK src765.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_365 46147

theorem width765 : Lower6960.HelperSource.WidthGuard src765.bank 179730 2308 src765.reserve := requestWidth (by decide)

def ends765 : List ℕ := [2308, 2309, 2313]

theorem inside765 : Research6966.TerminalBanks.inside src765.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover765 : Cover (Triangular src765) 2313 2308 ends765 := triangleCover (by decide +kernel)

def src766 : Request := ⟨⟨⟨1444,2007,436,57255⟩,90721755332608,447571244646⟩,6,3,1,385979,13⟩

theorem rank766 : P3_7_1.BankOK src766.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1444_2007_436 57255

theorem width766 : Lower6960.HelperSource.WidthGuard src766.bank 179730 2308 src766.reserve := requestWidth (by decide)

def ends766 : List ℕ := [2308, 2309, 2313]

theorem inside766 : Research6966.TerminalBanks.inside src766.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover766 : Cover (Triangular src766) 2313 2308 ends766 := triangleCover (by decide +kernel)

def src767 : Request := ⟨⟨⟨1735,2410,527,72320⟩,157993412853760,934671348902⟩,10,3,1,385979,13⟩

theorem rank767 : P3_7_1.BankOK src767.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1735_2410_527 72320

theorem width767 : Lower6960.HelperSource.WidthGuard src767.bank 179730 2308 src767.reserve := requestWidth (by decide)

def ends767 : List ℕ := [2308, 2309, 2313]

theorem inside767 : Research6966.TerminalBanks.inside src767.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover767 : Cover (Triangular src767) 2313 2308 ends767 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources52

section Pack_R6970Height2313CommonSources53

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src768 : Request := ⟨⟨⟨2604,3624,783,108744⟩,529573399756800,4729003348328⟩,20,3,1,386273,13⟩

theorem rank768 : P3_7_1.BankOK src768.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3624_783 108744

theorem width768 : Lower6960.HelperSource.WidthGuard src768.bank 179730 2308 src768.reserve := requestWidth (by decide)

def ends768 : List ℕ := [2308, 2309, 2313]

theorem inside768 : Research6966.TerminalBanks.inside src768.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover768 : Cover (Triangular src768) 2313 2308 ends768 := triangleCover (by decide +kernel)

def src769 : Request := ⟨⟨⟨2610,3628,793,119660⟩,537473153499136,4792991160379⟩,22,3,1,386273,13⟩

theorem rank769 : P3_7_1.BankOK src769.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2610_3628_793 119660

theorem width769 : Lower6960.HelperSource.WidthGuard src769.bank 179730 2308 src769.reserve := requestWidth (by decide)

def ends769 : List ℕ := [2308, 2309, 2313]

theorem inside769 : Research6966.TerminalBanks.inside src769.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover769 : Cover (Triangular src769) 2313 2308 ends769 := triangleCover (by decide +kernel)

def src77 : Request := ⟨⟨⟨2614,3625,819,24753⟩,552677752176640,4901614794409⟩,85,2,1,257319,56⟩

theorem rank77 : P3_7_1.BankOK src77.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3625_819 24753

theorem width77 : Lower6960.HelperSource.WidthGuard src77.bank 179730 2308 src77.reserve := requestWidth (by decide)

def ends77 : List ℕ := [2309, 2313]

theorem inside77 : Research6966.TerminalBanks.inside src77.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover77 : Cover (Triangular src77) 2313 2308 ends77 := triangleCover (by decide +kernel)

def src770 : Request := ⟨⟨⟨2953,4105,897,120358⟩,778135319085056,7851902147204⟩,24,3,1,386273,13⟩

theorem rank770 : P3_7_1.BankOK src770.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2953_4105_897 120358

theorem width770 : Lower6960.HelperSource.WidthGuard src770.bank 179730 2308 src770.reserve := requestWidth (by decide)

def ends770 : List ℕ := [2308, 2309, 2313]

theorem inside770 : Research6966.TerminalBanks.inside src770.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover770 : Cover (Triangular src770) 2313 2308 ends770 := triangleCover (by decide +kernel)

def src771 : Request := ⟨⟨⟨2604,3627,783,337644⟩,529573399756800,4741611634368⟩,32,3,1,385979,13⟩

theorem rank771 : P3_7_1.BankOK src771.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2604_3627_783 337644

theorem width771 : Lower6960.HelperSource.WidthGuard src771.bank 179730 2308 src771.reserve := requestWidth (by decide)

def ends771 : List ℕ := [2308, 2309, 2313]

theorem inside771 : Research6966.TerminalBanks.inside src771.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover771 : Cover (Triangular src771) 2313 2308 ends771 := triangleCover (by decide +kernel)

def src772 : Request := ⟨⟨⟨3226,4481,979,168323⟩,1013646399897600,11145301432991⟩,32,3,1,385979,13⟩

theorem rank772 : P3_7_1.BankOK src772.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3226_4481_979 168323

theorem width772 : Lower6960.HelperSource.WidthGuard src772.bank 179730 2308 src772.reserve := requestWidth (by decide)

def ends772 : List ℕ := [2308, 2309, 2313]




theorem cover772 : Cover (Triangular src772) 2313 2308 ends772 := triangleCover (by decide +kernel)

def src773 : Request := ⟨⟨⟨2868,4001,866,493259⟩,709662672158720,7033975845920⟩,38,3,1,386273,13⟩

theorem rank773 : P3_7_1.BankOK src773.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2868_4001_866 493259

theorem width773 : Lower6960.HelperSource.WidthGuard src773.bank 179730 2308 src773.reserve := requestWidth (by decide)

def ends773 : List ℕ := [2308, 2309, 2313]

theorem inside773 : Research6966.TerminalBanks.inside src773.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover773 : Cover (Triangular src773) 2313 2308 ends773 := triangleCover (by decide +kernel)

def src774 : Request := ⟨⟨⟨4822,6698,1461,168085⟩,3379359256412160,55533598470879⟩,40,3,1,385979,13⟩

theorem rank774 : P3_7_1.BankOK src774.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_4822_6698_1461 168085

theorem width774 : Lower6960.HelperSource.WidthGuard src774.bank 179730 2308 src774.reserve := requestWidth (by decide)

def ends774 : List ℕ := [2308, 2309, 2313]




theorem cover774 : Cover (Triangular src774) 2313 2308 ends774 := triangleCover (by decide +kernel)

def src775 : Request := ⟨⟨⟨5708,7952,1716,903339⟩,5571290233569280,109384694947514⟩,85,3,1,386273,13⟩

theorem rank775 : P3_7_1.BankOK src775.bank := 
  _root_.Research6970.Height2313.Physical.bank_5708_7952_1716 903339

theorem width775 : Lower6960.HelperSource.WidthGuard src775.bank 179730 2308 src775.reserve := requestWidth (by decide)

def ends775 : List ℕ := [2308, 2309, 2313]




theorem cover775 : Cover (Triangular src775) 2313 2308 ends775 := triangleCover (by decide +kernel)

def src776 : Request := ⟨⟨⟨10044,13953,3042,430651⟩,30515504591142912,1044710637160035⟩,110,3,1,385979,13⟩

theorem rank776 : P3_7_1.BankOK src776.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_10044_13953_3042 430651

theorem width776 : Lower6960.HelperSource.WidthGuard src776.bank 179730 2308 src776.reserve := requestWidth (by decide)

def ends776 : List ℕ := [2308, 2309, 2313]




theorem cover776 : Cover (Triangular src776) 2313 2308 ends776 := triangleCover (by decide +kernel)

def src777 : Request := ⟨⟨⟨1004,1395,305,32422⟩,30679368990720,105179950418⟩,0,3,1,385979,14⟩

theorem rank777 : P3_7_1.BankOK src777.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1004_1395_305 32422

theorem width777 : Lower6960.HelperSource.WidthGuard src777.bank 179730 2308 src777.reserve := requestWidth (by decide)

def ends777 : List ℕ := [2308, 2309, 2313]

theorem inside777 : Research6966.TerminalBanks.inside src777.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover777 : Cover (Triangular src777) 2313 2308 ends777 := triangleCover (by decide +kernel)

def src778 : Request := ⟨⟨⟨1003,1395,301,37725⟩,30305710243840,104105680031⟩,1,3,1,386273,14⟩

theorem rank778 : P3_7_1.BankOK src778.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1003_1395_301 37725

theorem width778 : Lower6960.HelperSource.WidthGuard src778.bank 179730 2308 src778.reserve := requestWidth (by decide)

def ends778 : List ℕ := [2308, 2309, 2313]

theorem inside778 : Research6966.TerminalBanks.inside src778.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover778 : Cover (Triangular src778) 2313 2308 ends778 := triangleCover (by decide +kernel)

def src779 : Request := ⟨⟨⟨1456,2023,445,41082⟩,93862507577344,466511127281⟩,3,3,1,386273,14⟩

theorem rank779 : P3_7_1.BankOK src779.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 41082

theorem width779 : Lower6960.HelperSource.WidthGuard src779.bank 179730 2308 src779.reserve := requestWidth (by decide)

def ends779 : List ℕ := [2308, 2309, 2313]

theorem inside779 : Research6966.TerminalBanks.inside src779.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover779 : Cover (Triangular src779) 2313 2308 ends779 := triangleCover (by decide +kernel)

def src78 : Request := ⟨⟨⟨2600,3625,775,31694⟩,523640687820800,4695421657977⟩,85,2,1,257319,57⟩

theorem rank78 : P3_7_1.BankOK src78.bank := by
  simpa only [src78, _root_.Research6969.TerminalAuxBanks.bank45] using _root_.Research6969.PackedRanks.TerminalRanks44To47.rank45 31694

theorem width78 : Lower6960.HelperSource.WidthGuard src78.bank 179730 2308 src78.reserve := requestWidth (by decide)

def ends78 : List ℕ := [2308, 2313]

theorem inside78 : Research6966.TerminalBanks.inside src78.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover78 : Cover (Triangular src78) 2313 2308 ends78 := triangleCover (by decide +kernel)

def src780 : Request := ⟨⟨⟨1456,2023,445,52658⟩,93862507577344,466511127281⟩,6,3,1,386273,14⟩

theorem rank780 : P3_7_1.BankOK src780.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 52658

theorem width780 : Lower6960.HelperSource.WidthGuard src780.bank 179730 2308 src780.reserve := requestWidth (by decide)

def ends780 : List ℕ := [2308, 2309, 2313]

theorem inside780 : Research6966.TerminalBanks.inside src780.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover780 : Cover (Triangular src780) 2313 2308 ends780 := triangleCover (by decide +kernel)

def src781 : Request := ⟨⟨⟨1753,2439,527,67901⟩,161683200802816,971347212742⟩,10,3,1,386273,14⟩

theorem rank781 : P3_7_1.BankOK src781.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1753_2439_527 67901

theorem width781 : Lower6960.HelperSource.WidthGuard src781.bank 179730 2308 src781.reserve := requestWidth (by decide)

def ends781 : List ℕ := [2308, 2309, 2313]

theorem inside781 : Research6966.TerminalBanks.inside src781.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover781 : Cover (Triangular src781) 2313 2308 ends781 := triangleCover (by decide +kernel)

def src782 : Request := ⟨⟨⟨2104,2928,632,76109⟩,279246119370752,2014688622700⟩,13,3,1,386273,14⟩

theorem rank782 : P3_7_1.BankOK src782.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2104_2928_632 76109

theorem width782 : Lower6960.HelperSource.WidthGuard src782.bank 179730 2308 src782.reserve := requestWidth (by decide)

def ends782 : List ℕ := [2308, 2309, 2313]

theorem inside782 : Research6966.TerminalBanks.inside src782.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover782 : Cover (Triangular src782) 2313 2308 ends782 := triangleCover (by decide +kernel)

def src783 : Request := ⟨⟨⟨2114,2938,640,133319⟩,284938289807360,2056978448546⟩,20,3,1,385979,14⟩

theorem rank783 : P3_7_1.BankOK src783.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2114_2938_640 133319

theorem width783 : Lower6960.HelperSource.WidthGuard src783.bank 179730 2308 src783.reserve := requestWidth (by decide)

def ends783 : List ℕ := [2308, 2309, 2313]

theorem inside783 : Research6966.TerminalBanks.inside src783.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover783 : Cover (Triangular src783) 2313 2308 ends783 := triangleCover (by decide +kernel)

def src784 : Request := ⟨⟨⟨3212,4465,971,93547⟩,997581528760320,10947490647200⟩,20,3,1,385979,14⟩

theorem rank784 : P3_7_1.BankOK src784.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_3212_4465_971 93547

theorem width784 : Lower6960.HelperSource.WidthGuard src784.bank 179730 2308 src784.reserve := requestWidth (by decide)

def ends784 : List ℕ := [2308, 2309, 2313]




theorem cover784 : Cover (Triangular src784) 2313 2308 ends784 := triangleCover (by decide +kernel)

def src785 : Request := ⟨⟨⟨2811,3907,854,104562⟩,671327256576000,6445344460182⟩,22,3,1,386273,14⟩

theorem rank785 : P3_7_1.BankOK src785.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2811_3907_854 104562

theorem width785 : Lower6960.HelperSource.WidthGuard src785.bank 179730 2308 src785.reserve := requestWidth (by decide)

def ends785 : List ℕ := [2308, 2309, 2313]

theorem inside785 : Research6966.TerminalBanks.inside src785.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover785 : Cover (Triangular src785) 2313 2308 ends785 := triangleCover (by decide +kernel)

def src786 : Request := ⟨⟨⟨2611,3627,791,302048⟩,536901863866368,4779330614481⟩,32,3,1,385979,14⟩

theorem rank786 : P3_7_1.BankOK src786.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2611_3627_791 302048

theorem width786 : Lower6960.HelperSource.WidthGuard src786.bank 179730 2308 src786.reserve := requestWidth (by decide)

def ends786 : List ℕ := [2308, 2309, 2313]

theorem inside786 : Research6966.TerminalBanks.inside src786.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover786 : Cover (Triangular src786) 2313 2308 ends786 := triangleCover (by decide +kernel)

def src787 : Request := ⟨⟨⟨5722,7953,1724,190021⟩,5621799092224000,109826875558354⟩,50,3,1,385979,14⟩

theorem rank787 : P3_7_1.BankOK src787.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5722_7953_1724 190021

theorem width787 : Lower6960.HelperSource.WidthGuard src787.bank 179730 2308 src787.reserve := requestWidth (by decide)

def ends787 : List ℕ := [2308, 2309, 2313]




theorem cover787 : Cover (Triangular src787) 2313 2308 ends787 := triangleCover (by decide +kernel)

def src788 : Request := ⟨⟨⟨5710,7949,1719,824260⟩,5583086713569280,109400975585001⟩,85,3,1,386273,14⟩

theorem rank788 : P3_7_1.BankOK src788.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_5710_7949_1719 824260

theorem width788 : Lower6960.HelperSource.WidthGuard src788.bank 179730 2308 src788.reserve := requestWidth (by decide)

def ends788 : List ℕ := [2308, 2309, 2313]




theorem cover788 : Cover (Triangular src788) 2313 2308 ends788 := triangleCover (by decide +kernel)

def src789 : Request := ⟨⟨⟨8306,11557,2498,313104⟩,17166966842195968,488471451219103⟩,85,3,1,386273,14⟩

theorem rank789 : P3_7_1.BankOK src789.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_8306_11557_2498 313104

theorem width789 : Lower6960.HelperSource.WidthGuard src789.bank 179730 2308 src789.reserve := requestWidth (by decide)

def ends789 : List ℕ := [2308, 2309, 2313]




theorem cover789 : Cover (Triangular src789) 2313 2308 ends789 := triangleCover (by decide +kernel)

def src79 : Request := ⟨⟨⟨2614,3625,819,24021⟩,552677752176640,4901614794409⟩,85,2,1,257319,57⟩

theorem rank79 : P3_7_1.BankOK src79.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2614_3625_819 24021

theorem width79 : Lower6960.HelperSource.WidthGuard src79.bank 179730 2308 src79.reserve := requestWidth (by decide)

def ends79 : List ℕ := [2309, 2313]

theorem inside79 : Research6966.TerminalBanks.inside src79.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover79 : Cover (Triangular src79) 2313 2308 ends79 := triangleCover (by decide +kernel)

def src790 : Request := ⟨⟨⟨987,1377,296,31599⟩,28865915781120,98554239032⟩,0,3,1,385979,15⟩

theorem rank790 : P3_7_1.BankOK src790.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_987_1377_296 31599

theorem width790 : Lower6960.HelperSource.WidthGuard src790.bank 179730 2308 src790.reserve := requestWidth (by decide)

def ends790 : List ℕ := [2308, 2309, 2313]

theorem inside790 : Research6966.TerminalBanks.inside src790.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover790 : Cover (Triangular src790) 2313 2308 ends790 := triangleCover (by decide +kernel)

def src791 : Request := ⟨⟨⟨1205,1674,368,32391⟩,53211572207616,218807905514⟩,1,3,1,386273,15⟩

theorem rank791 : P3_7_1.BankOK src791.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1205_1674_368 32391

theorem width791 : Lower6960.HelperSource.WidthGuard src791.bank 179730 2308 src791.reserve := requestWidth (by decide)

def ends791 : List ℕ := [2308, 2309, 2313]

theorem inside791 : Research6966.TerminalBanks.inside src791.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover791 : Cover (Triangular src791) 2313 2308 ends791 := triangleCover (by decide +kernel)

def src792 : Request := ⟨⟨⟨1193,1658,361,35899⟩,51280444129280,209005943830⟩,2,3,1,385979,15⟩

theorem rank792 : P3_7_1.BankOK src792.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 35899

theorem width792 : Lower6960.HelperSource.WidthGuard src792.bank 179730 2308 src792.reserve := requestWidth (by decide)

def ends792 : List ℕ := [2308, 2309, 2313]

theorem inside792 : Research6966.TerminalBanks.inside src792.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover792 : Cover (Triangular src792) 2313 2308 ends792 := triangleCover (by decide +kernel)

def src793 : Request := ⟨⟨⟨1193,1658,361,44997⟩,51280444129280,209005943830⟩,4,3,1,385979,15⟩

theorem rank793 : P3_7_1.BankOK src793.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1193_1658_361 44997

theorem width793 : Lower6960.HelperSource.WidthGuard src793.bank 179730 2308 src793.reserve := requestWidth (by decide)

def ends793 : List ℕ := [2308, 2309, 2313]

theorem inside793 : Research6966.TerminalBanks.inside src793.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover793 : Cover (Triangular src793) 2313 2308 ends793 := triangleCover (by decide +kernel)

def src794 : Request := ⟨⟨⟨1456,2023,445,59915⟩,93862507577344,466511127281⟩,8,3,1,386273,15⟩

theorem rank794 : P3_7_1.BankOK src794.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_1456_2023_445 59915

theorem width794 : Lower6960.HelperSource.WidthGuard src794.bank 179730 2308 src794.reserve := requestWidth (by decide)

def ends794 : List ℕ := [2308, 2309, 2313]

theorem inside794 : Research6966.TerminalBanks.inside src794.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover794 : Cover (Triangular src794) 2313 2308 ends794 := triangleCover (by decide +kernel)

def src795 : Request := ⟨⟨⟨2106,2926,636,58467⟩,281187434364928,2020172992773⟩,10,3,1,385979,15⟩

theorem rank795 : P3_7_1.BankOK src795.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2106_2926_636 58467

theorem width795 : Lower6960.HelperSource.WidthGuard src795.bank 179730 2308 src795.reserve := requestWidth (by decide)

def ends795 : List ℕ := [2308, 2309, 2313]

theorem inside795 : Research6966.TerminalBanks.inside src795.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover795 : Cover (Triangular src795) 2313 2308 ends795 := triangleCover (by decide +kernel)

def src796 : Request := ⟨⟨⟨2104,2924,634,86036⟩,279918727659520,2010792257808⟩,16,3,1,385979,15⟩

theorem rank796 : P3_7_1.BankOK src796.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_2104_2924_634 86036

theorem width796 : Lower6960.HelperSource.WidthGuard src796.bank 179730 2308 src796.reserve := requestWidth (by decide)

def ends796 : List ℕ := [2308, 2309, 2313]

theorem inside796 : Research6966.TerminalBanks.inside src796.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover796 : Cover (Triangular src796) 2313 2308 ends796 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical
end Pack_R6970Height2313CommonSources53

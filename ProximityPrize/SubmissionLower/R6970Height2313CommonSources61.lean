import ProximityPrize.SubmissionLower.R6970PhysicalRequestCompact
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Bundle6970_260481f54d2fe368
import ProximityPrize.SubmissionLower.Z6969Pack0589

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical
open Research6969.PhysicalWindow.Compact
open Research6969.PhysicalWindow

def src998 : Request := ⟨⟨⟨690,960,208,8679⟩,9921631092736,23488112384⟩,2,3,1,385979,31⟩

theorem rank998 : P3_7_1.BankOK src998.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_690_960_208 8679

theorem width998 : Lower6960.HelperSource.WidthGuard src998.bank 179730 2308 src998.reserve := requestWidth (by decide)

def ends998 : List ℕ := [2308, 2309, 2313]

theorem inside998 : Research6966.TerminalBanks.inside src998.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)




theorem cover998 : Cover (Triangular src998) 2313 2308 ends998 := triangleCover (by decide +kernel)

def src999 : Request := ⟨⟨⟨691,962,212,9763⟩,10098434375680,23997864317⟩,3,3,1,385979,31⟩

theorem rank999 : P3_7_1.BankOK src999.bank := 
  _root_.Research6970.Height2313.CommonBankRanks.bank_691_962_212 9763

theorem width999 : Lower6960.HelperSource.WidthGuard src999.bank 179730 2308 src999.reserve := requestWidth (by decide)

def ends999 : List ℕ := [2308, 2313]

theorem inside999 : Research6966.TerminalBanks.inside src999.shape Research6969.SpreadCatalogue.shape := requestInside (by decide)



theorem cover999 : Cover (Triangular src999) 2313 2308 ends999 := triangleCover (by decide +kernel)

end Research6970.Height2313.Physical

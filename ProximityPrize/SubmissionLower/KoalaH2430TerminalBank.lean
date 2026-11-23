import ProximityPrize.SubmissionLower.KoalaH2430TerminalData
import ProximityPrize.SubmissionLower.HighBankCore
import ProximityPrize.SubmissionLower.KoalaH2430Moment6675_1411

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Terminal
open P1_7_1_3 (momentEstimate)

theorem moment : momentEstimate 6675 1411 = 0x309c85fb6d6a :=
  KoalaH2430Banks.moment6675_1411

theorem terminal_ok : P3_7_1.BankOK terminal :=
  P3_7_1.checked terminal (m := 4800) (B := 6675) (J := 1411) (N := 0xb9273b5380000) (M := 0x309c85fb6d6a)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) moment

end KoalaH2430Terminal

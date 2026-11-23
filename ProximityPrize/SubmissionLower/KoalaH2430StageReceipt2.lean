import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage04_0 : BankCertificate 2430 4 0 KoalaH2430Banks.stage04.free :=
  checked (k := 144) (w := 112125) (z := 0x772a50fb00) (d := 0x255bc9ef7a0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage04_1 : BankCertificate 2430 4 1 KoalaH2430Banks.stage04.moving :=
  checked (k := 729) (w := 378889) (z := 0x10f27f45e6d8) (d := 0x19171d6c4d61688)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage05_0 : BankCertificate 2430 5 0 KoalaH2430Banks.stage05.free :=
  checked (k := 155) (w := 131222) (z := 0xcb13b19630) (d := 0x3459d221a20)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage05_1 : BankCertificate 2430 5 1 KoalaH2430Banks.stage05.moving :=
  checked (k := 905) (w := 706106) (z := 0x181c6a012c334) (d := 0x27bb5236b4c8248)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage06_0 : BankCertificate 2430 7 0 KoalaH2430Banks.stage06.free :=
  checked (k := 176) (w := 118181) (z := 0x5c34a2b0d0) (d := 0x5944b749a90)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage06_1 : BankCertificate 2430 7 1 KoalaH2430Banks.stage06.moving :=
  checked (k := 964) (w := 712594) (z := 0x4a26855dd8b50) (d := 0x43d9f4d3eaf2ca8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage07_0 : BankCertificate 2430 10 0 KoalaH2430Banks.stage07.free :=
  checked (k := 198) (w := 151515) (z := 0xd7412b89e0) (d := 0xcedeeb27690)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage07_1 : BankCertificate 2430 10 1 KoalaH2430Banks.stage07.moving :=
  checked (k := 1200) (w := 917658) (z := 0x317c6c3f36ee0) (d := 0xa316a63d18807e0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

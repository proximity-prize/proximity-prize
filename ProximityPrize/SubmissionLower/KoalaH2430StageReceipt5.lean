import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage16_0 : BankCertificate 2430 50 0 KoalaH2430Banks.stage16.free :=
  checked (k := 585) (w := 178576) (z := 0x29ce8fb15b20) (d := 0x9a6950f856ef0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage16_1 : BankCertificate 2430 50 1 KoalaH2430Banks.stage16.moving :=
  checked (k := 3772) (w := 2242176) (z := 0x2b6bed4478823cc) (d := 0xa1e007e50af2291fc)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage17_0 : BankCertificate 2430 64 0 KoalaH2430Banks.stage17.free :=
  checked (k := 716) (w := 706537) (z := 0xcf1687c8df80) (d := 0x1aec3b255b8500)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage17_1 : BankCertificate 2430 64 1 KoalaH2430Banks.stage17.moving :=
  checked (k := 4642) (w := 2704030) (z := 0x7d1f6f2fd2cbe30) (d := 0x1ca869195800c1c080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage18_0 : BankCertificate 2430 70 0 KoalaH2430Banks.stage18.free :=
  checked (k := 627) (w := 74734) (z := 0xbb48f494c750) (d := 0x195c6a403bc95270)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage18_1 : BankCertificate 2430 70 1 KoalaH2430Banks.stage18.moving :=
  checked (k := 3910) (w := 1865554) (z := 0x15adaef52c11514) (d := 0x24835ab69e417bfa6c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage19_0 : BankCertificate 2430 84 0 KoalaH2430Banks.stage19.free :=
  checked (k := 905) (w := 219696) (z := 0x2662895da8e70) (d := 0x58d24ffb78a2c8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage19_1 : BankCertificate 2430 84 1 KoalaH2430Banks.stage19.moving :=
  checked (k := 5823) (w := 3421597) (z := 0x68d2aab413d70d4) (d := 0x5c1e7bc1ac99439b2c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

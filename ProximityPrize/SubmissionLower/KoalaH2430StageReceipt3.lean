import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage08_0 : BankCertificate 2430 16 0 KoalaH2430Banks.stage08.free :=
  checked (k := 238) (w := 193119) (z := 0xe4afd8e9cc) (d := 0x4a9aed662c10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage08_1 : BankCertificate 2430 16 1 KoalaH2430Banks.stage08.moving :=
  checked (k := 1469) (w := 922731) (z := 0x11155e32ea9e8) (d := 0x22761ab4c6137ae0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage09_0 : BankCertificate 2430 10 0 KoalaH2430Banks.stage09.free :=
  checked (k := 248) (w := 195001) (z := 0x2b3cb0d1e50) (d := 0xc8f91f46530)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage09_1 : BankCertificate 2430 10 1 KoalaH2430Banks.stage09.moving :=
  checked (k := 1147) (w := 771702) (z := 0x77776637a5370) (d := 0x991257f4ed34c70)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage10_0 : BankCertificate 2430 17 0 KoalaH2430Banks.stage10.free :=
  checked (k := 334) (w := 250167) (z := 0xd72eafedc50) (d := 0x340318e49e90)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage10_1 : BankCertificate 2430 17 1 KoalaH2430Banks.stage10.moving :=
  checked (k := 1698) (w := 881340) (z := 0xaddb2f15951e0) (d := 0x310560beb81d7d0c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage11_0 : BankCertificate 2430 20 0 KoalaH2430Banks.stage11.free :=
  checked (k := 300) (w := 112481) (z := 0x89d1a4b7480) (d := 0x5475151a9340)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage11_1 : BankCertificate 2430 20 1 KoalaH2430Banks.stage11.moving :=
  checked (k := 1872) (w := 1147602) (z := 0xadc77a82c1224) (d := 0x515916de9bbc2bd0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

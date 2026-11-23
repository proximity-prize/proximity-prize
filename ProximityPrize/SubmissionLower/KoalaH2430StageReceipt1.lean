import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage00_0 : BankCertificate 2430 0 0 KoalaH2430Banks.stage00.free :=
  checked (k := 98) (w := 113143) (z := 0x10b7c96dc4) (d := 0x8f54b4e068)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage00_1 : BankCertificate 2430 0 1 KoalaH2430Banks.stage00.moving :=
  checked (k := 579) (w := 396512) (z := 0x6f6f3f2dcfc0) (d := 0x5195fba4157f5c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage01_0 : BankCertificate 2430 1 0 KoalaH2430Banks.stage01.free :=
  checked (k := 108) (w := 81005) (z := 0x1035c244e0) (d := 0xe0fc0f0be0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage01_1 : BankCertificate 2430 1 1 KoalaH2430Banks.stage01.moving :=
  checked (k := 605) (w := 464630) (z := 0xa679899aec80) (d := 0x7ca3dc7bc75b40)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage02_0 : BankCertificate 2430 2 0 KoalaH2430Banks.stage02.free :=
  checked (k := 120) (w := 151337) (z := 0x1b6d6c3ad0) (d := 0x13372a7e7c0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage02_1 : BankCertificate 2430 2 1 KoalaH2430Banks.stage02.moving :=
  checked (k := 726) (w := 543421) (z := 0xe53704b2b6d8) (d := 0xd5e1a6e47882e8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage03_0 : BankCertificate 2430 3 0 KoalaH2430Banks.stage03.free :=
  checked (k := 130) (w := 119199) (z := 0x6a464e9fe8) (d := 0x1bf5d6fd788)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage03_1 : BankCertificate 2430 3 1 KoalaH2430Banks.stage03.moving :=
  checked (k := 690) (w := 492861) (z := 0xf18a2fd08660) (d := 0x11b0f36a0a7dfac)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

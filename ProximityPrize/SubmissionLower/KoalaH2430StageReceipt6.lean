import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage20_0 : BankCertificate 2430 95 0 KoalaH2430Banks.stage20.free :=
  checked (k := 1032) (w := 557297) (z := 0x36b77debaa4c0) (d := 0x9a63042be124c0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage20_1 : BankCertificate 2430 95 1 KoalaH2430Banks.stage20.moving :=
  checked (k := 6607) (w := 3628969) (z := 0x160bd4eb05844ae0) (d := 0xa53ace8e42198ad8b8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage21_0 : BankCertificate 2430 61 0 KoalaH2430Banks.stage21.free :=
  checked (k := 555) (w := 27074) (z := 0x6eb829259ae0) (d := 0x61c151ae7def5e20)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage21_1 : BankCertificate 2430 61 1 KoalaH2430Banks.stage21.moving :=
  checked (k := 3000) (w := 1488512) (z := 0x3cfb7b92b7041c) (d := 0x2a2ba6f7ef13266f04)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

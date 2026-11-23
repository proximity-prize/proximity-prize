import ProximityPrize.SubmissionLower.HighCore82258Stages
import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Stages
open HighCore82258Stages

theorem stage12_0 : BankCertificate 2430 28 0 KoalaH2430Banks.stage12.free :=
  checked (k := 338) (w := 401647) (z := 0x2f61b130150) (d := 0x1bb4055c3ad90)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage12_1 : BankCertificate 2430 28 1 KoalaH2430Banks.stage12.moving :=
  checked (k := 2132) (w := 1170233) (z := 0x46acfc5ebe7fdc) (d := 0xe17d8bfd8fc411f0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage13_0 : BankCertificate 2430 32 0 KoalaH2430Banks.stage13.free :=
  checked (k := 356) (w := 225181) (z := 0xcbc07a25880) (d := 0x45297ef0056b0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage13_1 : BankCertificate 2430 32 1 KoalaH2430Banks.stage13.moving :=
  checked (k := 2034) (w := 1166291) (z := 0x51066d91baf9b8) (d := 0x18083037d1abafd5c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage14_0 : BankCertificate 2430 26 0 KoalaH2430Banks.stage14.free :=
  checked (k := 453) (w := 367484) (z := 0xf1b249665c4) (d := 0xd5786e43f744)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage14_1 : BankCertificate 2430 26 1 KoalaH2430Banks.stage14.moving :=
  checked (k := 2234) (w := 1498036) (z := 0x62addc0c3e40a0) (d := 0xc6f23b3c196cba88)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage15_0 : BankCertificate 2430 38 0 KoalaH2430Banks.stage15.free :=
  checked (k := 472) (w := 383249) (z := 0x422c403bf340) (d := 0x3318e1ede04c0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem stage15_1 : BankCertificate 2430 38 1 KoalaH2430Banks.stage15.moving :=
  checked (k := 2855) (w := 1752180) (z := 0x5a194e542a38fc) (d := 0x304580019995f550c)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Stages

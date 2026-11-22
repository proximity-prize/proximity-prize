import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt14Free :
    BankCertificate 2390 44 0 ⟨⟨376,522,118,5298⟩,0x183833c0000,0x7f6275d9⟩ :=
  checked (k := 523) (w := 259094) (z := 0x2ded3aa85840) (d := 0x5afa6733852e8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

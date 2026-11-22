import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt5Moving :
    BankCertificate 2390 4 1 ⟨⟨525,731,154,26968⟩,0x3e6d7fc0000,0x1cdc7da38⟩ :=
  checked (k := 729) (w := 360469) (z := 0x15b72436c5a54) (d := 0x1712f0ca90233c4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

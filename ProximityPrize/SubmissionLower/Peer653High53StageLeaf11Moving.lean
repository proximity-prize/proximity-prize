import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt11Moving :
    BankCertificate 2390 20 1 ⟨⟨1302,1815,383,49502⟩,0x3b50b1000000,0x442ac5ba92⟩ :=
  checked (k := 1806) (w := 572977) (z := 0xd93c1ddbeefe0) (d := 0x46218f1c7f469ab0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

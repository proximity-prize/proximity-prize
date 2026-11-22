import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt17Moving :
    BankCertificate 2390 103 1 ⟨⟨4774,6667,1405,189186⟩,0xb6532fbfc0000,0x304357eb723c⟩ :=
  checked (k := 6619) (w := 414937) (z := 0x7eb1c32eb51cbb8) (d := 0xbfbd30cbd84ebd3c08)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt4Free :
    BankCertificate 2390 3 0 ⟨⟨99,137,30,1144⟩,0x722180000,0x9dd5af⟩ :=
  checked (k := 138) (w := 166067) (z := 0x87e162a9e4) (d := 0x1a4d0027bc0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt15Moving :
    BankCertificate 2390 73 1 ⟨⟨3486,4863,1027,139224⟩,0x4711f2a780000,0xdb0e8041cee⟩ :=
  checked (k := 4833) (w := 992813) (z := 0x433e5ae51fb869c) (d := 0x289814b8560055f6c0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

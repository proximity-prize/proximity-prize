import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt12Moving :
    BankCertificate 2390 32 1 ⟨⟨1459,2035,429,91441⟩,0x536744d80000,0x6b96ecc888⟩ :=
  checked (k := 2023) (w := 449469) (z := 0x399346f7878c50) (d := 0x14f409c9a6a1cfc54)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

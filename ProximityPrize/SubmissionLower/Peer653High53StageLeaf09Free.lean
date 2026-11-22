import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt9Free :
    BankCertificate 2390 16 0 ⟨⟨171,237,50,3773⟩,0x2316e80000,0x53b7f45⟩ :=
  checked (k := 238) (w := 188339) (z := 0x189cfd315bc) (d := 0x4bf2c2579710)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

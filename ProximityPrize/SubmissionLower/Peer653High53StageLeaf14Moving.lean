import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt14Moving :
    BankCertificate 2390 44 1 ⟨⟨2253,3142,664,91156⟩,0x1334cd7ac0000,0x263b0eab16b⟩ :=
  checked (k := 3124) (w := 779666) (z := 0x1ba0b9b9f85baa8) (d := 0x4bca9c8888e1d4f40)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

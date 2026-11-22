import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt9Moving :
    BankCertificate 2390 16 1 ⟨⟨1014,1412,298,46976⟩,0x1c0729180000,0x1901657cf3⟩ :=
  checked (k := 1406) (w := 640492) (z := 0x459ce5bb3bd94) (d := 0x1e1fa40af4c36814)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

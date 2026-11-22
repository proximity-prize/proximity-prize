import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt13Moving :
    BankCertificate 2390 31 1 ⟨⟨1604,2235,472,73480⟩,0x6edb04b80000,0x9cb2a062f8⟩ :=
  checked (k := 2224) (w := 802969) (z := 0x2aa70270827d04) (d := 0x11ea0b364366b23cc)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

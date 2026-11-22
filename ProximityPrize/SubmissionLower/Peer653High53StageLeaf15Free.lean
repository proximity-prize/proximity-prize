import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt15Free :
    BankCertificate 2390 73 0 ⟨⟨599,831,188,7378⟩,0x617b2300000,0x32de21d13⟩ :=
  checked (k := 832) (w := 474853) (z := 0x19d52af2fc150) (d := 0x2a53f7a5abba18)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

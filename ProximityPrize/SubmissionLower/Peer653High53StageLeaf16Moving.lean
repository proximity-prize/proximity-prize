import ProximityPrize.SubmissionLower.Peer653High53Stages

/- Numerical port of HighCore82229StageReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace Peer653High53Stages

theorem receipt16Moving :
    BankCertificate 2390 76 1 ⟨⟨2760,3850,812,234140⟩,0x233f7cff80000,0x5601e71ab3f⟩ :=
  checked (k := 3826) (w := 727830) (z := 0x5a1c27ba0f46b8) (d := 0x3926fd85086585e148)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end Peer653High53Stages

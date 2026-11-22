import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsData

/- Numerical port of KoalaRectReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open Peer653High53 (terminal agreement)
open Peer653High53TerminalArithmetic (Parts)

private abbrev T := terminal .h2367

private abbrev row := runRow T.shape 2390 21 (rectWitness 21) 1671

theorem grade21Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1bc42ae0e314d032566c1efc0,0x1bc8b484fc7370d9f860f68c0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade21Chunk1 : P0_10_5.scan row 16 13 = ⟨true,0x1cb2f33a092bdd25f45296c0,0x1c6afc6ce2f7553337382a40⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

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

private abbrev row := runRow T.shape 2390 22 (rectWitness 22) 1657

theorem grade22Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1bcdc70b5f7dbc344e374cc20,0x1bd24fad837e7dcecd678f3e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade22Chunk1 : P0_10_5.scan row 16 12 = ⟨true,0x1c1c5a2c3ebc3026b73c0560,0x1bd473d1f52816da5f13d1e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

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

private abbrev row := runRow T.shape 2390 4 (rectWitness 4) 1558

theorem grade4Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xb85ea2a50669bac314f0d640,0xb87c713376f5bf552d3444e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade4Chunk1 : P0_10_5.scan row 16 9 = ⟨true,0xc44dbc197aedfabd6d302c0,0xc275444f111b83ee43f0700⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

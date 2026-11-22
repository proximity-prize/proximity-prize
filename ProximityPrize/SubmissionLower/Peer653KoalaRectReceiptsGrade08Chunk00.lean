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

private abbrev row := runRow T.shape 2390 8 (rectWitness 8) 1558

theorem grade8Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xafde474e0b2fc88eee07dec0,0xaffa85f9500f2c1bdb98ace0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade8Chunk1 : P0_10_5.scan row 16 9 = ⟨true,0xac8308e2550ef8f4cdaebc0,0xaac3598d97ab55b1eb4a480⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

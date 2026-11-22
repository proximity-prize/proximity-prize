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

private abbrev row := runRow T.shape 2390 24 (rectWitness 24) 1632

theorem grade24Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1beccb206c21c32055631ba80,0x1bf14f636befd1203954dd1e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade24Chunk1 : P0_10_5.scan row 16 11 = ⟨true,0x1a3d0e039b12e3f61e7e8880,0x19f56f723494c5d0282c2a40⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

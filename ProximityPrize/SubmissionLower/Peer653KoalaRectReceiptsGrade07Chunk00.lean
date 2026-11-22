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

private abbrev row := runRow T.shape 2390 7 (rectWitness 7) 1553

theorem grade7Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xae2ef845720e381aa20d6200,0xae4af1844b554f4efc514000⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade7Chunk1 : P0_10_5.scan row 16 8 = ⟨true,0xab9762a81e04d1a378dee00,0xa9dc00e0f7466b9d6c44a00⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

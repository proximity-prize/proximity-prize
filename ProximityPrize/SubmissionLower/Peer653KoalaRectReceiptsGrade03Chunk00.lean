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

private abbrev row := runRow T.shape 2390 3 (rectWitness 3) 1555

theorem grade3Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xb71c44786c56cc9d4f0f5c00,0xb739e267dfe992ce04b70740⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade3Chunk1 : P0_10_5.scan row 16 8 = ⟨true,0xc4a3f1977049d0c1507f4c0,0xc2ce7cf1c28a40f9a7b3e00⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

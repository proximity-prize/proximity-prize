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

private abbrev row := runRow T.shape 2390 9 (rectWitness 9) 1563

theorem grade9Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xb17e3533caa7ba8d8dd9dce0,0xb19ab5f28109d79bb9546260⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade9Chunk1 : P0_10_5.scan row 16 9 = ⟨true,0xad1d5eeee2435ecfa835c40,0xab59973963980b4f8705ec0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

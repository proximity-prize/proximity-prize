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

private abbrev row := runRow T.shape 2390 2 (rectWitness 2) 1552

theorem grade2Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xb5d022ff52e32617296bb080,0xb5ed8e0ae609c353d6147e80⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade2Chunk1 : P0_10_5.scan row 16 8 = ⟨true,0xc4bc1cb66ff7f5294577e00,0xc2e9cf458a9b85074c47e80⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

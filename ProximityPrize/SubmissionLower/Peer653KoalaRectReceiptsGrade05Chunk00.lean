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

private abbrev row := runRow T.shape 2390 5 (rectWitness 5) 1561

theorem grade5Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xb8d14b6d4bcb98479f8fa500,0xb8ef284a11ea8d8c9f8f8100⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade5Chunk1 : P0_10_5.scan row 16 9 = ⟨true,0xc2e5fac5f6ebe9b4462bd00,0xc10c9fe1b4e9bf67e96eb00⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

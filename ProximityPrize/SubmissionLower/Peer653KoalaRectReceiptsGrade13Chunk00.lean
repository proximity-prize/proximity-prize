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

private abbrev row := runRow T.shape 2390 13 (rectWitness 13) 1589

theorem grade13Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xbb9fda0c51823f28eb4b5dc0,0xbbbdfbd70bed7ac4a3948ee0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade13Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0xb31fb43ab1f274309e47b40,0xb14213f5a6deb6b49026a60⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

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

private abbrev row := runRow T.shape 2390 28 (rectWitness 28) 1594

theorem grade28Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1c1d016d35491a0de8fe282a0,0x1c217ee75447f2f93c53f76a0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade28Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0x1754419cb0d933053c362160,0x170d127b045c5c7265efdf80⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

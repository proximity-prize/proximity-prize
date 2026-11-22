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

private abbrev row := runRow T.shape 2390 27 (rectWitness 27) 1603

theorem grade27Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1c12651ce9de0091c14a04d60,0x1c16e414837e75d5b67e8ed20⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade27Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0x17f829470123570e1b224000,0x17b0e1ab0db19825a917cac0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

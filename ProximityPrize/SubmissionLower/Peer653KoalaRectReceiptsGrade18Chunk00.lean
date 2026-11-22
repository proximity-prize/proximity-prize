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

private abbrev row := runRow T.shape 2390 18 (rectWitness 18) 1722

theorem grade18Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1bafa72b6b7df86df49556140,0x1bb431e31256049954d8c7200⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade18Chunk1 : P0_10_5.scan row 16 15 = ⟨true,0x1dfb53943a76bf7b65561ce0,0x1db34b916094be96c135a340⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

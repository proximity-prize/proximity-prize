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

private abbrev row := runRow T.shape 2390 1 (rectWitness 1) 1645

theorem grade1Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x144dabc2798732e1bc6c41740,0x145113c021359a34474bf0960⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade1Chunk1 : P0_10_5.scan row 16 12 = ⟨true,0x1dea2ccdeea0457ad0980ae0,0x1db428f187acc9d337a7e0a0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

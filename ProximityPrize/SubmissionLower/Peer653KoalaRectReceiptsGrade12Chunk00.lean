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

private abbrev row := runRow T.shape 2390 12 (rectWitness 12) 1599

theorem grade12Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xc71d625e1547a8802b5f0680,0xc73d7f1f4e07d608aa28d480⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade12Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0xc6c138c199b1dc3f8ef6900,0xc4c42d8814210e251227880⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

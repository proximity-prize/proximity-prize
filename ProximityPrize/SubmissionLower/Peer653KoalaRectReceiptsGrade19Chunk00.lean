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

private abbrev row := runRow T.shape 2390 19 (rectWitness 19) 1703

theorem grade19Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1bb70c0e08a1b7df5c94cfb60,0x1bbb9664e1a46cabd1ed159c0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade19Chunk1 : P0_10_5.scan row 16 14 = ⟨true,0x1d8509fdb654dc2f7cf06080,0x1d3d080728e3330abb2dd840⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

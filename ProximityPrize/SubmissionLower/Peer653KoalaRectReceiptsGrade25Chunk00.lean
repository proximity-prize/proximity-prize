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

private abbrev row := runRow T.shape 2390 25 (rectWitness 25) 1622

theorem grade25Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1bfa5e618643aac463d2c2ac0,0x1bfee0bb064451ead2ba4a720⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade25Chunk1 : P0_10_5.scan row 16 11 = ⟨true,0x196b505523159ae436ae4bc0,0x1923d12ac23ab56e63ee2340⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

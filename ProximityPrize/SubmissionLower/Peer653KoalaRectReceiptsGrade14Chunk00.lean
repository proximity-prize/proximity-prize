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

private abbrev row := runRow T.shape 2390 14 (rectWitness 14) 1597

theorem grade14Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xbf1cdbb4709d97b9d8f9bb00,0xbf3b8bef1a58a9871b73eee0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade14Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0xb5122e2bdbc8d5135f6fa00,0xb32bba85645acebe4ba7560⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

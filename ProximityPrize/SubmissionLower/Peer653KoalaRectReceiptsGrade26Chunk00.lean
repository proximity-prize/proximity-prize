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

private abbrev row := runRow T.shape 2390 26 (rectWitness 26) 1612

theorem grade26Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0x1c06dc68b2dacbbc43f65cfa0,0x1c0b5cffdb48e059e324fe9e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade26Chunk1 : P0_10_5.scan row 16 11 = ⟨true,0x18aa537786f2a91107cf3fa0,0x1862f131bb171a53622f0cc0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

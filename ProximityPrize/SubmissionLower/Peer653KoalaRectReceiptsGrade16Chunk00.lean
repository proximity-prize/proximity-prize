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

private abbrev row := runRow T.shape 2390 16 (rectWitness 16) 1618

theorem grade16Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xc5718586744e453f15343380,0xc59137626b97ae7205341ec0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade16Chunk1 : P0_10_5.scan row 16 11 = ⟨true,0xb7e390780d1de17e4149640,0xb5ed2579e43530907cd7340⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

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

private abbrev row := runRow T.shape 2390 11 (rectWitness 11) 1592

theorem grade11Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xc436dfdbc3dcd6a760d8ca80,0xc456872eba2f0706d2477080⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade11Chunk1 : P0_10_5.scan row 16 10 = ⟨true,0xc59c16c1894c645eb180280,0xc3a6525e3fb10ee74cbc400⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

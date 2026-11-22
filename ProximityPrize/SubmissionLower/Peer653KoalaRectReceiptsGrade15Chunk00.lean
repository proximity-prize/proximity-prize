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

private abbrev row := runRow T.shape 2390 15 (rectWitness 15) 1611

theorem grade15Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xc4e49794496fa68908897300,0xc50439d8ae024b081ae83380⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade15Chunk1 : P0_10_5.scan row 16 11 = ⟨true,0xba26cf3a9b0d15f154e1200,0xb8315ba67639c81d639be80⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

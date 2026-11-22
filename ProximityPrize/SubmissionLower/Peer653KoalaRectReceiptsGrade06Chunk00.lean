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

private abbrev row := runRow T.shape 2390 6 (rectWitness 6) 1550

theorem grade6Chunk0 : P0_10_5.scan row 0 16 = ⟨true,0xad1e9094e56234732a607600,0xad3a61a47c7805557c0236e0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

theorem grade6Chunk1 : P0_10_5.scan row 16 8 = ⟨true,0xac2193486eebfabe9a59c60,0xaa68aeb9e897c08ba23e7c0⟩ := by
  exact P0_10_5.Row.eq_of_check (by decide +kernel)

end KoalaRectReceipts

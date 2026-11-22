import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade16Chunk00

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


theorem r16 : BlockChecks T.shape T.nodeRows T.poleMoment 2390 16 (rectWitness 16) :=
  certify (n := 1618) (last := 11) (cost := 0xd0ef985d7f7dedf964620700) (costNext := 0xd0ef9d9e024a9b1986621180)
    (Parts.more grade16Chunk0
      (Parts.final grade16Chunk1))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end KoalaRectReceipts

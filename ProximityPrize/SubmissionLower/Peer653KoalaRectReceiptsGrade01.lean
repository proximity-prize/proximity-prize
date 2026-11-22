import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade01Chunk00

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


theorem r1 : BlockChecks T.shape T.nodeRows T.poleMoment 2390 1 (rectWitness 1) :=
  certify (n := 1645) (last := 12) (cost := 0x162c4e245b333eb60ece20700) (costNext := 0x162c4e786360098810ee21180)
    (Parts.more grade1Chunk0
      (Parts.final grade1Chunk1))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end KoalaRectReceipts

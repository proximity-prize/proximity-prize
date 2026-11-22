import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade17Chunk00

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


theorem r17 : BlockChecks T.shape T.nodeRows T.poleMoment 2390 17 (rectWitness 17) :=
  certify (n := 1667) (last := 13) (cost := 0xebca57b116de274cc8620700) (costNext := 0xebca5cf199aad46cea621180)
    (Parts.more grade17Chunk0
      (Parts.final grade17Chunk1))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end KoalaRectReceipts

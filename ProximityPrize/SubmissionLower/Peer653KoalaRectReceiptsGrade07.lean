import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade07Chunk00

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


theorem r7 : BlockChecks T.shape T.nodeRows T.poleMoment 2390 7 (rectWitness 7) :=
  certify (n := 1553) (last := 8) (cost := 0xb8e84d0c2b5e424620620700) (costNext := 0xb8e8524cae2aef6642621180)
    (Parts.more grade7Chunk0
      (Parts.final grade7Chunk1))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)

end KoalaRectReceipts

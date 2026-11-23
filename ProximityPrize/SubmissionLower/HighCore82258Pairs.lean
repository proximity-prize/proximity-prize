import ProximityPrize.SubmissionLower.HighCore82258Source
import ProximityPrize.SubmissionLower.HighCore82258StageReceipts

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258
noncomputable section
open FrontCore82258 (AnchorModel AnchoredFamily)
open P1 (p)
open K1_14 (Shape Banks Jet FX triangle shapeSum seedHasse)
open K1_14_2 (UsesSeed)
open K1_14_2_1 (exists_layered)
open Polynomial Finset
open private fixed_of_no_seed from ProximityPrize.SubmissionLower.Fast051
open private eligible  cutoff_total from ProximityPrize.SubmissionLower.UpperBranch2
end
end HighCore82258
end


namespace HighCore82258
open FrontCore82258 (AnchorModel AnchoredFamily)
open K1_14 (Banks)


end HighCore82258

import ProximityPrize.SubmissionLower.HighCore82258Data
import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace HighCore82258Stages
open Finset
open P3 (p)
open HighCore82258 (agreement cutoffCount rawWidth  gain)
open HighCore82258 (Bank debit)
open K1_14 (Shape shapeSum triangle)
open K1_14_2_1 (twice_sum_linear)
open P2_7_2_2 (row rising level tailSum)
end HighCore82258Stages
end

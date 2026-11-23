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
open private twice_sum_linear from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private row rising level   tailSum  from ProximityPrize.SubmissionLower.SilverBase
end HighCore82258Stages
end

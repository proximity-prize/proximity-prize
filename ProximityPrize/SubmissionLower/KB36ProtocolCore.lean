/- Bome2017, joint projection accounting for 68.36 after Lucieno and BitWonka. -/
/- Apache-2.0. Adapted from the accepted Bome2017 68.32 proof and the 69.69 genuine reduction, after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.KB36Projection
import ProximityPrize.SubmissionLower.Mid6833OpenRange
import ProximityPrize.SubmissionLower.Mid6833IntermediateDegree6842Scalar
namespace ProximityPrize.SubmissionLower.JointProtocol6836
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
local instance normalFieldEq : DecidableEq IRSProfile.Field := Classical.decEq _
local instance normalIndexEq : DecidableEq IRSProfile.Index := Classical.decEq _
theorem protocol_at (rem : Intermediate.At 181039 274980640798883310) : ProtocolClaim 6836 332210175 1073741824 := by
  apply protocol_of_projected
  exact Intermediate.given_of_at (r:=radius) (by decide) (by decide) (by decide) (by norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]) rem
open K6969Global Koala6831Separation Koala6831Comparison Genuine6969 Genuine6969.IntermediateDivisor
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Koala6831BenchmarkField (prime)

theorem semilinear_price
    (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (SeedRing F)) (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (hard : Difficult U S P q N) (fit : ∀g∈S,181039≤(agreementSet Dmn U P g).card)
    (normalized : CanNormalize N 2133) :
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1) ≤ 274674055653798492 := by
  have sized : ScalarAt (131071+2133) 180980 274242766579991802 := by
    change ScalarAt 133204 180980 274242766579991802
    intro x u
    exact Frontier.SeedFreeze.scalar_list_intermediatedegree6842 x u
  exact semilinear_at (A:=180980) (C:=274242766579991802) (B:=274674055653798492) (k:=2133)
    (by decide) (by decide) sized (by decide) U S P q N hard
    (fun g hg => (show 180980≤181039 by decide).trans (fit g hg)) normalized

#print axioms word_list
#print axioms semilinear_price
end
end ProximityPrize.SubmissionLower.JointProtocol6836

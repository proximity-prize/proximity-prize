/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833OpenRange
import ProximityPrize.SubmissionLower.Mid6833Target6833
import ProximityPrize.SubmissionLower.Mid6833K6833CompleteLong
namespace ProximityPrize.SubmissionLower.Target6833
open ProximityPrize.Benchmark K6969Global Koala6831Separation Koala6831Comparison Genuine6969 Genuine6969.IntermediateDivisor
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Koala6831BenchmarkField (prime)
open scoped Classical
noncomputable section
local instance mid6833Local_Range6833_10  : DecidableEq IRSProfile.Field := Classical.decEq _
local instance mid6833Local_Range6833_11  : DecidableEq IRSProfile.Index := Classical.decEq _
set_option maxHeartbeats 4000000

/-- Only score-specific, genuinely agreeing, non-normalizable singular rows in the indicated range remain. -/
theorem protocol_of_short (unpriced : Intermediate.OpenAt 181059 274980695007758447 2235 9584) :
    ProtocolClaim 6834 332127561 1073741824 := by
  apply protocol_at
  intro U S P q N hard fit pencil
  by_cases norm : CanNormalize N 2235
  · exact semilinear_6833 U S P q N hard fit norm
  have lo : 2235<primitiveExcess 131071 q :=
    Nat.lt_of_not_ge (fun h => norm (Intermediate.can_of_excess N h))
  by_cases short : primitiveExcess 131071 q<9584
  · exact unpriced U S P q N hard fit pencil lo short norm
  let hchar := Koala6831BenchmarkField.characteristic
  have h := hard.actual
  have high : primitiveExcess 131071 q≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have bound := Koala6831BenchmarkResidual.separated_retained_6833 Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index h.primitive h.first_ne h.second_ne
    (Nat.le_of_not_gt short) high N h.good h.selection.degree_le fit pencil
  unfold prime
  omega
#print axioms protocol_of_short
end
end ProximityPrize.SubmissionLower.Target6833

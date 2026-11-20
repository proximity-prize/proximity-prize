/- Apache-2.0. Bome2017. Join the 68.36 short, normalizable and long families. -/
import ProximityPrize.SubmissionLower.KB36JCompleteLong
import ProximityPrize.SubmissionLower.KB36ProtocolCore
namespace ProximityPrize.SubmissionLower.JointProtocol6836
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
local instance joint6836ShortFieldEq : DecidableEq IRSProfile.Field := Classical.decEq _
local instance joint6836ShortIndexEq : DecidableEq IRSProfile.Index := Classical.decEq _
open K6969Global Koala6831Separation Koala6831Comparison Genuine6969 Genuine6969.IntermediateDivisor
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Koala6831BenchmarkField (prime)

theorem at_of_joint_short
    (unpriced : Intermediate.OpenAt 181039 274980640798883310 2133 9615) :
    Intermediate.At 181039 274980640798883310 := by
  intro U S P q N hard fit pencil
  by_cases normal : CanNormalize N 2133
  · exact (semilinear_price U S P q N hard fit normal).trans (by decide)
  have low : 2133<primitiveExcess 131071 q :=
    Nat.lt_of_not_ge (fun h => normal (Intermediate.can_of_excess N h))
  by_cases short : primitiveExcess 131071 q < 9615
  · exact unpriced U S P q N hard fit pencil low short normal
  let hchar := Koala6831BenchmarkField.characteristic
  have h := hard.actual
  have high : primitiveExcess 131071 q≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have bound := Koala6831BenchmarkResidual.separated_retained_joint6836 Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index h.primitive h.first_ne h.second_ne
    (Nat.le_of_not_gt short) high N h.good h.selection.degree_le
    fit pencil
  unfold prime
  omega

theorem protocol_of_joint_short
    (unpriced : Intermediate.OpenAt 181039 274980640798883310 2133 9615) :
    ProtocolClaim 6836 332210175 1073741824 :=
  protocol_at (at_of_joint_short unpriced)

#print axioms protocol_of_joint_short
end
end ProximityPrize.SubmissionLower.JointProtocol6836

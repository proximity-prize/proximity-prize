import ProximityPrize.SubmissionLower.Koala6844Endpoint
import ProximityPrize.SubmissionLower.Koala6844HighOrdinary
import ProximityPrize.SubmissionLower.Koala6844NormalizationDegreeOne


namespace ProximityPrize.SubmissionLower.Koala6844GeometryDispatch

open ProximityPrize.Benchmark
open Koala6844BenchmarkCases Koala6844BenchmarkRetention Koala6844BenchmarkGeometry
open Koala6844Comparison Koala6844Normalization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

def SeparatedRetainedBound : Prop :=
  ∀ (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field)),
    RetainedComparison received retained selected q →
    Koala6844Separation.NormalForm q 131071 (primitiveExcess 131071 q) →
    retained.card ≤ retainedSeedBudget

theorem remaining_geometry_of_separated (hSeparated : SeparatedRetainedBound) :
    RemainingGeometrySeedBound := by
  intro received retained selected q h hsingular
  let c := Koala6844HighOrdinary.weightDegree Koala6844HighOrdinary.totalWeights (primitiveRowLift q)
  by_cases hc : 2 ≤ c
  · by_cases hδ : 11500 ≤ primitiveExcess 131071 q
    · exact Koala6844HighOrdinary.benchmark_ordinary_retained_le_seed_budget
        received retained selected q h hδ hc
    · have hδ' : primitiveExcess 131071 q ≤ 11499 := by omega
      obtain ⟨N⟩ := normal_form_of_retained_singular h (hsingular hδ')
      exact hSeparated received retained selected q h N
  · have hc' : c ≤ 1 := by omega
    obtain ⟨N⟩ := normal_form_of_degree_one h hc'
    exact hSeparated received retained selected q h N

theorem protocolClaim_of_separated (hSeparated : SeparatedRetainedBound) :
    ProtocolClaim 6844 332537855 1073741824 :=
  Koala6844Assembly.protocolClaim_of_retained_geometry (remaining_geometry_of_separated hSeparated)

end

end ProximityPrize.SubmissionLower.Koala6844GeometryDispatch


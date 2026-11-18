/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833SingularOnly
import ProximityPrize.SubmissionLower.Mid6833CompleteLong
import ProximityPrize.SubmissionLower.Mid6833RetunedReduction
namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Separation ProximityPrize.Benchmark
open Koala6831BenchmarkField (prime frobenius)
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open scoped Classical
noncomputable section
variable {K I : Type} [Field K] [Fintype I]
def ShortNormalized (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (U : Received K I) (S : Finset K) (P : SelectionMap K) (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ U S P q → primitiveExcess 131071 q < 12137 →
    (∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0) →
    NormalForm q 131071 (primitiveExcess 131071 q) →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget

theorem protocol_of_short
    (remaining : ShortNormalized IRSProfile.domain frobenius.toRingHom) :
    ProtocolClaim 6969 337530879 1073741824 := by
  let hchar := Koala6831BenchmarkField.characteristic
  apply RetunedPrice6969.protocol6969_of_seed_bound
  apply selected_of_singular IRSProfile.domain frobenius Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index
  intro U S P q h _ singular N
  by_cases hshort : primitiveExcess 131071 q < 12137
  · exact remaining U S P q h hshort singular N
  have hδ : primitiveExcess 131071 q≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have bound := Koala6831BenchmarkResidual.separated_retained_6969 Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index h.primitive h.first_ne h.second_ne
    (by omega) hδ N h.good h.selection.degree_le h.selection.agreement h.selection.pencil
  unfold budget prime
  omega

#print axioms protocol_of_short
end
end ProximityPrize.SubmissionLower.K6969Global

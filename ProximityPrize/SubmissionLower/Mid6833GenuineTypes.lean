/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The rank split, primitive discard, and separation estimates are adapted from
the 69.69 reduction and Bome2017's accepted 68.32 proof after Lucieno and BitWonka.
Here the rank split is localized to one fixed family of genuinely bad supports. -/
import ProximityPrize.SubmissionLower.Mid6833ProtocolResidual
import ProximityPrize.SubmissionLower.Mid6833ProjectedProtocol
namespace ProximityPrize.SubmissionLower.Genuine6969
open ProximityPrize.Benchmark Koala6831Comparison Koala6831Ordinary Koala6831Separation K6969Global
open Koala6831BenchmarkField (prime frobenius)
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes coefficientDeterminant)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
variable {K I : Type} [Field K] [Fintype I]
/-- Both coordinates cannot be reconstructed on the support of any of these
witnesses. Each support is the full agreement set of its chosen polynomial. -/
def Bad (x : I ↪ K) (U : Received K I) (S : Finset K) (P : SelectionMap K) : Prop :=
  ∀ g∈S, ¬∃ V W : Polynomial K, V.natDegree≤131071 ∧ W.natDegree≤131071 ∧
    ∀ i∈agreementSet x U P g, V.eval (x i)=U 0 i ∧ W.eval (x i)=U 1 i

abbrev F := IRSProfile.Field
abbrev Dmn := IRSProfile.domain
abbrev σ := frobenius.toRingHom

end
end ProximityPrize.SubmissionLower.Genuine6969

/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833GoalJoin
import ProximityPrize.SubmissionLower.Mid6833MovingScalar
import ProximityPrize.SubmissionLower.Mid6833NormalDegree
namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Separation ProximityPrize.Benchmark
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open Koala6831BenchmarkField (prime frobenius)
open scoped Classical
noncomputable section
set_option maxRecDepth 20000

/-- Only these genuinely short singular normal forms still need a uniform count. -/
def Residual : Prop :=
  ∀ (U : Received IRSProfile.Field IRSProfile.Index) (S : Finset IRSProfile.Field)
    (P : SelectionMap IRSProfile.Field) (q : SymbolicRow (SeedRing IRSProfile.Field)),
    RetainedComparison IRSProfile.domain frobenius.toRingHom U S P q →
    primitiveExcess 131071 q < 12137 →
    (∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0) →
    ∀ N : NormalForm q 131071 (primitiveExcess 131071 q),
    combinedDegree q ≤ 2 →
    (pairDegree N.A+pairDegree N.B+472<primitiveExcess 131071 q ∨
      (N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0 ∧ N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0 ∧ IsCoprime N.d₀ N.d₁)) →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget

theorem protocol_reduction (remaining : Residual) :
    ProtocolClaim 6969 337530879 1073741824 := by
  apply protocol_of_short
  intro U S P q h hshort hmin N
  by_cases d : primitiveExcess 131071 q ≤ pairDegree N.A + pairDegree N.B + 472
  · by_cases left : N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0
    · by_cases right : N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0
      · by_cases cp : IsCoprime N.d₀ N.d₁
        · exact remaining U S P q h hshort hmin N (normal_degree N) (Or.inr ⟨left,right,cp⟩)
        · exact moving_determinant_class IRSProfile.domain frobenius.toRingHom
            Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inr (Or.inr cp)) d
      · exact moving_determinant_class IRSProfile.domain frobenius.toRingHom
          Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inr (Or.inl right)) d
    · exact moving_determinant_class IRSProfile.domain frobenius.toRingHom
        Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inl left) d
  · exact remaining U S P q h hshort hmin N (normal_degree N) (Or.inl (lt_of_not_ge d))

#print axioms protocol_reduction
end
end ProximityPrize.SubmissionLower.K6969Global

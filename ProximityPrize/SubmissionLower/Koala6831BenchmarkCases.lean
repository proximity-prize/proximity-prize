import ProximityPrize.SubmissionLower.Koala6831Assembly
import ProximityPrize.SubmissionLower.Koala6831BenchmarkField
import ProximityPrize.SubmissionLower.Koala6831BenchmarkPrimitive
import ProximityPrize.SubmissionLower.Koala6831RankTwo

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkCases

open ProximityPrize.Benchmark
open Koala6831BenchmarkField Koala6831Comparison Koala6831Protocol
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

abbrev ReceivedWords := Koala6831BenchmarkPrimitive.Received IRSProfile.Field IRSProfile.Index

abbrev ComparisonRows (received : ReceivedWords) (d : ℕ) :=
  Koala6831BenchmarkPrimitive.Rows IRSProfile.domain frobenius.toRingHom received d

abbrev coefficientDeterminant {received : ReceivedWords} {d₀ d₁ : ℕ}
    (first : ComparisonRows received d₀) (second : ComparisonRows received d₁) :=
  Koala6831BenchmarkPrimitive.coefficientDeterminant first.1 second.1

abbrev Selection (received : ReceivedWords) (seeds : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field) : Prop :=
  Koala6831BenchmarkPrimitive.Selection IRSProfile.domain received seeds selected

theorem independent_rows_le_seed_budget
    {received : ReceivedWords} {d₀ d₁ : ℕ} (hle₀ : d₀ ≤ 200) (hle₁ : d₁ ≤ 200)
    (first : ComparisonRows received d₀) (second : ComparisonRows received d₁)
    (hdet : coefficientDeterminant (received := received) (d₀ := d₀) (d₁ := d₁) first second ≠ 0)
    (seeds : Finset IRSProfile.Field) (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (support : Selection received seeds selected) : seeds.card ≤ mcaBudget := by
  unfold coefficientDeterminant Koala6831BenchmarkPrimitive.coefficientDeterminant at hdet
  have h := Koala6831RankTwo.independent_mixed_rows_card_le
    (K := IRSProfile.Field) (I := IRSProfile.Index)
    (A := 181084) (a := 50013) (d₀ := d₀) (d₁ := d₁)
    (p := prime) (D := 200) (w := 131071) (e := 81060)
    (by decide) (by decide) hle₀ hle₁ IRSProfile.domain received frobenius.toRingHom
    domain_fixed frobenius_apply (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide)
    first second hdet seeds selected support.degree_le
    (by exact support.agreement) (by exact support.pencil)
  rw [IRSProfile.card_index] at h
  exact h.trans (by decide +kernel)

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkCases

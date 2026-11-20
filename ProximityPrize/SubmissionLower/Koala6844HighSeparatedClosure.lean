import ProximityPrize.SubmissionLower.Koala6844HighSeparatedBenchmark
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedCurveBudget


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open ProximityPrize.Benchmark
open Koala6844BenchmarkCases Koala6844BenchmarkField Koala6844BenchmarkRetention Koala6844Comparison
open Koala6831Intrinsic Koala6831OrdinaryIncidence
open RCN135 RCN136 RCN137
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

private theorem carrier_seed_count {K I : Type} [Field K] [CharP K 2130706433]
    (hp : Nat.Prime 2130706433)
    (Q : Carrier K) (nonzero : Q ≠ 0)
    (caps : ∀ d ∈ Q.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧
      d 0 + 131071 * d 1 < 4000000)
    (domain : I ↪ K) (U₀ U₁ : I → K) (nodes : Finset I)
    (enough : 180959 ≤ nodes.card) (averaged : nodeAverage nodes.card 131071 180959 ≤ 3)
    (retained : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ retained, (selected g).natDegree ≤ 131071)
    (graph : ∀ g ∈ retained, graphSpecialize (selected g) g (g ^ 2130706433) Q = 0)
    (hagreements : ∀ g ∈ retained, 180959 ≤
      (nodes.filter (fun i => (selected g).eval (domain i) = U₀ i + g * U₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds retained selected P₀ P₁).card ≤ 81186) :
    retained.card ≤ retainedSeedBudget := by
  classical
  apply long_retained_seed_budget_of_factor_counts Q nonzero
    (fun d hd => ⟨(caps d hd).1, (caps d hd).2.1, (caps d hd).2.2.1⟩)
    retained selected graph
  intro F hF G hG
  obtain ⟨hY, hT, hZ, hweight⟩ := long_native_factor_caps Q F nonzero hF caps
  have hFirr := (normalizedFactorSet_spec Q F hF).1
  obtain ⟨hGirr, hGdiv⟩ := surfaceFactors_spec (polynomialEmbedding K) F G hG
  let seeds := longFactorSeeds F G retained selected
  have membership (g : K) (hg : g ∈ seeds) :
      g ∈ retained ∧ MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) G = 0 ∧
        graphSpecialize (selected g) g (g ^ 2130706433) F = 0 ∧
        graphSpecialize (selected g) g (g ^ 2130706433) (implicitRegularity F) ≠ 0 :=
    Finset.mem_filter.mp hg
  exact long_factor_seed_count F hp hFirr hweight hY hT hZ G hGirr hGdiv
    domain U₀ U₁ nodes enough averaged seeds retained (fun g hg => (membership g hg).1) selected
    (fun g hg => hdegree g (membership g hg).1)
    (fun g hg => (membership g hg).2.2.1)
    (fun g hg => (membership g hg).2.2.2)
    (fun g hg => (membership g hg).2.1)
    (fun g hg => hagreements g (membership g hg).1)
    hpencil

theorem high_separated_retained_le_seed_budget
    (hp : Nat.Prime 2130706433)
    (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field))
    (data : RetainedComparison received retained selected q)
    (high : 9800 ≤ primitiveExcess 131071 q)
    (normal : Koala6844Separation.NormalForm q 131071 (primitiveExcess 131071 q)) :
    retained.card ≤ retainedSeedBudget := by
  classical
  letI : CharP IRSProfile.Field 2130706433 := characteristic
  obtain ⟨Q, nonzero, support, graph⟩ :=
    exists_benchmark_carrier received retained selected q data high normal
  have caps (d : Fin 4 →₀ ℕ) (hd : d ∈ Q.support) :
      d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧
        d 0 + 131071 * d 1 < 4000000 := by
    obtain ⟨hy, ht, hz, hw, _⟩ := support d hd
    have hexcess : primitiveExcess 131071 q ≤ 31610 :=
      (Nat.le_add_right _ _).trans data.excess_bad
    exact ⟨hy, ht, hz, hw.trans_lt (by omega)⟩
  have enough : 180959 ≤ (Finset.univ : Finset IRSProfile.Index).card := by
    rw [Finset.card_univ, IRSProfile.card_index]
    decide
  have averaged : nodeAverage (Finset.univ : Finset IRSProfile.Index).card 131071 180959 ≤ 3 := by
    rw [Finset.card_univ, IRSProfile.card_index]
    decide +kernel
  exact carrier_seed_count hp Q nonzero caps IRSProfile.domain (received 0) (received 1)
    Finset.univ enough averaged retained selected data.selection.degree_le graph
    data.selection.agreement data.selection.pencil

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated


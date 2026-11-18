import ProximityPrize.SubmissionLower.Koala6831Assembly
import ProximityPrize.SubmissionLower.Koala6831BenchmarkCases
import ProximityPrize.SubmissionLower.Koala6831BenchmarkRetention
import ProximityPrize.SubmissionLower.Koala6831RankFour

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkGeometry

open ProximityPrize.Benchmark
open Koala6831BenchmarkField Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention
open Koala6831Comparison Koala6831Protocol
open scoped Classical Matrix

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000

variable {K I : Type} [Field K] [Fintype I]

private def word (σ : K →+* K) (received : Received K I) (i : I) : Fin 4 → K :=
  ![received 0 i, received 1 i, σ (received 0 i), σ (received 1 i)]

theorem rank_four_retained_le_seed_budget
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (h : RetainedComparison x σ received retained selected q)
    (hδ : primitiveExcess 131071 q ≤ 12501)
    (keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial)
    (hdet : (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det ≠ 0) :
    retained.card ≤ retainedSeedBudget := by
  let δ := primitiveExcess 131071 q
  have hbetaExcess : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
  have hβ : q.beta.natDegree ≤ 131071 + δ := by omega
  have hfirst : q.first.natDegree ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hsecond : q.second.natDegree ≤ δ := (le_max_right _ _).trans (le_max_right _ _)
  refine (Koala6831RankFour.retained_card_le
    x retained (agreementSet x received selected) selected
    q keys (word σ received) δ hδ hdet hβ hfirst hsecond h.selection.degree_le
    h.selection.agreement ?_ ?_ ?_).trans (by decide +kernel)
  · intro g hg i hi
    have hnotBad : i ∉ badNodes x σ received q :=
      fun hbad => (Finset.disjoint_left.mp (h.good g hg).2) hi hbad
    have hzero : q.atNode (seedNode x i)
        (affineSeedWord (conjugateWord σ (received 0)) (conjugateWord σ (received 1)) 0 i)
        (affineSeedWord (conjugateWord σ (received 0)) (conjugateWord σ (received 1)) 1 i) = 0 := by
      by_contra hnonzero
      apply hnotBad
      unfold badNodes primitiveBadNodes
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonzero⟩
    simpa [word, seedNode, affineSeedWord, conjugateWord] using hzero
  · intro g hg i hi
    simpa [word] using eval_eq_of_mem_agreementSet hi
  · intro p₀ p₁ hp₀ hp₁
    refine (Finset.card_le_card (t := RCN050.pencilSeeds retained selected p₀ p₁) ?_).trans
      (h.selection.pencil p₀ p₁ hp₀ hp₁)
    intro g hg
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hg)

def RemainingGeometrySeedBound (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ received retained selected q →
    (primitiveExcess 131071 q ≤ 12501 →
      ∀ keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial,
        (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det = 0) →
    retained.card ≤ retainedSeedBudget

theorem retained_bound_of_geometry
    (x : I ↪ K) (σ : K →+* K) (hGeometry : RemainingGeometrySeedBound x σ) :
    RetainedTwoSidedSeedBound x σ := by
  intro received retained selected q h
  by_cases hRankFour : primitiveExcess 131071 q ≤ 12501 ∧
      ∃ keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial,
        (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det ≠ 0
  · obtain ⟨hδ, keys, hdet⟩ := hRankFour
    exact rank_four_retained_le_seed_budget h hδ keys hdet
  · refine hGeometry received retained selected q h ?_
    intro hδ keys
    by_contra hdet
    exact hRankFour ⟨hδ, keys, hdet⟩

theorem seed_bound_of_geometry
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (hMixed : MixedRowsSeedBound x σ) (hGeometry : RemainingGeometrySeedBound x σ) :
    RCN050.SelectedNoLargePencilBound x 131071 errors mcaBudget :=
  seed_bound_of_two_sided_primitive x σ hfixed hpow hcard hMixed
    (primitive_bound_of_retained x σ hfixed hpow (retained_bound_of_geometry x σ hGeometry))

private theorem koala_mixed_rows_bound :
    MixedRowsSeedBound IRSProfile.domain frobenius.toRingHom := by
  intro received first second hdet seeds selected support
  exact Koala6831BenchmarkCases.independent_rows_le_seed_budget
    (received := received) (d₀ := 4) (d₁ := 62150) (by decide) (by decide)
    first second hdet seeds selected support

theorem protocolClaim_6832_of_geometry
    (hGeometry : RemainingGeometrySeedBound IRSProfile.domain frobenius.toRingHom) :
    ProtocolClaim 6832 332050431 1073741824 :=
  Koala6831Assembly.protocolClaim_6832_of_seed_bound
    (seed_bound_of_geometry IRSProfile.domain frobenius.toRingHom domain_fixed frobenius_apply
      IRSProfile.card_index koala_mixed_rows_bound hGeometry)

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkGeometry

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

import ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual
import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongFactorCount
import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongPersistentSurface

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention Koala6831BenchmarkResidual
open Koala6831OrdinaryIncidence RCN135 RCN136 RCN137
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4200000

variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

theorem long_separated_retained_count
    (x : I ↪ K) (σ : K →+* K) (hcard : Fintype.card I = 262144)
    (hp : Nat.Prime 2130706433) : LongSeparatedRetainedCount x σ := by
  intro received seeds selected q h _ hδ _ Q
  let nodes := (Finset.univ : Finset I)
  have hn : nodes.card = 262144 := Finset.card_univ.trans hcard
  have hAn : 181084 ≤ nodes.card := hn.symm ▸ (by decide)
  have haverage : nodeAverage nodes.card 131071 181084 ≤ 3 := by
    rw [hn]
    norm_num [nodeAverage]
  have hc (d : Fin 4 →₀ ℕ) (hd : d ∈ Q.polynomial.support) :
      d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧ d 0 + 131071 * d 1 < 4000000 := by
    obtain ⟨h₀, h₁, h₂, h₃, _⟩ := Q.support d hd
    exact ⟨h₀, h₁, h₂, by omega⟩
  apply long_retained_seed_budget_of_factor_counts Q.polynomial Q.nonzero
    (fun d hd => ⟨(hc d hd).1, (hc d hd).2.1, (hc d hd).2.2.1⟩) seeds selected Q.vanishes
  intro F hF G hG
  obtain ⟨hiF, _⟩ := normalizedFactorSet_spec Q.polynomial F hF
  obtain ⟨hiG, hdiv⟩ := surfaceFactors_spec (polynomialEmbedding K) F G hG
  obtain ⟨hy, ht, hz, hcode⟩ := long_native_factor_caps Q.polynomial F Q.nonzero hF hc
  obtain ⟨hGy, hGt, hGz, hyt, hmid⟩ := long_geometric_factor_caps F hiF.ne_zero G hdiv hy ht hz
  by_cases hfirst : G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F 131071)
  · let part := longFactorSeeds F G seeds selected
    have hs : part ⊆ seeds := Finset.filter_subset _ _
    have hgeom := long_persistent_surface_selected_count F hiF hcode
      (fun d hd => (long_native_seed_support F ht hz d hd).1)
      (fun d hd => (long_native_seed_support F ht hz d hd).2)
      G hiG hdiv hfirst hGy hGz x (received 0) (received 1) nodes hAn haverage
      part seeds hs selected (fun g hg => h.selection.degree_le g (hs hg))
      (fun g hg => (Finset.mem_filter.mp hg).2.2.1)
      (fun g hg => (Finset.mem_filter.mp hg).2.2.2)
      (fun g hg => (Finset.mem_filter.mp hg).2.1)
      (fun g hg => h.selection.agreement g (hs hg)) h.selection.pencil
    exact hgeom.trans (by rw [longFactorCharge_eq _ _ _ hyt]; exact Nat.le_add_left _ _)
  · exact long_proper_first_tail_factor_count F hp hiF hy ht hz G hiG hdiv hfirst
      (G.degreeOf 0) (longMiddleDegree G) (G.degreeOf 2) hyt hGy hGt hGz le_rfl hmid le_rfl
      4000000 81060 (by decide) (by decide) le_rfl hcode
      x (received 0) (received 1) nodes hAn haverage seeds selected
      h.selection.degree_le h.selection.agreement h.selection.pencil

theorem protocolClaim_6831_of_short_count
    (short : ShortSeparatedRetainedCount ProximityPrize.Benchmark.IRSProfile.domain
      Koala6831BenchmarkField.frobenius.toRingHom) :
    ProximityPrize.Benchmark.ProtocolClaim 6831 332025855 1073741824 := by
  have : CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433 :=
    Koala6831BenchmarkField.characteristic
  exact protocolClaim_6831_of_separated_counts
    (long_separated_retained_count ProximityPrize.Benchmark.IRSProfile.domain
      Koala6831BenchmarkField.frobenius.toRingHom ProximityPrize.Benchmark.IRSProfile.card_index
      (inferInstance : Fact (Nat.Prime 2130706433)).out)
    short

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic

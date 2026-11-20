import ProximityPrize.SubmissionLower.Koala6844VirtualHighBenchmarkSources
import ProximityPrize.SubmissionLower.Koala6844VirtualHighCenteredTrim
import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6844Normalization ProximityPrize.Benchmark RCN081 RCN137
open Koala6831OrdinaryIncidence
open scoped Classical Matrix

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {nodes : Finset IRSProfile.Index} {excess : ℕ}

def benchmarkTrimDegree : ℕ := 124396
def benchmarkPlainDegree : ℕ := 144396
def benchmarkReconstructionBound : ℕ := 124*180961+2*179*10000+179*144396+1

theorem benchmark_trim_characteristic_bounds :
    2 ≤ benchmarkReconstructionBound ∧
    benchmarkPlainDegree+1 ≤ benchmarkReconstructionBound ∧
    benchmarkReconstructionBound < 2130706433 ∧
    benchmarkPlainDegree < 180961 ∧
    benchmarkTrimDegree+1 ≤ (124397 : ℕ) ∧ 2 ≤ (124397 : ℕ) := by decide +kernel


theorem benchmark_node_card_le : nodes.card ≤ 262144 := by
  simpa only [IRSProfile.card_index] using Finset.card_le_univ nodes

theorem benchmark_plain_degree (D : BenchmarkVirtualFamily nodes excess)
    (_hstart : 6675 ≤ D.d0.natDegree + affineDegree D.A0)
    (hcap : D.d0.natDegree ≤ 10000) :
    131071 + D.d0.natDegree - affineDegree D.A0 ≤ benchmarkPlainDegree := by
  unfold benchmarkPlainDegree
  omega

theorem benchmark_node_reconstruction_average :
    nodeAverage nodes.card benchmarkPlainDegree 180961 ≤ 4 := by
  have h : (nodes.card : ℚ) ≤ 262144 := by exact_mod_cast (benchmark_node_card_le (nodes := nodes))
  unfold nodeAverage benchmarkPlainDegree
  apply (div_le_iff₀ (by norm_num)).2
  norm_num at *
  linarith

theorem benchmark_uniform_trim (D : BenchmarkVirtualFamily nodes excess)
    (sources : BenchmarkVirtualSources D)
    (hstart : 6675 ≤ D.d0.natDegree + affineDegree D.A0) :
    Nonempty (CenteredTrimCarrier D benchmarkTrimDegree benchmarkPlainDegree) :=
  exists_uniform_centered_trim_carrier D (Nat.le_of_add_right_le sources.support_le) hstart

theorem benchmark_primary_factor_weight (D : BenchmarkVirtualFamily nodes excess)
    (sources : BenchmarkVirtualSources D) (F : BenchmarkVirtualCarrier)
    (hdiv : F ∣ sources.primarySource.val) :
    RCN234.wt (![1,benchmarkPlainDegree,0,0] : Fin 4 → ℕ) F < benchmarkReconstructionBound := by
  let weights : Fin 4 → ℕ := ![1,benchmarkPlainDegree,0,0]
  let P := sources.primarySource.val
  have hP : P ≠ 0 := fun h => sources.primary_ne (Subtype.ext h)
  change MvPolynomial.weightedTotalDegree weights F < benchmarkReconstructionBound
  apply lt_of_le_of_lt (weightedTotalDegree_le_of_dvd weights F P hdiv hP)
  have hb := (mem_globalBox BenchmarkVirtualField _ _ _ _ _ P).mp sources.primarySource.property
  have hD : D.d0.natDegree ≤ 10000 := Nat.le_of_add_right_le sources.support_le
  have hw : MvPolynomial.weightedTotalDegree weights P ≤ benchmarkReconstructionBound-1 := by
    apply (weightedTotalDegree_le_iff weights P _).mpr
    intro e he
    obtain ⟨cut, hy, _, _⟩ := hb e he
    change e 0 + _ < mappedSourceCutoff primary D.d0.natDegree at cut
    change e 1 ≤ 179 at hy
    rw [weight_fin4]
    change e 0*1 + e 1*144396 + e 2*0 + e 3*0 ≤ benchmarkReconstructionBound-1
    norm_num [mappedSourceCutoff, primary, benchmarkReconstructionBound, benchmarkPlainDegree] at cut ⊢
    omega
  exact hw.trans_lt (by decide)

theorem benchmark_primary_factor_geometry (D : BenchmarkVirtualFamily nodes excess)
    (sources : BenchmarkVirtualSources D) (F : BenchmarkVirtualCarrier)
    (hF : F ∈ (normalizedFactorSet sources.primarySource.val).filter
      (fun f => 0 < f.degreeOf 1 ∧ 0 < f.degreeOf 2+f.degreeOf 3)) :
    Irreducible F ∧ 1 ≤ F.degreeOf 1 ∧
    0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 ∧
    RCN234.wt (![1,benchmarkPlainDegree,0,0] : Fin 4 → ℕ) F < benchmarkReconstructionBound := by
  have hf := Finset.mem_filter.mp hF
  have h := normalizedFactorSet_spec _ _ hf.1
  have hy := hf.2.1
  exact ⟨h.1, hy, by omega, benchmark_primary_factor_weight D sources F h.2⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

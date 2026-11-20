import ProximityPrize.SubmissionLower.Koala6844VirtualDispatch
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBenchmarkTrim
import ProximityPrize.SubmissionLower.Koala6844VirtualHighResidualPayment


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem benchmark_large_support : Koala6844VirtualDispatch.LargeSupportBound := by
  intro nodes excess hexcess D hstart
  obtain ⟨sources⟩ := exists_benchmark_virtual_sources D hexcess hstart
  obtain ⟨trim⟩ := benchmark_uniform_trim D sources hstart
  obtain ⟨U,hU,room,adaptiveDone,excluded,hcover,hroom,hadaptive,hexcluded,hcaps⟩ :=
    exists_benchmark_virtual_families D sources
  have hF (f : BenchmarkVirtualCarrier) (hf : f ∈ U) :=
    benchmark_primary_factor_geometry D sources f (hU hf)
  have hnz (f : BenchmarkVirtualCarrier) (hf : f ∈ U) : f ≠ 0 := (hF f hf).1.ne_zero
  have hprod : (∏ f ∈ U, f) ≠ 0 := Finset.prod_ne_zero_iff.mpr hnz
  have hcap (f : BenchmarkVirtualCarrier) (hf : f ∈ U) (i : Fin 4) :
      f.degreeOf i ≤ (∏ g ∈ U, g).degreeOf i :=
    RCN137.coordinate_degree_le_of_dvd i f _ (Finset.dvd_prod_of_mem (fun g => g) hf) hprod
  apply virtual_budget_of_factor_counts benchmarkVirtualSeed (benchmarkSurfaceValue D)
    D.seeds U room adaptiveDone excluded hcover hroom hadaptive hexcluded hnz hcaps ?_
  intro f hf
  rcases hcaps with he | hc
  · simp [he] at hf
  obtain ⟨_,hy,hb,hc,_⟩ := hc
  have hd : D.d0.natDegree ≤ 10000 := Nat.le_of_add_right_le sources.support_le
  obtain ⟨_,hbound,hchar,_,_,_⟩ := benchmark_trim_characteristic_bounds
  obtain ⟨hirr,hypos,_,hweight⟩ := hF f hf
  exact pay_benchmark_residual_factor D trim f hirr hypos (factorRectangle U)
    (hcap f hf 1) (hcap f hf 2) (hcap f hf 3) hy hb hc
    benchmarkReconstructionBound hbound hchar hweight
    (benchmark_plain_degree D hstart hd) benchmark_node_reconstruction_average

end
end ProximityPrize.SubmissionLower.Koala6844VirtualHigh


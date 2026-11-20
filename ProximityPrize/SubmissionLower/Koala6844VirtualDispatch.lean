import ProximityPrize.SubmissionLower.Koala6844GeometryDispatch
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedClosure
import ProximityPrize.SubmissionLower.Koala6844NormalizationShort
import ProximityPrize.SubmissionLower.Koala6844SeedChartApply


namespace ProximityPrize.SubmissionLower.Koala6844VirtualDispatch

open Polynomial ProximityPrize.Benchmark
open Koala6844BenchmarkCases Koala6844BenchmarkRetention Koala6844BenchmarkGeometry
open Koala6844Comparison Koala6844Normalization Koala6844GeometryDispatch
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 20000

abbrev VirtualFamily (nodes : Finset IRSProfile.Index) (excess : ℕ) :=
  CenteredVirtualData IRSProfile.domain nodes Koala6844BenchmarkField.frobenius 131071 180960 81184 excess

def activeBudget : ℕ := 270779581434104148

def LargeSupportBound : Prop :=
  ∀ (nodes : Finset IRSProfile.Index) (excess : ℕ), excess ≤ 9799 →
    ∀ (data : VirtualFamily nodes excess), 6677 ≤ data.d0.natDegree + affineDegree data.A0 →
      data.seeds.card ≤ activeBudget

def ShortSupportBound : Prop :=
  ∀ (nodes : Finset IRSProfile.Index) (excess : ℕ), excess ≤ 9799 →
    ∀ (data : VirtualFamily nodes excess), data.d0.natDegree + affineDegree data.A0 ≤ 6676 →
    (∀ i ∈ nodes, (data.A0 1).eval (IRSProfile.domain i) ≠ 0) →
      data.seeds.card ≤ activeBudget

private theorem field_larger_than_nodes (nodes : Finset IRSProfile.Index) :
    nodes.card < Fintype.card IRSProfile.Field := by
  have hi : Fintype.card IRSProfile.Index < Fintype.card IRSProfile.Field := by
    rw [IRSProfile.card_index, Koala6844BenchmarkField.field_card]
    decide +kernel
  exact (Finset.card_le_univ nodes).trans_lt hi

private theorem active_card_le (hLarge : LargeSupportBound) (hShort : ShortSupportBound)
    {nodes : Finset IRSProfile.Index} {excess : ℕ} (hexcess : excess ≤ 9799)
    (data : VirtualFamily nodes excess) : data.seeds.card ≤ activeBudget + 1 := by
  by_cases hbig : 6677 ≤ data.d0.natDegree + affineDegree data.A0
  · exact (hLarge nodes excess hexcess data hbig).trans (Nat.le_succ _)
  · have hsmall : data.d0.natDegree + affineDegree data.A0 ≤ 6676 := by omega
    obtain ⟨shifted, hcard, hsupport, hleading⟩ :=
      Koala6844SeedChart.exists_admissible_chart data (field_larger_than_nodes nodes)
    have hsmall' : shifted.d0.natDegree + affineDegree shifted.A0 ≤ 6676 :=
      hsupport ▸ hsmall
    exact hcard.trans (Nat.add_le_add_right (hShort nodes excess hexcess shifted hsmall' hleading) 1)

theorem separated_bound_of_active_counts
    (hLarge : LargeSupportBound) (hShort : ShortSupportBound) : SeparatedRetainedBound := by
  intro received retained selected q h N
  by_cases hbig : 9800 ≤ primitiveExcess 131071 q
  · exact Koala6844HighSeparated.high_separated_retained_le_seed_budget
      _root_.KoalaBear.is_prime received retained selected q h hbig N
  · have hlow : primitiveExcess 131071 q ≤ 9799 := by omega
    obtain hdegenerate | ⟨data, hcard⟩ := prepare_retained_short h hlow N
    · exact hdegenerate.trans (by decide +kernel)
    · exact (hcard.trans (Nat.add_le_add_right (active_card_le hLarge hShort hlow data) _)).trans
        (by decide +kernel)

theorem protocolClaim_of_active_counts (hLarge : LargeSupportBound) (hShort : ShortSupportBound) :
    ProtocolClaim 6844 332533759 1073741824 :=
  protocolClaim_of_separated (separated_bound_of_active_counts hLarge hShort)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualDispatch


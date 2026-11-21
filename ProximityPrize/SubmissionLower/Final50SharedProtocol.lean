import ProximityPrize.SubmissionLower.Final50Protocol
import ProximityPrize.SubmissionLower.Final50PriceActiveAllocation
import ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
import ProximityPrize.SubmissionLower.Final50FatCount

set_option Elab.async false
namespace Final50Protocol
open K1_13
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Cell82219 (p q)

theorem allocation_of_shared (shared : Final50SharedPrice.cShared) : Final50Geo.Allocation := by
  intro w Γ s hmsg top htop n f pieces sub small different fits active on E hE
  obtain ⟨orders, layers, cut⟩ := Final50Order.proper_layers hmsg
    (fun i => (small i).1) (fun i => (small i).2.1)
    (fun i => (small i).2.2.1.2.2.trans_lt (by decide : 14 < K1.p)) different
  exact Final50PriceActiveAllocation.sum_cost top htop f orders pieces hmsg sub small fits active
    layers on cut E hE Final50ActiveCycle.proof shared Final50FatCount.proof

/-- A common-surface count for the proper factors supplies the full score theorem. -/
theorem of_shared (shared : Final50SharedPrice.cShared) : ProtocolClaim 6950 p q :=
  of_allocation (allocation_of_shared shared)

#print axioms of_shared
end Final50Protocol

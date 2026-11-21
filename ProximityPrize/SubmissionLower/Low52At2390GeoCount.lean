import ProximityPrize.SubmissionLower.Low52At2390GeoFinish
import ProximityPrize.SubmissionLower.Low52At2390PriceActiveAllocation
import ProximityPrize.SubmissionLower.Low52At2390ActiveCycleMixed
import ProximityPrize.SubmissionLower.Low52At2390FatCount
import ProximityPrize.SubmissionLower.Shared52At2390Count

set_option Elab.async false
namespace Low52At2390Geo
open K1_13

theorem allocation_of_shared (shared : Low52At2390SharedPrice.cShared) : Low52At2390Geo.Allocation := by
  intro w Γ s hmsg top htop n f pieces sub small different fits active on E hE
  obtain ⟨orders, layers, cut⟩ := Low52At2390Order.proper_layers hmsg
    (fun i => (small i).1) (fun i => (small i).2.1)
    (fun i => (small i).2.2.1.2.2.trans_lt (by decide : 13 < K1.p)) different
  exact Low52At2390PriceActiveAllocation.sum_cost top htop f orders pieces hmsg sub small fits active
    layers on cut E hE Low52At2390ActiveCycle.proof shared Low52At2390FatCount.proof

/-- Count every ordinary family at 179,905 agreements through height 2,390. -/
theorem ordinary_count {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179905 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2390) : Γ.card ≤ 272512621865658327 :=
  count_of_allocation (allocation_of_shared Shared52At2390Count.proof) M F lo hi

#print axioms ordinary_count
end Low52At2390Geo

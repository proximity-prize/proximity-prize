import ProximityPrize.SubmissionLower.Low53At2389Primary
import ProximityPrize.SubmissionLower.Low53At2389GeoFinish
import ProximityPrize.SubmissionLower.Low53At2389PriceActiveAllocation
import ProximityPrize.SubmissionLower.Low53At2389ActiveCycleMixed
import ProximityPrize.SubmissionLower.Low53At2389FatCount
import ProximityPrize.SubmissionLower.Low53At2389SharedCount

set_option Elab.async false
namespace Low53At2389Geo
open K1_13

theorem allocation_of_shared (primary : ∀ w, Low53At2389Order.PrimaryRank w) (shared : Low53At2389SharedPrice.cShared) : Low53At2389Geo.Allocation := by
  intro w Γ s hmsg top htop n f pieces sub small different fits active on E hE
  obtain ⟨orders, layers, cut⟩ := Low53At2389Order.proper_layers_of_rank hmsg (primary w)
    (fun i => (small i).1) (fun i => (small i).2.1)
    (fun i => (small i).2.2.1.2.2.trans_lt (by decide : 13 < K1.p)) different
  exact Low53At2389PriceActiveAllocation.sum_cost top htop f orders pieces hmsg sub small fits active
    layers on cut E hE Low53At2389ActiveCycle.proof shared Low53At2389FatCount.proof

/-- Count every ordinary family at 179,896 agreements through height 2,389. -/
theorem ordinary_count (hLoc : Low53At2389Primary.LocalRankBound) {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179896 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2389) : Γ.card ≤ 272512621865658327 :=
  let primary := Low53At2389Primary.primary_rank hLoc
  count_of_allocation (allocation_of_shared primary (Low53At2389SharedCount.proof primary)) M F lo hi

#print axioms ordinary_count
end Low53At2389Geo

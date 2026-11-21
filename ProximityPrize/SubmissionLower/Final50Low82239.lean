import ProximityPrize.SubmissionLower.Final50GeoFinish
import ProximityPrize.SubmissionLower.Final50PriceActiveAllocation
import ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
import ProximityPrize.SubmissionLower.Final50FatCount
import ProximityPrize.SubmissionLower.Shared50Count

set_option Elab.async false

/-! PR649's low count (GordoAR 78870eea-f2c7-46bf-990f-c2d7c9d44bfc), retargeted to 179,905 agreements,
heights 1..2,377, with the theta primary rank (leap). -/
namespace Final50Low82239
open K1_13

theorem allocation : Final50Geo.Allocation := by
  intro w Γ s hmsg top htop n f pieces sub small different fits active on E hE
  obtain ⟨orders, layers, cut⟩ := Final50Order.proper_layers hmsg
    (fun i => (small i).1) (fun i => (small i).2.1)
    (fun i => (small i).2.2.1.2.2.trans_lt (by decide : 14 < K1.p)) different
  exact Final50PriceActiveAllocation.sum_cost top htop f orders pieces hmsg sub small fits active
    layers on cut E hE Final50ActiveCycle.proof Shared50Count.proof Final50FatCount.proof

theorem count {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179905 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2377) : Γ.card ≤ 272835953009060747 :=
  Final50Geo.count_of_allocation allocation M F lo hi

#print axioms count
end Final50Low82239

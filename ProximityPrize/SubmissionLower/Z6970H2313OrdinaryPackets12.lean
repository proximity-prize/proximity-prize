import ProximityPrize.SubmissionLower.R6970Height2313MainPlans
import ProximityPrize.SubmissionLower.R6970Height2313OrdinaryPlans
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryPacketCore

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early.NearSavedQuarticIntervals7
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,3944,58,742,true⟩

theorem exit_checked : terminalExit.Valid Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.plan Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.plan Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 4 53 56 514639 :=
  ⟨Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.plan, Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.price, Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.valid, Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.priced, Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.sources,
   Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.plan, Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.price, Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.sources, Research6970.Height2313.Lower6960.Prefix6969RescueData.QuarticIntervals7.priced,
   rfl,rfl,rfl,by decide,terminalExit,exit_checked,Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7.price.fee, .standard⟩

theorem fee_exact : data.fee = 200831419760682826 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel


theorem uniform_checked : data.uniform := by
  unfold NearCase.uniform
  rw [fee_exact]
  decide +kernel

end Research6970.Height2313.Lower6960.Prefix6969Early.NearSavedQuarticIntervals7

namespace Research6970.Height2313.Lower6960.Prefix6969Early.NearSavedRepricedHelperCases2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4085,63,849,true⟩

theorem exit_checked : terminalExit.Valid Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.plan Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.plan Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 5 41 56 643299 :=
  ⟨Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.plan, Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.price, Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.valid, Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.priced, Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.sources,
   Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.plan, Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.price, Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.sources, Research6970.Height2313.Lower6960.Prefix6969RescueData.RepricedHelperCases2.priced,
   rfl,rfl,rfl,by decide,terminalExit,exit_checked,Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2.price.fee, .standard⟩

theorem fee_exact : data.fee = 223268475779427542 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel


theorem uniform_checked : data.uniform := by
  unfold NearCase.uniform
  rw [fee_exact]
  decide +kernel

end Research6970.Height2313.Lower6960.Prefix6969Early.NearSavedRepricedHelperCases2

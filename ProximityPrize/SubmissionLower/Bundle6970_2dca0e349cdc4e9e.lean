import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryPacketCore
import ProximityPrize.SubmissionLower.Bundle6970_12ed39fb06b47c65
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryPackets12

section Pack_Z6970H2313OrdinaryChoose4

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose4 (j : Fin 56) (ok : UniformAllowed 4 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤514639 ∧ ∃ c : NearCase 4 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases2.data, ?_⟩
    exact NearSavedHigherHelperCases2.uniform_checked
  · refine ⟨2, 3, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases3.data, ?_⟩
    exact NearSavedHigherHelperCases3.uniform_checked
  · refine ⟨2, 3, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases3.data, ?_⟩
    exact NearSavedHigherHelperCases3.uniform_checked
  · refine ⟨4, 8, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    exact NearSavedHigherHelperCases4.uniform_checked
  · refine ⟨4, 8, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    exact NearSavedHigherHelperCases4.uniform_checked
  · refine ⟨4, 8, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    exact NearSavedHigherHelperCases4.uniform_checked
  · refine ⟨4, 8, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    exact NearSavedHigherHelperCases4.uniform_checked
  · refine ⟨4, 8, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    exact NearSavedHigherHelperCases4.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨9, 15, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    exact NearSavedHigherHelperCases5.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨16, 25, 514639, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    exact NearSavedHigherHelperCases6.uniform_checked
  · refine ⟨26, 29, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    exact NearSavedQuarticIntervals0.uniform_checked
  · refine ⟨26, 29, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    exact NearSavedQuarticIntervals0.uniform_checked
  · refine ⟨26, 29, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    exact NearSavedQuarticIntervals0.uniform_checked
  · refine ⟨26, 29, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    exact NearSavedQuarticIntervals0.uniform_checked
  · refine ⟨30, 33, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    exact NearSavedQuarticIntervals1.uniform_checked
  · refine ⟨30, 33, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    exact NearSavedQuarticIntervals1.uniform_checked
  · refine ⟨30, 33, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    exact NearSavedQuarticIntervals1.uniform_checked
  · refine ⟨30, 33, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    exact NearSavedQuarticIntervals1.uniform_checked
  · refine ⟨34, 37, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    exact NearSavedQuarticIntervals2.uniform_checked
  · refine ⟨34, 37, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    exact NearSavedQuarticIntervals2.uniform_checked
  · refine ⟨34, 37, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    exact NearSavedQuarticIntervals2.uniform_checked
  · refine ⟨34, 37, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    exact NearSavedQuarticIntervals2.uniform_checked
  · refine ⟨38, 40, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    exact NearSavedQuarticIntervals3.uniform_checked
  · refine ⟨38, 40, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    exact NearSavedQuarticIntervals3.uniform_checked
  · refine ⟨38, 40, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    exact NearSavedQuarticIntervals3.uniform_checked
  · refine ⟨41, 44, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    exact NearSavedQuarticIntervals4.uniform_checked
  · refine ⟨41, 44, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    exact NearSavedQuarticIntervals4.uniform_checked
  · refine ⟨41, 44, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    exact NearSavedQuarticIntervals4.uniform_checked
  · refine ⟨41, 44, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    exact NearSavedQuarticIntervals4.uniform_checked
  · refine ⟨45, 48, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    exact NearSavedQuarticIntervals5.uniform_checked
  · refine ⟨45, 48, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    exact NearSavedQuarticIntervals5.uniform_checked
  · refine ⟨45, 48, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    exact NearSavedQuarticIntervals5.uniform_checked
  · refine ⟨45, 48, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    exact NearSavedQuarticIntervals5.uniform_checked
  · refine ⟨49, 52, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    exact NearSavedQuarticIntervals6.uniform_checked
  · refine ⟨49, 52, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    exact NearSavedQuarticIntervals6.uniform_checked
  · refine ⟨49, 52, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    exact NearSavedQuarticIntervals6.uniform_checked
  · refine ⟨49, 52, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    exact NearSavedQuarticIntervals6.uniform_checked
  · refine ⟨53, 56, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    exact NearSavedQuarticIntervals7.uniform_checked
  · refine ⟨53, 56, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    exact NearSavedQuarticIntervals7.uniform_checked
  · refine ⟨53, 56, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    exact NearSavedQuarticIntervals7.uniform_checked
  · refine ⟨53, 56, 514639, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    exact NearSavedQuarticIntervals7.uniform_checked


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose4

section Pack_Z6970H2313OrdinaryChoose5

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose5 (j : Fin 56) (ok : UniformAllowed 5 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤643299 ∧ ∃ c : NearCase 5 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases7.data, ?_⟩
    exact NearSavedHigherHelperCases7.uniform_checked
  · refine ⟨2, 3, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases8.data, ?_⟩
    exact NearSavedHigherHelperCases8.uniform_checked
  · refine ⟨2, 3, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases8.data, ?_⟩
    exact NearSavedHigherHelperCases8.uniform_checked
  · refine ⟨4, 8, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    exact NearSavedHigherHelperCases9.uniform_checked
  · refine ⟨4, 8, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    exact NearSavedHigherHelperCases9.uniform_checked
  · refine ⟨4, 8, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    exact NearSavedHigherHelperCases9.uniform_checked
  · refine ⟨4, 8, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    exact NearSavedHigherHelperCases9.uniform_checked
  · refine ⟨4, 8, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    exact NearSavedHigherHelperCases9.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨9, 15, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    exact NearSavedHigherHelperCases10.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · refine ⟨16, 25, 643299, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    exact NearSavedHigherHelperCases11.uniform_checked
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked
  · refine ⟨41, 56, 643299, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    exact NearSavedRepricedHelperCases2.uniform_checked


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose5

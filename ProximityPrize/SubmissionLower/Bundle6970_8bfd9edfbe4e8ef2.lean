import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryPacketCore
import ProximityPrize.SubmissionLower.Bundle6970_12ed39fb06b47c65

section Pack_Z6970H2313OrdinaryChoose2

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose2 (j : Fin 56) (ok : UniformAllowed 2 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤threshold j ∧ ∃ c : NearCase 2 l u w, c.uniform := by
  fin_cases j
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
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · refine ⟨20, 20, 307237, by decide, by decide, by decide, NearSavedQuadraticSingletons1.data, ?_⟩
    exact NearSavedQuadraticSingletons1.uniform_checked
  · refine ⟨21, 21, 307116, by decide, by decide, by decide, NearSavedQuadraticSingletons2.data, ?_⟩
    exact NearSavedQuadraticSingletons2.uniform_checked
  · refine ⟨22, 22, 306989, by decide, by decide, by decide, NearSavedQuadraticSingletons3.data, ?_⟩
    exact NearSavedQuadraticSingletons3.uniform_checked
  · refine ⟨23, 23, 306855, by decide, by decide, by decide, NearSavedQuadraticSingletons4.data, ?_⟩
    exact NearSavedQuadraticSingletons4.uniform_checked
  · refine ⟨24, 24, 306716, by decide, by decide, by decide, NearSavedQuadraticSingletons5.data, ?_⟩
    exact NearSavedQuadraticSingletons5.uniform_checked
  · refine ⟨25, 25, 306571, by decide, by decide, by decide, NearSavedQuadraticSingletons6.data, ?_⟩
    exact NearSavedQuadraticSingletons6.uniform_checked
  · refine ⟨26, 26, 306420, by decide, by decide, by decide, NearSavedQuadraticSingletons7.data, ?_⟩
    exact NearSavedQuadraticSingletons7.uniform_checked
  · refine ⟨27, 27, 306263, by decide, by decide, by decide, NearSavedQuadraticSingletons8.data, ?_⟩
    exact NearSavedQuadraticSingletons8.uniform_checked
  · refine ⟨28, 28, 306100, by decide, by decide, by decide, NearSavedQuadraticSingletons9.data, ?_⟩
    exact NearSavedQuadraticSingletons9.uniform_checked
  · refine ⟨29, 29, 305932, by decide, by decide, by decide, NearSavedQuadraticSingletons10.data, ?_⟩
    exact NearSavedQuadraticSingletons10.uniform_checked
  · refine ⟨30, 30, 305757, by decide, by decide, by decide, NearSavedQuadraticSingletons11.data, ?_⟩
    exact NearSavedQuadraticSingletons11.uniform_checked
  · refine ⟨31, 31, 305576, by decide, by decide, by decide, NearSavedQuadraticSingletons12.data, ?_⟩
    exact NearSavedQuadraticSingletons12.uniform_checked
  · refine ⟨32, 32, 305390, by decide, by decide, by decide, NearSavedQuadraticSingletons13.data, ?_⟩
    exact NearSavedQuadraticSingletons13.uniform_checked
  · refine ⟨33, 33, 305197, by decide, by decide, by decide, NearSavedQuadraticSingletons14.data, ?_⟩
    exact NearSavedQuadraticSingletons14.uniform_checked
  · refine ⟨34, 34, 304999, by decide, by decide, by decide, NearSavedQuadraticSingletons15.data, ?_⟩
    exact NearSavedQuadraticSingletons15.uniform_checked
  · refine ⟨35, 35, 304795, by decide, by decide, by decide, NearSavedQuadraticSingletons16.data, ?_⟩
    exact NearSavedQuadraticSingletons16.uniform_checked
  · refine ⟨36, 36, 304585, by decide, by decide, by decide, NearSavedQuadraticSingletons17.data, ?_⟩
    exact NearSavedQuadraticSingletons17.uniform_checked
  · refine ⟨37, 37, 304368, by decide, by decide, by decide, NearSavedQuadraticSingletons18.data, ?_⟩
    exact NearSavedQuadraticSingletons18.uniform_checked
  · refine ⟨38, 38, 304146, by decide, by decide, by decide, NearSavedQuadraticSingletons19.data, ?_⟩
    exact NearSavedQuadraticSingletons19.uniform_checked
  · refine ⟨39, 39, 303918, by decide, by decide, by decide, NearSavedQuadraticSingletons20.data, ?_⟩
    exact NearSavedQuadraticSingletons20.uniform_checked
  · refine ⟨40, 40, 303684, by decide, by decide, by decide, NearSavedQuadraticSingletons21.data, ?_⟩
    exact NearSavedQuadraticSingletons21.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨41, 50, 296085, by decide, by decide, by decide, NearSavedHighQuadraticUpper0.data, ?_⟩
    exact NearSavedHighQuadraticUpper0.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked
  · refine ⟨51, 56, 292947, by decide, by decide, by decide, NearSavedHighQuadraticUpper1.data, ?_⟩
    exact NearSavedHighQuadraticUpper1.uniform_checked


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose2

section Pack_Z6970H2313OrdinaryChoose3

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose3 (j : Fin 56) (ok : UniformAllowed 3 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤385979 ∧ ∃ c : NearCase 3 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases0.data, ?_⟩
    exact NearSavedHigherHelperCases0.uniform_checked
  · refine ⟨2, 3, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    exact NearSavedHigherHelperCases1.uniform_checked
  · refine ⟨2, 3, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    exact NearSavedHigherHelperCases1.uniform_checked
  · refine ⟨4, 4, 385979, by decide, by decide, by decide, NearSavedCubicSingletons0.data, ?_⟩
    exact NearSavedCubicSingletons0.uniform_checked
  · refine ⟨5, 5, 385979, by decide, by decide, by decide, NearSavedCubicSingletons1.data, ?_⟩
    exact NearSavedCubicSingletons1.uniform_checked
  · refine ⟨6, 6, 385979, by decide, by decide, by decide, NearSavedCubicSingletons2.data, ?_⟩
    exact NearSavedCubicSingletons2.uniform_checked
  · refine ⟨7, 7, 385979, by decide, by decide, by decide, NearSavedCubicSingletons3.data, ?_⟩
    exact NearSavedCubicSingletons3.uniform_checked
  · refine ⟨8, 8, 385979, by decide, by decide, by decide, NearSavedCubicSingletons4.data, ?_⟩
    exact NearSavedCubicSingletons4.uniform_checked
  · refine ⟨9, 9, 385979, by decide, by decide, by decide, NearSavedCubicSingletons5.data, ?_⟩
    exact NearSavedCubicSingletons5.uniform_checked
  · refine ⟨10, 10, 385979, by decide, by decide, by decide, NearSavedCubicSingletons6.data, ?_⟩
    exact NearSavedCubicSingletons6.uniform_checked
  · refine ⟨11, 11, 385979, by decide, by decide, by decide, NearSavedCubicSingletons7.data, ?_⟩
    exact NearSavedCubicSingletons7.uniform_checked
  · refine ⟨12, 12, 385979, by decide, by decide, by decide, NearSavedCubicSingletons8.data, ?_⟩
    exact NearSavedCubicSingletons8.uniform_checked
  · refine ⟨13, 13, 385979, by decide, by decide, by decide, NearSavedCubicSingletons9.data, ?_⟩
    exact NearSavedCubicSingletons9.uniform_checked
  · refine ⟨14, 14, 385979, by decide, by decide, by decide, NearSavedCubicSingletons10.data, ?_⟩
    exact NearSavedCubicSingletons10.uniform_checked
  · refine ⟨15, 15, 385979, by decide, by decide, by decide, NearSavedCubicSingletons11.data, ?_⟩
    exact NearSavedCubicSingletons11.uniform_checked
  · refine ⟨16, 16, 385979, by decide, by decide, by decide, NearSavedCubicSingletons12.data, ?_⟩
    exact NearSavedCubicSingletons12.uniform_checked
  · refine ⟨17, 17, 385979, by decide, by decide, by decide, NearSavedCubicSingletons13.data, ?_⟩
    exact NearSavedCubicSingletons13.uniform_checked
  · refine ⟨18, 18, 385979, by decide, by decide, by decide, NearSavedCubicSingletons14.data, ?_⟩
    exact NearSavedCubicSingletons14.uniform_checked
  · refine ⟨19, 19, 385979, by decide, by decide, by decide, NearSavedCubicSingletons15.data, ?_⟩
    exact NearSavedCubicSingletons15.uniform_checked
  · refine ⟨20, 20, 385979, by decide, by decide, by decide, NearSavedCubicSingletons16.data, ?_⟩
    exact NearSavedCubicSingletons16.uniform_checked
  · refine ⟨21, 21, 385979, by decide, by decide, by decide, NearSavedCubicSingletons17.data, ?_⟩
    exact NearSavedCubicSingletons17.uniform_checked
  · refine ⟨22, 22, 385979, by decide, by decide, by decide, NearSavedCubicSingletons18.data, ?_⟩
    exact NearSavedCubicSingletons18.uniform_checked
  · refine ⟨23, 23, 385979, by decide, by decide, by decide, NearSavedCubicSingletons19.data, ?_⟩
    exact NearSavedCubicSingletons19.uniform_checked
  · refine ⟨24, 24, 385979, by decide, by decide, by decide, NearSavedCubicSingletons20.data, ?_⟩
    exact NearSavedCubicSingletons20.uniform_checked
  · refine ⟨25, 25, 385979, by decide, by decide, by decide, NearSavedCubicSingletons21.data, ?_⟩
    exact NearSavedCubicSingletons21.uniform_checked
  · refine ⟨26, 26, 385979, by decide, by decide, by decide, NearSavedCubicSingletons22.data, ?_⟩
    exact NearSavedCubicSingletons22.uniform_checked
  · refine ⟨27, 27, 385979, by decide, by decide, by decide, NearSavedCubicSingletons23.data, ?_⟩
    exact NearSavedCubicSingletons23.uniform_checked
  · refine ⟨28, 28, 385979, by decide, by decide, by decide, NearSavedCubicSingletons24.data, ?_⟩
    exact NearSavedCubicSingletons24.uniform_checked
  · refine ⟨29, 29, 385979, by decide, by decide, by decide, NearSavedCubicSingletons25.data, ?_⟩
    exact NearSavedCubicSingletons25.uniform_checked
  · refine ⟨30, 30, 385979, by decide, by decide, by decide, NearSavedCubicSingletons26.data, ?_⟩
    exact NearSavedCubicSingletons26.uniform_checked
  · refine ⟨31, 31, 385979, by decide, by decide, by decide, NearSavedCubicSingletons27.data, ?_⟩
    exact NearSavedCubicSingletons27.uniform_checked
  · refine ⟨32, 32, 385979, by decide, by decide, by decide, NearSavedCubicSingletons28.data, ?_⟩
    exact NearSavedCubicSingletons28.uniform_checked
  · refine ⟨33, 33, 385979, by decide, by decide, by decide, NearSavedCubicSingletons29.data, ?_⟩
    exact NearSavedCubicSingletons29.uniform_checked
  · refine ⟨34, 34, 385979, by decide, by decide, by decide, NearSavedCubicSingletons30.data, ?_⟩
    exact NearSavedCubicSingletons30.uniform_checked
  · refine ⟨35, 35, 385979, by decide, by decide, by decide, NearSavedCubicSingletons31.data, ?_⟩
    exact NearSavedCubicSingletons31.uniform_checked
  · refine ⟨36, 36, 385979, by decide, by decide, by decide, NearSavedCubicSingletons32.data, ?_⟩
    exact NearSavedCubicSingletons32.uniform_checked
  · refine ⟨37, 37, 385979, by decide, by decide, by decide, NearSavedCubicSingletons33.data, ?_⟩
    exact NearSavedCubicSingletons33.uniform_checked
  · refine ⟨38, 38, 385979, by decide, by decide, by decide, NearSavedCubicSingletons34.data, ?_⟩
    exact NearSavedCubicSingletons34.uniform_checked
  · refine ⟨39, 39, 385979, by decide, by decide, by decide, NearSavedCubicSingletons35.data, ?_⟩
    exact NearSavedCubicSingletons35.uniform_checked
  · refine ⟨40, 40, 385979, by decide, by decide, by decide, NearSavedCubicSingletons36.data, ?_⟩
    exact NearSavedCubicSingletons36.uniform_checked
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
  · exfalso; revert ok; decide


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose3

section Pack_Z6970H2313OrdinaryChoose6

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose6 (j : Fin 56) (ok : UniformAllowed 6 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤771959 ∧ ∃ c : NearCase 6 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases12.data, ?_⟩
    exact NearSavedHigherHelperCases12.uniform_checked
  · refine ⟨2, 3, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases13.data, ?_⟩
    exact NearSavedHigherHelperCases13.uniform_checked
  · refine ⟨2, 3, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases13.data, ?_⟩
    exact NearSavedHigherHelperCases13.uniform_checked
  · refine ⟨4, 8, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    exact NearSavedHigherHelperCases14.uniform_checked
  · refine ⟨4, 8, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    exact NearSavedHigherHelperCases14.uniform_checked
  · refine ⟨4, 8, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    exact NearSavedHigherHelperCases14.uniform_checked
  · refine ⟨4, 8, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    exact NearSavedHigherHelperCases14.uniform_checked
  · refine ⟨4, 8, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    exact NearSavedHigherHelperCases14.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨9, 15, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    exact NearSavedHigherHelperCases15.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨16, 25, 771959, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    exact NearSavedHigherHelperCases16.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨26, 40, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    exact NearSavedMarkedExitCandidates0.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked
  · refine ⟨41, 56, 771959, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    exact NearSavedMarkedExitCandidates1.uniform_checked


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose6

section Pack_Z6970H2313OrdinaryChoose7

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.Lower6960.Prefix6969Early
open _root_.Lower6960.Prefix6969Early (seed threshold)

theorem nearChoose7 (j : Fin 56) (ok : UniformAllowed 7 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤900619 ∧ ∃ c : NearCase 7 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases17.data, ?_⟩
    exact NearSavedHigherHelperCases17.uniform_checked
  · refine ⟨2, 3, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases18.data, ?_⟩
    exact NearSavedHigherHelperCases18.uniform_checked
  · refine ⟨2, 3, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases18.data, ?_⟩
    exact NearSavedHigherHelperCases18.uniform_checked
  · refine ⟨4, 8, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    exact NearSavedHigherHelperCases19.uniform_checked
  · refine ⟨4, 8, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    exact NearSavedHigherHelperCases19.uniform_checked
  · refine ⟨4, 8, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    exact NearSavedHigherHelperCases19.uniform_checked
  · refine ⟨4, 8, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    exact NearSavedHigherHelperCases19.uniform_checked
  · refine ⟨4, 8, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    exact NearSavedHigherHelperCases19.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨9, 15, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    exact NearSavedHigherHelperCases20.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨16, 25, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    exact NearSavedHigherHelperCases21.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨26, 40, 900619, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    exact NearSavedHigherHelperCases22.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked
  · refine ⟨41, 56, 900619, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    exact NearSavedMarkedExitCandidates2.uniform_checked


end Research6970.Height2313.Lower6960.Prefix6969Early
end Pack_Z6970H2313OrdinaryChoose7

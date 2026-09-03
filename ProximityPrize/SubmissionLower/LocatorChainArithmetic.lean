import ProximityPrize.SubmissionLower.N5

/-! A small, independently checkable receipt for the asymmetric derivative-chain cost. -/

namespace ProximityPrize.SubmissionLower.LocatorChainArithmetic

open RCN260

/-- In every nonterminal derivative-chain stage `j >= 1`, the left polynomial
has `R`-degree at most `32`, while the original factor on the right may still
have `R`-degree `33`. -/
def chainStage : UnequalParameters :=
  ⟨262144, 131071, 181392, 153, 32, 10381, 153, 33, 10381⟩

theorem chainStage_exact : chainStage.regularCountCap = 211479108682951 := by
  decide

end ProximityPrize.SubmissionLower.LocatorChainArithmetic

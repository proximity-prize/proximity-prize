import ProximityPrize.SubmissionLower.LocatorR1Source

/-! Packed from ProximityPrize.SubmissionLower.LocatorChainArithmetic. -/
section PackedLocator_LocatorChainArithmetic

/-! A small, independently checkable receipt for the asymmetric derivative-chain cost. -/

namespace ProximityPrize.SubmissionLower.LocatorChainArithmetic

open RCN260

/-- In every nonterminal derivative-chain stage `j >= 1`, the left polynomial
has `R`-degree at most `32`, while the original factor on the right may still
have `R`-degree `33`. -/
def chainStage : UnequalParameters :=
  ⟨262144, 131071, 181373, 153, 32, 12960, 153, 33, 12960⟩

theorem chainStage_exact : chainStage.regularCountCap = 264117369694349 := by
  decide

end ProximityPrize.SubmissionLower.LocatorChainArithmetic
end PackedLocator_LocatorChainArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier28 : True := by trivial
end ProximityPrize.SubmissionLower


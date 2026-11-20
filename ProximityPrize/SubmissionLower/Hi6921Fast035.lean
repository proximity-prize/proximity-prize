import ProximityPrize.SubmissionLower.Fast035
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_2Support
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace H21_3_2

noncomputable section

open H21 H21_3

open private minimalPairHeight from ProximityPrize.SubmissionLower.Fast035

export _root_.K1_14_3_2 (properPairCover)

end
end H21_3_2
end High_K1_14_3_2Support

section High_K1_14_3_4Defs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace H21_3_4

noncomputable section

open K21 H21 H21_3 H21_3_2 Polynomial
open scoped BigOperators

export _root_.K1_14_3_4 (graphCutter)

export _root_.K1_14_3_4 (ThresholdPair)
namespace ThresholdPair
export _root_.K1_14_3_4.ThresholdPair (casesOn factors heavy left left_caps mk noConfusion proper rec recOn residual_order right right_caps seed_budget y_budget)
end ThresholdPair

open private localLength from ProximityPrize.SubmissionLower.Fast035

export _root_.K1_14_3_4 (intersectionLength)

open private localLength_pos from ProximityPrize.SubmissionLower.Fast035

export _root_.K1_14_3_4 (intersectionLength_one)

export _root_.K1_14_3_4 (pairSectionDegree)

export _root_.K1_14_3_4 (residualSeed)

export _root_.K1_14_3_4 (residualOrdinate)

export _root_.K1_14_3_4 (residualMixed)

end
end H21_3_4
end High_K1_14_3_4Defs

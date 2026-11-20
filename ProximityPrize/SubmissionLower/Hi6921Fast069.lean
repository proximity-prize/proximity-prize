import ProximityPrize.SubmissionLower.Fast069
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921Fast057
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_2RCoprime
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace H21_3_2R

noncomputable section

open H21 H21_3 H21_3_2

export _root_.K1_14_3_2R (coprime_of_transport)

end
end H21_3_2R
end High_K1_14_3_2RCoprime

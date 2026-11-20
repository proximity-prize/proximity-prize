import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921P21Split
import ProximityPrize.SubmissionLower.Hi6921P32Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/

section High_K1_14_3_6Defs
set_option autoImplicit true
namespace H21_3_6

noncomputable section

open K21 K1_13 H21 H21_3 Polynomial
open K1_13_5_3

export _root_.K1_14_3_6 (total)

export _root_.K1_14_3_6 (atScalar)

export _root_.K1_14_3_6 (power)
export _root_.K1_14_3_6 (totalCap)
export _root_.K1_14_3_6 (topCap)

export _root_.K1_14_3_6 (AgreementChart)
namespace AgreementChart
export _root_.K1_14_3_6.AgreementChart (agrees casesOn cut mk noConfusion rec recOn top_bound total_bound)
end AgreementChart

end
end H21_3_6
end High_K1_14_3_6Defs

section High_K1_14_3_6Algebra
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace H21_3_6

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators

export _root_.K1_14_3_6 (atScalar_eq)

export _root_.K1_14_3_6 (atX_injective)

export _root_.K1_14_3_6 (outer_le_total)

export _root_.K1_14_3_6 (caps_degree)

export _root_.K1_14_3_6 (factor_cover)

export _root_.K1_14_3_6 (exception)

export _root_.K1_14_3_6 (exception_ne_zero)

export _root_.K1_14_3_6 (exception_degree)

export _root_.K1_14_3_6 (exception_root)

export _root_.K1_14_3_6 (root_count)

end
end H21_3_6
end High_K1_14_3_6Algebra

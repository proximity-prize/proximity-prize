import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_2RTransport
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000

namespace H21_3_2R

noncomputable section

open K21 H21 H21_3 Polynomial

open private Parameters from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private Whole from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private Sloped from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private par from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private free from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private t from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private y from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private v from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private scalar from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

export _root_.K1_14_3_2R (jetHom_ext)

open private positions from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private raw from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private forward from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private slope from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private co from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private offsets from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private other from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private backward from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private forward_backward from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private backward_forward from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private coordinateEquiv from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

open private raw_prime from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport

attribute [local instance] MvPolynomial.algebraMvPolynomial

export _root_.K1_14_3_2R (sectionChart)

export _root_.K1_14_3_2R (localized_prime)

end
end H21_3_2R
end High_K1_14_3_2RTransport

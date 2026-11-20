import ProximityPrize.SubmissionLower.Fast076
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921Fast057
import ProximityPrize.SubmissionLower.Hi6921Fast061
import ProximityPrize.SubmissionLower.Hi6921Fast067
import ProximityPrize.SubmissionLower.Hi6921Fast069
import ProximityPrize.SubmissionLower.Hi6921P21Split
import ProximityPrize.SubmissionLower.Hi6921P32RTransport
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_2RSplit
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace H21_3_2R

noncomputable section

open K21 H21 H21_3 H21_3_2 K1_14_3_2_3 Polynomial
open private mass_le from ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Split
open private raw from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private positions from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private t from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private y from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private v from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private scalar from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private par from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private free from ProximityPrize.SubmissionLower.Pack_K1_14_3_2RTransport
open private eval_y eval_v eval_seed baseMap from ProximityPrize.SubmissionLower.Pack_K1_14_3_2_3Aux3

open private chart_eq from ProximityPrize.SubmissionLower.Fast076

export _root_.K1_14_3_2R (prime_transport)

export _root_.K1_14_3_2R (proper_transport)

export _root_.K1_14_3_2R (residual_sections)

export _root_.K1_14_3_2R (graph_sections)

theorem of_children (seedImages : H21_3_2.c5) (jetImages : H21_3_2.c6) : H21_3.c2 :=
  assemble K1_14_3_2_1.proof residual_sections graph_sections seedImages jetImages K1_14_3_2_7.proof

end
end H21_3_2R
end High_K1_14_3_2RSplit

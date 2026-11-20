import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_4Cutter
set_option autoImplicit true
namespace H21_3_4

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open private dx from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private coeff_dx from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private innerTest from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private inner_coeff from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private inner_degree from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private eval_dx from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private specialize_nonzero from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private no_log_derivative from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private no_cross from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private toSeed from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
open private liftSeed from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
open private toField from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private liftSeed_inj from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private toField_inj from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private at_fibre from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private eqn_minimal from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private constant_ne from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private mapped_lift from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private exclude_inner from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

-- Keep this dichotomy valid when the shared definition adopts the explicit outer variable.
set_option linter.unreachableTactic false in
open private cutter_reading from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

open private lift_inner from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter

export _root_.K1_14_3_4 (graph_test_of_compatible)

end
end H21_3_4
end High_K1_14_3_4Cutter

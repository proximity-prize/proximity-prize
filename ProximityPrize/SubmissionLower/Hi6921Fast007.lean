import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- 69.21 specialization of the high-overhead proof in PR 627. -/
section High_K1_14Graph
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace H21
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

export _root_.K1_14 (graphExponent)

export _root_.K1_14 (frobeniusGraph)

export _root_.K1_14 (graphExponent_injOn)

export _root_.K1_14 (frobeniusGraph_monomial)

export _root_.K1_14 (frobeniusGraph_coeff)

export _root_.K1_14 (frobeniusGraph_ne_zero)

export _root_.K1_14 (frobeniusGraph_degree)

export _root_.K1_14 (frobenius_coefficient_exception_count)

end
end H21
end High_K1_14Graph

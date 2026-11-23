import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Numeric2Aux
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
def c7 : Prop :=
  ∀ qs : Finset Surface, qs.Nonempty → (∀ q ∈ qs, Parent q) →
    ∃ f : Equation, ProjectedProduct qs f
end
end K1_14_3
end

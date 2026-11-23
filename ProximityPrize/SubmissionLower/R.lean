import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.Q
import ProximityPrize.SubmissionLower.AA
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
namespace qQ
noncomputable section
open K1 cu Polynomial
open scoped BigOperators Classical
def c7:Prop :=
  ∀ qs :Finset zI,qs.Nonempty→(∀ q∈qs,N5 q) →
    ∃ f :Equation,aLQ qs f
end
end qQ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace bjG
noncomputable section
open K1 cu qQ XY Polynomial
open scoped BigOperators
def cT8 (g:aix) :Jet :=
  C (adV (a2x g)) +
    (Polynomial.X (R:=Equation))*C (adV g.derivative)
end
end bjG
end

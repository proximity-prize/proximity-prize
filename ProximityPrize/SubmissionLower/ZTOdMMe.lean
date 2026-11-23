import ProximityPrize.SubmissionLower.Z
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace anc
noncomputable section
open cu DP Ge Polynomial
open scoped BigOperators Polynomial
def numerator {F:Type} [Field F] (side :Fin 2) (a :F) :i5 F :=
  MvPolynomial.C a*MvPolynomial.X side
def denominator {F:Type} [Field F] (side :Fin 2) (b c:F) :i5 F :=
  MvPolynomial.C b+MvPolynomial.C c*MvPolynomial.X side
end
end anc

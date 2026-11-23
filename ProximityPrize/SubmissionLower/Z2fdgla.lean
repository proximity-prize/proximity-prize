import ProximityPrize.SubmissionLower.BG
set_option Elab.async false
set_option autoImplicit true
namespace ana
noncomputable section
open K1 aR oR Polynomial PolynomialDifferential
open scoped BigOperators nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev exponent:=2*bf - 5
end
end ana

import ProximityPrize.SubmissionLower.ZFSutke
import ProximityPrize.SubmissionLower.ZSLoCda
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qckEfrc
noncomputable section
open Finset MvPolynomial
open P5 (K)
open cu (FX L kr)




open scoped Polynomial
private theorem atX_inj:Function.Injective kr :=
  (IsFractionRing.injective cu.L[X] FX).comp
    (Polynomial.map_injective _ (algebraMap K L).injective)
end
end qckEfrc

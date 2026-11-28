import ProximityPrize.SubmissionLower.Z6970ExpandedColumns

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedLayerBank6970
noncomputable section
open K1_13_6 (GenericField)
open MvPolynomial
open ExpandedColumns6970 (jetExponents)

def ambient : Submodule GenericField (MvPolynomial (Fin 4) GenericField) :=
  restrictSupport GenericField jetExponents

instance : Module.Finite GenericField ambient :=
  restrictSupport_finite ExpandedColumns6970.jetExponents_finite

end
end ExpandedLayerBank6970

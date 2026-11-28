import ProximityPrize.SubmissionLower.Z6970ExpandedHceilH2307
import ProximityPrize.SubmissionLower.Z6970PlateauCertificate

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedOrderH2307

theorem actual_hceil : 46355 * (21230822871131 - 1) < sourceRank :=
  hceil_of_plateau ExpandedPlateauSum6970.certified_plateau

end ExpandedOrderH2307

import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers3
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment10
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment6
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment9

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank15_verified : Verified bank15 :=
  ⟨bank15_nodes, moment5370_1193,
    (by decide), (by decide), bank15_cover⟩
#print axioms bank15_verified

theorem bank16_verified : Verified bank16 :=
  ⟨bank16_nodes, moment5369_1193,
    (by decide), (by decide), bank16_cover⟩
#print axioms bank16_verified

theorem bank17_verified : Verified bank17 :=
  ⟨bank17_nodes, moment5018_1116,
    (by decide), (by decide), bank17_cover⟩
#print axioms bank17_verified

theorem bank18_verified : Verified bank18 :=
  ⟨bank18_nodes, moment3898_828,
    (by decide), (by decide), bank18_cover⟩
#print axioms bank18_verified

theorem bank19_verified : Verified bank19 :=
  ⟨bank19_nodes, moment5010_1065,
    (by decide), (by decide), bank19_cover⟩
#print axioms bank19_verified

end Research6966.HelperWindowCatalogue

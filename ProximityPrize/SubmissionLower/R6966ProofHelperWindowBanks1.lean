import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment2
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment8
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment9

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank5_verified : Verified bank5 :=
  ⟨bank5_nodes, moment3900_845,
    (by decide), (by decide), bank5_cover⟩
#print axioms bank5_verified

theorem bank6_verified : Verified bank6 :=
  ⟨bank6_nodes, moment3898_845,
    (by decide), (by decide), bank6_cover⟩
#print axioms bank6_verified

theorem bank7_verified : Verified bank7 :=
  ⟨bank7_nodes, moment5369_1193,
    (by decide), (by decide), bank7_cover⟩
#print axioms bank7_verified

theorem bank8_verified : Verified bank8 :=
  ⟨bank8_nodes, moment4467_947,
    (by decide), (by decide), bank8_cover⟩
#print axioms bank8_verified

theorem bank9_verified : Verified bank9 :=
  ⟨bank9_nodes, moment5026_1065,
    (by decide), (by decide), bank9_cover⟩
#print axioms bank9_verified

end Research6966.HelperWindowCatalogue

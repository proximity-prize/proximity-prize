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

theorem bank6_verified : Verified bank6 :=
  ⟨bank6_nodes, moment3898_845,
    (by decide), (by decide), bank6_cover⟩

theorem bank7_verified : Verified bank7 :=
  ⟨bank7_nodes, moment5369_1193,
    (by decide), (by decide), bank7_cover⟩

theorem bank8_verified : Verified bank8 :=
  ⟨bank8_nodes, moment4467_947,
    (by decide), (by decide), bank8_cover⟩

theorem bank9_verified : Verified bank9 :=
  ⟨bank9_nodes, moment5026_1065,
    (by decide), (by decide), bank9_cover⟩

end Research6966.HelperWindowCatalogue

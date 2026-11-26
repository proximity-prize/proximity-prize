import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers6
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment4
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment7
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment8

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank30_verified : Verified bank30 :=
  ⟨bank30_nodes, moment3898_828,
    (by decide), (by decide), bank30_cover⟩

theorem bank31_verified : Verified bank31 :=
  ⟨bank31_nodes, moment5010_1065,
    (by decide), (by decide), bank31_cover⟩

theorem bank32_verified : Verified bank32 :=
  ⟨bank32_nodes, moment5359_1116,
    (by decide), (by decide), bank32_cover⟩

theorem bank33_verified : Verified bank33 :=
  ⟨bank33_nodes, moment4466_992,
    (by decide), (by decide), bank33_cover⟩

theorem bank34_verified : Verified bank34 :=
  ⟨bank34_nodes, moment5024_1116,
    (by decide), (by decide), bank34_cover⟩

end Research6966.HelperWindowCatalogue

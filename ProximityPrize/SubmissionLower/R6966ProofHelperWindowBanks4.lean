import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers4
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment11
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment12
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment4

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank20_verified : Verified bank20 :=
  ⟨bank20_nodes, moment5374_1162,
    (by decide), (by decide), bank20_cover⟩

theorem bank21_verified : Verified bank21 :=
  ⟨bank21_nodes, moment5374_1193,
    (by decide), (by decide), bank21_cover⟩

theorem bank22_verified : Verified bank22 :=
  ⟨bank22_nodes, moment4466_966,
    (by decide), (by decide), bank22_cover⟩

theorem bank23_verified : Verified bank23 :=
  ⟨bank23_nodes, moment4466_966,
    (by decide), (by decide), bank23_cover⟩

theorem bank24_verified : Verified bank24 :=
  ⟨bank24_nodes, moment4466_966,
    (by decide), (by decide), bank24_cover⟩

end Research6966.HelperWindowCatalogue

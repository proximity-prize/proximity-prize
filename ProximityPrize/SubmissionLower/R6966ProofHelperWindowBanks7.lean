import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers7
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment0
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment3

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank35_verified : Verified bank35 :=
  ⟨bank35_nodes, moment3414_739,
    (by decide), (by decide), bank35_cover⟩
#print axioms bank35_verified

theorem bank36_verified : Verified bank36 :=
  ⟨bank36_nodes, moment2505_558,
    (by decide), (by decide), bank36_cover⟩
#print axioms bank36_verified

theorem bank37_verified : Verified bank37 :=
  ⟨bank37_nodes, moment3906_868,
    (by decide), (by decide), bank37_cover⟩
#print axioms bank37_verified

theorem bank38_verified : Verified bank38 :=
  ⟨bank38_nodes, moment3898_828,
    (by decide), (by decide), bank38_cover⟩
#print axioms bank38_verified

end Research6966.HelperWindowCatalogue

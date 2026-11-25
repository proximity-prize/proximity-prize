import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment10
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment2
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment4
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment6
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment7

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank25_verified : Verified bank25 :=
  ⟨bank25_nodes, moment4466_966,
    (by decide), (by decide), bank25_cover⟩
#print axioms bank25_verified

theorem bank26_verified : Verified bank26 :=
  ⟨bank26_nodes, moment5373_1193,
    (by decide), (by decide), bank26_cover⟩
#print axioms bank26_verified

theorem bank27_verified : Verified bank27 :=
  ⟨bank27_nodes, moment5024_1116,
    (by decide), (by decide), bank27_cover⟩
#print axioms bank27_verified

theorem bank28_verified : Verified bank28 :=
  ⟨bank28_nodes, moment5021_1116,
    (by decide), (by decide), bank28_cover⟩
#print axioms bank28_verified

theorem bank29_verified : Verified bank29 :=
  ⟨bank29_nodes, moment3900_845,
    (by decide), (by decide), bank29_cover⟩
#print axioms bank29_verified

end Research6966.HelperWindowCatalogue

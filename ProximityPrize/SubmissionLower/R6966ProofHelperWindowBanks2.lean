import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers2
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment11
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment7

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank10_verified : Verified bank10 :=
  ⟨bank10_nodes, moment5374_1139,
    (by decide), (by decide), bank10_cover⟩
#print axioms bank10_verified

theorem bank11_verified : Verified bank11 :=
  ⟨bank11_nodes, moment5374_1139,
    (by decide), (by decide), bank11_cover⟩
#print axioms bank11_verified

theorem bank12_verified : Verified bank12 :=
  ⟨bank12_nodes, moment5374_1162,
    (by decide), (by decide), bank12_cover⟩
#print axioms bank12_verified

theorem bank13_verified : Verified bank13 :=
  ⟨bank13_nodes, moment5024_1116,
    (by decide), (by decide), bank13_cover⟩
#print axioms bank13_verified

theorem bank14_verified : Verified bank14 :=
  ⟨bank14_nodes, moment5023_1116,
    (by decide), (by decide), bank14_cover⟩
#print axioms bank14_verified

end Research6966.HelperWindowCatalogue

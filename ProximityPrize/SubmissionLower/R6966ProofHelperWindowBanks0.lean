import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCovers0
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment3
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment7
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment9

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

theorem bank0_verified : Verified bank0 :=
  ⟨bank0_nodes, moment5024_1116,
    (by decide), (by decide), bank0_cover⟩

theorem bank1_verified : Verified bank1 :=
  ⟨bank1_nodes, moment3906_868,
    (by decide), (by decide), bank1_cover⟩

theorem bank2_verified : Verified bank2 :=
  ⟨bank2_nodes, moment4462_992,
    (by decide), (by decide), bank2_cover⟩

theorem bank3_verified : Verified bank3 :=
  ⟨bank3_nodes, moment3414_759,
    (by decide), (by decide), bank3_cover⟩

theorem bank4_verified : Verified bank4 :=
  ⟨bank4_nodes, moment5368_1162,
    (by decide), (by decide), bank4_cover⟩

end Research6966.HelperWindowCatalogue

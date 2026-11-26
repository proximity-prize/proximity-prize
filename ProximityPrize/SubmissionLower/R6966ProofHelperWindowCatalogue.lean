import ProximityPrize.SubmissionLower.R6966ProofHelperWindowNative
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks0
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks1
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks2
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks3
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks4
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks5
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks6
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowBanks7

set_option Elab.async false

namespace Research6966.HelperWindowCatalogue
open HelperWindowCertificate

def ordinary : Fin 39 → Witness :=
  ![bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38]

theorem ordinary_verified (i : Fin 39) : Verified (ordinary i) := by
  fin_cases i
  · exact bank0_verified
  · exact bank1_verified
  · exact bank2_verified
  · exact bank3_verified
  · exact bank4_verified
  · exact bank5_verified
  · exact bank6_verified
  · exact bank7_verified
  · exact bank8_verified
  · exact bank9_verified
  · exact bank10_verified
  · exact bank11_verified
  · exact bank12_verified
  · exact bank13_verified
  · exact bank14_verified
  · exact bank15_verified
  · exact bank16_verified
  · exact bank17_verified
  · exact bank18_verified
  · exact bank19_verified
  · exact bank20_verified
  · exact bank21_verified
  · exact bank22_verified
  · exact bank23_verified
  · exact bank24_verified
  · exact bank25_verified
  · exact bank26_verified
  · exact bank27_verified
  · exact bank28_verified
  · exact bank29_verified
  · exact bank30_verified
  · exact bank31_verified
  · exact bank32_verified
  · exact bank33_verified
  · exact bank34_verified
  · exact bank35_verified
  · exact bank36_verified
  · exact bank37_verified
  · exact bank38_verified

abbrev ordinary_projected_bounds (i : Fin 39) :=
  @HelperWindowNative.projected_bounds (ordinary i) (ordinary_verified i)

end Research6966.HelperWindowCatalogue

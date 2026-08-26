import ProximityPrize.SubmissionLower.BCHKSFrobeniusQuadraticRootRecovery6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusProjectiveSectionLine6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusCubicMassLedger6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusProjectiveSectionLine6401
set_option maxHeartbeats 1000000
def cubicOwnerCollapseThreshold6401 : Nat := 8
def cubicOwnerFibreMultiplicity6401 : Nat := 7
def linearYLowSupportPseudoRemainderCap6401 : Nat :=
  65537 + 196607 * 65536
def linearYLowSupportOwnerCap6401 : Nat :=
  linearYLowSupportPseudoRemainderCap6401 + 65536 + 1182
def unsplitWeakSeedOwnerPool6401 : Nat := 273591199342811068
def cubicOwnerPoolAfterLowSupport6401 : Nat :=
  unsplitWeakSeedOwnerPool6401 - linearYLowSupportOwnerCap6401
def cubicDenseLineFloor6401 : Nat := 128403981
theorem cubic_incidence_threshold_exact6401 :
    7 * (185353 - 131072) ≤ 3 * (262144 - 131072) ∧
      3 * (262144 - 131072) < 8 * (185353 - 131072) := by
  native_decide
theorem cubic_mass_constants_exact6401 :
    linearYLowSupportPseudoRemainderCap6401 = 12884901889 ∧
      linearYLowSupportOwnerCap6401 = 12884968607 ∧
      cubicOwnerPoolAfterLowSupport6401 = 273591186457842461 ∧
      cubicDenseLineFloor6401 = 128403981 := by
  native_decide
theorem cubic_projectivePlane_denseLine_inequality6401 :
    projectivePlaneLineCount6401 * (cubicDenseLineFloor6401 - 1) <
      cubicOwnerPoolAfterLowSupport6401 * (q6401 + 1) := by
  native_decide
theorem cubic_projectiveFq2Subline_dense_inequality6401 :
    projectiveFqSublineCount6401 * (cubicDenseLineFloor6401 - 1) <
      cubicOwnerPoolAfterLowSupport6401 *
        projectiveFqSublineReplication6401 := by
  native_decide
theorem cubic_sevenFibre_margin6401 :
    cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 <
      cubicDenseLineFloor6401 ∧
    cubicDenseLineFloor6401 -
        cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 =
      5241760 := by
  native_decide
theorem cubic_eightFibre_noMargin6401 :
    cubicDenseLineFloor6401 ≤
      cubicOwnerCollapseThreshold6401 * quadraticPencilFibreCap6401 := by
  native_decide
end BCHKSFrobeniusCubicMassLedger6401
end ProximityPrize.SubmissionLower

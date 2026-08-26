import ProximityPrize.SubmissionLower.BCHKSFrobeniusQuadraticRootRecovery6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusProjectiveSectionLine6401

/-!
# Corrected cubic-pencil mass ledger at score 64.01

Clearing a nonconstant denominator in the degree-one Frobenius branch can
produce a genuinely degree-three locator pencil.  The elementary
coordinate-incidence threshold is then eight owners, so failure of an
affine collapse permits seven owners per normalized spherical-list element.

The original positive-rank ledger discarded the old-radius owners before
the projective-section argument and was too small for this corrected factor
seven.  A linear-in-`Y` interpolation argument can instead charge all owners
whose actual error support is at most `54282`.  This file records the
conservative pseudo-remainder budget for that charge and verifies that the
remaining unsplit owner pool still has enough mass for the cubic factor.

Only the numerical ledger is asserted here.  The pseudo-remainder theorem
and the cubic received-lift theorem are separate algebraic obligations.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusCubicMassLedger6401

open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusProjectiveSectionLine6401

set_option maxHeartbeats 1000000

/-- Number of identities needed to force a degree-three parameter curve to
collapse to the benchmark affine owner curve. -/
def cubicOwnerCollapseThreshold6401 : Nat := 8

/-- Consequently, under failure of the desired curve, one normalized list
element can carry at most seven owners. -/
def cubicOwnerFibreMultiplicity6401 : Nat := 7

/-- Conservative degree of one nonzero coefficient of the pseudo-remainder
of `A` by `B` over `F(Z)[X]`.  The worst nonunit case has
`deg_X B = 1`:

`65537 + (196607 - 1 + 1) * 65536`.
-/
def linearYLowSupportPseudoRemainderCap6401 : Nat :=
  65537 + 196607 * 65536

/-- Add roots of the leading `X` coefficient of `B` and the `1182` owners
allowed in the global-divisor/no-curve branch. -/
def linearYLowSupportOwnerCap6401 : Nat :=
  linearYLowSupportPseudoRemainderCap6401 + 65536 + 1182

/-- The complete weak-seed pool before the old-radius subtraction. -/
def unsplitWeakSeedOwnerPool6401 : Nat := 273591199342811068

def cubicOwnerPoolAfterLowSupport6401 : Nat :=
  unsplitWeakSeedOwnerPool6401 - linearYLowSupportOwnerCap6401

/-- Dense projective-section floor retained after the conservative
low-support charge. -/
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

/-- Ordinary point--line averaging in `PG(2,q)` still gives the advertised
dense line after charging the complete conservative low-support cap. -/
theorem cubic_projectivePlane_denseLine_inequality6401 :
    projectivePlaneLineCount6401 * (cubicDenseLineFloor6401 - 1) <
      cubicOwnerPoolAfterLowSupport6401 * (q6401 + 1) := by
  native_decide

/-- The same floor is available after the rank-four `F_{q^2}`-subline
classification and averaging over its `F_q`-sublines. -/
theorem cubic_projectiveFq2Subline_dense_inequality6401 :
    projectiveFqSublineCount6401 * (cubicDenseLineFloor6401 - 1) <
      cubicOwnerPoolAfterLowSupport6401 *
        projectiveFqSublineReplication6401 := by
  native_decide

/-- Seven corrected cubic fibres fit strictly below the recovered rich
line.  The exact remaining margin is `5241760`. -/
theorem cubic_sevenFibre_margin6401 :
    cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 <
      cubicDenseLineFloor6401 ∧
    cubicDenseLineFloor6401 -
        cubicOwnerFibreMultiplicity6401 * quadraticPencilFibreCap6401 =
      5241760 := by
  native_decide

/-- Eight fibres no longer fit, matching the exact incidence threshold. -/
theorem cubic_eightFibre_noMargin6401 :
    cubicDenseLineFloor6401 ≤
      cubicOwnerCollapseThreshold6401 * quadraticPencilFibreCap6401 := by
  native_decide

end BCHKSFrobeniusCubicMassLedger6401
end ProximityPrize.SubmissionLower

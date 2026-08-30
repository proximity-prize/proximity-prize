import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger
import ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfile

/-!
# Affine positive ledger for a reduced static cut

The static coordinate projections use the reduced Taylor representative.
The moving-coordinate contribution still uses the sharp centre and surface
coming from the actual filtered-cut presentation.
-/

namespace ProximityPrize.SubmissionLower.ContactMovingReducedPositiveLedger

open scoped BigOperators
open ContactFlagBezout ContactFactoredFlagCount
open ContactResidualSupportParameters
open ContactMovingPositiveLedger
open ContactMovingAgreementCertificate
open ContactReducedTaylorProfile

def cutBase : FlagDegree := unitYZFlag

def reducedCut (support : ResidualSupportParameters) (d : ℕ) : FlagDegree :=
  cutBase + d • reducedAgreementDirection support

theorem reducedCut_eq_residualFlag (support : ResidualSupportParameters)
    (d : ℕ) :
    reducedCut support d = reducedResidualAgreementFlag support d := by
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;>
    simp only [cutBase, reducedAgreementDirection, unitYZFlag,
      nsmul_zOnly, nsmul_yz, nsmul_all] <;>
    ring

def degreeSlope (support : ResidualSupportParameters) (a b s : ℕ)
    (p : FlagDegree) : ℕ :=
  weightedMixed p (reducedAgreementDirection support) (normalFlag a b s) +
    flagMixed p (fiberFlag a b s) (surfaceFlag a b s)

def degreeBase (a b s : ℕ) (p : FlagDegree) : ℕ :=
  weightedMixed p cutBase (normalFlag a b s) +
    flagMixed p (fiberFlag a b s) (centreFlag a b s)

def unitSlope (support : ResidualSupportParameters) (a b s : ℕ)
    (p : FlagDegree) : ℕ :=
  weightedMixed p (reducedAgreementDirection support) (centreFlag a b s)

def unitBase (a b s : ℕ) (p : FlagDegree) : ℕ :=
  weightedMixed p cutBase (centreFlag a b s)

def zSlope (support : ResidualSupportParameters) (p : FlagDegree) : ℕ :=
  flagMixed p (reducedAgreementDirection support) unitZFlag

def zBase (p : FlagDegree) : ℕ := flagMixed p cutBase unitZFlag

def yzSlope (support : ResidualSupportParameters) (p : FlagDegree) : ℕ :=
  flagMixed p (reducedAgreementDirection support) unitYZFlag

def yzBase (p : FlagDegree) : ℕ := flagMixed p cutBase unitYZFlag

theorem degree_affine (support : ResidualSupportParameters)
    (a b s d : ℕ) (p : FlagDegree) :
    weightedMixed p (reducedCut support d) (normalFlag a b s) +
        flagMixed p (fiberFlag a b s)
          (centreFlag a b s + d • surfaceFlag a b s) =
      d * degreeSlope support a b s p + degreeBase a b s p := by
  simp only [weightedMixed, reducedCut, cutBase, degreeSlope, degreeBase,
    normalFlag, fiberFlag, surfaceFlag, centreFlag, directionFlag,
    reducedAgreementDirection, flagMixed, unitZFlag, unitYZFlag, unitAllFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem unit_affine (support : ResidualSupportParameters)
    (a b s d : ℕ) (p : FlagDegree) :
    weightedMixed p (reducedCut support d) (centreFlag a b s) =
      d * unitSlope support a b s p + unitBase a b s p := by
  simp only [weightedMixed, reducedCut, cutBase, unitSlope, unitBase,
    centreFlag, directionFlag, reducedAgreementDirection, flagMixed,
    unitZFlag, unitYZFlag, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem z_affine (support : ResidualSupportParameters) (d : ℕ)
    (p : FlagDegree) :
    flagMixed p (reducedCut support d) unitZFlag =
      d * zSlope support p + zBase p := by
  simp only [reducedCut, cutBase, zSlope, zBase, reducedAgreementDirection,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem yz_affine (support : ResidualSupportParameters) (d : ℕ)
    (p : FlagDegree) :
    flagMixed p (reducedCut support d) unitYZFlag =
      d * yzSlope support p + yzBase p := by
  simp only [reducedCut, cutBase, yzSlope, yzBase, reducedAgreementDirection,
    flagMixed, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

section Cumulative

variable {I : Type*} [Fintype I] (flags : I → FlagDegree) (p : FlagDegree)
variable (hs : (∑ i, (flags i).all) ≤ p.all)
variable (hm : (∑ i, ((flags i).yz + (flags i).all)) ≤ p.yz + p.all)
variable (ht : (∑ i, ((flags i).zOnly + (flags i).yz + (flags i).all)) ≤
  p.zOnly + p.yz + p.all)
include hs hm ht

theorem sum_weightedMixed_le (q r : FlagDegree) :
    (∑ i, weightedMixed (flags i) q r) ≤ weightedMixed p q r := by
  simp_rw [weightedMixed_eq]
  exact sum_flagMixed_le_of_cumulative flags p q r hs hm ht

theorem sum_degreeSlope_le (support : ResidualSupportParameters)
    (a b s : ℕ) :
    (∑ i, degreeSlope support a b s (flags i)) ≤
      degreeSlope support a b s p := by
  simp only [degreeSlope, Finset.sum_add_distrib]
  exact add_le_add
    (sum_weightedMixed_le flags p hs hm ht
      (reducedAgreementDirection support) (normalFlag a b s))
    (sum_flagMixed_le_of_cumulative flags p
      (fiberFlag a b s) (surfaceFlag a b s) hs hm ht)

theorem sum_degreeBase_le (a b s : ℕ) :
    (∑ i, degreeBase a b s (flags i)) ≤ degreeBase a b s p := by
  simp only [degreeBase, Finset.sum_add_distrib]
  exact add_le_add
    (sum_weightedMixed_le flags p hs hm ht cutBase (normalFlag a b s))
    (sum_flagMixed_le_of_cumulative flags p
      (fiberFlag a b s) (centreFlag a b s) hs hm ht)

theorem sum_unitSlope_le (support : ResidualSupportParameters)
    (a b s : ℕ) :
    (∑ i, unitSlope support a b s (flags i)) ≤
      unitSlope support a b s p :=
  sum_weightedMixed_le flags p hs hm ht
    (reducedAgreementDirection support) (centreFlag a b s)

theorem sum_unitBase_le (a b s : ℕ) :
    (∑ i, unitBase a b s (flags i)) ≤ unitBase a b s p :=
  sum_weightedMixed_le flags p hs hm ht cutBase (centreFlag a b s)

theorem sum_zSlope_le (support : ResidualSupportParameters) :
    (∑ i, zSlope support (flags i)) ≤ zSlope support p :=
  sum_flagMixed_le_of_cumulative flags p
    (reducedAgreementDirection support) unitZFlag hs hm ht

theorem sum_zBase_le : (∑ i, zBase (flags i)) ≤ zBase p :=
  sum_flagMixed_le_of_cumulative flags p cutBase unitZFlag hs hm ht

theorem sum_yzSlope_le (support : ResidualSupportParameters) :
    (∑ i, yzSlope support (flags i)) ≤ yzSlope support p :=
  sum_flagMixed_le_of_cumulative flags p
    (reducedAgreementDirection support) unitYZFlag hs hm ht

theorem sum_yzBase_le : (∑ i, yzBase (flags i)) ≤ yzBase p :=
  sum_flagMixed_le_of_cumulative flags p cutBase unitYZFlag hs hm ht

end Cumulative

end ProximityPrize.SubmissionLower.ContactMovingReducedPositiveLedger

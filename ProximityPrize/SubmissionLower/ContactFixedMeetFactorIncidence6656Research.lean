import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch
import ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet6656Research

/-!
# Fixed-meet factor incidence at score 66.56

This module specializes the accepted recursive terminal-incidence theorem to
the final recursive-GCD meet profile.  The only geometric input is the
factor-shaped terminal fiber inequality; all remaining work is exact
arithmetic with the meet profile's incidence ceilings.
-/

namespace ProximityPrize.SubmissionLower.ContactFixedMeetFactorIncidence6656Research

open scoped Classical
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The fixed support and the robust meet profile encode the same agreement
direction. -/
theorem fixedMeet_agreementDirection_eq :
    ResidualSupportParameters.fixedMeetSupport.agreementDirection =
      meetProfile.agreementDirection := by
  rw [ResidualSupportParameters.fixedMeet_agreement_direction]
  exact meet_parameter_values.2.2.2.2.2.2.1.symm

/-- Exact meet-profile incidence coefficients used below. -/
theorem meet_incidence_values :
    meetProfile.degreeIncidence = 9724036071 ∧
      meetProfile.unitIncidence = 131073 := by
  exact ⟨meet_parameter_values.2.2.2.1,
    meet_parameter_values.2.2.2.2.1⟩

/-- The exact rational ceiling used for the degree-weighted incidence part. -/
theorem meet_degree_incidence_ceiling :
    meetProfile.n * meetProfile.gap * meetProfile.w ≤
      meetProfile.degreeIncidence * meetProfile.agreements := by
  norm_num [meetProfile, Profile.gap, Profile.degreeIncidence]

/-- Uniform degree-part compression for every identity count `k`. -/
theorem meet_degree_part_bound (k : ℕ) (hk : k ≤ meetProfile.w) :
    (meetProfile.n - k) * meetProfile.gap * (meetProfile.w - k) ≤
      meetProfile.degreeIncidence * (meetProfile.agreements - k) := by
  have hcross := identity_degree_weight_cross_le meetProfile.n
    meetProfile.agreements meetProfile.w k hk
      (by norm_num [meetProfile]) (by norm_num [meetProfile])
  have hmul := Nat.mul_le_mul_right (meetProfile.agreements - k)
    meet_degree_incidence_ceiling
  have htotal :
      ((meetProfile.n - k) * meetProfile.gap * (meetProfile.w - k)) *
          meetProfile.agreements ≤
        (meetProfile.degreeIncidence * (meetProfile.agreements - k)) *
          meetProfile.agreements := by
    calc
      ((meetProfile.n - k) * meetProfile.gap * (meetProfile.w - k)) *
            meetProfile.agreements =
          (meetProfile.n - k) *
            (meetProfile.agreements - meetProfile.w) *
            (meetProfile.w - k) * meetProfile.agreements := by
              rfl
      _ ≤ meetProfile.n * (meetProfile.agreements - meetProfile.w) *
          meetProfile.w * (meetProfile.agreements - k) := hcross
      _ ≤ (meetProfile.degreeIncidence * meetProfile.agreements) *
          (meetProfile.agreements - k) := by
            simpa only [Profile.gap] using hmul
      _ = (meetProfile.degreeIncidence * (meetProfile.agreements - k)) *
          meetProfile.agreements := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by norm_num [meetProfile])

/-- Uniform unit-part compression for every identity count `k`. -/
theorem meet_unit_part_bound (k : ℕ) (hk : k ≤ meetProfile.w) :
    (meetProfile.n - k) * meetProfile.gap ≤
      meetProfile.unitIncidence * (meetProfile.agreements - k) := by
  simpa only [Profile.gap, Profile.unitIncidence] using
    identity_unit_weight_le meetProfile.n meetProfile.agreements
      meetProfile.w k hk (by norm_num [meetProfile]) (by norm_num [meetProfile])

/-- The coefficient multiplying the terminal residual degree. -/
def meetFactorDegreeCost (p : FlagDegree) : ℕ :=
  (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
        ResidualSupportParameters.fixedMeetSupport.agreementDirection *
      meetProfile.degreeIncidence +
    flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
        unitYZFlag * meetProfile.unitIncidence) +
  (meetProfile.errors + 1) * meetProfile.gap *
    (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
        unitZFlag +
      flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
        unitAllFlag)

/-- The affine-unit coefficient in the terminal factor fiber bound. -/
def meetFactorUnitCost (p : FlagDegree) : ℕ :=
  (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
        unitYZFlag * meetProfile.degreeIncidence +
    flagMixed p unitYZFlag unitYZFlag * meetProfile.unitIncidence) +
  (meetProfile.errors + 1) * meetProfile.gap *
    (flagMixed p unitYZFlag unitZFlag +
      flagMixed p unitYZFlag unitAllFlag)

/-- Expanding the two incidence coefficients gives exactly the robust
factor-regular ledger. -/
theorem meet_incidence_cost_eq_factorRegularLedger (p : FlagDegree) :
    meetProfile.degreeIncidence * meetFactorDegreeCost p +
      meetProfile.unitIncidence * meetFactorUnitCost p =
      meetProfile.factorRegularLedger p := by
  simp only [meetFactorDegreeCost, meetFactorUnitCost]
  rw [fixedMeet_agreementDirection_eq]
  simp only [Profile.factorRegularLedger, Profile.factorPrimary,
    Profile.factorZTail, Profile.factorAllTail]
  ring

/-- Fixed-meet factorwise outer incidence.  It is the score-66.56 analogue
of `recursive_scaled_factor_6600`: the recursive geometry is reused through
`recursive_scaled_stratified_incidence_bound`, while this theorem supplies
the meet profile's exact incidence arithmetic.
-/
theorem recursive_scaled_factor_6656
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
      ResidualSupportParameters.fixedMeetSupport)
    (p : FlagDegree)
    (hnodes : S.nodes.card = meetProfile.n)
    (hagreement : ∀ gamma ∈ Gamma,
      meetProfile.agreements ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card *
          meetProfile.gap ≤
        D.degree * meetFactorDegreeCost p + meetFactorUnitCost p) :
    Gamma.card * meetProfile.gap ^ 2 ≤
      meetProfile.factorRegularLedger p := by
  have h := recursive_scaled_stratified_incidence_bound
    hphi S (meetFactorDegreeCost p) (meetFactorUnitCost p)
      meetProfile.degreeIncidence meetProfile.unitIncidence
      (by norm_num [meetProfile]) hagreement hfiber
      (by
        intro k hk
        rw [hnodes]
        exact meet_degree_part_bound k hk)
      (by
        intro k hk
        rw [hnodes]
        exact meet_unit_part_bound k hk)
  calc
    Gamma.card * meetProfile.gap ^ 2 ≤
        meetProfile.degreeIncidence * meetFactorDegreeCost p +
          meetProfile.unitIncidence * meetFactorUnitCost p := by
            simpa only [Profile.gap] using h
    _ = meetProfile.factorRegularLedger p :=
      meet_incidence_cost_eq_factorRegularLedger p

end

end ProximityPrize.SubmissionLower.ContactFixedMeetFactorIncidence6656Research

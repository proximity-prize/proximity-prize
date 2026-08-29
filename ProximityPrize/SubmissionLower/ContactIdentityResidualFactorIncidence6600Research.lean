import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch

/-!
# Factorwise outer residual incidence for score 66

The surface can have several irreducible factors.  The recursive incidence
bound must therefore retain each factor's own flag and only aggregate after
the factorwise bound is proved.  This is the factor-symbolic counterpart of
`recursive_scaled_primary_z_6600`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research

open scoped Classical
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactNearPencil6600FlagResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The accepted factor ledger with its residual agreement direction left
symbolic. -/
def factorRegularLedgerFor (p direction : FlagDegree) : ℕ :=
  degreeIncidence *
      ((flagMixed p direction direction * degreeIncidence +
          flagMixed p direction unitYZFlag * unitIncidence) +
        (errors + 1) * gap *
          (flagMixed p direction unitZFlag +
            flagMixed p direction unitAllFlag)) +
    unitIncidence *
      ((flagMixed p direction unitYZFlag * degreeIncidence +
          flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
        (errors + 1) * gap *
          (flagMixed p unitYZFlag unitZFlag +
            flagMixed p unitYZFlag unitAllFlag))

/-- Exact factorwise outer compression, including the branch-local `Z` and
all-coordinate tails.  All coefficients remain symbolic in the factor flag `p`; the
conclusion is exactly `factorRegularLedger p`.
-/
theorem recursive_scaled_factor_with_support_6600
    (hphi : Function.Injective phi)
    (support : ResidualSupportParameters)
    (S : ResidualStage phi Gamma x pchar errors flag w support)
    (p : FlagDegree)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
        D.degree *
            ((flagMixed p support.agreementDirection support.agreementDirection *
                degreeIncidence +
              flagMixed p support.agreementDirection unitYZFlag *
                unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p support.agreementDirection unitZFlag +
                  flagMixed p support.agreementDirection unitAllFlag)) +
          ((flagMixed p support.agreementDirection unitYZFlag *
                degreeIncidence +
              flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
            (errors + 1) * gap *
              (flagMixed p unitYZFlag unitZFlag +
                flagMixed p unitYZFlag unitAllFlag))) :
    Gamma.card * gap ^ 2 ≤
      factorRegularLedgerFor p support.agreementDirection := by
  have h := recursive_scaled_stratified_incidence_bound
    hphi S
    ((flagMixed p support.agreementDirection support.agreementDirection *
          degreeIncidence +
        flagMixed p support.agreementDirection unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p support.agreementDirection unitZFlag +
          flagMixed p support.agreementDirection unitAllFlag))
    ((flagMixed p support.agreementDirection unitYZFlag * degreeIncidence +
        flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p unitYZFlag unitZFlag +
          flagMixed p unitYZFlag unitAllFlag))
    degreeIncidence unitIncidence
    (by norm_num [agreements, n, errors, w])
    hagreement hfiber
    (by
      intro k hk
      rw [hnodes]
      exact degree_part_bound k hk)
    (by
      intro k hk
      rw [hnodes]
      exact unit_part_bound k hk)
  calc
    Gamma.card * gap ^ 2 ≤
        degreeIncidence *
            ((flagMixed p support.agreementDirection support.agreementDirection *
                  degreeIncidence +
                flagMixed p support.agreementDirection unitYZFlag *
                  unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p support.agreementDirection unitZFlag +
                  flagMixed p support.agreementDirection unitAllFlag)) +
          unitIncidence *
            ((flagMixed p support.agreementDirection unitYZFlag *
                  degreeIncidence +
                flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p unitYZFlag unitZFlag +
                  flagMixed p unitYZFlag unitAllFlag)) := by
      simpa only [gap] using h
    _ = factorRegularLedgerFor p support.agreementDirection := rfl

/-- Accepted residual-direction compatibility wrapper. -/
theorem recursive_scaled_factor_6600
    (hphi : Function.Injective phi)
    (S : ResidualStage phi Gamma x pchar errors flag w)
    (p : FlagDegree)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
        D.degree *
            ((flagMixed p agreementDirection6600 agreementDirection6600 *
                degreeIncidence +
              flagMixed p agreementDirection6600 unitYZFlag *
                unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p agreementDirection6600 unitZFlag +
                  flagMixed p agreementDirection6600 unitAllFlag)) +
          ((flagMixed p agreementDirection6600 unitYZFlag *
                degreeIncidence +
              flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
            (errors + 1) * gap *
              (flagMixed p unitYZFlag unitZFlag +
                flagMixed p unitYZFlag unitAllFlag))) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedger p := by
  have h := recursive_scaled_factor_with_support_6600 hphi
    ResidualSupportParameters.acceptedSupport S p hnodes hagreement
      (by
        simpa [ResidualSupportParameters.acceptedSupport,
          ResidualSupportParameters.agreementDirection,
          agreementDirection6600] using hfiber)
  calc
    Gamma.card * gap ^ 2 ≤
        factorRegularLedgerFor p
          ResidualSupportParameters.acceptedSupport.agreementDirection := h
    _ = factorRegularLedger p := by
      simp [factorRegularLedgerFor, factorRegularLedger, factorPrimary,
        factorZTail, factorAllTail,
        ResidualSupportParameters.acceptedSupport,
        ResidualSupportParameters.agreementDirection,
        agreementDirection6600]
      ring

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research

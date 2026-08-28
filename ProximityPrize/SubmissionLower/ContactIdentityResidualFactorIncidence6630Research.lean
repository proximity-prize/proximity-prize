import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6600Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidence6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FactorLedgerResearch

/-!
# Factorwise outer residual incidence for score 66

The surface can have several irreducible factors.  The recursive incidence
bound must therefore retain each factor's own flag and only aggregate after
the factorwise bound is proved.  This is the factor-symbolic counterpart of
`recursive_scaled_primary_z_6600`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6630Research

open scoped Classical
open ContactIdentityResidualIteration6630Research
open ContactIdentityResidualTerminalIncidence6630Research
open ContactNearPencil6630ArithmeticResearch
open ContactNearPencil6630FlagResearch
open ContactNearPencil6630FactorLedgerResearch
open ContactPrimeSeedIncidence
open ContactFlagBezout6543Research

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Exact factorwise outer compression, including the branch-local `Z` and
all-coordinate tails.  All coefficients remain symbolic in the factor flag `p`; the
conclusion is exactly `factorRegularLedgerYZ p`.
-/
theorem recursive_scaled_factor_6630_z_yz
    (hphi : Function.Injective phi)
    (S : ResidualStage6630 phi Gamma x pchar errors flag w)
    (p : FlagDegree)
    (hnodes : S.nodes.card = n)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant, ∀ i ∈ D.stage.nodes,
      ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card * gap ≤
        D.degree *
            ((flagMixed p agreementDirection6630 agreementDirection6630 *
                degreeIncidence +
              flagMixed p agreementDirection6630 unitYZFlag *
                unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p agreementDirection6630 unitZFlag +
                  flagMixed p agreementDirection6630 unitYZFlag)) +
          ((flagMixed p agreementDirection6630 unitYZFlag *
                degreeIncidence +
              flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
            (errors + 1) * gap *
              (flagMixed p unitYZFlag unitZFlag +
                flagMixed p unitYZFlag unitYZFlag))) :
    Gamma.card * gap ^ 2 ≤ factorRegularLedgerYZ p := by
  have h := recursive_scaled_stratified_incidence_bound
    hphi S
    ((flagMixed p agreementDirection6630 agreementDirection6630 *
          degreeIncidence +
        flagMixed p agreementDirection6630 unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p agreementDirection6630 unitZFlag +
          flagMixed p agreementDirection6630 unitYZFlag))
    ((flagMixed p agreementDirection6630 unitYZFlag * degreeIncidence +
        flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
      (errors + 1) * gap *
        (flagMixed p unitYZFlag unitZFlag +
          flagMixed p unitYZFlag unitYZFlag))
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
            ((flagMixed p agreementDirection6630 agreementDirection6630 *
                  degreeIncidence +
                flagMixed p agreementDirection6630 unitYZFlag *
                  unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p agreementDirection6630 unitZFlag +
                  flagMixed p agreementDirection6630 unitYZFlag)) +
          unitIncidence *
            ((flagMixed p agreementDirection6630 unitYZFlag *
                  degreeIncidence +
                flagMixed p unitYZFlag unitYZFlag * unitIncidence) +
              (errors + 1) * gap *
                (flagMixed p unitYZFlag unitZFlag +
                  flagMixed p unitYZFlag unitYZFlag)) := by
      simpa only [gap] using h
    _ = factorRegularLedgerYZ p := by
      simp only [factorRegularLedgerYZ, factorPrimary6630, factorZTail6630, factorYZTail6630]
      ring

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualFactorIncidence6630Research.recursive_scaled_factor_6630_z_yz

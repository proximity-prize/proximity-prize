import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount
import ProximityPrize.SubmissionLower.ContactSingularLedger

namespace ProximityPrize.SubmissionLower.ContactSingularBranch

open scoped BigOperators
open ContactParameters ContactSingularLedger
open ContactSelectedSeedDecomposition ContactImplicitPairBudgets
open ContactImplicitContactLift ContactSingularAuxiliary
open ContactSingularDegreeBounds ContactInterpolation ContactTranslation
open ContactImplicitPairSeedCount
open ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount

noncomputable section

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev ImplicitIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(implicitPairSet (singularAuxiliary Q))

def implicitSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (q : ImplicitIndex Q) : Finset K := by
  classical
  exact Gamma.filter (fun gamma => LiftedSolutionPair q.1 (selected gamma) gamma)

def implicitVector (Q : MvPolynomial (Fin 4) K)
    (q : ImplicitIndex Q) : DegreeVector :=
  ⟨pairYCost q.1, pairRCost q.1, pairZCost q.1⟩

def singularSeeds (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) : Finset K := by
  classical
  exact Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
    exceptionalSeeds (singularAuxiliary Q) Gamma selected

theorem implicitSeeds_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (q : ImplicitIndex Q) : implicitSeeds Q selected Gamma q ⊆ Gamma := by
  classical
  exact Finset.filter_subset _ _

theorem implicitSeeds_solution (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (q : ImplicitIndex Q) (gamma : K)
    (hgamma : gamma ∈ implicitSeeds Q selected Gamma q) :
    LiftedSolutionPair q.1 (selected gamma) gamma := by
  classical
  exact (Finset.mem_filter.mp hgamma).2

theorem singularSeeds_card_le_sum
    (Q : MvPolynomial (Fin 4) K)
    (selected : K -> Polynomial K) (Gamma : Finset K) :
    (singularSeeds Q selected Gamma).card ≤
      (∑ q : ImplicitIndex Q, (implicitSeeds Q selected Gamma q).card) +
        (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card := by
  classical
  unfold singularSeeds
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right Finset.card_biUnion_le _)

variable {Iota : Type}

end
end ProximityPrize.SubmissionLower.ContactSingularBranch

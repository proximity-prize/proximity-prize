import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactParameters6600Research
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactNearPencil6600FactorLedgerResearch

/-!
# Rectangular flag adapter for the actual score-66 surface factors

Each positive-`R` irreducible factor is enclosed by the flag
`Flag(deg_Z, deg_Y, deg_R)`.  This deliberately uses the robust rectangular
outer flag: the existing factor theorem immediately bounds the three sums by
`(516,41,8)`, and the resulting ledger still proves score 66.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research

open scoped BigOperators
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactGenericSurface
open ContactFlagBezout6543Research

noncomputable section

variable {K Omega : Type} [Field K] [Field Omega]

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(positiveRFactors Q)


end

end ProximityPrize.SubmissionLower.ContactRegularFactorFlag6600Research

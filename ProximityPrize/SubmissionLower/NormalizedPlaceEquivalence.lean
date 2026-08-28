import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PurelyInseparableValuation
import ProximityPrize.SubmissionLower.CoordinatePlaceClassification
import ProximityPrize.SubmissionLower.NormalizedPlaceClassification

/-!
# Equivalence-rigidity of normalized curve places

The common place type stores surjective integer-valued valuations.  On
the fixed finite/separable normalization, equivalent valuations come
from the same height-one place.  This strengthens the existing
injectivity theorem, which was stated only for literal equality.
-/

namespace ProximityPrize.SubmissionLower.NormalizedPlaceEquivalence

open scoped WithZero

noncomputable section

open CoordinatePlaceClassification

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Equivalent normalized valuations are the same common curve place. -/
theorem eq_of_isEquiv
    (v w : NormalizedValuation K L) (h : v.val.IsEquiv w.val) : v = w := by
  apply Subtype.ext
  exact NormalizedPlaceClassification.eq_of_equiv_surjective
    v.val w.val v.property.1 w.property.1 h

end

end ProximityPrize.SubmissionLower.NormalizedPlaceEquivalence

#print axioms ProximityPrize.SubmissionLower.NormalizedPlaceEquivalence.eq_of_isEquiv

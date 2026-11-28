import ProximityPrize.SubmissionLower.Z6970ExpandedPrimarySupport

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000

namespace ExpandedWidePrimary6970

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open ExpandedPrimary6970 (nodeMap wordMap row_bounds primaryBox TrueWeightLE JetsBounded contact_of_word_kernel)
open ExpandedColumns6970
open ExpandedTaper6970 (BlockIndex debit)
open scoped BigOperators
open ExpandedPrimary6970 (local_range_finite)
open P0_9_2 (map_independent_family)

open PolynomialDifferential ReedSolomon.HiddenDerivative

@[irreducible] noncomputable def rankCharge : ℕ := ∑ i : BlockIndex, debit i

theorem rankCharge_eq : rankCharge = ∑ i : BlockIndex, debit i := by
  unfold rankCharge
  rfl

end
end ExpandedWidePrimary6970

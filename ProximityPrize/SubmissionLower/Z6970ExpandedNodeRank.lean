import ProximityPrize.SubmissionLower.Z6970ExpandedPrimarySupport
import ProximityPrize.SubmissionLower.Z6970ExpandedRankCharge

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

theorem rank_at_position {A D : ℕ} (x y : Geom) :
    Module.finrank Geom (LinearMap.range (nodeMap (A:=A) (D:=D) x y)) ≤ rankCharge := by
  letI := local_range_finite x y
  have hr := ExpandedTaper6970.local_rank x y
  rw [← rankCharge_eq] at hr
  apply (Submodule.finrank_mono ?_).trans hr
  rintro _ ⟨Q, rfl⟩
  exact ⟨⟨Q.1, fun e he => (Q.2 he).1⟩, rfl⟩

end
end ExpandedWidePrimary6970

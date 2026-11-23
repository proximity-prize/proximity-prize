import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch1
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_1
open P1_7 (Bank)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_1_2 (six_nodeRows sixPerNode)
open P1_7_1_3 (momentEstimate grouped_bound)
open P1_7_1_3_2 (ExactMoment)
structure BankOK (t : Bank) : Prop where
  nodes : nodeRows t.shape = t.nodeRows
  moment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p
theorem checked (t : Bank) {m B J N M : ℕ}
    (hm : t.shape.m = m) (hB : t.shape.B = B) (hJ : t.shape.J = J)
    (hN : t.nodeRows = N) (hM : t.poleMoment = M)
    (hmJ : 2*J ≤ m) (hJB : m+J ≤ B+1)
    (hnode : 262144 * sixPerNode (m-2*J) J = 6*N)
    (hchar : B < K1.p) (hbound : momentEstimate B J = M) : BankOK t := by
  have h := six_nodeRows t.shape (by rw [hm, hJ]; exact hmJ) (by rw [hm, hJ, hB]; exact hJB)
  rw [hm, hJ, hnode, ← hN] at h
  refine ⟨by omega, ?_⟩
  rw [hB, hJ, hM]
  exact ⟨(grouped_bound _ _).trans hbound.le, hchar⟩
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000



















































end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000




















































end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000














































end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000





















































end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000






























end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000















































end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000


























































end P3_7_1
end
section
namespace P3_7_1
open P3 (HighBand)
open P3_7 (Bank Stage terminal stages  )
open scoped P1_7_1_3_2
local notation "b!" depth "," grade "," deriv "," nodes "," moment ";" h =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) h
end P3_7_1
end

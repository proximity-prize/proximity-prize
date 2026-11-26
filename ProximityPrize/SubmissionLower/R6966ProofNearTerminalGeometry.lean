import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ProximityPrize.SubmissionLower.R6966ProofSpreadInterval
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofPadeResidualBank

set_option Elab.async false

namespace Research6966.NearTerminal
open Finset Polynomial
open K1 (p I)
open K1_14 (Jet Equation L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree seedDegree_le)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure)
open PadeNativeQuotient (Native axis axis_le)

open NearBook

open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 6500000
set_option maxRecDepth 6500
set_option backward.isDefEq.respectTransparency false

theorem axis_seed (P : Jet) (z : Fin 2) : axis P z≤seedDegree P :=
  (axis_le ..).mpr (fun j i=>
    (MvPolynomial.degreeOf_le_totalDegree ..).trans ((seedDegree_le P _).mp le_rfl j i))

theorem seeded_of_positive {P : Jet} (pos : 0<seedDegree P) : K1_14_2.UsesSeed P := by
  unfold K1_14_2.UsesSeed
  by_contra! none
  exact (Nat.not_le_of_lt pos) ((seedDegree_le P 0).mpr none)



























































































end
end Research6966.NearTerminal

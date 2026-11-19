/- Apache-2.0. 68.36 degree-interval receipts by Bome2017 over the BitWonka and Lucieno physical bounds. -/
import ProximityPrize.SubmissionLower.Night6836Pool
import ProximityPrize.SubmissionLower.Night6836AbstractPrice
namespace ProximityPrize.SubmissionLower.Night6836PhysicalPrice
open scoped Classical
open RCN095 RCN266 Koala6831Moving Koala6831MovingPaid LocatorFactorAggregate
open Raw6836 Night6836Bank
open Koala6835.Offers (valid)
open Koala6836.Offers (bank)
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]
theorem factor_bounds {x:I ↪ K} {H:MvPolynomial (Fin 4) K} {S:Finset K} {sel:K→Polynomial K}
    {u v:I→K} {D:ℕ} (A:Original x H S sel u v D) (F:RegularIndex H) {r e z:ℕ}
    (pos:0<r) (eq:contactFlag F.1=⟨z,e,r⟩) (cap:r≤18 ∧ r+e≤76 ∧ r+e+z≤9352) :
    (regularFiber H S sel F).card≤Koala6836.Tables.oneUnits r e (z/100)*10000000000000 ∧
    (r+e+z ≤ Koala6836.Room.maxTotal r e →
      (regularFiber H S sel F).card≤Koala6836.Room.budget r e (r+e+z)) :=
  factor_bounds_of_bank A F pos eq cap (fun i => (chosen i).w)
    (fun i => (chosen i).count) (fun i => (chosen i).dims)
    (fun i h => project_bank i r e (r+e+z) pos h)
#print axioms factor_bounds
end ProximityPrize.SubmissionLower.Night6836PhysicalPrice

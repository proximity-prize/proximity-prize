/- Apache-2.0. The actual regular-factor population on one hard run.
   Uses the additive flags of the Bome2017–Lucieno construction. -/
import ProximityPrize.SubmissionLower.PhysicalDP
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts
namespace ProximityPrize.SubmissionLower.NightPhysicalPartition
open scoped Classical BigOperators
open RCN095 RCN130 RCN156 RCN167 RCN234 RCN266 RCN275
open Koala6831Moving Koala6831MovingPaid LocatorFactorAggregate LocatorBatchProductRoute LocatorPhase6800Oracle
open Koala6835.Partition
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
variable {K : Type} [Field K]
theorem actual_partition (H : MvPolynomial (Fin 4) K) (Γ : Finset K)
    (P : K→Polynomial K) (S : Finset (RegularIndex H))
    (rMax yMax tMax width : ℕ) (hw : 0<width) (one all many : Price)
    (cert : Certificate one all many rMax yMax tMax width)
    (multiple : 1<S.card)
    (pay : ∀F∈S, (regularFiber H Γ P F).card≤one (contactFlag F.1).all
       (contactFlag F.1).yz ((contactFlag F.1).zOnly/width))
    (rk : (contactFlag (regularProduct H S)).all≤rMax)
    (md : middle (contactFlag (regularProduct H S))≤yMax)
    (td : total (contactFlag (regularProduct H S))≤tMax)
    (budget : ℕ)
    (room : ∀k≤(contactFlag (regularProduct H S)).zOnly/width,
       many (contactFlag (regularProduct H S)).all (contactFlag (regularProduct H S)).yz k ≤ budget) :
    (S.biUnion (regularFiber H Γ P)).card≤budget := by
  classical
  let r (F:RegularIndex H) := (contactFlag F.1).all
  let e (F:RegularIndex H) := (contactFlag F.1).yz
  let z (F:RegularIndex H) := (contactFlag F.1).zOnly
  have geom := contactFlag_regularProduct H S
  have gr : (∑F∈S,r F)=(contactFlag (regularProduct H S)).all := by rw [geom,sumFlag_all]
  have ge : (∑F∈S,e F)=(contactFlag (regularProduct H S)).yz := by rw [geom]; rfl
  have gz : (∑F∈S,z F)=(contactFlag (regularProduct H S)).zOnly := by rw [geom]; rfl
  have mid : (∑F∈S,r F)+(∑F∈S,e F)≤yMax := by rw [gr,ge,add_comm]; exact md
  have full : (∑F∈S,r F)+(∑F∈S,e F)+(∑F∈S,z F)≤tMax := by
    rw [gr,ge,gz]; unfold total at td; omega
  have units := floor_total S z width hw
  have scaled := (Nat.le_div_iff_mul_le hw).mp units
  have est := finite_partition r e (fun i => z i/width) (fun i => (regularFiber H Γ P i).card)
    one all many rMax yMax tMax width cert S (Finset.card_pos.mp (by omega))
    (fun F _ => regularCumulativeFlag_positive H F) pay (gr ▸ rk) mid
    ((Nat.add_le_add_left scaled _).trans full)
  apply Finset.card_biUnion_le.trans ((est.2 multiple).trans ?_)
  rw [gr,ge]; exact room _ (gz ▸ units)
#print axioms actual_partition
end
end ProximityPrize.SubmissionLower.NightPhysicalPartition

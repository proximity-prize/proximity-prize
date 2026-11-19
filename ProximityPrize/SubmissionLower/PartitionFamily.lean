/- Apache-2.0. Join a verified individual-factor price and a verified multifactor
   convolution on the same selected family. -/
import ProximityPrize.SubmissionLower.PartitionReal
import ProximityPrize.SubmissionLower.Night6836GridData
import ProximityPrize.SubmissionLower.Night6836Room
namespace ProximityPrize.SubmissionLower.NightPhysicalPartition
open scoped BigOperators Classical
open RCN095 RCN130 RCN156 RCN167 RCN234 RCN266 RCN275
open Koala6831Moving Koala6831MovingPaid LocatorFactorAggregate LocatorBatchProductRoute
open Koala6835.Partition
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K]
theorem combined (H:MvPolynomial (Fin 4) K) (Γ:Finset K) (P:K→Polynomial K)
    (S:Finset (RegularIndex H)) (ne:S.Nonempty) (one all many:Price)
    (cert:Certificate one all many 18 76 9352 100)
    (charge:∀ (F:RegularIndex H), let f:=contactFlag F.1; f.all≤18 →
      f.all+f.yz≤76 → f.all+f.yz+f.zOnly≤9352 →
      (regularFiber H Γ P F).card≤one f.all f.yz (f.zOnly/100) ∧
      (f.all+f.yz+f.zOnly≤Koala6836.Room.maxTotal f.all f.yz →
       (regularFiber H Γ P F).card≤Koala6836.Room.budget f.all f.yz (f.all+f.yz+f.zOnly)))
    (room:∀r e t k:ℕ,1≤r → r≤18 → r+e≤76 → r+e≤t →
      t≤min 9352 (Koala6836.Room.maxTotal r e) → k≤(t-(r+e))/100 →
      many r e k≤Koala6836.Room.budget r e t)
    (rk:(contactFlag (regularProduct H S)).all≤18)
    (ym:middle (contactFlag (regularProduct H S))≤76)
    (tm:total (contactFlag (regularProduct H S))≤min 9352
      (Koala6836.Room.maxTotal (contactFlag (regularProduct H S)).all (contactFlag (regularProduct H S)).yz)) :
    (S.biUnion (regularFiber H Γ P)).card ≤ Koala6836.Room.budget
      (contactFlag (regularProduct H S)).all (contactFlag (regularProduct H S)).yz (total (contactFlag (regularProduct H S))) := by
  classical
  obtain ⟨mt,cell⟩ := le_min_iff.mp tm
  by_cases several:1<S.card
  · refine actual_partition H Γ P S 18 76 9352 100 (by decide) one all many cert several ?_ rk ym mt _ ?_
    · intro F hf
      have hdvd : F.1 ∣ regularProduct H S :=
        ⟨regularCofactor H S F,(regularFactor_mul_cofactor H S F hf).symm⟩
      obtain ⟨a,b,c⟩ := contactFlag_below_of_dvd (regularProduct_ne_zero H S) hdvd
      apply (charge F (a.trans rk) ?_ ?_).1
      · simpa only [middle,Nat.add_comm] using b.trans ym
      · simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using c.trans mt
    · intro k hk
      let f:=contactFlag (regularProduct H S)
      have pos:0<f.all := by
        obtain ⟨F,mem⟩ := ne
        have hdvd : F.1 ∣ regularProduct H S :=
          ⟨regularCofactor H S F,(regularFactor_mul_cofactor H S F mem).symm⟩
        exact (regularCumulativeFlag_positive H F).trans_le
          (contactFlag_below_of_dvd (regularProduct_ne_zero H S) hdvd).1
      have mid : f.all+f.yz≤76 := by change f.yz+f.all≤76 at ym; omega
      have ly : f.all+f.yz ≤ total f := by change _≤f.zOnly+f.yz+f.all; omega
      have z : total f-(f.all+f.yz)=f.zOnly := by change f.zOnly+f.yz+f.all-_=f.zOnly; omega
      apply room f.all f.yz (total f) k pos rk mid ly tm
      rw [z]; exact hk
  · obtain ⟨F,rfl⟩ := Finset.card_eq_one.mp (show S.card=1 from
      Nat.le_antisymm (Nat.le_of_not_gt several) (Finset.card_pos.mpr ne))
    simp only [regularProduct,Finset.prod_singleton,Finset.singleton_biUnion] at rk ym mt cell ⊢
    let f:=contactFlag F.1
    have mid : f.all+f.yz≤76 := by change f.yz+f.all≤76 at ym; omega
    have deg : f.all+f.yz+f.zOnly=total f := by change _=f.zOnly+f.yz+f.all; omega
    have paid := (charge F rk mid (deg.trans_le mt)).2 (deg.trans_le cell)
    change (regularFiber H Γ P F).card ≤ Koala6836.Room.budget f.all f.yz (f.all+f.yz+f.zOnly) at paid
    rw [deg] at paid
    exact paid
#print axioms combined
end
end ProximityPrize.SubmissionLower.NightPhysicalPartition

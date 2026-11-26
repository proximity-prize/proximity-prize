import ProximityPrize.SubmissionBinaryLower.B6402MissedInterpolation
import ProximityPrize.SubmissionBinaryLower.B6402LocalMoments

/-! Convert the actual extra row and column dimensions into the two
charges used in the Table 4 inequalities. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402InterpolationPrice
open B6401ContactKerD B6401QuotInterp B6402SeedCoordinates B6402PrimarySystem B6402QuotientSpace
open B6402ExceptionalSystem B6402JointMissSystem B6402RegularSystem B6402QuotientDimension
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def regularCost (J s m b : ℕ) := b*(J+s-2*m+1)+b*(b-1)
def exceptionalCost (s b : ℕ) := 2*b*(s+1)+3*b*(b-1)

private theorem sum_charge (s b : ℕ) : (∑ i ∈ Finset.range b, (s+3*i+1)*2)=exceptionalCost s b := by
  calc _ = ∑ i ∈ Finset.range b,(2*(s+1)+3*(i*2)) := Finset.sum_congr rfl (fun i _ => by ring)
       _ = _ := by
         rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,←Finset.mul_sum,
           ←Finset.sum_mul,Finset.sum_range_id_mul_two]; unfold exceptionalCost; ring

theorem bad_price (J s T H b : ℕ) (hJ : 2≤J) (hT : H≤T) :
    (∑ i : Fin b,(testBox s J T H i).card) ≤
    (∑ i : Fin b,(auxBox s J T H 2 i).card) + exceptionalCost s b*(T+1+(J+16*b+2)*H) := by
  let rate := T+1+(J+16*b+2)*H
  have h (i : Fin b) :
      (testBox s J T H i).card≤(auxBox s J T H 2 i).card + ((s+3*i.val+1)*2)*rate := by
    simp only [testBox,auxBox,card_box]
    have he := exceptional_layer (J+5*i.val) J 2 T i.val b H le_rfl (by omega) hT i.isLt.le le_rfl
    have hrate := Nat.mul_le_mul_left (s+3*i.val+1) he
    simpa only [rate,mul_add,mul_assoc] using hrate
  have hi := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin b))) => h i)
  rw [Finset.sum_add_distrib,←Finset.sum_mul] at hi
  have hsum : (∑ i : Fin b,(s+3*i.val+1)*2)=exceptionalCost s b :=
    (Fin.sum_univ_eq_sum_range (fun i => (s+3*i+1)*2) b).trans (sum_charge s b)
  rwa [hsum] at hi

theorem extra_price (R B : Type*) [Fintype R] [Fintype B] (s m b J T H : ℕ)
    (hJ : 2≤J) (hT : H≤T) (hm : 2*m≤J+s) (hb : b≤m) :
    Fintype.card (Targets R B s m b J T H) ≤ Fintype.card (Columns B s J T H b (fun _=>2))+
      Fintype.card R*(regularCost J s m b*(T+s*H+1))+
      Fintype.card B*(exceptionalCost s b*(T+1+(J+16*b+2)*H)) := by
  rw [Fintype.card_sum,Fintype.card_prod,card_tests _ _ _ _ _ hm hb]
  simp only [Fintype.card_sigma,Fintype.card_coe,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have h := Nat.mul_le_mul_left (Fintype.card B) (bad_price J s T H b hJ hT)
  rw [Nat.mul_add] at h
  unfold regularCost; omega

#print axioms extra_price
end ProximityPrize.SubmissionBinaryLower.B6402InterpolationPrice

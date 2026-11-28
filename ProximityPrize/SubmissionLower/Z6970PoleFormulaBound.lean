import ProximityPrize.SubmissionLower.Z6970PoleSteps
import ProximityPrize.SubmissionLower.Z6970PolePieces
import ProximityPrize.SubmissionLower.Z6970PoleAffineSum
import ProximityPrize.SubmissionLower.Z6970PoleAffineValue
import ProximityPrize.SubmissionLower.Z6970PoleLateValue

set_option autoImplicit false

namespace PoleAffine6970
open Finset P1_7_1 PoleSteps6970
open Research6966.HelperWindowMoments (cutOffset offset_le cutOffset_affine cutOffset_late_value)

theorem early_term (B J t : ℕ) (lo : J ≤ t) (hi : t < B) :
    offsetMoment B J t ≤ charge (B+1) (J+1) (t-J+1) := by
  let k := t-J+1
  have cut := cutOffset_affine B J t k lo hi rfl
  have charge_eq : 6*charge (B+1) (J+1) k =
      3*(B+1-k)*min k (J+1)*(2*k+1-min k (J+1)) := by
    unfold charge
    rw [show 6*((B+1-k)*(tri k - tri (k-(J+1)))) =
      3*(B+1-k)*(2*(tri k-tri (k-(J+1)))) by ring, twice_diff]
    ring
  have eq := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 6) (cut.trans charge_eq.symm)
  exact (offset_le B J t k (by dsimp [k]; omega)).trans_eq eq

theorem late_term (B J t : ℕ) (shape : 2*J ≤ B) (lo : B ≤ t) (hi : t < B+2*J) :
    offsetMoment B J t ≤ tailTerm B J (B+2*J-t) := by
  let e := B+2*J-t
  let w := min (J+1) e
  let p := (e+1)/2
  let r := p*(e+1-p)
  let d := (r-1)/w
  have cut := late_cut B J e shape (by dsimp [e];omega) (by dsimp [e];omega)
  change d ≤ J ∧ w ≤ B-d+1 at cut
  have eq := cutOffset_late_value B J t (B-d) shape lo hi (Nat.sub_le _ _) cut.2
  change cutOffset _ _ _ _ = (2*r*(B-d) + w*(B-(B-d))*(B-(B-d)+1) - r*(e-1))/2 at eq
  have hd : d ≤ B := cut.1.trans (by omega)
  rw [Nat.sub_sub_self hd] at eq
  exact (offset_le B J t (B-d) (Nat.sub_le _ _)).trans_eq eq

theorem budget_bound (B J : ℕ) (shape : 2*J ≤ B) : groupedPoleMoment B J ≤ budget B J := by
  apply whole
  have a : interval B J J (B-J) ≤ chargePrefix (B+1) (J+1) (B-J+1) := by
    have sum := span_sum (B+1) (J+1) 1 (B-J) (by omega)
    have zero : chargePrefix (B+1) (J+1) 1 = 0 := by
      rw [← charge_sum _ _ _ (by omega), sum_range_one]
      simp [charge]
    rw [zero, Nat.sub_zero, Nat.add_comm 1] at sum
    rw [← sum]
    apply sum_le_sum
    intro i hi
    have := mem_range.mp hi
    simpa only [Nat.add_sub_cancel_left, Nat.add_comm 1] using
      early_term B J (J+i) (by omega) (by omega)
  have b : interval B J B (2*J) ≤ tailSum B J (2*J) := by
    rw [← reverse_tail]
    apply sum_le_sum
    intro i hi
    have := mem_range.mp hi
    convert late_term B J (B+i) shape (by omega) (by omega) using 1 <;> congr 1 <;> omega
  rw [show B+J = (B-J)+(2*J) by omega]
  exact append a (by simpa only [Nat.add_sub_of_le (by omega : J ≤ B)] using b)

theorem certified (B J total : ℕ) (shape : 2*J ≤ B) (h : budget B J ≤ total) :
    groupedPoleMoment B J ≤ total := (budget_bound B J shape).trans h

end PoleAffine6970

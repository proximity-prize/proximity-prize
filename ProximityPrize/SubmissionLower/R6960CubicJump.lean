import ProximityPrize.SubmissionLower.R6960CubicOdd

/-! Arithmetic and the variable-degree Sylvester loss for the normalized cubic family. -/
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Lower6960.CubicJump
open Polynomial Finset CurvatureSquares ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators Polynomial

/-- The same nonzero determinant accounts for all special abscissa degrees. -/
theorem sum_losses {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd : L → ℕ) {r v : ℕ}
    (hr : 0 < r) (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z) :
    (∑ z ∈ T, (r-odd z+1)/2) ≤ (2*r-1)*v := by
  have each (z) (hz : z ∈ T) : (r-odd z+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,a,eq,da⟩ := fact z hz
    have fit : (h^2*a).natDegree ≤ r := by rw [←eq]; exact natDegree_map_le.trans height
    rw [←derivative_map,eq]
    exact CurvatureSquares.cofactor_corank (L:=L) (r:=r) (e:=odd z) h a hr da fit
  have bound := Finset.sum_le_sum each
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have fee := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed
    (fun j => by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial L))+1)=C ((j:L)+1) by simp]
      exact (natDegree_C_mul_le ..).trans (seed _))
  calc _ ≤ _ := (bound.trans upper).trans fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega

/-- Price the good seeds from a global splitting-jump bound and the actual
Sylvester determinant. The geometric splitting-jump estimate is an input. -/
theorem marked_price {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd jump : L → ℕ) {r q s m v : ℕ}
    (large : 812 ≤ r) (thin : 1600*q ≤ r) (ramification : 2*s ≤ r+2*q+2) (weight : m ≤ 140915)
    (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ 4*v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z)
    (fibre : ∀ z ∈ T, odd z ≤ 2*(jump z + (2*s)/3))
    (global : (∑ z ∈ T, jump z) ≤ (6*m+s)*v) : T.card ≤ 6495*v := by
  let losses := fun z => (r-odd z+1)/2
  have det : (∑ z ∈ T, losses z) ≤ (2*r-1)*(4*v) :=
    sum_losses Q T odd (by omega) height seed sep fact
  let debit := 3*r-4*s
  have pos : 0 < debit := by dsimp [debit]; omega
  have local_bound (z) (mem : z ∈ T) : debit ≤ 6*(jump z+losses z) := by
    have := fibre z mem
    dsimp [debit,losses]
    omega
  have total := Finset.sum_le_sum local_bound
  simp only [sum_const,nsmul_eq_mul,←Finset.mul_sum,Finset.sum_add_distrib] at total
  have rate : 6*((6*m+s)+4*(2*r-1)) ≤ 6495*debit := by dsimp [debit]; omega
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc T.card*debit ≤ 6*((∑ z ∈ T, jump z)+(∑ z ∈ T, losses z)) := total
       _ ≤ 6*((6*m+s)*v+(2*r-1)*(4*v)) := Nat.mul_le_mul_left _ (Nat.add_le_add global det)
       _ = (6*((6*m+s)+4*(2*r-1)))*v := by ring
       _ ≤ (6495*debit)*v := Nat.mul_le_mul_right v rate
       _ = _ := by ring

/-- The tame-branch, active-root and splitting-change inequalities cover the plane. -/
theorem partition (r q : ℕ) :
    8*(r+q)+5 ≤ 6500 ∨ (0<q ∧ 4*r ≤ 6477*q) ∨ (812≤r ∧ 1600*q≤r) := by omega

#print axioms partition
#print axioms sum_losses
#print axioms marked_price
end Lower6960.CubicJump

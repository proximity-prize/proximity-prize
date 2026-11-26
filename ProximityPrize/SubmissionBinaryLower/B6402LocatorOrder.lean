import ProximityPrize.SubmissionBinaryLower.B6402LocatorDivision

namespace ProximityPrize.SubmissionBinaryLower.B6402LocatorOrder
open Polynomial B6401ContactKerD B6401ResLineOrd B6402LocatorDivision P64LineOrder
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I : Type*} [Field K] [CharP K 2] [DecidableEq I]

theorem fibre_ord (a x : K) (y : K[X]) : lineOrd (fibre a) x y ≤ (if a=x then 1 else 0) := by
  by_cases h : a=x
  · subst a; rw [if_pos rfl]
    by_contra bad
    have hz := (ordGE_iff (fibre_ne x) x y 2).mpr (by omega) 1 0 (by decide)
    change (((lineShiftHom x y (fibre x)).coeff 0).coeff 1)=0 at hz
    have he : lineShiftHom x y (fibre x)=C (Polynomial.X : Polynomial (Polynomial K)) := by
      unfold fibre
      rw [map_sub,map_sub,lineShiftHom_CX,lineShiftHom_CC,←map_sub,add_sub_cancel_right]
    simp [he] at hz
  · rw [if_neg h]
    have ne : evalXAt (fibre a) x ≠ 0 := by
      have hx : x-a≠0 := sub_ne_zero.mpr (Ne.symm h)
      simpa [fibre,evalXAt,←map_sub] using hx
    exact (lineOrd_le_natDegree x y ne).trans_eq (natDegree_C _)

theorem ord_le (x : I ↪ K) (S : Finset I) (b : ℕ) (i : I) (y : K[X]) :
    lineOrd (locator x S b) (x i) y ≤ if i∈S then 2*b else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := lineOrd_pow (fibre_ne (x i)) (x i) y 0
    simpa [locator,h] using le_of_eq h
  | insert j S hj ih =>
    have hp : locator x (insert j S) b=fibre (x j)^(2*b)*locator x S b := by simp [locator,hj]
    rw [hp,lineOrd_mul (pow_ne_zero _ (fibre_ne _)) (loc_ne x S b),lineOrd_pow (fibre_ne _)]
    have h := fibre_ord (x j) (x i) y
    by_cases hji : j=i
    · subst j
      simp only [ite_true] at h
      simp only [hj,ite_false] at ih
      rw [if_pos (Finset.mem_insert_self _ _)]
      have hh := Nat.mul_le_mul_left (2*b) h
      omega
    · have hne := x.injective.ne hji
      rw [if_neg hne] at h
      rw [show lineOrd (fibre (x j)) (x i) y=0 by omega,Nat.mul_zero,Nat.zero_add]
      simpa [Finset.mem_insert,Ne.symm hji] using ih

theorem residual_line (x : I ↪ K) (S : Finset I) (b : ℕ) (i : I) (y : K[X])
    (p r : BiPoly (Polynomial K)) (hr : r≠0) (eq : p=locator x S b*r) :
    lineOrd p (x i) y ≤ (if i∈S then 2*b else 0)+lineOrd r (x i) y := by
  rw [eq,lineOrd_mul (loc_ne x S b) hr]
  exact Nat.add_le_add_right (ord_le x S b i y) _

#print axioms residual_line
end ProximityPrize.SubmissionBinaryLower.B6402LocatorOrder

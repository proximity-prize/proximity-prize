import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ArkLib.Data.Polynomial.ResultantDegree

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2200000

namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open K1_14 (L)
open scoped Polynomial BigOperators

private theorem resultant_weighted_add_le {R : Type*} [CommRing R]
    (P Q : Polynomial (Polynomial R)) (m n a b d : ℕ)
    (hp : ∀ i≤m, (P.coeff i).natDegree+d*i≤a)
    (hq : ∀ i≤n, (Q.coeff i).natDegree+d*i≤b) :
    (resultant P Q m n).natDegree+d*(m*n)≤n*a+m*b := by
  classical
  let M := sylvester P Q m n
  let w : Fin (m+n) → ℕ := Fin.addCases (fun j : Fin m => b+d*j.val)
    (fun j : Fin n => a+d*j.val)
  have entry (σ : Equiv.Perm (Fin (m+n))) (i : Fin (m+n)) (ne : M (σ i) i≠0) :
      (M (σ i) i).natDegree+d*(σ i).val≤w i := by
    cases i using Fin.addCases with
    | left j =>
      have eq : M (σ (j.castAdd n)) (j.castAdd n) =
          if (σ (j.castAdd n)).val ∈ Set.Icc j.val (j.val+n) then
            Q.coeff ((σ (j.castAdd n)).val-j.val) else 0 := by simp [M,sylvester]
      rw [eq] at ne ⊢
      split_ifs at ne ⊢ with h
      · have low : j.val≤(σ (j.castAdd n)).val := h.1
        have small : (σ (j.castAdd n)).val-j.val≤n := by have := h.2; omega
        have c := hq _ small
        have step : d*((σ (j.castAdd n)).val-j.val)+d*j.val=d*(σ (j.castAdd n)).val := by
          rw [← Nat.mul_add,Nat.sub_add_cancel low]
        simp only [w,Fin.addCases_left]
        omega
      · exact (ne rfl).elim
    | right j =>
      have eq : M (σ (j.natAdd m)) (j.natAdd m) =
          if (σ (j.natAdd m)).val ∈ Set.Icc j.val (j.val+m) then
            P.coeff ((σ (j.natAdd m)).val-j.val) else 0 := by simp [M,sylvester]
      rw [eq] at ne ⊢
      split_ifs at ne ⊢ with h
      · have low : j.val≤(σ (j.natAdd m)).val := h.1
        have small : (σ (j.natAdd m)).val-j.val≤m := by have := h.2; omega
        have c := hp _ small
        have step : d*((σ (j.natAdd m)).val-j.val)+d*j.val=d*(σ (j.natAdd m)).val := by
          rw [← Nat.mul_add,Nat.sub_add_cancel low]
        simp only [w,Fin.addCases_right]
        omega
      · exact (ne rfl).elim
  let s := (∑ j : Fin m, d*j.val) + ∑ j : Fin n, d*j.val
  have ws : ∑ i,w i = n*a+m*b+s := by
    simp only [w,s,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Finset.sum_add_distrib,
      Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  have pos : d*(m*n)≤n*a+m*b := by
    have h : d*m≤a := (Nat.le_add_left ..).trans (hp m le_rfl)
    calc
      _ = (d*m)*n := by ring
      _ ≤ a*n := Nat.mul_le_mul_right n h
      _ ≤ _ := by rw [Nat.mul_comm a n]; exact Nat.le_add_right ..
  have idx : (∑ i : Fin (m+n), d*i.val)=d*(m*n)+s := by
    simp only [s,Fin.sum_univ_add,Fin.val_castAdd,Fin.val_natAdd,Nat.mul_add,
      Finset.sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  have terms (σ : Equiv.Perm (Fin (m+n))) :
      (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree≤n*a+m*b-d*(m*n) := by
    apply (Polynomial.natDegree_smul_le _ _).trans
    by_cases exists_zero : ∃ i, M (σ i) i=0
    · obtain ⟨i,h⟩ := exists_zero
      have zero : (∏ j : Fin (m+n), M (σ j) j)=0 :=
        Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) h
      rw [zero,natDegree_zero]
      exact Nat.zero_le _
    · push Not at exists_zero
      have bound := natDegree_prod_le Finset.univ (fun i=>M (σ i) i)
      have sum : (∑ i, ((M (σ i) i).natDegree+d*(σ i).val))≤∑ i,w i :=
        Finset.sum_le_sum (fun i _ => entry σ i (exists_zero i))
      have perm : (∑ i, d*(σ i).val) = ∑ i : Fin (m+n), d*i.val :=
        Equiv.sum_comp σ (fun i=>d*i.val)
      rw [Finset.sum_add_distrib,perm,ws,idx] at sum
      omega
  have det := natDegree_sum_le_of_forall_le (Finset.univ : Finset (Equiv.Perm (Fin (m+n)))) _
    (fun σ _ => terms σ)
  rw [← Matrix.det_apply] at det
  change M.det.natDegree+d*(m*n)≤_
  omega

theorem derivative_weighted_add_le {R : Type*} [CommRing R]
    (P : Polynomial (Polynomial R)) (e H d : ℕ) (he : 0<e)
    (cap : ∀ i≤e,(P.coeff i).natDegree+d*i≤H) :
    (P.resultant P.derivative e (e-1)).natDegree+d*e^2≤(2*e-1)*H := by
  have dh : d≤H := by have h := cap 1 he; simp at h; omega
  have der (i : ℕ) (hi : i≤e-1) :
      (P.derivative.coeff i).natDegree+d*i≤H-d := by
    have h := cap (i+1) (by omega)
    rw [Nat.mul_add,Nat.mul_one] at h
    have q := Polynomial.coeff_derivative_natDegree_le P i
    omega
  have bound := resultant_weighted_add_le P P.derivative e (e-1) H (H-d) d cap der
  have sum : (e-1)*H+e*(H-d)+e*d=(2*e-1)*H := by
    rw [add_assoc,← Nat.mul_add e (H-d) d,Nat.sub_add_cancel dh,← add_mul]
    have same : e-1+e=2*e-1 := by omega
    rw [same]
  have quad : d*(e*(e-1))+e*d=d*e^2 := by
    have delta : e-1+1=e := Nat.sub_add_cancel he
    calc
      _ = d*e*(e-1+1) := by ring
      _ = _ := by rw [delta]; ring
  have h := Nat.add_le_add_right bound (e*d)
  rw [sum,add_assoc,quad] at h
  exact h

/-- The padded derivative resultant satisfies the doubled tame-abscissa
degree bound, including the separate contribution at infinity. -/
theorem derivative_resultant_tame (f : Curve (Polynomial L)) (d : ℕ)
    (lo : 2≤f.degreeOf ordinate) (hi : f.degreeOf ordinate≤47) (degree : d≤164670)
    (bounded : height d f≤heightCap (f.degreeOf ordinate) d) :
    2*((view f).resultant (view f).derivative (f.degreeOf ordinate)
      (f.degreeOf ordinate-1)).natDegree+2*(f.degreeOf ordinate-1)<2130706433 := by
  let e := f.degreeOf ordinate
  let P := view f
  have caps (i : ℕ) (hi : i≤e) : (P.coeff i).natDegree+d*i≤(2*e-1)*d := by
    by_cases nz : P.coeff i=0
    · rw [nz,natDegree_zero,zero_add,mul_comm d i]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f d i nz).trans bounded
  have bound := derivative_weighted_add_le P e ((2*e-1)*d) d (by omega) caps
  have compensation : (2*e-1)*((2*e-1)*d)=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 1≤e from by omega)
    rw [hk, show 2*(1+k)-1=2*k+1 by omega, show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  rw [compensation] at bound
  have R : (P.resultant P.derivative e (e-1)).natDegree≤(3*e-1)*(e-1)*d := by omega
  have numerics : 2*((3*e-1)*(e-1)*d)+2*(e-1)<2130706433 := by
    apply LT.lt.trans_le' _ (Nat.add_le_add
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 hi) 1) (Nat.sub_le_sub_right hi 1)) degree))
      (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hi 1)))
    decide +kernel
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 R) _).trans_lt numerics

theorem derivative_resultant_nonzero (f : Curve (Polynomial L)) (ir : Irreducible f)
    (pos : 0<f.degreeOf ordinate) (small : f.degreeOf ordinate<K1.p) :
    (view f).resultant (view f).derivative (f.degreeOf ordinate)
      (f.degreeOf ordinate-1)≠0 := by
  let P := view f
  have ip : Irreducible P := (MulEquiv.irreducible_iff view).mpr ir
  have dP : P.natDegree=f.degreeOf ordinate := view_y f
  have ne : ((P.natDegree : ℕ) : Polynomial (Polynomial L)) ≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff (Polynomial (Polynomial L)) K1.p P.natDegree).mp zero
    exact (Nat.ne_of_gt (dP.symm ▸ pos)) (Nat.eq_zero_of_dvd_of_lt dvd (dP.symm ▸ small))
  have der : P.derivative≠0 := by
    intro zero
    have base : P.natDegree-1+1=P.natDegree := Nat.sub_add_cancel (dP.symm ▸ pos)
    have h := congrArg (fun Q => Q.coeff (P.natDegree-1)) zero
    rw [coeff_derivative,← Nat.cast_add_one,base,coeff_natDegree,coeff_zero] at h
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr ip.ne_zero) ne h
  have result := Polynomial.resultant_derivative_ne_zero_of_irreducible P ip der
  rwa [dP] at result

#print axioms derivative_resultant_nonzero
#print axioms derivative_resultant_tame
end
end Lower6960.RetainedCompression

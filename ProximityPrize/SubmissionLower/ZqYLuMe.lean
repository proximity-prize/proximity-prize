import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.ZcHSdRd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qO4AyGb
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open P5_7_7 (Dg)
open private other other_degree reflect_partials from ProximityPrize.SubmissionLower.ZN2gA7a
private def DU (f :L[X][X]) :L[X][X] :=
 f.sum fun j b=>Polynomial.monomial j b.derivative
theorem physicalDerivative_coeff (f :Dg) (i:ℕ) :
   (physicalDerivative f).coeff i=DU (f.coeff i) := by
 classical
 rw [physicalDerivative,coeff_sum,sum_def]
 simp only [coeff_monomial,Finset.sum_ite_eq']
 split_ifs with h
 · rfl
 · rw [notMem_support_iff.mp h]
   simp [DU]
theorem a7C (J:Input) :
   polar J true = -(jU J true^(J.l-2)*polar J false) ∧
     jet J true = -(jU J true^2*jet J false) := by
 let m:=J.l-1
 have h₂:=J.Ca.two_le
 have hm:m+1=J.l:= by omega
 have hF:J.F.natDegree=m+1 :=J.Ca.jU.trans hm.symm
 let y :=jU J false
 let q:=jU J true
 have hq:q=y⁻¹:=rfl
 have hy :y≠0:=ordinate_false_ne_zero J
 have hq₀:q≠0:=hq ▸ inv_ne_zero hy
 have hyq:y*q=1 :=hq ▸ mul_inv_cancel₀ hy
 let _:=invertibleOfNonzero hy
 have c7J (f :Dg) (n:ℕ) (hf :f.natDegree≤n) :
     KM J true (f.reflect n)=KM J false f*q^n:= by
   have h:=eval₂_reflect_mul_pow ((a7W J).comp Polynomial.C) y n f hf
   rw [invOf_eq_inv,← hq] at h
   have he :KM J true (f.reflect n)*y^n=KM J false f :=h
   calc
     _=KM J false f/y^n:=(eq_div_iff (pow_ne_zero _ hy)).mpr he
     _ = _:= by rw [div_eq_mul_inv,← inv_pow,← hq]
 have hroot :KM J false J.F=0:=chart_root J false
 have hOther :KM J false (other J.l J.F) = -(y*polar J false) := by
   change KM J false (Polynomial.C (J.l:L[X][X])*J.F -
     Polynomial.X*J.F.derivative) = -(jU J false*KM J false J.F.derivative)
   rw [map_sub (KM J false),map_mul (KM J false),
     map_mul (KM J false),hroot,mul_zero,zero_sub,chartEval_X]
 have hp:polar J true = -(q^(J.l-2)*polar J false) := by
   have h:=(reflect_partials J.F m hF).1
   change KM J true J.F.reverse.derivative= _
   rw [← h,c7J _ _ (other_degree J.F m hF.le),hm,hOther,neg_mul]
   congr 1
   have he :y*q^m=q^(J.l-2) := by
     rw [show m=(J.l-2)+1 by omega,pow_succ',← mul_assoc,hyq,one_mul]
   rw [mul_comm y,mul_assoc,he,mul_comm]
 have hd: (physicalDerivative J.F).natDegree≤J.l:= by
   apply natDegree_le_iff_coeff_eq_zero.mpr
   intro i hi
   rw [physicalDerivative_coeff,coeff_eq_zero_of_natDegree_lt (J.Ca.jU ▸ hi)]
   simp [DU]
 have hr :physicalDerivative J.F.reverse=(physicalDerivative J.F).reflect J.l:= by
   ext i:1
   rw [physicalDerivative_coeff,coeff_reverse,coeff_reflect,physicalDerivative_coeff,
     J.Ca.jU]
 have hX:KM J true (physicalDerivative J.F.reverse) =
     KM J false (physicalDerivative J.F)*q^J.l:= by
   rw [hr,c7J _ _ hd]
 refine ⟨hp,?_⟩
 change -(KM J true (physicalDerivative J.F.reverse))/polar J true =
   -(q^2*(-(KM J false (physicalDerivative J.F))/polar J false))
 rw [hX,hp,show q^J.l=q^(J.l-2)*q^2 by rw [← pow_add,Nat.sub_add_cancel h₂]]
 field_simp [polar_false_ne_zero J,hq₀]
theorem gauge_mul_reciprocal (J:Input) (τ:L) :
  gauge J τ*jU J true=jU J true+constant J τ:= by
 change (1+constant J τ*jU J false)*(jU J false)⁻¹= _
 rw [add_mul,one_mul,mul_assoc,mul_inv_cancel₀ (ordinate_false_ne_zero J),mul_one]
 rfl
end
end qO4AyGb

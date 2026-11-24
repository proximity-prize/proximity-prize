import ProximityPrize.SubmissionLower.A8
import ProximityPrize.SubmissionLower.AJ
import ProximityPrize.SubmissionLower.AZ
import ProximityPrize.SubmissionLower.C0
set_option Elab.async false
set_option autoImplicit true
section
namespace ai4
open bu MvPolynomial
open oT (Interpolant)
open private cU vT from ProximityPrize.SubmissionLower.C0
noncomputable section
private theorem ajh (n i:ℕ) : (n.descFactorial i:Ground)=cU i (n:Ground) := by
 by_cases hi:i≤n
 · rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod,cU]
   exact Finset.prod_congr rfl fun j hj=>Nat.cast_sub (by have :=Finset.mem_range.mp hj; omega)
 · have hlt:n< i:= by omega
   rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt,Nat.cast_zero,vT hlt]
private theorem Nm (φ:Interpolant →ₐ[Ground] Ground) (i:ℕ) (Q:Interpolant) :
 φ (cU i Q)=cU i (φ Q) := by simp [cU]
end
end ai4
end

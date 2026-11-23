import Mathlib.Algebra.Polynomial.Sequence
import ProximityPrize.SubmissionLower.BW
set_option Elab.async false
set_option autoImplicit true
section
namespace Kk
open bu MvPolynomial










noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bgG {P:Polynomial Ground} (h:P.natDegree≤1) (n:ℕ) :
   (P^n).reflect n=P.reflect 1^n:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [pow_succ,Polynomial.reflect_mul _ _ (by simpa using Polynomial.natDegree_pow_le_of_le n h) h,
     ih,pow_succ]
private theorem fVl (s u k :ℕ) (hk :k≤ s+u) :
   let Q:Polynomial Ground :=(1+Polynomial.X)^s*(1-Polynomial.X)^u
   Q.coeff k=(-1 :Ground)^u*Q.coeff (s+u-k) := by
 let P:Polynomial Ground :=1+Polynomial.X
 let R:Polynomial Ground :=1-Polynomial.X
 have hp:P.natDegree≤1 :=(Polynomial.natDegree_add_le _ _).trans (by simp)
 have hr :R.natDegree≤1 :=(Polynomial.natDegree_sub_le _ _).trans (by simp)
 have hP:P.reflect 1=P:= by simp [P,add_comm]
 have hR:R.reflect 1 = -R:= by simp [R,neg_sub]
 have he : (P^s*R^u).reflect (s+u)=Polynomial.C ((-1 :Ground)^u)*(P^s*R^u) := by
   rw [Polynomial.reflect_mul _ _ (by simpa using Polynomial.natDegree_pow_le_of_le s hp)
     (by simpa using Polynomial.natDegree_pow_le_of_le u hr),bgG hp,bgG hr,
     hP,hR,neg_eq_neg_one_mul,mul_pow,map_pow,map_neg,map_one]
   ring
 have hh:=congrArg (fun Q:Polynomial Ground=>Q.coeff (s+u-k)) he
 rw [Polynomial.coeff_reflect,Polynomial.revAt_le (Nat.sub_le ..),
   show s+u-(s+u-k)=k by omega,Polynomial.coeff_C_mul] at hh
 exact hh
end
end Kk
end

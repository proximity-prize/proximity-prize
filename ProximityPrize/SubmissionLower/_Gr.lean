import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.HE
namespace ProximityPrize.SubmissionLower.DifferentialTaylorCoefficients
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Derivation
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem leibniz_product (D:Derivation K A A) (a b:A):
   D (a*b)=D a*b+a*D b:=by
 calc
   D (a*b)=a*D b+b*D a:=by
     simpa only [smul_eq_mul] using D.leibniz a b
   _=D a*b+a*D b:=by ac_rfl
theorem iterate_zero (D:Derivation K A A) (n:ℕ):D^[n] (0:A)=0:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih]
theorem iterate_add (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a+b)=D^[n] a+D^[n] b:=by
 induction n with
 | zero => rfl
 | succ n ih => simp [Function.iterate_succ_apply',ih,map_add]
theorem iterate_one_of_ne_zero (D:Derivation K A A) (n:ℕ) (hn:n≠0):
   D^[n] (1:A)=0:=by
 cases n with
 | zero => exact (hn rfl).elim
 | succ n =>
   rw [Function.iterate_succ_apply,D.map_one_eq_zero]
   exact iterate_zero D n
theorem iterate_product (D:Derivation K A A) (n:ℕ) (a b:A):
   D^[n] (a*b)=
     ∑ ij∈antidiagonal n,
       n.choose ij.1 • (D^[ij.1] a*D^[ij.2] b):=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [sum_antidiagonal_choose_succ_nsmul (M:=A)
     (fun i j => D^[i] a*D^[j] b) n]
   simp only [Function.iterate_succ_apply',ih,map_sum,map_nsmul,
     leibniz_product,smul_add,sum_add_distrib]
   rw [add_comm,add_right_inj]
   refine sum_congr rfl fun ⟨i,j⟩ hij => ?_
   rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
end Derivation
section NormalizedCoefficients
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem factorial_cast_ne_zero_below_characteristic
   (p:ℕ) [CharP L p]:∀ n:ℕ,n < p → (n.factorial:L)≠0:=by
 intro n
 induction n with
 | zero =>
   intro hn
   simp
 | succ n ih =>
   intro hn
   have hcast:((n+1:ℕ):L)≠0:=by
     intro hz
     have hdiv:p∣n+1:=(CharP.cast_eq_zero_iff L p (n+1)).mp hz
     exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) hdiv)
   rw [Nat.factorial_succ,Nat.cast_mul]
   exact mul_ne_zero hcast (ih (by omega))
noncomputable def jetCoefficient
   (D:Derivation K A A) (value:A →+*L) (a:A) (n:ℕ):L:=
 value (D^[n] a)/(n.factorial:L)
theorem factorial_term_product
   (n i j:ℕ) (hij:i+j=n) (x y:L)
   (hn:(n.factorial:L)≠0)
   (hi:(i.factorial:L)≠0)
   (hj:(j.factorial:L)≠0):
   (n.choose i:L)*(x*y)/(n.factorial:L)=
     (x/(i.factorial:L))*(y/(j.factorial:L)):=by
 have hle:i ≤ n:=by omega
 have hsub:n-i=j:=by omega
 have hnat:=Nat.choose_mul_factorial_mul_factorial hle
 rw [hsub] at hnat
 have hcast:(n.choose i:L)*(i.factorial:L)*(j.factorial:L)=
     (n.factorial:L):=by
   simpa only [Nat.cast_mul] using congrArg (fun k:ℕ => (k:L)) hnat
 field_simp
 linear_combination (x*y)*hcast
theorem jetCoefficient_zero (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 0 n=0:=by
 simp [jetCoefficient,iterate_zero]
theorem jetCoefficient_one (D:Derivation K A A) (value:A →+*L) (n:ℕ):
   jetCoefficient D value 1 n=if n=0 then 1 else 0:=by
 by_cases hn:n=0
 · subst n
   simp [jetCoefficient]
 · simp [jetCoefficient,iterate_one_of_ne_zero D n hn,hn]
theorem jetCoefficient_add
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ):
   jetCoefficient D value (a+b) n=
     jetCoefficient D value a n+jetCoefficient D value b n:=by
 simp only [jetCoefficient,iterate_add,map_add,add_div]
theorem jetCoefficient_product
   (D:Derivation K A A) (value:A →+*L) (a b:A) (n:ℕ)
   (hfactorial:∀ i ≤ n,(i.factorial:L)≠0):
   jetCoefficient D value (a*b) n=
     ∑ ij∈antidiagonal n,
       jetCoefficient D value a ij.1*jetCoefficient D value b ij.2:=by
 unfold jetCoefficient
 rw [iterate_product,map_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=n:=mem_antidiagonal.mp hij
 have hi:ij.1 ≤ n:=by omega
 have hj:ij.2 ≤ n:=by omega
 rw [map_nsmul,nsmul_eq_mul,map_mul]
 exact factorial_term_product n ij.1 ij.2 hsum
   (value (D^[ij.1] a)) (value (D^[ij.2] b))
   (hfactorial n le_rfl) (hfactorial ij.1 hi) (hfactorial ij.2 hj)
noncomputable def jetPolynomial
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A):Polynomial L:=
 ∑ j∈range bound,Polynomial.monomial j (jetCoefficient D value a j)
theorem jetPolynomial_coeff
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a:A) (j:ℕ):
   (jetPolynomial D value bound a).coeff j=
     if j < bound then jetCoefficient D value a j else 0:=by
 classical
 simp [jetPolynomial,Polynomial.coeff_monomial]
theorem jetPolynomial_zero
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ):
   jetPolynomial D value bound 0=0:=by
 ext j
 simp [jetPolynomial_coeff,jetCoefficient_zero]
theorem jetPolynomial_one
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (hbound:0 < bound):
   jetPolynomial D value bound 1=1:=by
 ext j
 by_cases hj:j=0
 · subst j
   simp [jetPolynomial_coeff,jetCoefficient_one,hbound]
 · simp [jetPolynomial_coeff,jetCoefficient_one,hj,Polynomial.coeff_one]
theorem jetPolynomial_add
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A):
   jetPolynomial D value bound (a+b)=
     jetPolynomial D value bound a+jetPolynomial D value bound b:=by
 ext j
 by_cases hj:j < bound <;>
   simp [jetPolynomial_coeff,jetCoefficient_add,hj]
theorem X_pow_dvd_jetPolynomial_product_error
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ) (a b:A)
   (hfactorial:∀ j < bound,(j.factorial:L)≠0):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 rw [Polynomial.X_pow_dvd_iff]
 intro j hj
 rw [Polynomial.coeff_sub]
 apply sub_eq_zero.mpr
 rw [jetPolynomial_coeff,if_pos hj,Polynomial.coeff_mul,
   jetCoefficient_product D value a b j (fun k hk =>
     hfactorial k (lt_of_le_of_lt hk hj))]
 apply Finset.sum_congr rfl
 intro ij hij
 have hsum:ij.1+ij.2=j:=mem_antidiagonal.mp hij
 have hi:ij.1 < bound:=by omega
 have hk:ij.2 < bound:=by omega
 rw [jetPolynomial_coeff,if_pos hi,jetPolynomial_coeff,if_pos hk]
theorem X_pow_dvd_jetPolynomial_product_error_of_char
   (D:Derivation K A A) (value:A →+*L) (p bound:ℕ) [CharP L p]
   (hbound:bound ≤ p) (a b:A):
   (Polynomial.X:Polynomial L)^bound∣
     jetPolynomial D value bound (a*b)-
       jetPolynomial D value bound a*jetPolynomial D value bound b:=by
 apply X_pow_dvd_jetPolynomial_product_error
 intro j hj
 exact factorial_cast_ne_zero_below_characteristic p j (lt_of_lt_of_le hj hbound)
end NormalizedCoefficients
end ProximityPrize.SubmissionLower.DifferentialTaylorCoefficients

import ProximityPrize.SubmissionLower.A6
namespace ProximityPrize.SubmissionLower.ContactBaseIdealAgreement6676Research
open ContactDifferentialRing ContactTaylorNumerators
open ContactBaseIdealAlgebra6676Research ContactBaseIdealCoefficients6676Research
noncomputable section
variable {K:Type*} [Field K]
def agreementLow (c:ℕ → K) (x u₀ u₁:K):Poly4 K:=
 MvPolynomial.C (c 0)*MvPolynomial.X (1:Fin 4)+
   MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))-affineSeedPolynomial u₀ u₁
def agreementHighCoefficient (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x:K)
   (n j:ℕ):Poly4 K:=
 MvPolynomial.C (c (n+2))*polyH K F^(d-(n+2)+3)*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2)
def agreementCoefficients (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (j:ℕ):Poly4 K:=
 (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0)+
   ∑ n∈Finset.range (d-1),agreementHighCoefficient F d c x n j
theorem agreementNumerator_eq_low_add_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=polyH K F^(2*d)*agreementLow c x u₀ u₁+
     ∑ n∈Finset.range (d-1),commonNumeratorTerm F d c x (n+2):=by
 have hpow:polyH K F^2*polyH K F^(2*(d-1))=polyH K F^(2*d):=by
   rw [←pow_add,show 2+2*(d-1)=2*d by omega]
 unfold agreementNumerator clearedTaylorNumerator
 rw [show d+1=2+(d-1) by omega,Finset.sum_range_add]
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,
   show ∀ n:ℕ,2+n=n+2 from fun n => Nat.add_comm 2 n]
 simp only [commonNumeratorTerm,numerator_one,numerator_zero,Nat.sub_zero,
   pow_zero,mul_one,pow_one]
 unfold agreementLow
 linear_combination (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4)))*hpow
theorem highCoefficient_monomial (F:Poly4 K) (d n j:ℕ)
   (hn:n+2 ≤ d) (hj:j ≤ n+1) (c:ℕ → K) (x:K):
   baseMonomial F (d-1) j (agreementHighCoefficient F d c x n j)=
     MvPolynomial.C (c (n+2))*polyH K F^3*
       (polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j)*
         polyH K F^(2*(d-(n+2)))*
           (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2):=by
 have hp:polyH K F^(d-1-j)*polyH K F^(d-(n+2)+3)=
     polyH K F^3*polyH K F^(n+1-j)*polyH K F^(2*(d-(n+2))):=by
   simp only [←pow_add]
   congr 1
   omega
 unfold baseMonomial agreementHighCoefficient
 linear_combination (MvPolynomial.C (c (n+2))*polyG K F^j*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2))*hp
theorem commonNumeratorTerm_eq_coefficient_sum (F:Poly4 K) (d n:ℕ)
   (hn:n+2 ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x (n+2)=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
 have hs:(∑ j∈Finset.range (n+2),baseMonomial F (d-1) j
     (agreementHighCoefficient F d c x n j))=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
   apply Finset.sum_subset (Finset.range_mono hn)
   intro j _ hj
   have hz:=baseCoefficients_zero F n j (by simp only [Finset.mem_range] at hj;omega)
   simp only [baseMonomial,agreementHighCoefficient,hz,mul_zero,zero_mul]
 rw [←hs]
 unfold commonNumeratorTerm
 rw [numerator_eq_coefficient_sum]
 simp only [Finset.mul_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro j hj
 simpa only [mul_assoc] using (highCoefficient_monomial F d n j hn
   (by have:=Finset.mem_range.mp hj;omega) c x).symm
theorem agreementNumerator_eq_coefficient_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=
     ∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
       agreementCoefficients F d c x u₀ u₁ j:=by
 rw [agreementNumerator_eq_low_add_sum F d hd c x u₀ u₁]
 have hlo:(∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
     (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0))=
     polyH K F^(2*d)*agreementLow c x u₀ u₁:=by
   rw [Finset.sum_eq_single 0]
   · simp only [Nat.sub_zero,pow_zero,mul_one,if_true]
     rw [←mul_assoc, ←pow_add,show d-1+(d+1)=2*d by omega]
   · intro j _ hj
     simp only [if_neg hj,mul_zero]
   · intro hj
     exact (hj (Finset.mem_range.mpr (by omega))).elim
 simp only [agreementCoefficients,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
 rw [hlo,Finset.sum_comm]
 apply congrArg (fun P:Poly4 K => polyH K F^(2*d)*agreementLow c x u₀ u₁+P)
 apply Finset.sum_congr rfl
 intro n hn
 exact commonNumeratorTerm_eq_coefficient_sum F d n
   (by have:=Finset.mem_range.mp hn;omega) c x
end
end ProximityPrize.SubmissionLower.ContactBaseIdealAgreement6676Research

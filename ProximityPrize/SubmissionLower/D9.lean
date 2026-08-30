import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A4
import ProximityPrize.SubmissionLower.BJ
namespace ProximityPrize.SubmissionLower.ContactPolynomialSolutions
open ContactDifferentialRing ContactRegularPoint ContactPolynomiality
open ContactTaylorNumerators ContactAgreementEvaluation
open ContactTranslation DifferentialTaylorCoefficients
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section PolynomialIdentities
variable (K:Type*) [Field K]
theorem derivative_specialization (P:Polynomial K) (γ:K) (Q:Poly4 K):
   (specialization K P γ Q).derivative=
     specialization K P γ (MvPolynomial.pderiv (0:Fin 4) Q)+
     P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) Q)+
     P.derivative.derivative*
       specialization K P γ (MvPolynomial.pderiv (2:Fin 4) Q):=by
 induction Q using MvPolynomial.induction_on with
 | C a => simp [specialization]
 | add Q S hQ hS =>
     simp only [map_add,hQ,hS]
     ring
 | mul_X Q i hQ =>
     simp only [MvPolynomial.pderiv_mul,map_add,map_mul,
       Polynomial.derivative_mul,hQ]
     fin_cases i <;> simp [specialization] <;> ring
theorem solution_slope_identity (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (polyH K F)*P.derivative.derivative=
     specialization K P γ (polyG K F):=by
 have hchain:=derivative_specialization K P γ F
 rw [hsolution,Polynomial.derivative_zero] at hchain
 have hG:specialization K P γ (polyG K F)=
     -(specialization K P γ (MvPolynomial.pderiv (0:Fin 4) F)+
       P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) F)):=by
   simp [polyG,specialization]
 rw [hG]
 change specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)*
     P.derivative.derivative=_
 linear_combination-hchain
theorem specialization_numeratorStep
   (F M:Poly4 K) (P:Polynomial K) (γ:K) (b:ℕ)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (numeratorStep K F b M)=
     specialization K P γ (polyH K F)^2*
       (specialization K P γ M).derivative-
     (2*b:Polynomial K)*specialization K P γ M*
       specialization K P γ (polyH K F)*
       (specialization K P γ (polyH K F)).derivative:=by
 simp only [numeratorStep,clearedStep,map_sub,map_add,map_mul,
   map_pow,map_natCast]
 have hR:specialization K P γ (MvPolynomial.X (2:Fin 4))=P.derivative:=by
   simp [specialization]
 rw [hR, ←solution_slope_identity K F P γ hsolution,
   derivative_specialization K P γ M,
   derivative_specialization K P γ (polyH K F)]
 push_cast
 ring
theorem derivative_power_cancellation (H A:Polynomial K) (n:ℕ):
   H^2*(H^n*A).derivative-
     (n:Polynomial K)*(H^n*A)*H*H.derivative=
     H^(n+2)*A.derivative:=by
 cases n with
 | zero => simp [pow_two]
 | succ n =>
     rw [Polynomial.derivative_mul,Polynomial.derivative_pow_succ]
     simp only [Polynomial.C_add,Polynomial.C_1,Polynomial.C_eq_natCast,
       Nat.cast_add,Nat.cast_one,pow_succ]
     ring
theorem specialization_numerator_eq
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ):
   specialization K P γ (numerator K F b)=
     specialization K P γ (polyH K F)^(2*b)*Polynomial.derivative^[b] P:=by
 induction b with
 | zero => simp [numerator_zero,specialization]
 | succ b ih =>
     rw [numerator_succ,specialization_numeratorStep K F (numerator K F b) P γ b
       hsolution,ih]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp,Function.iterate_succ_apply']
     simpa only [Nat.cast_mul,Nat.cast_ofNat] using
       derivative_power_cancellation K (specialization K P γ (polyH K F))
         (Polynomial.derivative^[b] P) (2*b)
theorem specialization_numerator_zero_of_degree
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   specialization K P γ (numerator K F b)=0:=by
 rw [specialization_numerator_eq K F P γ hsolution b,
   Polynomial.iterate_derivative_eq_zero hb,mul_zero]
end PolynomialIdentities
section ActualPoints
variable {K L:Type*} [Field K] [Field L]
def polynomialPoint (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L):
   Fin 4 → L:=
 ![ξ,P.eval₂ coefficients ξ,P.derivative.eval₂ coefficients ξ,coefficients γ]
theorem eval_polynomialPoint_eq_specialization
   (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L) (Q:Poly4 K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) Q=
     (specialization K P γ Q).eval₂ coefficients ξ:=by
 have hhom:
     (Polynomial.eval₂RingHom coefficients ξ).comp (specialization K P γ).toRingHom=
       MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,specialization]
   · intro i
     fin_cases i <;> simp [RingHom.comp_apply,specialization,polynomialPoint]
 exact (DFunLike.congr_fun hhom Q).symm
theorem polynomialPoint_relation
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) F=0:=by
 rw [eval_polynomialPoint_eq_specialization,hsolution]
 simp
theorem polynomialPoint_numerator_zero
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (numerator K F b)=0:=by
 rw [eval_polynomialPoint_eq_specialization,
   specialization_numerator_zero_of_degree K F P γ hsolution b hb]
 simp
theorem polynomialPoint_all_tail_jets_zero
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hdegree:P.natDegree ≤ w):
   ∀ b,w < b →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) b=0:=by
 intro b hb
 rw [jetCoefficient_eq_evaluated_numerator,
   polynomialPoint_numerator_zero coefficients F P γ ξ hsolution b (hdegree.trans_lt hb)]
 simp
end ActualPoints
end
end ProximityPrize.SubmissionLower.ContactPolynomialSolutions

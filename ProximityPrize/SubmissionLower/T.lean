import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D9
namespace ProximityPrize.SubmissionLower.ContactPolynomialRecovery
open ContactDifferentialRing ContactRegularPoint ContactPolynomiality
open ContactTaylorNumerators ContactAgreementEvaluation ContactPolynomialSolutions
open ContactGlobalPolynomiality ContactTranslation DifferentialTaylorCoefficients
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem taylor_coeff_eq_derivative_div_factorial
   (P:Polynomial L) (ξ:L) (j:ℕ) (hfactorial:(j.factorial:L)≠0):
   (Polynomial.taylor ξ P).coeff j=
     (Polynomial.derivative^[j] P).eval ξ/(j.factorial:L):=by
 have hpoly:(j.factorial:Polynomial L)*Polynomial.hasseDeriv j P=
     Polynomial.derivative^[j] P:=by
   have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=L) j) P
   change j.factorial • (Polynomial.hasseDeriv j P)=
     Polynomial.derivative^[j] P at h
   simpa only [nsmul_eq_mul] using h
 have hvalue:=congrArg (Polynomial.evalRingHom ξ) hpoly
 simp only [map_mul,map_natCast] at hvalue
 change (j.factorial:L)*(Polynomial.hasseDeriv j P).eval ξ=
   (Polynomial.derivative^[j] P).eval ξ at hvalue
 rw [Polynomial.taylor_coeff]
 apply (eq_div_iff hfactorial).mpr
 simpa only [mul_comm] using hvalue
theorem polynomialPoint_jetCoefficient_eq
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.derivative^[j] P).eval₂ coefficients ξ/(j.factorial:L):=by
 let v:=polynomialPoint coefficients P γ ξ
 let h:=MvPolynomial.eval₂Hom coefficients v (polyH K F)
 have hH:h≠0:=hregular
 have hnum:MvPolynomial.eval₂Hom coefficients v (numerator K F j)=
     h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by
   rw [eval_polynomialPoint_eq_specialization,
     specialization_numerator_eq K F P γ hsolution j,
     Polynomial.eval₂_mul,Polynomial.eval₂_pow]
   rw [←eval_polynomialPoint_eq_specialization coefficients P γ ξ (polyH K F)]
 have hcancel:h^(2*j)*h⁻¹^(2*j)=1:=by
   rw [←mul_pow,mul_inv_cancel₀ hH,one_pow]
 rw [jetCoefficient_eq_evaluated_numerator,hnum]
 change (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*
     h⁻¹^(2*j)/(j.factorial:L)=_
 congr 1
 calc
   (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*h⁻¹^(2*j)=
       (h^(2*j)*h⁻¹^(2*j))*
         (Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by ring
   _=(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by rw [hcancel,one_mul]
theorem polynomialPoint_jetCoefficient_eq_taylor_coeff
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ)
   (hfactorial:(j.factorial:L)≠0):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.taylor ξ (P.map coefficients)).coeff j:=by
 rw [polynomialPoint_jetCoefficient_eq coefficients F P γ ξ hsolution hregular j,
   Polynomial.eval₂_eq_eval_map, ←Polynomial.iterate_derivative_map]
 exact (taylor_coeff_eq_derivative_div_factorial (P.map coefficients) ξ j hfactorial).symm
theorem reconstructedPolynomial_eq_taylor_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     Polynomial.taylor ξ (P.map coefficients):=by
 ext j
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 by_cases hj:j < w+1
 · rw [if_pos hj]
   exact polynomialPoint_jetCoefficient_eq_taylor_coeff coefficients F P γ ξ
     hsolution hregular j
     (factorial_cast_ne_zero_below_characteristic p j (by omega))
 · rw [if_neg hj]
   have hmap:(P.map coefficients).natDegree ≤ w:=
     Polynomial.natDegree_map_le.trans hdegree
   symm
   apply Polynomial.coeff_eq_zero_of_natDegree_lt
   rw [Polynomial.natDegree_taylor]
   omega
theorem globalPolynomial_eq_map_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   globalPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     P.map coefficients:=by
 change Polynomial.taylor (-ξ)
   (reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w)=_
 rw [reconstructedPolynomial_eq_taylor_of_solution coefficients F P γ ξ hsolution
   hregular p w hchar hdegree,Polynomial.taylor_taylor,neg_add_cancel,
   Polynomial.taylor_zero]
theorem factorial_agreement_zero_iff_original_agreement
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w)
   (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
       (agreementNumerator F w (fun j:ℕ => (j.factorial:K)⁻¹) x u₀ u₁)=0 ↔
     P.eval x=u₀+γ*u₁:=by
 have heq:=factorial_agreement_zero_iff_actual_agreement coefficients F
   (polynomialPoint coefficients P γ ξ)
   (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w x u₀ u₁
 rw [←globalPolynomial_eval coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w (coefficients x),
   globalPolynomial_eq_map_of_solution coefficients F P γ ξ hsolution hregular
     p w hchar hdegree] at heq
 have hvalue:(P.map coefficients).eval (coefficients x)=coefficients (P.eval x):=by
   rw [←Polynomial.eval₂_eq_eval_map,Polynomial.eval₂_at_apply]
 have hseed:polynomialPoint coefficients P γ ξ (3:Fin 4)=coefficients γ:=rfl
 rw [hvalue,hseed, ←map_mul, ←map_add] at heq
 exact heq.trans coefficients.injective.eq_iff
end
end ProximityPrize.SubmissionLower.ContactPolynomialRecovery

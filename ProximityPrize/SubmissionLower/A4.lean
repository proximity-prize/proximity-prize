import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.W
import ProximityPrize.SubmissionLower.E0
namespace ProximityPrize.SubmissionLower.RCN047
open RCN077 RCN269 RCN233
open RCN313 RCN347
noncomputable section
section ScalarClearing
variable {A:Type*} [CommRing A]
theorem common_denominator_power (h u:A) (hHU:h*u=1)
   (w j:ℕ) (hj:j ≤ w):
   h^(2*w)*u^(2*j)=h^(2*(w-j)):=by
 have hexp:2*w=2*(w-j)+2*j:=by omega
 rw [hexp,pow_add,mul_assoc, ←mul_pow,hHU,one_pow,mul_one]
theorem common_denominator_term (h u:A) (hHU:h*u=1)
   (w j:ℕ) (hj:j ≤ w) (c m z:A):
   c*m*h^(2*(w-j))*z^j=
     h^(2*w)*(c*m*u^(2*j)*z^j):=by
 rw [←common_denominator_power h u hHU w j hj]
 ring
theorem common_denominator_sum (h u:A) (hHU:h*u=1)
   (w:ℕ) (c m:ℕ → A) (z a:A):
   (∑ j∈Finset.range (w+1),c j*m j*h^(2*(w-j))*z^j)-
       a*h^(2*w)=
     h^(2*w)*
       ((∑ j∈Finset.range (w+1),c j*m j*u^(2*j)*z^j)-a):=by
 calc
   (∑ j∈Finset.range (w+1),c j*m j*h^(2*(w-j))*z^j)-
       a*h^(2*w)=
     (∑ j∈Finset.range (w+1),
       h^(2*w)*(c j*m j*u^(2*j)*z^j))-a*h^(2*w):=by
         congr 1
         apply Finset.sum_congr rfl
         intro j hj
         exact common_denominator_term h u hHU w j
           (by have hh:=Finset.mem_range.mp hj;omega) (c j) (m j) z
   _=h^(2*w)*
       ((∑ j∈Finset.range (w+1),c j*m j*u^(2*j)*z^j)-a):=by
         rw [mul_sub,Finset.mul_sum]
         ring
end ScalarClearing
section PolynomialClearing
variable {K A:Type*} [Field K] [CommRing A]
theorem map_agreementNumerator
   (φ:Poly4 K →+*A) (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (u:A) (hHU:φ (polyH K F)*u=1):
   φ (agreementNumerator F w c x u₀ u₁)=
     φ (polyH K F)^(2*w)*
       ((∑ j∈Finset.range (w+1),
           φ (MvPolynomial.C (c j))*φ (numerator K F j)*u^(2*j)*
             (φ (MvPolynomial.C x)-φ (MvPolynomial.X (0:Fin 4)))^j)-
         (φ (MvPolynomial.C u₀)+
           φ (MvPolynomial.X (3:Fin 4))*φ (MvPolynomial.C u₁))):=by
 simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
   affineSeedPolynomial,map_sub,map_sum,map_mul,map_pow,map_add]
 exact common_denominator_sum (φ (polyH K F)) u hHU w
   (fun j => φ (MvPolynomial.C (c j))) (fun j => φ (numerator K F j))
   (φ (MvPolynomial.C x)-φ (MvPolynomial.X (0:Fin 4)))
   (φ (MvPolynomial.C u₀)+
     φ (MvPolynomial.X (3:Fin 4))*φ (MvPolynomial.C u₁))
end PolynomialClearing
section ActualPoint
variable {K L:Type*} [Field K] [Field L]
theorem polyImage_eq_coordinate (F:Poly4 K) (i:Fin 4):
   polyImage K F (MvPolynomial.X i)=contactCoordinate K F i:=
 polyImage_X K F i
theorem regularPointValue_polyImage
   (coefficients:K →+*L) (F P:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   regularPointValue coefficients F v hF hregular (polyImage K F P)=
     MvPolynomial.eval₂Hom coefficients v P:=by
 rw [polyImage_apply,regularPointValue_mk,pointEvaluation_liftFour]
theorem regularPointValue_inverseCoordinate
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   regularPointValue coefficients F v hF hregular (inverseCoordinate K F)=
     (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹:=by
 rw [inverseCoordinate,regularPointValue_mk]
 exact pointEvaluation_U coefficients F v
theorem evaluated_iterate_Y
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (b:ℕ):
   regularPointValue coefficients F v hF hregular
       ((contactDerivation K F)^[b] (contactCoordinate K F (1:Fin 4)))=
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)*
       (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b):=by
 rw [←polyImage_eq_coordinate F (1:Fin 4),iterate_Y_eq_numerator,
   map_mul,map_pow,regularPointValue_polyImage,regularPointValue_inverseCoordinate]
theorem jetCoefficient_eq_evaluated_numerator
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (b:ℕ):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)*
       (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b)/
         (b.factorial:L):=by
 rw [jetCoefficient,evaluated_iterate_Y]
theorem numerator_eval_zero_iff_jetCoefficient_zero
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (b:ℕ) (hfactorial:(b.factorial:L)≠0):
   MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0 ↔
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0:=by
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)≠0:=hregular
 have hU:(MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*b)≠0:=
   pow_ne_zero _ (inv_ne_zero hH)
 have hfac:((b.factorial:L)⁻¹)≠0:=inv_ne_zero hfactorial
 rw [jetCoefficient_eq_evaluated_numerator]
 simp only [div_eq_mul_inv,mul_eq_zero,hU,hfac,or_false]
theorem numerator_eval_zero_iff_jetCoefficient_zero_of_char
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p b:ℕ) [CharP L p] (hb:b < p):
   MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0 ↔
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0:=
 numerator_eval_zero_iff_jetCoefficient_zero coefficients F v hF hregular b
   (factorial_cast_ne_zero_below_characteristic p b hb)
theorem all_tail_numerators_iff_all_tail_jets
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hchar:bound < p):
   (∀ b,w < b → b ≤ bound →
     MvPolynomial.eval₂Hom coefficients v (numerator K F b)=0) ↔
   (∀ b,w < b → b ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) b=0):=by
 constructor
 · intro h b hwb hbb
   exact (numerator_eval_zero_iff_jetCoefficient_zero_of_char
     coefficients F v hF hregular p b (hbb.trans_lt hchar)).mp (h b hwb hbb)
 · intro h b hwb hbb
   exact (numerator_eval_zero_iff_jetCoefficient_zero_of_char
     coefficients F v hF hregular p b (hbb.trans_lt hchar)).mpr (h b hwb hbb)
theorem reconstructedPolynomial_eval
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (z:L):
   (reconstructedPolynomial coefficients F v hF hregular w).eval z=
     ∑ j∈Finset.range (w+1),
       jetCoefficient (contactDerivation K F)
         (regularPointValue coefficients F v hF hregular)
         (contactCoordinate K F (1:Fin 4)) j*z^j:=by
 simp only [reconstructedPolynomial,jetPolynomial,Polynomial.eval_finsetSum,
   Polynomial.eval_monomial]
theorem eval_agreementNumerator_clearing
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v (agreementNumerator F w c x u₀ u₁)=
     MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)*
       ((∑ j∈Finset.range (w+1),
           coefficients (c j)*MvPolynomial.eval₂Hom coefficients v (numerator K F j)*
             (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*j)*
               (coefficients x-v 0)^j)-
         (coefficients u₀+v 3*coefficients u₁)):=by
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)≠0:=hregular
 simpa only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X'] using
   map_agreementNumerator (MvPolynomial.eval₂Hom coefficients v) F w c x u₀ u₁
     (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹ (mul_inv_cancel₀ hH)
theorem eval_factorial_agreementNumerator
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v
       (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)=
     MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)*
       ((reconstructedPolynomial coefficients F v hF hregular w).eval
           (coefficients x-v 0)-coefficients u₀-v 3*coefficients u₁):=by
 rw [eval_agreementNumerator_clearing coefficients F v hregular]
 have hsum:
     (∑ j∈Finset.range (w+1),
       coefficients ((j.factorial:K)⁻¹)*
         MvPolynomial.eval₂Hom coefficients v (numerator K F j)*
         (MvPolynomial.eval₂Hom coefficients v (polyH K F))⁻¹^(2*j)*
         (coefficients x-v 0)^j)=
     (reconstructedPolynomial coefficients F v hF hregular w).eval
       (coefficients x-v 0):=by
   rw [reconstructedPolynomial_eval]
   apply Finset.sum_congr rfl
   intro j hj
   rw [jetCoefficient_eq_evaluated_numerator]
   simp only [map_inv₀,map_natCast,div_eq_mul_inv]
   ring
 rw [hsum]
 ring
theorem factorial_agreement_zero_iff_actual_agreement
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients v
       (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)=0 ↔
     (reconstructedPolynomial coefficients F v hF hregular w).eval
       (coefficients x-v 0)=coefficients u₀+v 3*coefficients u₁:=by
 rw [eval_factorial_agreementNumerator coefficients F v hF hregular w x u₀ u₁]
 have hH:MvPolynomial.eval₂Hom coefficients v (polyH K F)^(2*w)≠0:=
   pow_ne_zero _ hregular
 constructor
 · intro h
   have hz:=(mul_eq_zero.mp h).resolve_left hH
   linear_combination hz
 · intro h
   rw [h]
   ring
end ActualPoint
end
end ProximityPrize.SubmissionLower.RCN047

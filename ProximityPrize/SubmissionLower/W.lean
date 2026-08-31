import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.B5
namespace ProximityPrize.SubmissionLower.RCN313
open RCN077 RCN347
noncomputable section
section AlgebraicStep
variable {K A B:Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
def clearedStep (n:ℕ) (m mx my mr r g h hx hy hr:A):A:=
 h^2*mx+r*h^2*my+g*h*mr-
   (n:A)*m*(h*hx+r*h*hy+g*hr)
theorem map_clearedStep (φ:A →+*B) (n:ℕ) (m mx my mr r g h hx hy hr:A):
   φ (clearedStep n m mx my mr r g h hx hy hr)=
     clearedStep n (φ m) (φ mx) (φ my) (φ mr) (φ r) (φ g) (φ h)
       (φ hx) (φ hy) (φ hr):=by
 simp only [clearedStep,map_sub,map_add,map_mul,map_pow,map_natCast]
theorem derivation_inverse_power
   (D:Derivation K A A) (u a:A) (hU:D u= -(u^2*a)) (n:ℕ):
   D (u^n)= -(n:A)*u^(n+1)*a:=by
 induction n with
 | zero =>
     simp only [pow_zero,D.map_one_eq_zero,Nat.cast_zero,neg_zero,zero_mul]
 | succ n ih =>
     rw [pow_succ,leibniz_product,ih,hU]
     simp only [Nat.cast_succ,pow_succ]
     ring
theorem differentiated_fraction_step
   (D:Derivation K A A) (n:ℕ) (m mx my mr r g h hx hy hr u:A)
   (hHU:h*u=1)
   (hM:D m=mx+r*my+g*u*mr)
   (hU:D u= -(u^2*(hx+r*hy+g*u*hr))):
   D (m*u^n)=clearedStep n m mx my mr r g h hx hy hr*u^(n+2):=by
 rw [leibniz_product,hM,
   derivation_inverse_power D u (hx+r*hy+g*u*hr) hU n]
 simp only [pow_add,pow_one]
 unfold clearedStep
 linear_combination
   -(u^n)*((1+h*u)*(mx+r*my)+g*u*mr-
     (n:A)*m*u*(hx+r*hy))*hHU
end AlgebraicStep
section ContactQuotient
variable (K:Type*) [CommRing K]
def polyH (F:Poly4 K):Poly4 K:=MvPolynomial.pderiv (2:Fin 4) F
def polyG (F:Poly4 K):Poly4 K:=
 -(MvPolynomial.pderiv (0:Fin 4) F+
   MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) F)
theorem partial_liftFour_zero (P:Poly4 K):
   MvPolynomial.pderiv (0:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (0:Fin 4) P):=
 partial_liftFour K P (0:Fin 4)
theorem partial_liftFour_one (P:Poly4 K):
   MvPolynomial.pderiv (1:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (1:Fin 4) P):=
 partial_liftFour K P (1:Fin 4)
theorem partial_liftFour_two (P:Poly4 K):
   MvPolynomial.pderiv (2:Fin 5) (liftFour K P)=
     liftFour K (MvPolynomial.pderiv (2:Fin 4) P):=
 partial_liftFour K P (2:Fin 4)
theorem castSucc_two:(2:Fin 4).castSucc=(2:Fin 5):=rfl
theorem contactH_eq_lift (F:Poly4 K):
   contactH K F=liftFour K (polyH K F):=
 partial_liftFour K F (2:Fin 4)
theorem contactG_eq_lift (F:Poly4 K):
   contactG K F=liftFour K (polyG K F):=by
 unfold contactG polyG
 rw [partial_liftFour_zero,partial_liftFour_one]
 simp only [liftFour,map_neg,map_add,map_mul,MvPolynomial.rename_X,
   castSucc_two]
def polyImage (F:Poly4 K):Poly4 K →+*ContactRing K F:=
 (Ideal.Quotient.mk (contactIdeal K F)).comp
   (MvPolynomial.rename (R:=K) (Fin.castSucc:Fin 4 → Fin 5)).toRingHom
theorem polyImage_apply (F P:Poly4 K):
   polyImage K F P=Ideal.Quotient.mk (contactIdeal K F) (liftFour K P):=rfl
@[simp] theorem polyImage_X (F:Poly4 K) (i:Fin 4):
   polyImage K F (MvPolynomial.X i)=
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc):=by
 rw [polyImage_apply]
 simp only [liftFour,MvPolynomial.rename_X]
def inverseCoordinate (F:Poly4 K):ContactRing K F:=
 Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))
theorem polyImage_H_mul_inverse (F:Poly4 K):
   polyImage K F (polyH K F)*inverseCoordinate K F=1:=by
 change Ideal.Quotient.mk (contactIdeal K F) (liftFour K (polyH K F))*
   Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1
 rw [←contactH_eq_lift]
 exact contactRing_inverse K F
theorem contactDerivation_polyImage (F P:Poly4 K):
   contactDerivation K F (polyImage K F P)=
     polyImage K F (MvPolynomial.pderiv (0:Fin 4) P)+
       polyImage K F (MvPolynomial.X (2:Fin 4))*
         polyImage K F (MvPolynomial.pderiv (1:Fin 4) P)+
       polyImage K F (polyG K F)*inverseCoordinate K F*
         polyImage K F (MvPolynomial.pderiv (2:Fin 4) P):=by
 rw [polyImage_apply,contactDerivation_mk,contactVectorField,
   inverseVectorField_apply,partial_extra_liftFour,mul_zero,sub_zero]
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two,contactG_eq_lift]
 simp only [map_add,map_mul,polyImage_apply,inverseCoordinate,
   liftFour,MvPolynomial.rename_X,castSucc_two]
theorem contactDerivation_inverseCoordinate (F:Poly4 K):
   contactDerivation K F (inverseCoordinate K F)=
     -(inverseCoordinate K F^2*
       (polyImage K F (MvPolynomial.pderiv (0:Fin 4) (polyH K F))+
         polyImage K F (MvPolynomial.X (2:Fin 4))*
           polyImage K F (MvPolynomial.pderiv (1:Fin 4) (polyH K F))+
         polyImage K F (polyG K F)*inverseCoordinate K F*
           polyImage K F (MvPolynomial.pderiv (2:Fin 4) (polyH K F)))):=by
 rw [inverseCoordinate,contactDerivation_mk,contactVectorField,inverseVectorField_U]
 rw [contactG_eq_lift,contactH_eq_lift]
 unfold inverseDerivative
 rw [partial_liftFour_zero,partial_liftFour_one,partial_liftFour_two]
 simp only [map_neg,map_mul,map_pow,map_add,polyImage_apply,
   inverseCoordinate,liftFour,MvPolynomial.rename_X,castSucc_two]
def numeratorStep (F:Poly4 K) (b:ℕ) (M:Poly4 K):Poly4 K:=
 clearedStep (2*b) M
   (MvPolynomial.pderiv (0:Fin 4) M)
   (MvPolynomial.pderiv (1:Fin 4) M)
   (MvPolynomial.pderiv (2:Fin 4) M)
   (MvPolynomial.X (2:Fin 4)) (polyG K F) (polyH K F)
   (MvPolynomial.pderiv (0:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (1:Fin 4) (polyH K F))
   (MvPolynomial.pderiv (2:Fin 4) (polyH K F))
def numerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b+1 => numeratorStep K F b (numerator F b)
@[simp] theorem numerator_zero (F:Poly4 K):
   numerator K F 0=MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem numerator_succ (F:Poly4 K) (b:ℕ):
   numerator K F (b+1)=numeratorStep K F b (numerator K F b):=rfl
theorem iterate_Y_eq_numerator (F:Poly4 K) (b:ℕ):
   (contactDerivation K F)^[b] (polyImage K F (MvPolynomial.X (1:Fin 4)))=
     polyImage K F (numerator K F b)*inverseCoordinate K F^(2*b):=by
 induction b with
 | zero => simp
 | succ b ih =>
     rw [Function.iterate_succ_apply',ih,numerator_succ,numeratorStep,
       map_clearedStep]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp]
     apply differentiated_fraction_step
     · exact polyImage_H_mul_inverse K F
     · exact contactDerivation_polyImage K F (numerator K F b)
     · exact contactDerivation_inverseCoordinate K F
end ContactQuotient
section DegreeBounds
variable {K:Type*} [Field K]
theorem support_before_pderiv (i:Fin 4) (P:Poly4 K) (d:Fin 4 →₀ ℕ)
   (hd:d∈(MvPolynomial.pderiv i P).support):
   d+Finsupp.single i 1∈P.support:=by
 apply MvPolynomial.mem_support_iff.mpr
 intro hzero
 have hne:=MvPolynomial.mem_support_iff.mp hd
 apply hne
 rw [MvPolynomial.coeff_pderiv,hzero,zero_mul]
theorem pderiv_degree_bound (i j:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf j ≤ a):(MvPolynomial.pderiv i P).degreeOf j ≤ a:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply] at hh
 omega
theorem pderiv_same_degree_bound (i:Fin 4) (P:Poly4 K) (a:ℕ)
   (hP:P.degreeOf i ≤ a):(MvPolynomial.pderiv i P).degreeOf i ≤ a-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hh:=MvPolynomial.degreeOf_le_iff.mp hP
   (d+Finsupp.single i 1) (support_before_pderiv i P d hd)
 simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
 omega
theorem pderiv_eq_zero_of_degree_bound_zero (i:Fin 4) (P:Poly4 K)
   (hP:P.degreeOf i ≤ 0):MvPolynomial.pderiv i P=0:=by
 ext d
 rw [MvPolynomial.coeff_zero,MvPolynomial.coeff_pderiv]
 have hzero:MvPolynomial.coeff (d+Finsupp.single i 1) P=0:=by
   by_contra hne
   have hh:=MvPolynomial.degreeOf_le_iff.mp hP
     (d+Finsupp.single i 1) (MvPolynomial.mem_support_iff.mpr hne)
   simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
   omega
 rw [hzero,zero_mul]
theorem degree_mul_bound (i:Fin 4) {P Q:Poly4 K} {a b:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ b):
   (P*Q).degreeOf i ≤ a+b:=
 (MvPolynomial.degreeOf_mul_le i P Q).trans (Nat.add_le_add hP hQ)
theorem degree_add_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P+Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_add_le i P Q).trans (max_le hP hQ)
theorem degree_sub_bound (i:Fin 4) {P Q:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a) (hQ:Q.degreeOf i ≤ a):
   (P-Q).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sub_le i P Q).trans (max_le hP hQ)
theorem degree_pow_bound (i:Fin 4) (n:ℕ) {P:Poly4 K} {a:ℕ}
   (hP:P.degreeOf i ≤ a):(P^n).degreeOf i ≤ n*a:=
 (MvPolynomial.degreeOf_pow_le i P n).trans (Nat.mul_le_mul_left n hP)
theorem degree_natCast_eq_zero (i:Fin 4) (n:ℕ):
   (n:Poly4 K).degreeOf i=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K) n]
 exact MvPolynomial.degreeOf_C (n:K) i
theorem polyG_degree_bound (i:Fin 4) (F:Poly4 K) (a r:ℕ)
   (hF:F.degreeOf i ≤ a) (hR:(MvPolynomial.X (2:Fin 4):Poly4 K).degreeOf i ≤ r):
   (polyG K F).degreeOf i ≤ a+r:=by
 unfold polyG
 rw [MvPolynomial.degreeOf_neg]
 apply degree_add_bound i
 · have hh:=pderiv_degree_bound (0:Fin 4) i F a hF
   omega
 · have hh:=degree_mul_bound i hR (pderiv_degree_bound (1:Fin 4) i F a hF)
   simpa only [Nat.add_comm] using hh
theorem numeratorStep_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F M:Poly4 K) (b a c:ℕ)
   (hF:F.degreeOf i ≤ c) (hM:M.degreeOf i ≤ a):
   (numeratorStep K F b M).degreeOf i ≤ a+2*c:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf i ≤ 0:=by
   simp only [R,MvPolynomial.degreeOf_X_of_ne hi,le_refl]
 have hH:H.degreeOf i ≤ c:=pderiv_degree_bound (2:Fin 4) i F c hF
 have hG:G.degreeOf i ≤ c:=by
   simpa only [Nat.add_zero] using polyG_degree_bound i F c 0 hF hR
 have hH2:=degree_pow_bound i 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) i M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) i M a hM
 have hMR:=pderiv_degree_bound (2:Fin 4) i M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) i H c hH
 have hHY:=pderiv_degree_bound (1:Fin 4) i H c hH
 have hHR:=pderiv_degree_bound (2:Fin 4) i H c hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf i ≤ a+2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hG hH) hMR
   omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i (degree_mul_bound i hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf i ≤ 2*c:=by
   have hh:=degree_mul_bound i hG hHR
   omega
 have hbrace:=degree_add_bound i (degree_add_bound i hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf i ≤ 0:=
   le_of_eq (degree_natCast_eq_zero i (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf i ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound i hn hM
 have h4:=degree_mul_bound i hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf i ≤ a+2*c
 exact degree_sub_bound i (degree_add_bound i (degree_add_bound i h1 h2) h3) h4
theorem numeratorStep_R_degree_bound
   (F M:Poly4 K) (b a s:ℕ) (hs:1 ≤ s)
   (hF:F.degreeOf (2:Fin 4) ≤ s) (hM:M.degreeOf (2:Fin 4) ≤ a):
   (numeratorStep K F b M).degreeOf (2:Fin 4) ≤ a+(2*s-1):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s+1:=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hH2:=degree_pow_bound (2:Fin 4) 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) M a hM
 have hMY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) M a hM
 have hMR:=pderiv_same_degree_bound (2:Fin 4) M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) H (s-1) hH
 have hHY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) H (s-1) hH
 have hHR:=pderiv_same_degree_bound (2:Fin 4) H (s-1) hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf (2:Fin 4) ≤
     a+(2*s-1):=by
   by_cases ha:a=0
   · have hz:MvPolynomial.pderiv (2:Fin 4) M=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) M (by simpa only [ha] using hM)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hG hH) hMR
     omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   have hh:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf (2:Fin 4) ≤ 2*s-1:=by
   by_cases hsone:s=1
   · have hz:MvPolynomial.pderiv (2:Fin 4) H=0:=
       pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) H (by simpa [hsone] using hH)
     rw [hz,mul_zero,MvPolynomial.degreeOf_zero]
     exact Nat.zero_le _
   · have hh:=degree_mul_bound (2:Fin 4) hG hHR
     omega
 have hbrace:=degree_add_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf (2:Fin 4) ≤ 0:=
   le_of_eq (degree_natCast_eq_zero (2:Fin 4) (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf (2:Fin 4) ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound (2:Fin 4) hn hM
 have h4:=degree_mul_bound (2:Fin 4) hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf (2:Fin 4) ≤ a+(2*s-1)
 exact degree_sub_bound (2:Fin 4)
   (degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) h1 h2) h3) h4
theorem numerator_nonR_degree_bound
   (i:Fin 4) (hi:i≠2) (F:Poly4 K) (c a₀:ℕ)
   (hF:F.degreeOf i ≤ c) (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (b:ℕ):(numerator K F b).degreeOf i ≤ a₀+2*b*c:=by
 induction b with
 | zero => simpa only [numerator_zero,Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using hbase
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_nonR_degree_bound i hi F (numerator K F b) b
       (a₀+2*b*c) c hF ih
     have heq:a₀+2*(b+1)*c=(a₀+2*b*c)+2*c:=by ring
     rw [heq]
     exact hh
theorem numerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ):
   (numerator K F b).degreeOf (2:Fin 4) ≤ b*(2*s-1):=by
 induction b with
 | zero => simp [numerator_zero,MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠1)]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_R_degree_bound F (numerator K F b) b
       (b*(2*s-1)) s hs hF ih
     simpa only [Nat.add_mul,Nat.one_mul] using hh
theorem numerator_degree_bounds
   (F:Poly4 K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf (1:Fin 4) ≤ ell)
   (hR:F.degreeOf (2:Fin 4) ≤ s)
   (hZ:F.degreeOf (3:Fin 4) ≤ L) (b:ℕ):
   (numerator K F b).degreeOf (1:Fin 4) ≤ 1+2*b*ell∧
   (numerator K F b).degreeOf (2:Fin 4) ≤ b*(2*s-1)∧
   (numerator K F b).degreeOf (3:Fin 4) ≤ 2*b*L:=by
 refine ⟨?_,numerator_R_degree_bound F s hs hR b,?_⟩
 · exact numerator_nonR_degree_bound (1:Fin 4) (by decide) F ell 1 hY (by simp) b
 · have hh:=numerator_nonR_degree_bound (3:Fin 4) (by decide) F L 0 hZ
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(3:Fin 4)≠1)]) b
   simpa only [Nat.zero_add] using hh
end DegreeBounds
section AgreementNumerators
variable {K:Type*} [Field K]
def commonNumeratorTerm (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K) (j:ℕ):
   Poly4 K:=
 MvPolynomial.C (c j)*numerator K F j*
   polyH K F^(2*(w-j))*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j
def clearedTaylorNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x:K):Poly4 K:=
 ∑ j∈Finset.range (w+1),commonNumeratorTerm F w c x j
def affineSeedPolynomial (u₀ u₁:K):Poly4 K:=
 MvPolynomial.C u₀+MvPolynomial.X (3:Fin 4)*MvPolynomial.C u₁
def agreementNumerator (F:Poly4 K) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   Poly4 K:=
 clearedTaylorNumerator F w c x-affineSeedPolynomial u₀ u₁*polyH K F^(2*w)
theorem shiftedX_degree_bound (i:Fin 4) (hi:i≠0) (x:K):
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K).degreeOf i ≤ 0:=by
 apply degree_sub_bound i
 · simp only [MvPolynomial.degreeOf_C,le_refl]
 · simp only [MvPolynomial.degreeOf_X_of_ne hi,le_refl]
theorem degree_sum_bound (i:Fin 4) (I:Finset ℕ) (f:ℕ → Poly4 K) (a:ℕ)
   (hf:∀ j∈I,(f j).degreeOf i ≤ a):
   (∑ j∈I,f j).degreeOf i ≤ a:=
 (MvPolynomial.degreeOf_sum_le i I f).trans (Finset.sup_le hf)
theorem commonNumeratorTerm_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf i ≤ a₀+2*w*cap:=by
 have hM:=numerator_nonR_degree_bound i hi₂ F cap a₀ hF hbase j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf i ≤ a₀+2*j*cap:=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) i (c j)).trans hM
 have hH:(polyH K F).degreeOf i ≤ cap:=
   pderiv_degree_bound (2:Fin 4) i F cap hF
 have hHP:=degree_pow_bound i (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf i ≤ 0:=by
   simpa only [Nat.mul_zero] using degree_pow_bound i j (shiftedX_degree_bound i hi₀ x)
 have hterm:=degree_mul_bound i (degree_mul_bound i hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have heq:(a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*w*cap:=by
   calc
     (a₀+2*j*cap)+2*(w-j)*cap+0=a₀+2*(j+(w-j))*cap:=by ring
     _=a₀+2*w*cap:=by rw [hw]
 exact hterm.trans (le_of_eq heq)
theorem commonNumeratorTerm_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K):
   (commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 have hM:=numerator_R_degree_bound F s hs hF j
 have hCM:(MvPolynomial.C (c j)*numerator K F j).degreeOf (2:Fin 4) ≤ j*(2*s-1):=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) (2:Fin 4) (c j)).trans hM
 have hH:(polyH K F).degreeOf (2:Fin 4) ≤ s-1:=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2*(w-j)) hH
 have hXP:((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j).degreeOf (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have hterm:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCM hHP) hXP
 have hw:j+(w-j)=w:=by omega
 have hs':2*s-1=2*(s-1)+1:=by omega
 have hcap:j*(2*s-1)+2*(w-j)*(s-1) ≤ w*(2*s-1):=by
   rw [hs']
   calc
     j*(2*(s-1)+1)+2*(w-j)*(s-1)=
         2*(j+(w-j))*(s-1)+j:=by ring
     _=2*w*(s-1)+j:=by rw [hw]
     _ ≤ 2*w*(s-1)+w:=Nat.add_le_add_left hj _
     _=w*(2*(s-1)+1):=by ring
 have hterm':(commonNumeratorTerm F w c x j).degreeOf (2:Fin 4) ≤
     j*(2*s-1)+2*(w-j)*(s-1):=by
   simpa only [commonNumeratorTerm,Nat.add_zero] using hterm
 exact hterm'.trans hcap
theorem clearedTaylorNumerator_nonR_degree_bound
   (i:Fin 4) (hi₀:i≠0) (hi₂:i≠2)
   (F:Poly4 K) (cap a₀:ℕ) (hF:F.degreeOf i ≤ cap)
   (hbase:(MvPolynomial.X (1:Fin 4):Poly4 K).degreeOf i ≤ a₀)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf i ≤ a₀+2*w*cap:=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound i
 intro j hj
 exact commonNumeratorTerm_nonR_degree_bound i hi₀ hi₂ F cap a₀ hF hbase w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem clearedTaylorNumerator_R_degree_bound
   (F:Poly4 K) (s:ℕ) (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K):
   (clearedTaylorNumerator F w c x).degreeOf (2:Fin 4) ≤ w*(2*s-1):=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact commonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have hh:=Finset.mem_range.mp hj;omega) c x
theorem affineSeedPolynomial_degree_bound (i:Fin 4) (cap:ℕ)
   (hZ:(MvPolynomial.X (3:Fin 4):Poly4 K).degreeOf i ≤ cap) (u₀ u₁:K):
   (affineSeedPolynomial u₀ u₁).degreeOf i ≤ cap:=by
 unfold affineSeedPolynomial
 apply degree_add_bound i
 · simp only [MvPolynomial.degreeOf_C,Nat.zero_le]
 · have hC:(MvPolynomial.C u₁:Poly4 K).degreeOf i ≤ 0:=by
     simp only [MvPolynomial.degreeOf_C,le_refl]
   simpa only [Nat.add_zero] using degree_mul_bound i hZ hC
theorem agreementNumerator_degree_bounds
   (F:Poly4 K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf (1:Fin 4) ≤ ell)
   (hR:F.degreeOf (2:Fin 4) ≤ s)
   (hZ:F.degreeOf (3:Fin 4) ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   (agreementNumerator F w c x u₀ u₁).degreeOf (1:Fin 4) ≤ 1+2*w*ell∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (2:Fin 4) ≤ w*(2*s-1)∧
   (agreementNumerator F w c x u₀ u₁).degreeOf (3:Fin 4) ≤ 2*w*L+1:=by
 unfold agreementNumerator
 refine ⟨?_,?_,?_⟩
 · apply degree_sub_bound (1:Fin 4)
   · exact clearedTaylorNumerator_nonR_degree_bound (1:Fin 4) (by decide) (by decide)
       F ell 1 hY (by simp) w c x
   · have ha:=affineSeedPolynomial_degree_bound (1:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 4)≠3)]) u₀ u₁
     have hH:(polyH K F).degreeOf (1:Fin 4) ≤ ell:=
       pderiv_degree_bound (2:Fin 4) (1:Fin 4) F ell hY
     have hh:=degree_mul_bound (1:Fin 4) ha (degree_pow_bound (1:Fin 4) (2*w) hH)
     omega
 · apply degree_sub_bound (2:Fin 4)
   · exact clearedTaylorNumerator_R_degree_bound F s hs hR w c x
   · have ha:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
       (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4)≠3)]) u₀ u₁
     have hH:=pderiv_same_degree_bound (2:Fin 4) F s hR
     have hh:=degree_mul_bound (2:Fin 4) ha (degree_pow_bound (2:Fin 4) (2*w) hH)
     have hs':2*s-1=2*(s-1)+1:=by omega
     have hcap:0+(2*w)*(s-1) ≤ w*(2*s-1):=by
       rw [hs']
       calc
         0+(2*w)*(s-1) ≤ 2*w*(s-1)+w:=by omega
         _=w*(2*(s-1)+1):=by ring
     exact hh.trans hcap
 · apply degree_sub_bound (3:Fin 4)
   · have hh:=clearedTaylorNumerator_nonR_degree_bound (3:Fin 4) (by decide) (by decide)
       F L 0 hZ
         (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(3:Fin 4)≠1)]) w c x
     omega
   · have ha:=affineSeedPolynomial_degree_bound (3:Fin 4) 1 (by simp) u₀ u₁
     have hH:(polyH K F).degreeOf (3:Fin 4) ≤ L:=
       pderiv_degree_bound (2:Fin 4) (3:Fin 4) F L hZ
     have hh:=degree_mul_bound (3:Fin 4) ha (degree_pow_bound (3:Fin 4) (2*w) hH)
     omega
end AgreementNumerators
end
end ProximityPrize.SubmissionLower.RCN313

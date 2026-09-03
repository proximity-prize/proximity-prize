import ProximityPrize.SubmissionLower.PackedLegacyCore0

/-! Packed from ProximityPrize.SubmissionLower.B5. -/
section PackedLegacy_B5
namespace ProximityPrize.SubmissionLower.RCN077
open RCN347
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section StableIdeals
variable {K A:Type*} [CommRing K] [CommRing A] [Algebra K A]
theorem derivation_preserves_span
   (D:Derivation K A A) (generators:Set A)
   (hgenerators:∀ x∈generators,D x∈Ideal.span generators):
   ∀ x∈Ideal.span generators,D x∈Ideal.span generators:=by
 intro x hx
 induction hx using Submodule.span_induction with
 | mem x hx => exact hgenerators x hx
 | zero => simpa only [map_zero] using (Ideal.span generators).zero_mem
 | add x y hx hy hDx hDy =>
   simpa only [map_add] using (Ideal.span generators).add_mem hDx hDy
 | smul c x hx hDx =>
   change D (c*x)∈Ideal.span generators
   rw [leibniz_product]
   exact (Ideal.span generators).add_mem
     ((Ideal.span generators).mul_mem_left (D c) hx)
     ((Ideal.span generators).mul_mem_left c hDx)
noncomputable def quotientDerivation
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I):
   Derivation K (A ⧸ I) (A ⧸ I):=
 Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K I)
   (d:=D) (fun x hx => by
     change Ideal.Quotient.mk I (D x)=0
     change Ideal.Quotient.mk I x=0 at hx
     exact Ideal.Quotient.eq_zero_iff_mem.mpr
       (hstable x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))
theorem quotientDerivation_mk
   (D:Derivation K A A) (I:Ideal A)
   (hstable:∀ x∈I,D x∈I) (x:A):
   quotientDerivation D I hstable (Ideal.Quotient.mk I x)=
     Ideal.Quotient.mk I (D x):=by
 unfold quotientDerivation
 exact Derivation.liftOfSurjective_apply _ _ x
end StableIdeals
section PolynomialVectorField
variable (K:Type*) [CommRing K]
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev Poly5:=MvPolynomial (Fin 5) K
noncomputable def liftFour (F:Poly4 K):Poly5 K:=
 MvPolynomial.rename Fin.castSucc F
theorem partial_extra_liftFour (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (liftFour K F)=0:=by
 induction F using MvPolynomial.induction_on with
 | C c => simp [liftFour]
 | add F G hF hG =>
   dsimp only [liftFour] at hF hG
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F+G))=0
   rw [map_add,map_add,hF,hG,add_zero]
 | mul_X F i hF =>
   dsimp only [liftFour] at hF
   have hne:(i.castSucc:Fin 5)≠4:=by
     intro h
     have hv:i.val=4:=congrArg Fin.val h
     have hi:=i.isLt
     omega
   change MvPolynomial.pderiv (4:Fin 5)
     (MvPolynomial.rename Fin.castSucc (F*MvPolynomial.X i))=0
   rw [map_mul,MvPolynomial.rename_X,leibniz_product,hF,
     MvPolynomial.pderiv_X_of_ne hne,zero_mul,mul_zero,add_zero]
theorem partial_liftFour (F:Poly4 K) (i:Fin 4):
   MvPolynomial.pderiv i.castSucc (liftFour K F)=
     liftFour K (MvPolynomial.pderiv i F):=by
 have hinj:Function.Injective (Fin.castSucc:Fin 4 → Fin 5):=by
   intro i j hij
   apply Fin.ext
   exact congrArg (fun x:Fin 5 => x.val) hij
 exact MvPolynomial.pderiv_rename hinj i F
noncomputable def inverseRelation (H:Poly5 K):Poly5 K:=
 H*MvPolynomial.X (4:Fin 5)-1
noncomputable def inverseDerivative (G H:Poly5 K):Poly5 K:=
 MvPolynomial.pderiv (0:Fin 5) H+
   MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) H+
   G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) H
noncomputable def inverseVectorField (G H:Poly5 K):
   Derivation K (Poly5 K) (Poly5 K):=
 (MvPolynomial.pderiv (0:Fin 5):Derivation K (Poly5 K) (Poly5 K))+
   (MvPolynomial.X (2:Fin 5):Poly5 K) • MvPolynomial.pderiv (1:Fin 5)+
   (G*MvPolynomial.X (4:Fin 5)) • MvPolynomial.pderiv (2:Fin 5)-
   ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H) •
     MvPolynomial.pderiv (4:Fin 5)
theorem inverseVectorField_apply (G H P:Poly5 K):
   inverseVectorField K G H P=
     MvPolynomial.pderiv (0:Fin 5) P+
       MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) P+
       G*MvPolynomial.X (4:Fin 5)*MvPolynomial.pderiv (2:Fin 5) P-
       ((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H)*
         MvPolynomial.pderiv (4:Fin 5) P:=by
 simp only [inverseVectorField,Derivation.add_apply,Derivation.sub_apply,
   Derivation.smul_apply,smul_eq_mul]
theorem inverseVectorField_X (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (0:Fin 5))=1:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Y (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (1:Fin 5))=
     MvPolynomial.X (2:Fin 5):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_R (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (2:Fin 5))=
     G*MvPolynomial.X (4:Fin 5):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_Z (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (3:Fin 5))=0:=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_U (G H:Poly5 K):
   inverseVectorField K G H (MvPolynomial.X (4:Fin 5))=
     -((MvPolynomial.X (4:Fin 5))^2*inverseDerivative K G H):=by
 simp [inverseVectorField_apply,MvPolynomial.pderiv_X,Pi.single_apply]
theorem inverseVectorField_H (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H H=inverseDerivative K G H:=by
 rw [inverseVectorField_apply,hH,mul_zero,sub_zero]
 rfl
theorem inverseVectorField_inverseRelation (G H:Poly5 K)
   (hH:MvPolynomial.pderiv (4:Fin 5) H=0):
   inverseVectorField K G H (inverseRelation K H)=
     -(inverseDerivative K G H*MvPolynomial.X (4:Fin 5))*
       inverseRelation K H:=by
 rw [inverseRelation,map_sub,(inverseVectorField K G H).map_one_eq_zero,
   sub_zero,leibniz_product,inverseVectorField_H K G H hH,inverseVectorField_U]
 ring
noncomputable def contactH (F:Poly4 K):Poly5 K:=
 MvPolynomial.pderiv (2:Fin 5) (liftFour K F)
noncomputable def contactG (F:Poly4 K):Poly5 K:=
 -(MvPolynomial.pderiv (0:Fin 5) (liftFour K F)+
     MvPolynomial.X (2:Fin 5)*MvPolynomial.pderiv (1:Fin 5) (liftFour K F))
noncomputable def contactVectorField (F:Poly4 K):
   Derivation K (Poly5 K) (Poly5 K):=
 inverseVectorField K (contactG K F) (contactH K F)
theorem partial_extra_contactH (F:Poly4 K):
   MvPolynomial.pderiv (4:Fin 5) (contactH K F)=0:=by
 have h:=partial_liftFour K F (2:Fin 4)
 change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
 rw [h]
 exact partial_extra_liftFour K _
theorem contactVectorField_F (F:Poly4 K):
   contactVectorField K F (liftFour K F)=
     contactG K F*inverseRelation K (contactH K F):=by
 rw [contactVectorField,inverseVectorField_apply,partial_extra_liftFour,
   mul_zero,sub_zero]
 unfold contactG contactH inverseRelation
 ring
noncomputable def contactIdeal (F:Poly4 K):Ideal (Poly5 K):=
 Ideal.span ({liftFour K F,inverseRelation K (contactH K F)}:Set (Poly5 K))
theorem contactIdeal_stable (F:Poly4 K):
   ∀ P∈contactIdeal K F,contactVectorField K F P∈contactIdeal K F:=by
 apply derivation_preserves_span
 intro P hP
 have hrel:inverseRelation K (contactH K F)∈contactIdeal K F:=
   Ideal.subset_span (by simp)
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
 rcases hP with rfl | rfl
 · rw [contactVectorField_F]
   exact (contactIdeal K F).mul_mem_left _ hrel
 · rw [contactVectorField,
     inverseVectorField_inverseRelation K _ _ (partial_extra_contactH K F)]
   exact (contactIdeal K F).mul_mem_left _ hrel
abbrev ContactRing (F:Poly4 K):=Poly5 K ⧸ contactIdeal K F
noncomputable def contactDerivation (F:Poly4 K):
   Derivation K (ContactRing K F) (ContactRing K F):=
 quotientDerivation (contactVectorField K F) (contactIdeal K F) (contactIdeal_stable K F)
theorem contactDerivation_mk (F:Poly4 K) (P:Poly5 K):
   contactDerivation K F (Ideal.Quotient.mk (contactIdeal K F) P)=
     Ideal.Quotient.mk (contactIdeal K F) (contactVectorField K F P):=
 quotientDerivation_mk _ _ _ P
theorem contactRing_relation (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=0:=by
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 exact Ideal.subset_span (by simp)
theorem contactRing_inverse (F:Poly4 K):
   Ideal.Quotient.mk (contactIdeal K F) (contactH K F)*
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (4:Fin 5))=1:=by
 have hrel:Ideal.Quotient.mk (contactIdeal K F)
     (inverseRelation K (contactH K F))=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
 simpa only [inverseRelation,map_sub,map_mul,map_one,sub_eq_zero] using hrel
end PolynomialVectorField
end ProximityPrize.SubmissionLower.RCN077
end PackedLegacy_B5

/-! Packed from ProximityPrize.SubmissionLower.W. -/
section PackedLegacy_W
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
end PackedLegacy_W

/-! Packed from ProximityPrize.SubmissionLower.O1. -/
section PackedLegacy_O1
namespace ProximityPrize.SubmissionLower.RCN269
open RCN077
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Evaluation
variable {K L:Type*} [CommRing K] [Field L]
def extendPoint (v:Fin 4 → L) (inverseValue:L):Fin 5 → L:=
 ![v 0,v 1,v 2,v 3,inverseValue]
theorem extendPoint_castSucc (v:Fin 4 → L) (inverseValue:L) (i:Fin 4):
   extendPoint v inverseValue i.castSucc=v i:=by
 fin_cases i <;> rfl
theorem extendPoint_last (v:Fin 4 → L) (inverseValue:L):
   extendPoint v inverseValue (4:Fin 5)=inverseValue:=rfl
theorem eval_liftFour
   (coefficients:K →+*L) (v:Fin 4 → L) (inverseValue:L) (P:Poly4 K):
   MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue) (liftFour K P)=
     MvPolynomial.eval₂Hom coefficients v P:=by
 have hhom:
     (MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue)).comp
         (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
           Poly4 K →ₐ[K] Poly5 K).toRingHom=
       MvPolynomial.eval₂Hom coefficients v:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
 exact RingHom.congr_fun hhom P
noncomputable def pointEvaluation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):Poly5 K →+*L:=
 MvPolynomial.eval₂Hom coefficients
   (extendPoint v ((MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F))⁻¹))
theorem pointEvaluation_liftFour
   (coefficients:K →+*L) (F P:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (liftFour K P)=
     MvPolynomial.eval₂Hom coefficients v P:=
 eval_liftFour coefficients v _ P
theorem pointEvaluation_H
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (contactH K F)=
     MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F):=by
 have h:=partial_liftFour K F (2:Fin 4)
 change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
 rw [h,pointEvaluation_liftFour]
theorem pointEvaluation_U
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
   pointEvaluation coefficients F v (MvPolynomial.X (4:Fin 5))=
     (MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F))⁻¹:=by
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_last]
theorem contactIdeal_le_ker_pointEvaluation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   contactIdeal K F ≤ RingHom.ker (pointEvaluation coefficients F v):=by
 apply Ideal.span_le.mpr
 intro P hP
 change pointEvaluation coefficients F v P=0
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
 rcases hP with rfl | rfl
 · rw [pointEvaluation_liftFour,hF]
 · rw [inverseRelation,map_sub,map_mul,map_one,pointEvaluation_H,
     pointEvaluation_U,mul_inv_cancel₀ hregular,sub_self]
noncomputable def regularPointValue
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):ContactRing K F →+*L:=
 Ideal.Quotient.lift (contactIdeal K F) (pointEvaluation coefficients F v)
   (fun P hP => RingHom.mem_ker.mp
     (contactIdeal_le_ker_pointEvaluation coefficients F v hF hregular hP))
theorem regularPointValue_mk
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (P:Poly5 K):
   regularPointValue coefficients F v hF hregular
     (Ideal.Quotient.mk (contactIdeal K F) P)=pointEvaluation coefficients F v P:=rfl
theorem regularPointValue_algebraMap
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (c:K):
   regularPointValue coefficients F v hF hregular
     (algebraMap K (ContactRing K F) c)=coefficients c:=by
 change regularPointValue coefficients F v hF hregular
   (Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.C c))=coefficients c
 rw [regularPointValue_mk]
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_C]
theorem regularPointValue_comp_algebraMap
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   (regularPointValue coefficients F v hF hregular).comp
     (algebraMap K (ContactRing K F))=coefficients:=by
 ext c
 exact regularPointValue_algebraMap coefficients F v hF hregular c
end Evaluation
section Coordinates
variable (K:Type*) [CommRing K]
noncomputable def contactCoordinate (F:Poly4 K) (i:Fin 4):ContactRing K F:=
 Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc)
theorem coordinate_relation (F:Poly4 K):
   MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
     (contactCoordinate K F) F=0:=by
 have hhom:
     (Ideal.Quotient.mk (contactIdeal K F)).comp
         (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
           Poly4 K →ₐ[K] Poly5 K).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
         (contactCoordinate K F):=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
     rfl
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
       MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X']
     rfl
 have hF:=RingHom.congr_fun hhom F
 change Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=
   MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F)) (contactCoordinate K F) F at hF
 rw [contactRing_relation] at hF
 exact hF.symm
theorem derivation_coordinate_X (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (0:Fin 4))=1:=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (0:Fin 5)))=1
 rw [inverseVectorField_X,map_one]
theorem derivation_coordinate_Y (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (1:Fin 4))=
     contactCoordinate K F (2:Fin 4):=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (1:Fin 5)))=
     Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (2:Fin 5))
 rw [inverseVectorField_Y]
theorem derivation_coordinate_Z (F:Poly4 K):
   contactDerivation K F (contactCoordinate K F (3:Fin 4))=0:=by
 rw [contactCoordinate,contactDerivation_mk]
 change Ideal.Quotient.mk (contactIdeal K F)
   (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (3:Fin 5)))=0
 rw [inverseVectorField_Z,map_zero]
variable {L:Type*} [Field L]
theorem regularPointValue_coordinate
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (i:Fin 4):
   regularPointValue coefficients F v hF hregular (contactCoordinate K F i)=v i:=by
 rw [contactCoordinate,regularPointValue_mk]
 simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
end Coordinates
end ProximityPrize.SubmissionLower.RCN269
end PackedLegacy_O1

/-! Packed from ProximityPrize.SubmissionLower.E0. -/
section PackedLegacy_E0
namespace ProximityPrize.SubmissionLower.RCN233
open RCN347 RCN348 RCN077 RCN269
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section GeneralTaylorCoordinates
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem iterate_affine_coordinate_ge_two
   (D:Derivation K A A) (a:A) (ha:D a=1) (j:ℕ):
   D^[j+2] a=0:=by
 rw [Function.iterate_add_apply]
 change D^[j] (D (D a))=0
 rw [ha,D.map_one_eq_zero]
 exact iterate_zero D j
theorem jetPolynomial_affine_coordinate
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:2 ≤ bound) (a:A) (ha:D a=1):
   jetPolynomial D value bound a=Polynomial.C (value a)+Polynomial.X:=by
 ext j
 cases j with
 | zero =>
   have hb:0 < bound:=by omega
   simp [jetPolynomial_coeff,jetCoefficient,hb]
 | succ j =>
   cases j with
   | zero =>
     have hb:1 < bound:=by omega
     simp [jetPolynomial_coeff,jetCoefficient,hb,ha]
   | succ j =>
     have hz:jetCoefficient D value a (j+2)=0:=by
       simp only [jetCoefficient,iterate_affine_coordinate_ge_two D a ha j,
         map_zero,zero_div]
     have hn0:j+2≠0:=by omega
     have hn1:j+2≠1:=by omega
     change (jetPolynomial D value bound a).coeff (j+2)=
       (Polynomial.C (value a)+Polynomial.X).coeff (j+2)
     simp [jetPolynomial_coeff,hz,Polynomial.coeff_C,Polynomial.coeff_X,hn0,hn1]
theorem jetPolynomial_natDegree_le
   (D:Derivation K A A) (value:A →+*L) (w:ℕ) (a:A):
   (jetPolynomial D value (w+1) a).natDegree ≤ w:=by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [jetPolynomial_coeff,if_neg (by omega)]
end GeneralTaylorCoordinates
section ActualRegularPoint
variable {K L:Type*} [CommRing K] [Field L]
noncomputable def reconstructedPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 jetPolynomial (contactDerivation K F)
   (regularPointValue coefficients F v hF hregular) (w+1)
   (contactCoordinate K F (1:Fin 4))
noncomputable def reconstructionSubstitution
   (v:Fin 4 → L) (P:Polynomial L):Fin 4 → Polynomial L:=
 ![Polynomial.C (v 0)+Polynomial.X,P,P.derivative,Polynomial.C (v 3)]
noncomputable def reconstructedEquation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
   (reconstructionSubstitution v (reconstructedPolynomial coefficients F v hF hregular w)) F
theorem reconstructedPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).natDegree ≤ w:=
 jetPolynomial_natDegree_le _ _ _ _
theorem reconstructedPolynomial_coeff_zero
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 0=v 1:=by
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,
   regularPointValue_coordinate]
theorem reconstructedPolynomial_coeff_one
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 1=v 2:=by
 have hb:1 < w+1:=by omega
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,hb,
   derivation_coordinate_Y,regularPointValue_coordinate]
theorem coordinate_taylor_eq_reconstruction
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   ∀ i:Fin 4,
     jetPolynomial (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular) bound
       (contactCoordinate K F i)=
     reconstructionSubstitution v
       (reconstructedPolynomial coefficients F v hF hregular w) i:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let P:=reconstructedPolynomial coefficients F v hF hregular w
 have hbound:0 < bound:=by omega
 have hfull:jetPolynomial D value bound (contactCoordinate K F (1:Fin 4))=P:=by
   apply jetPolynomial_eq_shorter_of_tails_zero D value (w+1) bound
     (contactCoordinate K F (1:Fin 4)) hshort
   intro j hj hjbound
   exact htails j (by omega) hjbound.le
 have hlast:jetCoefficient D value (contactCoordinate K F (1:Fin 4)) bound=0:=
   htails bound (by omega) le_rfl
 have hdr:=jetPolynomial_derivation_eq_derivative_of_char D value p bound hchar
   (contactCoordinate K F (1:Fin 4)) hlast
 have hDy:D (contactCoordinate K F (1:Fin 4))=
     contactCoordinate K F (2:Fin 4):=derivation_coordinate_Y K F
 rw [hDy,hfull] at hdr
 have hx:=jetPolynomial_affine_coordinate D value bound (by omega)
   (contactCoordinate K F (0:Fin 4)) (derivation_coordinate_X K F)
 have hvalueX:value (contactCoordinate K F (0:Fin 4))=v 0:=
   regularPointValue_coordinate K coefficients F v hF hregular 0
 rw [hvalueX] at hx
 have hz:=jetPolynomial_of_derivation_eq_zero D value bound hbound
   (contactCoordinate K F (3:Fin 4)) (derivation_coordinate_Z K F)
 have hvalueZ:value (contactCoordinate K F (3:Fin 4))=v 3:=
   regularPointValue_coordinate K coefficients F v hF hregular 3
 rw [hvalueZ] at hz
 intro i
 fin_cases i
 · exact hx
 · exact hfull
 · exact hdr
 · exact hz
theorem polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0)
   (hdegree:(reconstructedEquation coefficients F v hF hregular w).natDegree < bound):
   reconstructedEquation coefficients F v hF hregular w=0:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let sigmaPolys:=reconstructionSubstitution v
   (reconstructedPolynomial coefficients F v hF hregular w)
 have hcoeff:value.comp (algebraMap K (ContactRing K F))=coefficients:=
   regularPointValue_comp_algebraMap coefficients F v hF hregular
 have hcoordinates:∀ i:Fin 4,
     jetPolynomial D value bound (contactCoordinate K F i)=sigmaPolys i:=
   coordinate_taylor_eq_reconstruction coefficients F v hF hregular p bound w
     hw hshort hchar htails
 have hfactorial:∀ j < bound,(j.factorial:L)≠0:=by
   intro j hj
   exact factorial_cast_ne_zero_below_characteristic p j (hj.trans hchar)
 have hdeg:(MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K (ContactRing K F)))) sigmaPolys F).natDegree <
       bound:=by
   rw [hcoeff]
   exact hdegree
 have hzero:=polynomial_relation_of_taylor_substitution D value bound (by omega)
   hfactorial (contactCoordinate K F) sigmaPolys hcoordinates F
   (coordinate_relation K F) hdeg
 rw [hcoeff] at hzero
 exact hzero
end ActualRegularPoint
end ProximityPrize.SubmissionLower.RCN233
end PackedLegacy_E0

/-! Packed from ProximityPrize.SubmissionLower.A4. -/
section PackedLegacy_A4
namespace ProximityPrize.SubmissionLower.RCN047
open RCN077 RCN269 RCN233 RCN313 RCN347
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
end PackedLegacy_A4

/-! Packed from ProximityPrize.SubmissionLower.N4. -/
section PackedLegacy_N4
namespace ProximityPrize.SubmissionLower.RCN256
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
private def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
private def minusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0-MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
def shiftMinus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (minusVariables K)
theorem shiftMinus_comp_shiftPlus:
   (shiftMinus K).comp (shiftPlus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
theorem shiftPlus_comp_shiftMinus:
   (shiftPlus K).comp (shiftMinus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
@[simp] theorem shiftMinus_shiftPlus (f:Poly K):
   shiftMinus K (shiftPlus K f)=f:=
 DFunLike.congr_fun (shiftMinus_comp_shiftPlus K) f
@[simp] theorem shiftPlus_shiftMinus (f:Poly K):
   shiftPlus K (shiftMinus K f)=f:=
 DFunLike.congr_fun (shiftPlus_comp_shiftMinus K) f
@[simp] theorem shiftPlus_slopeDifference:
   shiftPlus K (slopeDifference K)=MvPolynomial.X 0:=by
 simp [slopeDifference,shiftPlus,plusVariables]
@[simp] theorem shiftMinus_X_zero:
   shiftMinus K (MvPolynomial.X 0)=slopeDifference K:=by
 simp [shiftMinus,minusVariables,slopeDifference]
theorem slopeDifference_ne_zero:slopeDifference K≠0:=by
 intro h
 have hh:=congrArg (shiftPlus K) h
 simpa using hh
def monomialRemainder (d:Fin 3 →₀ ℕ):Poly K →ₗ[K] Poly K where
 toFun f:=f.modMonomial d
 map_add' f g:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
 map_smul' c f:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
def contactJet (h:ℕ):Poly K →ₗ[K] Poly K:=
 (monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus K).toLinearMap
theorem contactJet_apply (h:ℕ) (f:Poly K):
   contactJet K h f=(shiftPlus K f).modMonomial (Finsupp.single 0 h):=rfl
theorem contactJet_eq_zero_iff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔ slopeDifference K^h∣f:=by
 rw [contactJet_apply,
   ←MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero,
   ←MvPolynomial.X_pow_eq_monomial]
 constructor
 · rintro ⟨q,hq⟩
   refine ⟨shiftMinus K q,?_⟩
   have hh:=congrArg (shiftMinus K) hq
   simpa only [shiftMinus_shiftPlus,map_mul,map_pow,shiftMinus_X_zero] using hh
 · rintro ⟨q,rfl⟩
   exact ⟨shiftPlus K q,by simp⟩
theorem contactJet_mul_slopeDifference (h:ℕ) (q:Poly K):
   contactJet K h (slopeDifference K^h*q)=0:=
 (contactJet_eq_zero_iff K h _).2 ⟨q,rfl⟩
theorem contactJet_eq_zero_iff_coeff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔
     ∀ d:Fin 3 →₀ ℕ,d 0 < h → MvPolynomial.coeff d (shiftPlus K f)=0:=by
 constructor
 · intro hf d hd
   have hnot:¬ Finsupp.single (0:Fin 3) h ≤ d:=by
     intro hle
     have hh:=hle 0
     simp only [Finsupp.single_eq_same] at hh
     omega
   have hh:=congrArg (MvPolynomial.coeff d) hf
   simpa [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hnot] using hh
 · intro hf
   ext d
   by_cases hle:Finsupp.single (0:Fin 3) h ≤ d
   · simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_le _ hle]
   · have hd:d 0 < h:=by
       by_contra hnot
       apply hle
       intro i
       by_cases hi:i=0
       · subst i
         simp only [Finsupp.single_eq_same]
         omega
       · simp [Finsupp.single_eq_of_ne hi]
     simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hle,hf d hd]
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 2 ≤ L∧d 1 ≤ s}
def coefficientBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (boxExponents M L s)
theorem mem_coefficientBox_iff (M L s:ℕ) (f:Poly K):
   f∈coefficientBox K M L s ↔
     ∀ d∈f.support,d 0 ≤ M∧d 0+d 2 ≤ L∧d 1 ≤ s:=by
 rfl
theorem coefficientBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈coefficientBox K M L s)
   (hg:g∈coefficientBox K M' L' s'):
   f*g∈coefficientBox K (M+M') (L+L') (s+s'):=by
 have hset:boxExponents M L s+boxExponents M' L' s' ⊆
     boxExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd2,hd1⟩
   rcases he with ⟨he0,he2,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_coefficientBox:
   slopeDifference K∈coefficientBox K 1 1 1:=by
 apply (coefficientBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem slopeDifference_pow_mem_coefficientBox (h:ℕ):
   slopeDifference K^h∈coefficientBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ h ih =>
     simpa only [pow_succ] using coefficientBox_mul K ih (slopeDifference_mem_coefficientBox K)
theorem slopeDifference_mul_mem_coefficientBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈coefficientBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈coefficientBox K M L s:=by
 have hh:=coefficientBox_mul K (slopeDifference_pow_mem_coefficientBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,Nat.add_sub_of_le hs] using hh
private def exponentTriple (i j z:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] private theorem exponentTriple_zero (i j z:ℕ):
   exponentTriple i j z 0=i:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_one (i j z:ℕ):
   exponentTriple i j z 1=j:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_two (i j z:ℕ):
   exponentTriple i j z 2=z:=by simp [exponentTriple]
private theorem exponentTriple_eta (d:Fin 3 →₀ ℕ):
   exponentTriple (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i <;> simp
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (min M L+1)) × (Fin (s+1) × Fin (L-i.val+1))
private theorem finPair_heq_of_val_eq
   {n a b:ℕ} {i j:Fin n} {u:Fin a} {v:Fin b}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (i,u) (j,v):=by
 subst b
 have hi:i=j:=Fin.ext hij
 have hu:u=v:=Fin.ext huv
 cases hi
 cases hu
 rfl
def boxExponentsEquivIndex (M L s:ℕ):
   boxExponents M L s ≃ BoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨⟨d.val 1,by
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩,
       ⟨d.val 2,by
         change d.val 2 < L-d.val 0+1
         rcases d.property with ⟨hM,hL,hs⟩
         omega⟩⟩⟩
 invFun q:=
   ⟨exponentTriple q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,exponentTriple_zero,
       exponentTriple_one,exponentTriple_two]
     omega⟩
 left_inv d:=Subtype.ext (exponentTriple_eta d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   simp
   apply finPair_heq_of_val_eq
   · simp [exponentTriple]
   · rfl
   · rfl
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
theorem coefficientBox_finrank (M L s:ℕ):
   Module.finrank K (coefficientBox K M L s)=
     (s+1)*∑ i:Fin (min M L+1),(L-i.val+1):=by
 change Module.finrank K (MvPolynomial.restrictSupport K (boxExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (boxExponents M L s))]
 rw [Fintype.card_congr (boxExponentsEquivIndex M L s)]
 simp [BoxIndex,Fintype.card_sigma,Finset.mul_sum]
theorem coefficientBox_finrank_of_le (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     (s+1)*∑ i:Fin (M+1),(L-i.val+1):=by
 have hmin:min M L=M:=Nat.min_eq_left hML
 have hh:=coefficientBox_finrank K M L s
 rw [hmin] at hh
 exact hh
def multiplyIntoBox {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     coefficientBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_coefficientBox K hM hL hs q.property⟩
 map_add' q r:=by
   apply Subtype.ext
   simp [mul_add]
 map_smul' c q:=by
   apply Subtype.ext
   simp [mul_smul_comm]
theorem multiplyIntoBox_injective
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=slopeDifference K^h*r.val:=
   congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
def kernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (blockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (blockJet K M L s h))
   (multiplyIntoBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem kernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (kernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoBox_injective K hM hL hs
 exact congrArg Subtype.val heq
theorem blockJet_rank_add_quotient_finrank_le {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h))+
       Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) ≤
     Module.finrank K (coefficientBox K M L s):=by
 have hker:=LinearMap.finrank_le_finrank_of_injective
   (kernelEmbedding_injective K hM hL hs)
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 omega
theorem blockJet_rank_le_triangle_difference {M L s h:ℕ}
   (hML:M ≤ L) (hM:h ≤ M) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (s+1)*(∑ i:Fin (M+1),(L-i.val+1))-
       (s-h+1)*(∑ i:Fin (M-h+1),(L-h-i.val+1)):=by
 have hineq:=blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
 rw [coefficientBox_finrank_of_le K M L s hML,
   coefficientBox_finrank_of_le K (M-h) (L-h) (s-h)
     (Nat.sub_le_sub_right hML h)] at hineq
 omega
theorem blockJet_rank_le_input (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (s+1)*∑ i:Fin (M+1),(L-i.val+1):=by
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 rw [coefficientBox_finrank_of_le K M L s hML] at hsum
 omega
theorem coefficientBox_finrank_range (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     (s+1)*∑ i∈Finset.range (M+1),(L+1-i):=by
 rw [coefficientBox_finrank_of_le K M L s hML]
 congr 1
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro i hi
 have hiM:=i.isLt
 omega
def blockInputCount (M L s:ℕ):ℕ:=
 (s+1)*∑ i∈Finset.range (M+1),(L+1-i)
def blockKernelLowerBound (M L s h:ℕ):ℕ:=
 (s+1-h)*
   ∑ i∈Finset.range (M+1-h),(L+1-h-i)
def contactRankBound (M L s h:ℕ):ℕ:=
 blockInputCount M L s-blockKernelLowerBound M L s h
theorem blockJet_rank_le_contactRankBound (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     contactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hineq:=blockJet_rank_add_quotient_finrank_le K hM hL hs
     rw [coefficientBox_finrank_range K M L s hML,
       coefficientBox_finrank_range K (M-h) (L-h) (s-h)
         (Nat.sub_le_sub_right hML h)] at hineq
     have hMeq:M-h+1=M+1-h:=by omega
     have hLeq:L-h+1=L+1-h:=by omega
     have hseq:s-h+1=s+1-h:=by omega
     rw [hMeq,hLeq,hseq] at hineq
     unfold contactRankBound blockInputCount blockKernelLowerBound
     omega
   · have hzero:s+1-h=0:=by omega
     have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
     rw [coefficientBox_finrank_range K M L s hML] at hsum
     simp only [contactRankBound,blockKernelLowerBound,hzero,zero_mul,Nat.sub_zero,
       blockInputCount]
     omega
 · have hzero:M+1-h=0:=by omega
   have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
   rw [coefficientBox_finrank_range K M L s hML] at hsum
   simp only [contactRankBound,blockKernelLowerBound,hzero,Finset.range_zero,
     Finset.sum_empty,mul_zero,Nat.sub_zero,blockInputCount]
   omega
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   contactRankBound (min r L) L s (min (r+1) (m-r))
theorem sum_blockJet_ranks_le_localRankBound (m L s:ℕ):
   (∑ r∈Finset.range m,
     Module.finrank K (LinearMap.range
       (blockJet K (min r L) L s (min (r+1) (m-r))))) ≤
     localRankBound m L s:=by
 apply Finset.sum_le_sum
 intro r hr
 exact blockJet_rank_le_contactRankBound K (min r L) L s
   (min (r+1) (m-r)) (min_le_right r L)
end
end ProximityPrize.SubmissionLower.RCN256
end PackedLegacy_N4

/-! Packed from ProximityPrize.SubmissionLower.Y2. -/
section PackedLegacy_Y2
namespace ProximityPrize.SubmissionLower.RCN051
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def n:ℕ:=262144
def w:ℕ:=131071
def agreements:ℕ:=184720
def prime:ℕ:=2130706433
def errors:ℕ:=n-agreements
def alignmentBudget:ℕ:=100000000000000000
def multiplicity:ℕ:=18
def seedTotalCap:ℕ:=176
def slopeCap:ℕ:=5
def weightedCap:ℕ:=multiplicity*agreements
def yCap:ℕ:=(weightedCap-1)/w
def gap:ℕ:=agreements-w
def algebraicCap:ℕ:=(2*slopeCap-1)*seedTotalCap
def coefficientCount:ℕ:=
 ∑ i∈range (seedTotalCap+1),
   ∑ j∈range (slopeCap+1),
     (seedTotalCap+1-i)*(weightedCap-w*i-(w-1)*j)
def contactExponent (r:ℕ):ℕ:=min (r+1) (multiplicity-r)
def localContactRank:ℕ:=
 ∑ r∈range multiplicity,
   (((slopeCap+1)*
       (∑ f∈range (min r seedTotalCap+1),(seedTotalCap+1-f)))-
     ((slopeCap+1-contactExponent r)*
       (∑ f∈range (min r seedTotalCap+1-contactExponent r),
         (seedTotalCap+1-contactExponent r-f))))
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
 a.r*b.y*c.z+a.r*b.z*c.y+
 a.z*b.y*c.r+a.z*b.r*c.y
def unitY:DegreeVector:=⟨1,0,0⟩
def unitR:DegreeVector:=⟨0,1,0⟩
def unitZ:DegreeVector:=⟨0,0,1⟩
def tailVector (h:ℕ):DegreeVector:=
 ⟨1+h*(2*yCap-1),h*(2*slopeCap-1),2*h*seedTotalCap⟩
def firstTail:DegreeVector:=tailVector (w+1)
def lastTail:DegreeVector:=tailVector weightedCap
def agreementVector:DegreeVector:=
 ⟨1+w*(2*yCap-1),w*(2*slopeCap-1),2*w*seedTotalCap+1⟩
def cutNumerator (v:DegreeVector):ℕ:=
 gap^2*mixed v firstTail lastTail+
 n*gap*mixed v firstTail agreementVector+
 (errors+1)*gap^2*mixed v firstTail unitZ
def wholeNumerator (v:DegreeVector):ℕ:=
 (n-w)^2*mixed v agreementVector agreementVector+
 (errors+1)*(n-w)*gap*mixed v agreementVector unitZ
def regularNumerator:ℕ:=
 yCap*wholeNumerator unitY+
 slopeCap*wholeNumerator unitR+
 seedTotalCap*wholeNumerator unitZ
def singularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
     algebraicCap*(1+2*(w+1)*(algebraicCap-1))+
     (errors+1)*algebraicCap)+
   n*algebraicCap*(1+2*w*(algebraicCap-1))
def totalNumerator:ℕ:=regularNumerator+gap*singularNumerator
theorem parameter_values:
   weightedCap=3324960∧yCap=25∧gap=53649∧
   errors=77424∧algebraicCap=1584:=by
 norm_num [weightedCap,multiplicity,agreements,yCap,w,gap,errors,
   n,algebraicCap,slopeCap,seedTotalCap]
theorem coefficient_count_exact:coefficientCount=36613226930:=by
 norm_num [coefficientCount,seedTotalCap,slopeCap,weightedCap,
   multiplicity,agreements,w,Finset.sum_range_succ]
theorem contact_rank_exact:localContactRank=139668:=by
 norm_num [localContactRank,contactExponent,multiplicity,seedTotalCap,
   slopeCap,Finset.sum_range_succ]
theorem interpolation_gate:n*localContactRank < coefficientCount:=by
 rw [coefficient_count_exact,contact_rank_exact]
 norm_num [n]
theorem characteristic_gates:
   w < weightedCap∧(2*slopeCap-1)*weightedCap < prime∧
   algebraicCap < prime∧slopeCap < prime:=by
 norm_num [w,weightedCap,multiplicity,agreements,slopeCap,prime,
   algebraicCap,seedTotalCap]
theorem branch_dominance:
   wholeNumerator unitY ≤ cutNumerator unitY∧
   wholeNumerator unitR ≤ cutNumerator unitR∧
   wholeNumerator unitZ ≤ cutNumerator unitZ:=by
 norm_num [wholeNumerator,cutNumerator,unitY,unitR,unitZ,mixed,
   firstTail,lastTail,tailVector,agreementVector,yCap,weightedCap,
   multiplicity,agreements,w,gap,n,errors,slopeCap,seedTotalCap]
theorem ledger_numerator_exact:
   totalNumerator=143519632029158837406857181:=by
 norm_num [totalNumerator,regularNumerator,singularNumerator,
   wholeNumerator,cutNumerator,unitY,unitR,unitZ,mixed,
   firstTail,lastTail,tailVector,agreementVector,yCap,weightedCap,
   multiplicity,agreements,w,gap,n,errors,slopeCap,seedTotalCap,
   algebraicCap]
theorem denominator_exact:gap^2=2878215201:=by
 norm_num [gap,agreements,w]
theorem division_certificate:
   totalNumerator=49864107443840450*gap^2+398176731∧
   398176731 < gap^2:=by
 rw [ledger_numerator_exact,denominator_exact]
 norm_num
theorem strict_ledger_budget:totalNumerator < alignmentBudget*gap^2:=by
 rw [ledger_numerator_exact,denominator_exact]
 norm_num [alignmentBudget]
theorem below_budget_of_scaled_cardinality_bound
   (cardinality:ℕ) (h:cardinality*gap^2 ≤ totalNumerator):
   cardinality < alignmentBudget:=by
 have hstrict:=h.trans_lt strict_ledger_budget
 rw [denominator_exact] at hstrict
 exact Nat.lt_of_mul_lt_mul_right hstrict
end ProximityPrize.SubmissionLower.RCN051
end PackedLegacy_Y2

/-! Packed from ProximityPrize.SubmissionLower.Q. -/
section PackedLegacy_Q
namespace ProximityPrize.SubmissionLower.RCN174
open RCN256 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
theorem coefficientBox_mono {M L s M' L' s':ℕ}
   (hM:M ≤ M') (hL:L ≤ L') (hs:s ≤ s'):
   coefficientBox K M L s ≤ coefficientBox K M' L' s':=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 exact ⟨hd.1.trans hM,hd.2.1.trans hL,hd.2.2.trans hs⟩
def localMonomial (f j z:ℕ):Poly K:=
 MvPolynomial.monomial
   (Finsupp.single 0 f+Finsupp.single 1 j+Finsupp.single 2 z) 1
theorem localMonomial_mem (f j z:ℕ):
   localMonomial K f j z∈coefficientBox K f (f+z) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [boxExponents]
def seedAffine (u₀ u₁:K):Poly K:=
 MvPolynomial.C u₀+MvPolynomial.monomial (Finsupp.single 2 1) u₁
theorem seedAffine_mem (u₀ u₁:K):
   seedAffine K u₀ u₁∈coefficientBox K 0 1 0:=by
 apply (coefficientBox K 0 1 0).add_mem
 · change MvPolynomial.monomial 0 u₀∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem seedAffine_pow_mem (u₀ u₁:K) (t:ℕ):
   seedAffine K u₀ u₁^t∈coefficientBox K 0 t 0:=by
 induction t with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ t ih =>
     simpa only [pow_succ,Nat.zero_add] using
       coefficientBox_mul K ih (seedAffine_mem K u₀ u₁)
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (L+1-i.val) × Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ} (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val+Finsupp.single 3 c.2.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 0=c.2.2.2.val:=by simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 1=c.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 2=c.2.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 3=c.2.2.1.val:=by simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 have hz:=congrArg (fun e:Fin 4 →₀ ℕ => e 3) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 simp only [columnExponent_z] at hz
 subst di
 subst dj
 subst dz
 subst de
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have hz:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 simp only [globalExponents,Set.mem_setOf_eq,columnExponent_x,
   columnExponent_y,columnExponent_r,columnExponent_z]
 omega
def reconstruct (D w L s:ℕ) (θ:CoefficientIndex D w L s → K):
   MvPolynomial (Fin 4) K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (θ c)
theorem reconstruct_coeff (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s θ)=θ c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro θ η h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (hθ:θ≠0):
   reconstruct K D w L s θ≠0:=by
 intro hzero
 apply hθ
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hzero
theorem reconstruct_mem_globalCoefficientBox (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   reconstruct K D w L s θ∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (θ c)
theorem reconstruct_support_caps (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   ∀ d∈(reconstruct K D w L s θ).support,
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=
 reconstruct_mem_globalCoefficientBox K D w L s θ
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     (L+1-i)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,Finset.sum_range]
def blockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):Poly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     (((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)) •
         (seedAffine K u₀ u₁^(c.1.val-f.val)*
           localMonomial K f.val c.2.1.val c.2.2.1.val)
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u₀ u₁ c r∈
     coefficientBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (coefficientBox K (min r L) L s).smul_mem
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have hz:=c.2.2.1.isLt
   have hfi:=f.isLt
   have hmul:=coefficientBox_mul K
     (seedAffine_pow_mem K u₀ u₁ (c.1.val-f.val))
     (localMonomial_mem K f.val c.2.1.val c.2.2.1.val)
   apply coefficientBox_mono K (show 0+f.val ≤ min r L by omega)
     (show c.1.val-f.val+(f.val+c.2.2.1.val) ≤ L by omega)
     (show 0+c.2.1.val ≤ s by omega)
   exact hmul
 · exact (coefficientBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   coefficientBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u₀ u₁ c r,
   blockEntry_mem K D w L s x u₀ u₁ c r⟩
def extractBlock (D w L s:ℕ) (x u₀ u₁:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     coefficientBox K (min r L) L s where
 toFun θ:=∑ c:CoefficientIndex D w L s,
   θ c • boundedBlockEntry K D w L s x u₀ u₁ c r
 map_add' θ η:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a θ:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]
theorem full_contactRankBound_eq (r m L s:ℕ):
   contactRankBound (min r L) L s (m-r)=
     contactRankBound (min r L) L s (min (r+1) (m-r)):=by
 by_cases h:r+1 ≤ m-r
 · have hM:min r L ≤ r:=min_le_left r L
   have hzero:min r L+1-(m-r)=0:=by omega
   have hzero':min r L+1-(r+1)=0:=by omega
   simp only [Nat.min_eq_left h,contactRankBound,blockKernelLowerBound,
     hzero,hzero',Finset.range_zero,Finset.sum_empty,mul_zero,Nat.sub_zero]
 · have h':m-r ≤ r+1:=by omega
   rw [Nat.min_eq_right h']
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 have hh:=blockJet_rank_le_contactRankBound K (min r.val L) L s (m-r.val)
   (min_le_right r.val L)
 rw [full_contactRankBound_eq] at hh
 exact hh
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
theorem globalTarget_finrank_le {I:Type*} [Fintype I] (m L s:ℕ):
   Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
 change Module.finrank K (I → LocalTarget K m L s) ≤ _
 rw [Module.finrank_pi_fintype]
 calc
   (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
       ∑ _i:I,localRankBound m L s:=by
     apply Finset.sum_le_sum
     intro i hi
     exact localTarget_finrank_le K m L s
   _=Fintype.card I*localRankBound m L s:=by simp
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
theorem constraintMap_apply {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (θ:CoefficientIndex D w L s → K) (i:I) (r:Fin m):
   ((constraintMap K D w L s m nodes u₀ u₁ θ i r):Poly K)=
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K):=rfl
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,
     θ≠0∧constraintMap K D w L s m nodes u₀ u₁ θ=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective (constraintMap K D w L s m nodes u₀ u₁):=by
   intro θ η heq
   by_contra hne
   apply hnone
   refine ⟨θ-η,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have hupper:=globalTarget_finrank_le K (I:=I) m L s
 exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)
theorem exists_nonzero_block_equations {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,θ≠0∧
     ∀ (i:I) (r:Fin m),
       contactJet K (m-r.val)
         ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0:=by
 obtain ⟨θ,hθ,hzero⟩:=exists_nonzero_kernel_array K D w L s m nodes u₀ u₁ hgate
 refine ⟨θ,hθ,?_⟩
 intro i r
 have hh:=congrArg (fun t:GlobalTarget K I m L s => ((t i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0 at hh
 exact hh
theorem all_blocks_divisible_of_equations
   (D w L s m:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K)
   (h:∀ r:Fin m,contactJet K (m-r.val)
     ((extractBlock K D w L s x u₀ u₁ r.val θ):Poly K)=0):
   ∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 intro r
 by_cases hr:r < m
 · exact (contactJet_eq_zero_iff K (m-r) _).mp (h ⟨r,hr⟩)
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
abbrev FrozenCoefficientIndex:=CoefficientIndex 3324960 131071 176 5
theorem exists_frozen_nonzero_contact_array
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ θ:FrozenCoefficientIndex → IRSProfile.Field,θ≠0∧
     ∀ (i:IRSProfile.Index) (r:Fin 18),
       contactJet IRSProfile.Field (18-r.val)
         ((extractBlock IRSProfile.Field 3324960 131071 176 5
           (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ):Poly IRSProfile.Field)=0:=by
 apply exists_nonzero_block_equations IRSProfile.Field 3324960 131071 176 5 18
   (fun i:IRSProfile.Index => IRSProfile.domain i) u₀ u₁
 rw [show Fintype.card IRSProfile.Index=262144 by norm_num [IRSProfile.Index]]
 exact RCN051.interpolation_gate
theorem exists_frozen_nonzero_polynomial_and_equations
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ (Q:MvPolynomial (Fin 4) IRSProfile.Field)
     (θ:FrozenCoefficientIndex → IRSProfile.Field),
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field 3324960 131071 176 5∧
     Q=reconstruct IRSProfile.Field 3324960 131071 176 5 θ∧
     ∀ (i:IRSProfile.Index) (r:Fin 18),
       contactJet IRSProfile.Field (18-r.val)
         ((extractBlock IRSProfile.Field 3324960 131071 176 5
           (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ):Poly IRSProfile.Field)=0:=by
 obtain ⟨θ,hθ,hconstraints⟩:=exists_frozen_nonzero_contact_array u₀ u₁
 exact ⟨reconstruct IRSProfile.Field 3324960 131071 176 5 θ,θ,
   reconstruct_ne_zero IRSProfile.Field 3324960 131071 176 5 θ hθ,
   reconstruct_mem_globalCoefficientBox IRSProfile.Field 3324960 131071 176 5 θ,
   rfl,hconstraints⟩
end
end ProximityPrize.SubmissionLower.RCN174
end PackedLegacy_Q

/-! Packed from ProximityPrize.SubmissionLower.DC. -/
section PackedLegacy_DC
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubstitutionVanish
noncomputable def specializeZ {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F):
   Polynomial (Polynomial F):=
 Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q
noncomputable def triEval {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F) (P:Polynomial F):
   Polynomial F:=Polynomial.eval P (specializeZ Q z)
lemma map_comp_X_add_C {F:Type*} [Field F]
   (A:Polynomial (Polynomial F)) (x:Polynomial F) (z:F):
   Polynomial.map (Polynomial.evalRingHom z)
       (A.comp (Polynomial.X+Polynomial.C x))=
     (Polynomial.map (Polynomial.evalRingHom z) A).comp
       (Polynomial.X+Polynomial.C (Polynomial.eval z x)):=by
 rw [Polynomial.map_comp]
 simp
lemma specializeZ_shift {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (x y:Polynomial F) (z:F):
   specializeZ (Polynomial.Bivariate.shift Q x y) z=
     Polynomial.Bivariate.shift (specializeZ Q z)
       (Polynomial.eval z x) (Polynomial.eval z y):=by
 induction Q using Polynomial.induction_on' with
 | add Q R hQ hR =>
     calc
       specializeZ (Polynomial.Bivariate.shift (Q+R) x y) z=
           specializeZ (Polynomial.Bivariate.shift Q x y) z+
             specializeZ (Polynomial.Bivariate.shift R x y) z:=by
               simp [Polynomial.Bivariate.shift,specializeZ]
       _=Polynomial.Bivariate.shift (specializeZ Q z)
             (Polynomial.eval z x) (Polynomial.eval z y)+
           Polynomial.Bivariate.shift (specializeZ R z)
             (Polynomial.eval z x) (Polynomial.eval z y):=by rw [hQ,hR]
       _=Polynomial.Bivariate.shift (specializeZ (Q+R) z)
             (Polynomial.eval z x) (Polynomial.eval z y):=by
               simp [Polynomial.Bivariate.shift,specializeZ]
 | monomial n A =>
     simp [Polynomial.Bivariate.shift,specializeZ,Polynomial.monomial_comp,
       Polynomial.map_monomial,map_comp_X_add_C]
lemma comp_eval_eq_shift_eval_tail {F:Type*} [Field F]
   (B:Polynomial (Polynomial F)) (P:Polynomial F) (ω y:F):
   (Polynomial.eval P B).comp (Polynomial.X+Polynomial.C ω)=
     Polynomial.eval (P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y)
       (Polynomial.Bivariate.shift B ω y):=by
 induction B using Polynomial.induction_on' with
 | add B C hB hC =>
     calc
       (Polynomial.eval P (B+C)).comp (Polynomial.X+Polynomial.C ω)=
           (Polynomial.eval P B).comp (Polynomial.X+Polynomial.C ω)+
             (Polynomial.eval P C).comp (Polynomial.X+Polynomial.C ω):=by simp
       _=Polynomial.eval (P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y)
             (Polynomial.Bivariate.shift B ω y)+
           Polynomial.eval (P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y)
             (Polynomial.Bivariate.shift C ω y):=by rw [hB,hC]
       _=Polynomial.eval (P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y)
             (Polynomial.Bivariate.shift (B+C) ω y):=by
               simp [Polynomial.Bivariate.shift]
 | monomial n A =>
     simp [Polynomial.Bivariate.shift,Polynomial.monomial_comp,
       Polynomial.eval_monomial,Polynomial.map_mul,Polynomial.map_pow,
       Polynomial.map_C,Polynomial.coe_compRingHom_apply]
lemma X_dvd_comp_sub_C_eval {F:Type*} [Field F]
   (P:Polynomial F) (ω y:F) (hmatch:Polynomial.eval ω P=y):
   Polynomial.X∣P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y:=by
 rw [Polynomial.X_dvd_iff,Polynomial.coeff_zero_eq_eval_zero,
   Polynomial.eval_sub,Polynomial.eval_comp]
 simp [hmatch]
lemma X_pow_dvd_mul_pow_of_total_coeff_zero {F:Type*} [Field F]
   {A U:Polynomial F} {m b:Nat}
   (hU:Polynomial.X∣U)
   (hzero:∀ a,a+b < m → A.coeff a=0):
   Polynomial.X^m∣A*U^b:=by
 by_cases hb:b < m
 · have hA:Polynomial.X^(m-b)∣A:=by
     rw [Polynomial.X_pow_dvd_iff]
     intro d hd
     exact hzero d (by omega)
   have hUb:Polynomial.X^b∣U^b:=pow_dvd_pow_of_dvd hU b
   rcases hA with ⟨A',hA'⟩
   rcases hUb with ⟨U',hU'⟩
   refine ⟨A'*U',?_⟩
   rw [hA',hU']
   ring_nf
   rw [←pow_add]
   have hmb:m-b+b=m:=Nat.sub_add_cancel (Nat.le_of_lt hb)
   rw [hmb]
 · have hbm:m ≤ b:=Nat.le_of_not_gt hb
   have hXb:(Polynomial.X:Polynomial F)^m∣Polynomial.X^b:=
     pow_dvd_pow Polynomial.X hbm
   have hUb:Polynomial.X^b∣U^b:=pow_dvd_pow_of_dvd hU b
   exact dvd_mul_of_dvd_right (dvd_trans hXb hUb) A
lemma X_pow_dvd_eval_of_total_coeff_zero {F:Type*} [Field F]
   {B:Polynomial (Polynomial F)} {U:Polynomial F} {m:Nat}
   (hU:Polynomial.X∣U)
   (hzero:∀ a b,a+b < m → (B.coeff b).coeff a=0):
   Polynomial.X^m∣Polynomial.eval U B:=by
 rw [Polynomial.eval_eq_sum]
 apply Finset.dvd_sum
 intro b hb
 exact X_pow_dvd_mul_pow_of_total_coeff_zero (m:=m) (b:=b) hU
   (fun a ha => hzero a b ha)
lemma specialize_shift_total_coeff_zero {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (ω z:F) (yZ:Polynomial F)
   (m:Nat)
   (hvan:∀ s t h,s+t < m →
     ((((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s).coeff h)=0):
   ∀ s t,s+t < m →
     (((Polynomial.Bivariate.shift (specializeZ Q z) ω (Polynomial.eval z yZ)).coeff t).coeff s)=0:=by
 intro s t hst
 have hpoly:
     ((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s=0:=by
   apply Polynomial.ext
   intro h
   exact hvan s t h hst
 have hshift:=specializeZ_shift Q (Polynomial.C ω) yZ z
 simp only [Polynomial.eval_C] at hshift
 rw [←hshift]
 simp [specializeZ,hpoly]
theorem rootMultiplicity_triEval_ge_of_shift_coeff_zero
   {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (ω z:F)
   (yZ P:Polynomial F) (m:Nat)
   (hvan:∀ s t h,s+t < m →
     ((((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s).coeff h)=0)
   (hmatch:Polynomial.eval ω P=Polynomial.eval z yZ)
   (hne:triEval Q z P≠0):
   m ≤ (triEval Q z P).rootMultiplicity ω:=by
 let y:=Polynomial.eval z yZ
 let B:=specializeZ Q z
 let U:=P.comp (Polynomial.X+Polynomial.C ω)-Polynomial.C y
 have hzero:∀ a b,a+b < m →
     (((Polynomial.Bivariate.shift B ω y).coeff b).coeff a)=0:=by
   exact specialize_shift_total_coeff_zero Q ω z yZ m hvan
 have hU:Polynomial.X∣U:=
   X_dvd_comp_sub_C_eval P ω y (by simpa [y] using hmatch)
 have hdvd:Polynomial.X^m∣
     (triEval Q z P).comp (Polynomial.X+Polynomial.C ω):=by
   rw [show triEval Q z P=Polynomial.eval P B by rfl]
   rw [comp_eval_eq_shift_eval_tail B P ω y]
   exact X_pow_dvd_eval_of_total_coeff_zero hU hzero
 rw [Polynomial.rootMultiplicity_eq_rootMultiplicity]
 have hshiftne:
     (triEval Q z P).comp (Polynomial.X+Polynomial.C ω)≠0:=by
   exact (Polynomial.comp_X_add_C_eq_zero_iff.not.mpr hne)
 rw [Polynomial.le_rootMultiplicity_iff hshiftne]
 simpa using hdvd
theorem mul_card_le_natDegree_of_rootMultiplicity
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (R:Polynomial F) (ω:ι ↪ F) (A:Finset ι) (m:Nat)
   (hmult:∀ i∈A,m ≤ R.rootMultiplicity (ω i)):
   m*A.card ≤ R.natDegree:=by
 let xs:Finset F:=A.map ω
 have hselected:
     ∑ x∈xs,Multiset.count x R.roots ≤ R.roots.card:=by
   let all:=xs ∪ R.roots.toFinset
   calc
     ∑ x∈xs,Multiset.count x R.roots ≤
         ∑ x∈all,Multiset.count x R.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ x∈R.roots.toFinset,Multiset.count x R.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro x hxall hxroots
       exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
     _=R.roots.card:=Multiset.toFinset_sum_count_eq R.roots
 calc
   m*A.card=∑ i∈A,m:=by simp [Nat.mul_comm]
   _ ≤ ∑ i∈A,R.rootMultiplicity (ω i):=
     Finset.sum_le_sum fun i hi => hmult i hi
   _=∑ x∈xs,R.rootMultiplicity x:=by
     symm
     exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
   _=∑ x∈xs,Multiset.count x R.roots:=by
     apply Finset.sum_congr rfl
     intro x hx
     exact (Polynomial.count_roots R).symm
   _ ≤ R.roots.card:=hselected
   _ ≤ R.natDegree:=Polynomial.card_roots' R
theorem triEval_eq_zero_of_many_shift_vanishing
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F)
   (P:Polynomial F) (ω:ι ↪ F) (A:Finset ι)
   (yZ:ι → Polynomial F) (m DX:Nat)
   (hvan:∀ i∈A,∀ s t h,s+t < m →
     ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h)=0)
   (hmatch:∀ i∈A,Polynomial.eval (ω i) P=Polynomial.eval z (yZ i))
   (hdegree:(triEval Q z P).natDegree ≤ DX)
   (hmany:DX < m*A.card):
   triEval Q z P=0:=by
 by_contra hne
 have hmult:∀ i∈A,m ≤ (triEval Q z P).rootMultiplicity (ω i):=by
   intro i hi
   exact rootMultiplicity_triEval_ge_of_shift_coeff_zero
     Q (ω i) z (yZ i) P m (hvan i hi) (hmatch i hi) hne
 have hrootdeg:=mul_card_le_natDegree_of_rootMultiplicity
   (triEval Q z P) ω A m hmult
 omega
theorem triEval_natDegree_le_of_weighted_X_cap
   {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F) (P:Polynomial F)
   (k DX:Nat) (hP:P.natDegree ≤ k)
   (hcap:∀ j a,((Q.coeff j).coeff a)≠0 → a+k*j ≤ DX):
   (triEval Q z P).natDegree ≤ DX:=by
 rw [triEval,Polynomial.eval_eq_sum]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro j hj
 let A:Polynomial F:=(specializeZ Q z).coeff j
 have hAeq:A=Polynomial.map (Polynomial.evalRingHom z) (Q.coeff j):=by
   simp [A,specializeZ]
 have hA0:A≠0:=by
   exact Polynomial.mem_support_iff.mp hj
 have hAdeg:A.natDegree+k*j ≤ DX:=by
   have hlead:A.coeff A.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hA0
   have horig:(Q.coeff j).coeff A.natDegree≠0:=by
     intro horig0
     apply hlead
     calc
       A.coeff A.natDegree=
           Polynomial.eval z ((Q.coeff j).coeff A.natDegree):=by
         rw [hAeq,Polynomial.coeff_map]
         rfl
       _=0:=by rw [horig0];simp
   exact hcap j A.natDegree horig
 calc
   (A*P^j).natDegree ≤ A.natDegree+(P^j).natDegree:=
     Polynomial.natDegree_mul_le
   _ ≤ A.natDegree+j*k:=by
     exact Nat.add_le_add_left (Polynomial.natDegree_pow_le_of_le j hP) A.natDegree
   _=A.natDegree+k*j:=by rw [Nat.mul_comm j k]
   _ ≤ DX:=hAdeg
theorem triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F)
   (P:Polynomial F) (ω:ι ↪ F) (A:Finset ι)
   (yZ:ι → Polynomial F) (m k DX:Nat)
   (hvan:∀ i∈A,∀ s t h,s+t < m →
     ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h)=0)
   (hmatch:∀ i∈A,Polynomial.eval (ω i) P=Polynomial.eval z (yZ i))
   (hP:P.natDegree ≤ k)
   (hcap:∀ j a,((Q.coeff j).coeff a)≠0 → a+k*j ≤ DX)
   (hmany:DX < m*A.card):
   triEval Q z P=0:=by
 apply triEval_eq_zero_of_many_shift_vanishing Q z P ω A yZ m DX
   hvan hmatch (triEval_natDegree_le_of_weighted_X_cap Q z P k DX hP hcap) hmany
end BCHKSSubstitutionVanish
end ProximityPrize.SubmissionLower
end PackedLegacy_DC

/-! Packed from ProximityPrize.SubmissionLower.C6. -/
section PackedLegacy_C6
namespace ProximityPrize.SubmissionLower.RCN185
open Polynomial
section LocalRing
variable {F:Type*} [CommRing F]
theorem shifted_power_dvd_iff_taylor_coeff_zero
   (P:F[X]) (x:F) (h:ℕ):
   (Polynomial.X-Polynomial.C x)^h∣P ↔
     ∀ j < h,(taylor x P).coeff j=0:=by
 have hshift:taylor x ((Polynomial.X-Polynomial.C x)^h)=
     (Polynomial.X:F[X])^h:=by
   rw [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right]
 have hdiv:=map_dvd_iff (taylorEquiv x)
   (a:=((Polynomial.X:F[X])-Polynomial.C x)^h) (b:=P)
 change taylor x ((Polynomial.X-Polynomial.C x)^h)∣taylor x P ↔
   (Polynomial.X-Polynomial.C x)^h∣P at hdiv
 rw [hshift] at hdiv
 exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f:=taylor x P) (n:=h))
noncomputable def contactResidual (P:F[X]) (x:F):F[X]:=
 taylor x P-Polynomial.C (P.eval x)-
   Polynomial.X*taylor x P.derivative
theorem X_sq_dvd_contactResidual (P:F[X]) (x:F):
   (Polynomial.X:F[X])^2∣contactResidual P x:=by
 rw [X_pow_dvd_iff]
 intro j hj
 have hcases:j=0∨j=1:=by omega
 rcases hcases with rfl | rfl
 · simp [contactResidual]
 · simp [contactResidual,coeff_X_mul]
theorem contact_monomial_dvd
   (A S R:F[X]) (m i j k:ℕ)
   (hS:(Polynomial.X:F[X])^2∣S) (hweight:m ≤ i+2*j):
   (Polynomial.X:F[X])^m∣A*Polynomial.X^i*S^j*R^k:=by
 have hSj:(Polynomial.X:F[X])^(2*j)∣S^j:=by
   simpa only [pow_mul] using pow_dvd_pow_of_dvd hS j
 have hprod:(Polynomial.X:F[X])^i*Polynomial.X^(2*j)∣
     Polynomial.X^i*S^j:=
   mul_dvd_mul (dvd_refl _) hSj
 have hsum:(Polynomial.X:F[X])^(i+2*j)∣
     Polynomial.X^i*S^j:=by
   simpa only [pow_add] using hprod
 have hsmall:(Polynomial.X:F[X])^m∣Polynomial.X^i*S^j:=
   (pow_dvd_pow Polynomial.X hweight).trans hsum
 have hleft:(Polynomial.X:F[X])^m∣A*(Polynomial.X^i*S^j):=
   dvd_mul_of_dvd_right hsmall A
 have hright:(Polynomial.X:F[X])^m∣
     (A*(Polynomial.X^i*S^j))*R^k:=
   dvd_mul_of_dvd_left hleft (R^k)
 simpa only [mul_assoc] using hright
theorem contact_sum_dvd
   {J:Type*} (terms:Finset J) (coefficient:J → F[X])
   (tExp sExp rExp:J → ℕ) (S R:F[X]) (m:ℕ)
   (hS:(Polynomial.X:F[X])^2∣S)
   (hweight:∀ b∈terms,m ≤ tExp b+2*sExp b):
   (Polynomial.X:F[X])^m∣
     ∑ b∈terms,coefficient b*Polynomial.X^tExp b*S^sExp b*R^rExp b:=by
 apply Finset.dvd_sum
 intro b hb
 exact contact_monomial_dvd (coefficient b) S R m
   (tExp b) (sExp b) (rExp b) hS (hweight b hb)
end LocalRing
section GlobalVanishing
variable {F I J:Type*} [Field F] [DecidableEq F] [DecidableEq I]
theorem eq_zero_of_contact_representations
   (P H:F[X]) (nodes:I ↪ F) (support:Finset I) (m:ℕ)
   (terms:I → Finset J) (coefficient:I → J → F[X])
   (tExp sExp rExp:I → J → ℕ)
   (hweight:∀ i∈support,∀ b∈terms i,
     m ≤ tExp i b+2*sExp i b)
   (hrepresentation:∀ i∈support,
     taylor (nodes i) H=
       ∑ b∈terms i,coefficient i b*Polynomial.X^tExp i b*
         (contactResidual P (nodes i))^sExp i b*
         (taylor (nodes i) P.derivative)^rExp i b)
   (hdegree:H.natDegree < m*support.card):H=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,m ≤ H.rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:(Polynomial.X:F[X])^m∣taylor (nodes i) H:=by
     rw [hrepresentation i hi]
     exact contact_sum_dvd (terms i) (coefficient i) (tExp i) (sExp i)
       (rExp i) (contactResidual P (nodes i))
       (taylor (nodes i) P.derivative) m
       (X_sq_dvd_contactResidual P (nodes i)) (hweight i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣H:=
     (shifted_power_dvd_iff_taylor_coeff_zero H (nodes i) m).mpr
       (X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hbound:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   H nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hbound
end GlobalVanishing
end ProximityPrize.SubmissionLower.RCN185
end PackedLegacy_C6

/-! Packed from ProximityPrize.SubmissionLower.K. -/
section PackedLegacy_K
namespace ProximityPrize.SubmissionLower.RCN319
open RCN256 RCN174 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
abbrev LocalPolynomial:=Polynomial (Poly K)
def translationVariables (x u₀ u₁:K):Fin 4 → LocalPolynomial K:=
 ![Polynomial.X+Polynomial.C (MvPolynomial.C x),
   Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
     Polynomial.C (seedAffine K u₀ u₁),
   Polynomial.C (MvPolynomial.X 1),
   Polynomial.C (MvPolynomial.X 2)]
def homogenizedTranslation (x u₀ u₁:K):
   MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K:=
 MvPolynomial.aeval (translationVariables K x u₀ u₁)
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val*
       MvPolynomial.X 3^c.2.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j z:ℕ):
   localMonomial K f j z=
     MvPolynomial.X 0^f*MvPolynomial.X 1^j*MvPolynomial.X 2^z:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.X_pow_eq_monomial]
theorem coeff_shifted_affine_product
   {A:Type*} [CommRing A] (x a y b:A) (e i r:ℕ):
   (((Polynomial.X+Polynomial.C x)^e*
       (Polynomial.X*Polynomial.C y+Polynomial.C a)^i*
       Polynomial.C b):Polynomial A).coeff r=
     ∑ f:Fin (i+1),if f.val ≤ r then
       (x^(e-(r-f.val))*(e.choose (r-f.val):A))*
         (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b)
     else 0:=by
 rw [add_pow (Polynomial.X*Polynomial.C y) (Polynomial.C a) i,
   Finset.mul_sum,Finset.sum_mul,Polynomial.finsetSum_coeff]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro f hf
 have hfactor:
     (((Polynomial.X+Polynomial.C x)^e*
       ((Polynomial.X*Polynomial.C y)^f.val*
         Polynomial.C a^(i-f.val)*(i.choose f.val:Polynomial A)))*
         Polynomial.C b)=
       (((Polynomial.X+Polynomial.C x)^e*
         Polynomial.C (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b))*
         Polynomial.X^f.val):=by
   simp only [mul_pow,map_mul,map_pow,map_natCast]
   ring
 rw [hfactor,Polynomial.coeff_mul_X_pow']
 split_ifs with hfr
 · rw [Polynomial.coeff_mul_C,Polynomial.coeff_X_add_C_pow]
 · rfl
theorem translation_column (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K):
   homogenizedTranslation K x u₀ u₁ (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       (Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
       (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
         Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
       Polynomial.C (MvPolynomial.X 1)^c.2.1.val*
       Polynomial.C (MvPolynomial.X 2)^c.2.2.1.val:=by
 rw [columnMonomial_eq K D w L s c a]
 simp [homogenizedTranslation,translationVariables,
   Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
theorem translation_column_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u₀ u₁ c r:=by
 have hfactor:
     homogenizedTranslation K x u₀ u₁
       (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       ((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
         (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
           Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
         Polynomial.C (MvPolynomial.X 1^c.2.1.val*
           MvPolynomial.X 2^c.2.2.1.val)):=by
   rw [translation_column K D w L s x u₀ u₁ c a]
   simp only [map_mul,map_pow]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,
     map_mul,map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁ (reconstruct K D w L s θ)).coeff r=
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
   θ c • blockEntry K D w L s x u₀ u₁ c r)=
     (((∑ c:CoefficientIndex D w L s,
       θ c • boundedBlockEntry K D w L s x u₀ u₁ c r):
         coefficientBox K (min r L) L s):Poly K)
 simp [boundedBlockEntry]
theorem exists_frozen_translated_contact_interpolant
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧Q∈globalCoefficientBox IRSProfile.Field 3324960 131071 176 5∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(18-r)∣
         (homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (u₀ i) (u₁ i) Q).coeff r:=by
 obtain ⟨Q,θ,hQ,hcaps,hreconstruct,hequations⟩:=
   exists_frozen_nonzero_polynomial_and_equations u₀ u₁
 refine ⟨Q,hQ,hcaps,?_⟩
 intro i r
 rw [hreconstruct,translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations IRSProfile.Field 3324960 131071 176 5 18
   (IRSProfile.domain i) (u₀ i) (u₁ i) θ (hequations i) r
def contactEvaluation (R B:Polynomial K) (γ:K):Poly K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![R+Polynomial.X*B,R,Polynomial.C γ]
def outerEvaluation (R B:Polynomial K) (γ:K):
   LocalPolynomial K →+*Polynomial K:=
 Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X
@[simp] theorem contactEvaluation_slopeDifference (R B:Polynomial K) (γ:K):
   contactEvaluation K R B γ (slopeDifference K)=Polynomial.X*B:=by
 simp [contactEvaluation,slopeDifference]
theorem contactEvaluation_seedAffine (R B:Polynomial K) (γ u₀ u₁:K):
   contactEvaluation K R B γ (seedAffine K u₀ u₁)=
     Polynomial.C (u₀+γ*u₁):=by
 rw [seedAffine, ←MvPolynomial.C_mul_X_eq_monomial]
 simp [contactEvaluation,Polynomial.algebraMap_eq,mul_comm]
theorem outerEvaluation_contact_dvd
   (H:LocalPolynomial K) (m:ℕ) (R B:Polynomial K) (γ:K)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣H.coeff r):
   (Polynomial.X:Polynomial K)^m∣outerEvaluation K R B γ H:=by
 classical
 change (Polynomial.X:Polynomial K)^m∣
   H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
 rw [Polynomial.eval₂_eq_sum]
 change (Polynomial.X:Polynomial K)^m∣
   ∑ r∈H.support,contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r
 apply Finset.dvd_sum
 intro r hr
 have hlocal:(Polynomial.X:Polynomial K)^(m-r)∣
     contactEvaluation K R B γ (H.coeff r):=by
   obtain ⟨q,hq⟩:=hcoeff r
   refine ⟨B^(m-r)*contactEvaluation K R B γ q,?_⟩
   simp only [hq,map_mul,map_pow,contactEvaluation_slopeDifference,
     mul_pow,mul_assoc]
 have hprod:=mul_dvd_mul hlocal
   (dvd_refl ((Polynomial.X:Polynomial K)^r))
 have htotal:(Polynomial.X:Polynomial K)^((m-r)+r)∣
     contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r:=by
   simpa only [pow_add] using hprod
 exact (pow_dvd_pow Polynomial.X (show m ≤ (m-r)+r by omega)).trans htotal
def specialization (P:Polynomial K) (γ:K):
   MvPolynomial (Fin 4) K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![Polynomial.X,P,P.derivative,Polynomial.C γ]
theorem outerEvaluation_translation
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (B:Polynomial K)
   (hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B)):
   outerEvaluation K (Polynomial.taylor x P.derivative) B γ
       (homogenizedTranslation K x u₀ u₁ Q)=
     Polynomial.taylor x (specialization K P γ Q):=by
 have hhom:
     (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
       (homogenizedTranslation K x u₀ u₁).toRingHom=
     (Polynomial.taylorAlgHom x).toRingHom.comp
       (specialization K P γ).toRingHom:=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
       homogenizedTranslation,specialization,Polynomial.algebraMap_apply,
       MvPolynomial.algebraMap_eq]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
         homogenizedTranslation,translationVariables,specialization,
         seedAffine,MvPolynomial.aeval_monomial,Polynomial.algebraMap_apply,
         MvPolynomial.algebraMap_eq,hP] <;> ring
 exact DFunLike.congr_fun hhom Q
theorem X_pow_dvd_taylor_specialization
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (m:ℕ)
   (hvalue:P.eval x=u₀+γ*u₁)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K x u₀ u₁ Q).coeff r):
   (Polynomial.X:Polynomial K)^m∣
     Polynomial.taylor x (specialization K P γ Q):=by
 obtain ⟨B,hB⟩:=RCN185.X_sq_dvd_contactResidual P x
 have hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B):=by
   change Polynomial.taylor x P-Polynomial.C (P.eval x)-
     Polynomial.X*Polynomial.taylor x P.derivative=Polynomial.X^2*B at hB
   rw [hvalue] at hB
   linear_combination hB
 have hh:=outerEvaluation_contact_dvd K
   (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
 rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
 exact hh
theorem specialization_eq_zero_of_contact_and_degree
   [DecidableEq K] {I:Type*} [DecidableEq I]
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (nodes:I ↪ K) (u₀ u₁:I → K) (support:Finset I) (m:ℕ)
   (hcontact:∀ i∈support,∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
   (hvalues:∀ i∈support,P.eval (nodes i)=u₀ i+γ*u₁ i)
   (hdegree:(specialization K P γ Q).natDegree < m*support.card):
   specialization K P γ Q=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,
     m ≤ (specialization K P γ Q).rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:=X_pow_dvd_taylor_specialization K Q P
     (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣
       specialization K P γ Q:=
     (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
       (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   (specialization K P γ Q) nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hh
theorem monomial_eq (d:Fin 4 →₀ ℕ) (a:K):
   MvPolynomial.monomial d a=
     MvPolynomial.C a*MvPolynomial.X 0^d 0*MvPolynomial.X 1^d 1*
       MvPolynomial.X 2^d 2*MvPolynomial.X 3^d 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem specialization_monomial
   (P:Polynomial K) (γ:K) (d:Fin 4 →₀ ℕ) (a:K):
   specialization K P γ (MvPolynomial.monomial d a)=
     Polynomial.C a*Polynomial.X^d 0*P^d 1*P.derivative^d 2*
       Polynomial.C γ^d 3:=by
 rw [monomial_eq K d a]
 simp [specialization,Polynomial.algebraMap_eq]
theorem specialization_monomial_natDegree_le
   (P:Polynomial K) (γ:K) (w:ℕ) (hP:P.natDegree ≤ w)
   (d:Fin 4 →₀ ℕ) (a:K):
   (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
     d 0+w*d 1+(w-1)*d 2:=by
 rw [specialization_monomial]
 have hc:(Polynomial.C a:Polynomial K).natDegree ≤ 0:=by simp
 have hx:((Polynomial.X:Polynomial K)^d 0).natDegree ≤ d 0:=by simp
 have hy:(P^d 1).natDegree ≤ d 1*w:=
   Polynomial.natDegree_pow_le_of_le (d 1) hP
 have hderiv:P.derivative.natDegree ≤ w-1:=
   (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
 have hr:(P.derivative^d 2).natDegree ≤ d 2*(w-1):=
   Polynomial.natDegree_pow_le_of_le (d 2) hderiv
 have hz:((Polynomial.C γ:Polynomial K)^d 3).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
     (show (Polynomial.C γ:Polynomial K).natDegree ≤ 0 by simp)
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le
     (Polynomial.natDegree_mul_le_of_le
       (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
 simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_comm] using hh
theorem specialization_natDegree_lt
   (D w L s:ℕ) (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (hD:0 < D) (hcaps:Q∈globalCoefficientBox K D w L s)
   (hP:P.natDegree ≤ w):
   (specialization K P γ Q).natDegree < D:=by
 classical
 have hsupport:∀ d∈Q.support,
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=hcaps
 have hterms:∀ d∈Q.support,
     (specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤
       D-1:=by
   intro d hd
   have hweight:=(hsupport d hd).2.2
   have hh:=specialization_monomial_natDegree_le K P γ w hP d (MvPolynomial.coeff d Q)
   omega
 rw [MvPolynomial.as_sum Q,map_sum]
 have hh:=Polynomial.natDegree_sum_le_of_forall_le Q.support
   (fun d => specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
 exact lt_of_le_of_lt hh (by omega)
theorem exists_frozen_universal_vanishing_interpolant
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧Q∈globalCoefficientBox IRSProfile.Field 3324960 131071 176 5∧
     ∀ (γ:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ 131071 → 184720 ≤ support.card →
       (∀ i∈support,P.eval (IRSProfile.domain i)=u₀ i+γ*u₁ i) →
       specialization IRSProfile.Field P γ Q=0:=by
 classical
 obtain ⟨Q,hQ,hcaps,hcontact⟩:=exists_frozen_translated_contact_interpolant u₀ u₁
 refine ⟨Q,hQ,hcaps,?_⟩
 intro γ P support hP hcard hvalues
 apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P γ
   IRSProfile.domain u₀ u₁ support 18
 · intro i hi r
   exact hcontact i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt IRSProfile.Field
     3324960 131071 176 5 Q P γ (by decide) hcaps hP
   have hbound:3324960 ≤ 18*support.card:=by omega
   exact hdegree.trans_le hbound
end
end ProximityPrize.SubmissionLower.RCN319
end PackedLegacy_K

/-! Packed from ProximityPrize.SubmissionLower.BJ. -/
section PackedLegacy_BJ
namespace ProximityPrize.SubmissionLower.RCN139
open RCN077 RCN269 RCN233 RCN347 RCN174 RCN319
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem derivative_taylor (r:L) (P:Polynomial L):
   (Polynomial.taylor r P).derivative=Polynomial.taylor r P.derivative:=by
 simp [Polynomial.taylor_apply,Polynomial.derivative_comp]
theorem taylor_reconstruction_eq_specialization
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L) (P:Polynomial L):
   Polynomial.taylor (-(v 0))
       (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
         (reconstructionSubstitution v P) F)=
     specialization L (Polynomial.taylor (-(v 0)) P) (v 3)
       (MvPolynomial.map coefficients F):=by
 have hhom:
     (Polynomial.taylorAlgHom (-(v 0))).toRingHom.comp
         (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
           (reconstructionSubstitution v P))=
       (specialization L (Polynomial.taylor (-(v 0)) P) (v 3)).toRingHom.comp
         (MvPolynomial.map coefficients):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,reconstructionSubstitution,specialization]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,reconstructionSubstitution,specialization,
         derivative_taylor]
 exact DFunLike.congr_fun hhom F
theorem map_mem_globalCoefficientBox
   (coefficients:K →+*L) (F:Poly4 K) (bound w seedCap slopeCap:ℕ)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   MvPolynomial.map coefficients F∈globalCoefficientBox L bound w seedCap slopeCap:=by
 intro d hd
 exact hcaps (MvPolynomial.support_map_subset coefficients F hd)
noncomputable def globalPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 Polynomial.taylor (-(v 0)) (reconstructedPolynomial coefficients F v hF hregular w)
theorem globalPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).natDegree ≤ w:=by
 simpa only [globalPolynomial,Polynomial.natDegree_taylor] using
   reconstructedPolynomial_natDegree_le coefficients F v hF hregular w
theorem globalPolynomial_eval
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (x:L):
   (globalPolynomial coefficients F v hF hregular w).eval x=
     (reconstructedPolynomial coefficients F v hF hregular w).eval (x-v 0):=by
 simp only [globalPolynomial,Polynomial.taylor_eval,sub_eq_add_neg]
theorem globalPolynomial_initial_value
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).eval (v 0)=v 1:=by
 rw [globalPolynomial_eval,sub_self, ←Polynomial.taylor_coeff_zero (0:L),
   Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_zero coefficients F v hF hregular w
theorem globalPolynomial_initial_slope
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (globalPolynomial coefficients F v hF hregular w).derivative.eval (v 0)=v 2:=by
 rw [globalPolynomial,derivative_taylor,Polynomial.taylor_eval,add_neg_cancel]
 rw [←Polynomial.taylor_coeff_one (0:L),Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_one coefficients F v hF hregular w hw
theorem reconstructedEquation_natDegree_lt
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (bound w seedCap slopeCap:ℕ) (hbound:0 < bound)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   (reconstructedEquation coefficients F v hF hregular w).natDegree < bound:=by
 have hdeg:=specialization_natDegree_lt L bound w seedCap slopeCap
   (MvPolynomial.map coefficients F) (globalPolynomial coefficients F v hF hregular w)
   (v 3) hbound (map_mem_globalCoefficientBox coefficients F bound w seedCap slopeCap hcaps)
   (globalPolynomial_natDegree_le coefficients F v hF hregular w)
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,Polynomial.natDegree_taylor] at hdeg
 exact hdeg
theorem global_polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 have hdegree:=reconstructedEquation_natDegree_lt coefficients F v hF hregular
   bound w seedCap slopeCap (by omega) hcaps
 have hzero:=polynomiality_of_all_tails coefficients F v hF hregular p bound w
   hw hshort hchar htails hdegree
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,hzero,map_zero]
theorem exists_global_polynomial_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   ∃ P:Polynomial L,P.natDegree ≤ w∧
     specialization L P (v 3) (MvPolynomial.map coefficients F)=0∧
     P.eval (v 0)=v 1∧P.derivative.eval (v 0)=v 2:=by
 refine ⟨globalPolynomial coefficients F v hF hregular w,
   globalPolynomial_natDegree_le coefficients F v hF hregular w,?_,
   globalPolynomial_initial_value coefficients F v hF hregular w,
   globalPolynomial_initial_slope coefficients F v hF hregular w hw⟩
 exact global_polynomiality_of_all_tails coefficients F v hF hregular p bound w seedCap
   slopeCap hw hshort hchar hcaps htails
end
end ProximityPrize.SubmissionLower.RCN139
end PackedLegacy_BJ

/-! Packed from ProximityPrize.SubmissionLower.D9. -/
section PackedLegacy_D9
namespace ProximityPrize.SubmissionLower.RCN231
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN319 RCN347
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
end ProximityPrize.SubmissionLower.RCN231
end PackedLegacy_D9

/-! Packed from ProximityPrize.SubmissionLower.T. -/
section PackedLegacy_T
namespace ProximityPrize.SubmissionLower.RCN229
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN319 RCN347
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
end ProximityPrize.SubmissionLower.RCN229
end PackedLegacy_T

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier07 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.B0. -/
section PackedLegacy_B0
namespace ProximityPrize.SubmissionLower.RCN065
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCoefficients:K →+*CoordinateField Ω P:=
 (algebraMap Ω (CoordinateField Ω P)).comp (φ.comp Polynomial.C)
def componentPoint:Fin 4 → CoordinateField Ω P:=
 Fin.cases (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) (coordinate Ω P)
theorem component_evaluation (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=
     coordinateEvaluation Ω P (surfaceMap φ F):=by
 have hhom:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)=
     (coordinateEvaluation Ω P).toRingHom.comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [componentCoefficients,RingHom.comp_apply]
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i
     · simp [componentPoint,RingHom.comp_apply]
     · simp only [MvPolynomial.eval₂Hom_X',RingHom.comp_apply,surfaceMap_X_succ]
       rfl
 exact RingHom.congr_fun hhom F
theorem component_evaluation_zero_iff (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0 ↔
     surfaceMap φ F∈P:=by
 rw [component_evaluation]
 change surfaceMap φ F∈RingHom.ker (coordinateEvaluation Ω P).toRingHom ↔ _
 rw [coordinateEvaluation_ker]
variable (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
include hF in
theorem component_relation:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0:=
 (component_evaluation_zero_iff φ P F).mpr hF
include hH in
theorem component_regular:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (component_evaluation_zero_iff φ P _).not.mpr hH
def truncatedPolynomial (w:ℕ):Polynomial (CoordinateField Ω P):=
 globalPolynomial (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_natDegree_le (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).natDegree ≤ w:=
 globalPolynomial_natDegree_le _ _ _ _ _ _
theorem truncatedPolynomial_initial_value (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 0:=
 globalPolynomial_initial_value (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_initial_slope (w:ℕ) (hw:1 ≤ w):
   (truncatedPolynomial φ P F hF hH w).derivative.eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 1:=
 globalPolynomial_initial_slope (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w hw
theorem agreement_mem_iff_truncated_value (w:ℕ) (x u₀ u₁:K):
   surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)∈P ↔
     (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)=
       componentCoefficients φ P u₀+coordinate Ω P 2*componentCoefficients φ P u₁:=by
 rw [←component_evaluation_zero_iff]
 rw [factorial_agreement_zero_iff_actual_agreement (componentCoefficients φ P) F
   (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)]
 rw [←globalPolynomial_eval]
 rfl
def identityNodes {ι:Type*} (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):Finset ι:=by
 classical
 exact nodes.filter (fun i => surfaceMap φ
   (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i))∈P)
theorem identityNodes_subset {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):
   identityNodes φ P F nodes x u₀ u₁ w ⊆ nodes:=by
 classical
 exact Finset.filter_subset _ _
theorem exists_common_pencil_of_many_identities {ι τ:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (seed:τ → K) (selected:τ → Polynomial K)
   (hdegree:∀ t,(selected t).natDegree ≤ w)
   (hvalues:∀ t i,i∈identityNodes φ P F nodes x u₀ u₁ w →
     (selected t).eval (x i)=u₀ i+seed t*u₁ i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     truncatedPolynomial φ P F hF hH w=
       P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
         P₁.map (componentCoefficients φ P)∧
     ∀ t,selected t=P₀+Polynomial.C (seed t)*P₁:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let seeds:Option τ → CoordinateField Ω P:=fun
   | none => coordinate Ω P 2
   | some t => componentCoefficients φ P (seed t)
 let polys:Option τ → Polynomial (CoordinateField Ω P):=fun
   | none => truncatedPolynomial φ P F hF hH w
   | some t => (selected t).map (componentCoefficients φ P)
 have hI:Set.InjOn x I:=hinj.mono (identityNodes_subset φ P F nodes x u₀ u₁ w)
 have hd:∀ t,(polys t).natDegree ≤ w:=by
   intro t
   cases t with
   | none => exact truncatedPolynomial_natDegree_le φ P F hF hH w
   | some t => exact Polynomial.natDegree_map_le.trans (hdegree t)
 have hv:∀ t i,i∈I → (polys t).eval (componentCoefficients φ P (x i))=
     componentCoefficients φ P (u₀ i)+seeds t*componentCoefficients φ P (u₁ i):=by
   intro t i hi
   cases t with
   | none =>
     apply (agreement_mem_iff_truncated_value φ P F hF hH w (x i) (u₀ i) (u₁ i)).mp
     exact (Finset.mem_filter.mp hi).2
   | some t =>
     change ((selected t).map (componentCoefficients φ P)).eval _=_
     rw [Polynomial.eval_map_apply,hvalues t i hi,map_add,map_mul]
 obtain ⟨P₀,P₁,h₀,h₁,hp⟩:=exists_basefield_affine_pencil_of_identity_nodes
   (componentCoefficients φ P) I x u₀ u₁ w hcard hI seeds polys hd hv
 refine ⟨P₀,P₁,h₀,h₁,hp none,?_⟩
 intro t
 apply Polynomial.map_injective (componentCoefficients φ P) (componentCoefficients φ P).injective
 simpa only [polys,seeds,Polynomial.map_add,Polynomial.map_mul,
   Polynomial.map_C] using hp (some t)
theorem coordinates_affine_of_basefield_pencil (w:ℕ) (hw:1 ≤ w)
   (P₀ P₁:Polynomial K)
   (hp:truncatedPolynomial φ P F hF hH w=
     P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
       P₁.map (componentCoefficients φ P)):
   coordinate Ω P 0=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))∧
   coordinate Ω P 1=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X)):=by
 apply affine_coordinates_of_polynomial_pencil Ω P (φ Polynomial.X)
   (truncatedPolynomial φ P F hF hH w)
   (P₀.map (φ.comp Polynomial.C)) (P₁.map (φ.comp Polynomial.C))
 · simpa only [Polynomial.map_map,componentCoefficients] using hp
 · exact truncatedPolynomial_initial_value φ P F hF hH w
 · exact truncatedPolynomial_initial_slope φ P F hF hH w hw
include hF hH in
theorem identityNodes_card_le_of_r_dependent_principal {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:1 ≤ w)
   (hinj:Set.InjOn x nodes)
   (g:MvPolynomial (Fin 3) Ω) (hP:P=Ideal.span {g}) (hr:0 < g.degreeOf 1):
   (identityNodes φ P F nodes x u₀ u₁ w).card ≤ w:=by
 by_contra h
 have hc:w < (identityNodes φ P F nodes x u₀ u₁ w).card:=Nat.lt_of_not_ge h
 obtain ⟨P₀,P₁,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
     (fun t:Empty => t.elim) (fun t:Empty => t.elim)
     (fun t => t.elim) (fun t => t.elim)
 have hy:=(coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp).1
 exact not_y_affine_of_r_dependent_principal Ω P g hP hr _ _ hy
include hF hH in
theorem seed_transcendental_of_many_identities {ι:Type*} [IsAlgClosed Ω]
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:1 ≤ w)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (hnonpoint:∀ v:Fin 3 → Ω,P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Ω (coordinate Ω P 2):=by
 obtain ⟨P₀,P₁,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hcard
     (fun t:Empty => t.elim) (fun t:Empty => t.elim)
     (fun t => t.elim) (fun t => t.elim)
 obtain ⟨hy,hr⟩:=coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp
 exact seed_transcendental_of_affine_coordinates Ω P hnonpoint _ _ _ _ hy hr
theorem selected_agrees_on_identity_nodes {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (p w:ℕ) [CharP Ω p]
   (hw:w < p) (S:Polynomial K) (γ:K) (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:P ≤ RingHom.ker (MvPolynomial.aeval
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)).toRingHom):
   ∀ i∈identityNodes φ P F nodes x u₀ u₁ w,
     S.eval (x i)=u₀ i+γ*u₁ i:=by
 classical
 intro i hi
 have hmem:=(Finset.mem_filter.mp hi).2
 have hz:=hpoint hmem
 change MvPolynomial.eval
   (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)
   (surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹)
     (x i) (u₀ i) (u₁ i)))=0 at hz
 rw [eval_surfaceMap] at hz
 have hv:Fin.cases (φ Polynomial.X)
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)=
     polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv] at hz
 exact (factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F S γ
   (φ Polynomial.X) hsolution hregular p w hw hdegree (x i) (u₀ i) (u₁ i)).mp hz
end
end ProximityPrize.SubmissionLower.RCN065
end PackedLegacy_B0

/-! Packed from ProximityPrize.SubmissionLower.HJ. -/
section PackedLegacy_HJ
section ProximityFlatProofPort
open Finset Function Relator
variable {R α β:Type*}
namespace Finset
section Bipartite
variable (r:α → β → Prop) (s:Finset α) (t:Finset β) (a:α) (b:β)
 [DecidablePred (r a)] [∀ a,Decidable (r a b)] {m n:ℕ}
def bipartiteBelow:Finset α:={a∈s | r a b}
def bipartiteAbove:Finset β:={b∈t | r a b}
theorem bipartiteBelow_swap:t.bipartiteBelow (swap r) a=t.bipartiteAbove r a:=rfl
theorem bipartiteAbove_swap:s.bipartiteAbove (swap r) b=s.bipartiteBelow r b:=rfl
@[simp,norm_cast]
theorem coe_bipartiteBelow:s.bipartiteBelow r b=({a∈s | r a b}:Set α):=coe_filter _ _
@[simp,norm_cast]
theorem coe_bipartiteAbove:t.bipartiteAbove r a=({b∈t | r a b}:Set β):=coe_filter _ _
variable {s t a b}
@[simp]
theorem mem_bipartiteBelow {a:α}:a∈s.bipartiteBelow r b ↔ a∈s∧r a b:=mem_filter
@[simp]
theorem mem_bipartiteAbove {b:β}:b∈t.bipartiteAbove r a ↔ b∈t∧r a b:=mem_filter
@[to_additive]
theorem prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
   [CommMonoid R] (f:α → β → R) [∀ a b,Decidable (r a b)]:
   ∏ a∈s,∏ b∈t.bipartiteAbove r a,f a b=∏ b∈t,∏ a∈s.bipartiteBelow r b,f a b:=by
 simp_rw [bipartiteAbove,bipartiteBelow,prod_filter]
 exact prod_comm
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [∀ a b,Decidable (r a b)]:
   (∑ a∈s,#(t.bipartiteAbove r a))=∑ b∈t,#(s.bipartiteBelow r b):=by
 simp_rw [card_eq_sum_ones,sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]
section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {m n:R}
theorem card_nsmul_le_card_nsmul [∀ a b,Decidable (r a b)]
   (hm:∀ a∈s,m ≤ #(t.bipartiteAbove r a))
   (hn:∀ b∈t,#(s.bipartiteBelow r b) ≤ n):#s • m ≤ #t • n:=
 calc
   _ ≤ ∑ a∈s,(#(t.bipartiteAbove r a):R):=s.card_nsmul_le_sum _ _ hm
   _=∑ b∈t,(#(s.bipartiteBelow r b):R):=by
     norm_cast;rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
   _ ≤ _:=t.sum_le_card_nsmul _ _ hn
theorem card_nsmul_le_card_nsmul' [∀ a b,Decidable (r a b)]
   (hn:∀ b∈t,n ≤ #(s.bipartiteBelow r b))
   (hm:∀ a∈s,#(t.bipartiteAbove r a) ≤ m):#t • n ≤ #s • m:=
 card_nsmul_le_card_nsmul (swap r) hn hm
end OrderedSemiring
section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] (r:α → β → Prop)
 {s:Finset α} {t:Finset β} (a b) {m n:R}
theorem card_nsmul_lt_card_nsmul_of_lt_of_le [∀ a b,Decidable (r a b)] (hs:s.Nonempty)
   (hm:∀ a∈s,m < #(t.bipartiteAbove r a))
   (hn:∀ b∈t,#(s.bipartiteBelow r b) ≤ n):#s • m < #t • n:=
 calc
   _=∑ _a∈s,m:=by rw [sum_const]
   _ < ∑ a∈s,(#(t.bipartiteAbove r a):R):=sum_lt_sum_of_nonempty hs hm
   _=∑ b∈t,(#(s.bipartiteBelow r b):R):=by
     norm_cast;rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
   _ ≤ _:=t.sum_le_card_nsmul _ _ hn
theorem card_nsmul_lt_card_nsmul_of_le_of_lt [∀ a b,Decidable (r a b)] (ht:t.Nonempty)
   (hm:∀ a∈s,m ≤ #(t.bipartiteAbove r a))
   (hn:∀ b∈t,#(s.bipartiteBelow r b) < n):#s • m < #t • n:=
 calc
   _ ≤ ∑ a∈s,(#(t.bipartiteAbove r a):R):=s.card_nsmul_le_sum _ _ hm
   _=∑ b∈t,(#(s.bipartiteBelow r b):R):=by
     norm_cast;rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
   _ < ∑ _b∈t,n:=sum_lt_sum_of_nonempty ht hn
   _=_:=sum_const _
theorem card_nsmul_lt_card_nsmul_of_lt_of_le' [∀ a b,Decidable (r a b)] (ht:t.Nonempty)
   (hn:∀ b∈t,n < #(s.bipartiteBelow r b))
   (hm:∀ a∈s,#(t.bipartiteAbove r a) ≤ m):#t • n < #s • m:=
 card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm
theorem card_nsmul_lt_card_nsmul_of_le_of_lt' [∀ a b,Decidable (r a b)] (hs:s.Nonempty)
   (hn:∀ b∈t,n ≤ #(s.bipartiteBelow r b))
   (hm:∀ a∈s,#(t.bipartiteAbove r a) < m):#t • n < #s • m:=
 card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm
end StrictOrderedSemiring
theorem card_mul_le_card_mul [∀ a b,Decidable (r a b)]
   (hm:∀ a∈s,m ≤ #(t.bipartiteAbove r a))
   (hn:∀ b∈t,#(s.bipartiteBelow r b) ≤ n):#s*m ≤ #t*n:=
 card_nsmul_le_card_nsmul _ hm hn
theorem card_mul_le_card_mul' [∀ a b,Decidable (r a b)]
   (hn:∀ b∈t,n ≤ #(s.bipartiteBelow r b))
   (hm:∀ a∈s,#(t.bipartiteAbove r a) ≤ m):#t*n ≤ #s*m:=
 card_nsmul_le_card_nsmul' _ hn hm
theorem card_mul_eq_card_mul [∀ a b,Decidable (r a b)]
   (hm:∀ a∈s,#(t.bipartiteAbove r a)=m)
   (hn:∀ b∈t,#(s.bipartiteBelow r b)=n):#s*m=#t*n:=
 (card_mul_le_card_mul _ (fun a ha↦(hm a ha).ge) fun b hb↦(hn b hb).le).antisymm <|
   card_mul_le_card_mul' _ (fun a ha↦(hn a ha).ge) fun b hb↦(hm b hb).le
theorem card_le_card_of_forall_subsingleton (hs:∀ a∈s,∃ b,b∈t∧r a b)
   (ht:∀ b∈t,({ a∈s | r a b}:Set α).Subsingleton):#s ≤ #t:=by
 classical
   rw [←mul_one #s, ←mul_one #t]
   exact card_mul_le_card_mul r
     (fun a h↦card_pos.2 (by
       rw [←coe_nonempty,coe_bipartiteAbove]
       exact hs _ h:(t.bipartiteAbove r a).Nonempty))
     (fun b h↦card_le_one.2 (by
       simp_rw [mem_bipartiteBelow]
       exact ht _ h))
theorem card_le_card_of_forall_subsingleton' (ht:∀ b∈t,∃ a,a∈s∧r a b)
   (hs:∀ a∈s,({ b∈t | r a b}:Set β).Subsingleton):#t ≤ #s:=
 card_le_card_of_forall_subsingleton (swap r) ht hs
lemma sum_card_eq_sum_biUnion_card [Fintype α] [DecidableEq α] [DecidableEq β]
   (B:α → Finset β) (s:Finset α):
   ∑ j∈s,#(B j)=∑ x∈s.biUnion B,#{j | j∈s∧x∈B j}:=by
 convert sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x∈B j)
 · grind [bipartiteAbove]
 · grind [bipartiteBelow]
end Bipartite
end Finset
namespace Fintype
variable [Fintype α] [Fintype β] {r:α → β → Prop}
theorem card_le_card_of_leftTotal_unique (h₁:LeftTotal r) (h₂:LeftUnique r):
   Fintype.card α ≤ Fintype.card β:=
 card_le_card_of_forall_subsingleton r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂↦h₂ ha₁.2 ha₂.2
theorem card_le_card_of_rightTotal_unique (h₁:RightTotal r) (h₂:RightUnique r):
   Fintype.card β ≤ Fintype.card α:=
 card_le_card_of_forall_subsingleton' r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂↦h₂ ha₁.2 ha₂.2
end Fintype
end ProximityFlatProofPort
end PackedLegacy_HJ

/-! Packed from ProximityPrize.SubmissionLower.BX. -/
section PackedLegacy_BX
namespace ProximityPrize.SubmissionLower.RCN173
theorem enlarge_exempt_card_bound
   {q n a i w M:ℕ}
   (hiw:i ≤ w) (hwa:w ≤ a) (han:a ≤ n)
   (hcount:q*(a-i) ≤ (n-i)*M):
   q*(a-w) ≤ (n-w)*M:=by
 by_cases hqM:q ≤ M
 · calc
     q*(a-w) ≤ M*(a-w):=Nat.mul_le_mul_right _ hqM
     _ ≤ M*(n-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _=(n-w)*M:=Nat.mul_comm _ _
 · have hMq:M ≤ q:=(Nat.lt_of_not_ge hqM).le
   have ha:a-i=(a-w)+(w-i):=by omega
   have hn:n-i=(n-w)+(w-i):=by omega
   have hcount':
       q*(a-w)+q*(w-i) ≤
         (n-w)*M+(w-i)*M:=by
     simpa only [ha,hn,Nat.mul_add,Nat.add_mul] using hcount
   have hcancel:(w-i)*M ≤ q*(w-i):=by
     calc
       (w-i)*M ≤ (w-i)*q:=Nat.mul_le_mul_left _ hMq
       _=q*(w-i):=Nat.mul_comm _ _
   omega
section FiniteIncidence
variable {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
 (relation:Seed → Node → Prop)
 [∀ seed node,Decidable (relation seed node)]
theorem incidence_after_exempt_nodes
   (seeds:Finset Seed) (nodes identities:Finset Node) (a M:ℕ)
   (hidentities:identities ⊆ nodes)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-identities.card) ≤
     (nodes.card-identities.card)*M:=by
 have hremaining (seed:Seed) (hseed:seed∈seeds):
     a-identities.card ≤ ((nodes \ identities).filter (relation seed)).card:=by
   have hsub:(nodes.filter (relation seed)) \ identities ⊆
       (nodes \ identities).filter (relation seed):=by
     intro node hnode
     obtain ⟨hfiltered,hnot⟩:=Finset.mem_sdiff.mp hnode
     obtain ⟨hnodes,hagree⟩:=Finset.mem_filter.mp hfiltered
     exact Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨hnodes,hnot⟩,hagree⟩
   calc
     a-identities.card ≤
         (nodes.filter (relation seed)).card-identities.card:=
       Nat.sub_le_sub_right (hagreement seed hseed) identities.card
     _ ≤ ((nodes.filter (relation seed)) \ identities).card:=
       Finset.le_card_sdiff identities (nodes.filter (relation seed))
     _ ≤ ((nodes \ identities).filter (relation seed)).card:=
       Finset.card_le_card hsub
 have hdouble:seeds.card • (a-identities.card) ≤
     (nodes \ identities).card • M:=
   Finset.card_nsmul_le_card_nsmul (R:=ℕ) (r:=relation)
     (s:=seeds) (t:=nodes \ identities) hremaining hfiber
 simpa [nsmul_eq_mul,Finset.card_sdiff_of_subset hidentities] using hdouble
theorem sharp_incidence_bound
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-w) ≤ (nodes.card-w)*M:=by
 exact enlarge_exempt_card_bound hcard hwa.le han
   (incidence_after_exempt_nodes relation seeds nodes identities a M
     hidentities hagreement hfiber)
theorem card_le_sharp_incidence_quotient
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card ≤ ((nodes.card-w)*M)/(a-w):=by
 apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hwa)).mpr
 exact sharp_incidence_bound relation seeds nodes identities a w M
   hidentities hcard hwa han hagreement hfiber
end FiniteIncidence
end ProximityPrize.SubmissionLower.RCN173
end PackedLegacy_BX

/-! Packed from ProximityPrize.SubmissionLower.J. -/
section PackedLegacy_J
namespace ProximityPrize.SubmissionLower.RCN238
open scoped Classical BigOperators
open RCN002 RCN005 RCN007 RCN136 RCN231 RCN229 RCN313 RCN065 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def selectedPoint (selected:K → Polynomial K) (γ:K):Fin 3 → Ω:=
 fun i↦polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X) i.succ
theorem selectedPoint_seed (selected:K → Polynomial K) (γ:K):
   selectedPoint φ selected γ (2:Fin 3)=(φ.comp Polynomial.C) γ:=rfl
theorem selectedPoint_injective (selected:K → Polynomial K):
   Function.Injective (selectedPoint φ selected):=by
 intro γ η h
 apply (φ.comp Polynomial.C).injective
 simpa only [selectedPoint_seed] using congrFun h (2:Fin 3)
def agreementPolynomial (F:MvPolynomial (Fin 4) K) (w:ℕ) (x u₀ u₁:K):
   MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁)
theorem selected_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (γ:K) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:specialization K (selected γ) γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u₀ u₁:K):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (agreementPolynomial φ F w x u₀ u₁)=0 ↔
       (selected γ).eval x=u₀+γ*u₁:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (agreementNumerator F w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁))=0 ↔ _
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F
   (selected γ) γ (φ Polynomial.X) hsolution hregular p w hchar hdegree x u₀ u₁
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCost (cap:Fin 3 → ℕ):ℕ:=
 ∑ j,cap j*actualCoordinateDegree Ω P j
theorem agreement_fiber_card_le
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (hproper:agreementPolynomial φ F w x u₀ u₁∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Ω P hproj hnonpoint
   (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinateDegree_pos_of_transcendental
   (hproj:ProjectionsFiniteSeparable Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1 ≤ actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=(hproj j hj).1
 rw [actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
def NoLargeSelectedPencil (selected:K → Polynomial K) (Γ:Finset K) (w e:ℕ):Prop:=
 ∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
   (Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)).card ≤ e+1
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤ (nodes.card-w)*componentCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ componentCost P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le φ P hproj hnonpoint F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) hproper cap (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (componentCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
     hagreement hfiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH nodes x u₀ u₁ w hw
     hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem prime_seed_incidence
   (hproj:ProjectionsFiniteSeparable Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤ nodes.card*componentCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 have h:=prime_seed_incidence_sharp φ P hproj hnonpoint F hF hH selected Γ
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hdegree hsolution hregular hpoint
   hagreement hnoPencil cap hcap
 have hcost:(nodes.card-w)*componentCost P cap ≤ nodes.card*componentCost P cap:=
   Nat.mul_le_mul_right _ (Nat.sub_le _ _)
 exact h.trans (Nat.add_le_add_right hcost _)
end
end ProximityPrize.SubmissionLower.RCN238
end PackedLegacy_J

/-! Packed from ProximityPrize.SubmissionLower.X2. -/
section PackedLegacy_X2
namespace ProximityPrize.SubmissionLower.RCN371
open RCN002
noncomputable section
variable (K:Type) [Field K]
abbrev Original:=MvPolynomial (Fin 3) K
abbrev Collected:=MvPolynomial (Fin 2) (Polynomial K)
abbrev RationalPolynomials:=MvPolynomial (Fin 2) (RatFunc K)
def collectFirst:Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)).trans
   (MvPolynomial.optionEquivRight K (Fin 2))
def collect (order:Fin 3 ≃ Fin 3):Original K ≃ₐ[K] Collected K:=
 (MvPolynomial.renameEquiv K order.symm).trans (collectFirst K)
@[simp] theorem collect_C (order:Fin 3 ≃ Fin 3) (a:K):
   collect K order (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_first (order:Fin 3 ≃ Fin 3):
   collect K order (MvPolynomial.X (order 0))=MvPolynomial.C Polynomial.X:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem collect_X_other (order:Fin 3 ≃ Fin 3) (j:Fin 2):
   collect K order (MvPolynomial.X (order j.succ))=MvPolynomial.X j:=by
 simp [collect,collectFirst,MvPolynomial.renameEquiv_apply]
def coefficientLift (order:Fin 3 ≃ Fin 3):Polynomial K →+*Original K:=
 (collect K order).symm.toRingHom.comp MvPolynomial.C
@[simp] theorem coefficientLift_C (order:Fin 3 ≃ Fin 3) (a:K):
   coefficientLift K order (Polynomial.C a)=MvPolynomial.C a:=by
 apply (collect K order).injective
 simp [coefficientLift]
@[simp] theorem coefficientLift_X (order:Fin 3 ≃ Fin 3):
   coefficientLift K order Polynomial.X=MvPolynomial.X (order 0):=by
 apply (collect K order).injective
 simp [coefficientLift]
def rationalMap (order:Fin 3 ≃ Fin 3):Original K →+*RationalPolynomials K:=
 (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))).comp
   (collect K order).toRingHom
theorem rationalMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (rationalMap K order):=
 (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).comp
   (collect K order).injective
theorem rationalMap_ne_zero (order:Fin 3 ≃ Fin 3) (F:Original K) (hF:F≠0):
   rationalMap K order F≠0:=by
 intro h
 apply hF
 apply rationalMap_injective K order
 simpa only [map_zero] using h
attribute [local instance] MvPolynomial.algebraMvPolynomial
def coefficientDenominators:Submonoid (Collected K):=
 (nonZeroDivisors (Polynomial K)).map MvPolynomial.C
local instance:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
theorem rationalMap_eq (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=
     algebraMap (Collected K) (RationalPolynomials K) (collect K order F):=rfl
theorem collected_principal_isPrime (order:Fin 3 ≃ Fin 3)
   (G:Original K) (hG:Irreducible G):
   (Ideal.span ({collect K order G}:Set (Collected K))).IsPrime:=by
 have hi:Irreducible (collect K order G):=
   (MulEquiv.irreducible_iff (collect K order)).mpr hG
 exact Ideal.isPrime_span_singleton_of_prime hi.prime
section ActualComponent
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
def collectedEvaluation:Collected K →+*CoordinateField K P:=
 (coordinateEvaluation K P).toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K order P (collect K order F)=coordinateEvaluation K P F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K order P (MvPolynomial.C H)=
     Polynomial.aeval (coordinate K P (order 0)) H:=by
 have hhom:(coordinateEvaluation K P).toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (coordinate K P (order 0))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change coordinateEvaluation K P (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (coordinate K P (order 0)) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact MvPolynomial.algHom_C (coordinateEvaluation K P) a
   · change coordinateEvaluation K P (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (coordinate K P (order 0)) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
     rfl
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_component
   (G:Original K) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 have hGzero:coordinateEvaluation K P G=0:=by
   change G∈RingHom.ker (coordinateEvaluation K P).toRingHom
   rw [coordinateEvaluation_ker]
   exact hmem
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hroot:Polynomial.aeval (coordinate K P (order 0)) H=0:=by
   have heval:=congrArg (collectedEvaluation K order P) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hGzero,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hroot)
theorem localized_principal_isPrime_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_component K order P G hmem ht)
 simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
theorem rationalMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   Irreducible (rationalMap K order G):=by
 exact ((Ideal.span_singleton_prime (rationalMap_ne_zero K order G hG.ne_zero)).mp
   (localized_principal_isPrime_of_component K order P G hG hmem ht)).irreducible
theorem rationalMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_component K order P G hmem ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · intro hdiv
   exact map_dvd (rationalMap K order) hdiv
theorem rationalMap_proper_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))) (hproper:¬ G∣H):
   ¬ rationalMap K order G∣rationalMap K order H:=by
 intro h
 exact hproper ((rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp h)
end ActualComponent
end
end ProximityPrize.SubmissionLower.RCN371
end PackedLegacy_X2

/-! Packed from ProximityPrize.SubmissionLower.AX. -/
section PackedLegacy_AX
namespace ProximityPrize.SubmissionLower.RCN011
open RCN002 RCN005 RCN371
noncomputable section
def bivariateEquiv (A:Type) [Field A]:
   MvPolynomial (Fin 2) A ≃ₐ[A] Polynomial (Polynomial A):=
 (MvPolynomial.finSuccEquiv A 1).trans
   (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))
@[simp] theorem bivariateEquiv_C (A:Type) [Field A] (a:A):
   bivariateEquiv A (MvPolynomial.C a)=Polynomial.C (Polynomial.C a):=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_zero (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (0:Fin 2))=Polynomial.X:=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_one (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (1:Fin 2))=Polynomial.C Polynomial.X:=by
 change Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   ((MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X (0:Fin 1).succ))=
     Polynomial.C Polynomial.X
 rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
 simp [MvPolynomial.uniqueAlgEquiv]
variable (K:Type) [Field K]
abbrev PlaneRing:=Polynomial (Polynomial (RatFunc K))
def planeMap (order:Fin 3 ≃ Fin 3):Original K →+*PlaneRing K:=
 (bivariateEquiv (RatFunc K)).toRingHom.comp (rationalMap K order)
@[simp] theorem planeMap_C (order:Fin 3 ≃ Fin 3) (a:K):
   planeMap K order (MvPolynomial.C a)=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_first (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 0))=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_outer (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 1))=Polynomial.X:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [planeMap,rationalMap,h]
@[simp] theorem planeMap_X_inner (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 2))=Polynomial.C Polynomial.X:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [planeMap,rationalMap,h]
theorem planeMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (planeMap K order):=
 (bivariateEquiv (RatFunc K)).injective.comp (rationalMap_injective K order)
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
include ht in
theorem planeMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P):
   Irreducible (planeMap K order G):=by
 exact (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_component K order P G hG hmem ht)
include ht in
theorem planeMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp hrat
 · intro hdiv
   exact map_dvd (planeMap K order) hdiv
def actualPlaneEvaluation:PlaneRing K →+*CoordinateField K P:=
 (Polynomial.evalRingHom (coordinate K P (order 1))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom (rationalBaseEmbedding K P (order 0) ht).toRingHom
       (coordinate K P (order 2))))
@[simp] theorem actualPlaneEvaluation_C_C (a:RatFunc K):
   actualPlaneEvaluation K order P ht (Polynomial.C (Polynomial.C a))=
     rationalBaseEmbedding K P (order 0) ht a:=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_X:
   actualPlaneEvaluation K order P ht Polynomial.X=coordinate K P (order 1):=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_C_X:
   actualPlaneEvaluation K order P ht (Polynomial.C Polynomial.X)=
     coordinate K P (order 2):=by
 simp [actualPlaneEvaluation]
theorem actualPlaneEvaluation_comp_planeMap:
   (actualPlaneEvaluation K order P ht).comp (planeMap K order)=
     (coordinateEvaluation K P).toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,actualPlaneEvaluation_C_C,
     rationalBaseEmbedding_polynomial,Polynomial.aeval_C]
   exact (MvPolynomial.algHom_C (coordinateEvaluation K P) a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,actualPlaneEvaluation_C_C,
       rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,actualPlaneEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h => hj (Fin.ext h)
     have hjone:j.val≠1:=fun h => hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,actualPlaneEvaluation_C_X]
   rfl
def actualRelationKernel:Ideal (PlaneRing K):=
 RingHom.ker (actualPlaneEvaluation K order P ht)
theorem actualRelationKernel_contract:
   (actualRelationKernel K order P ht).comap (planeMap K order)=P:=by
 rw [actualRelationKernel,RingHom.comap_ker,actualPlaneEvaluation_comp_planeMap]
 exact coordinateEvaluation_ker K P
theorem actualPlane_root_iff (F:Original K):
   actualPlaneEvaluation K order P ht (planeMap K order F)=0 ↔ F∈P:=by
 change ((actualPlaneEvaluation K order P ht).comp (planeMap K order)) F=0 ↔ F∈P
 rw [actualPlaneEvaluation_comp_planeMap]
 change F∈RingHom.ker (coordinateEvaluation K P).toRingHom ↔ F∈P
 rw [coordinateEvaluation_ker]
end Component
theorem prime_eq_of_actualRelationKernel_eq
   (order:Fin 3 ≃ Fin 3) (P Q:Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
   (hP:Transcendental K (coordinate K P (order 0)))
   (hQ:Transcendental K (coordinate K Q (order 0)))
   (heq:actualRelationKernel K order P hP=actualRelationKernel K order Q hQ):
   P=Q:=by
 have h:=congrArg (Ideal.comap (planeMap K order)) heq
 simpa only [actualRelationKernel_contract] using h
theorem actualRelationKernel_family_injective
   (order:Fin 3 ≃ Fin 3) {I:Type} (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P):
   Function.Injective (fun i => actualRelationKernel K order (P i) (ht i)):=by
 intro i j hij
 apply hinj
 exact prime_eq_of_actualRelationKernel_eq K order (P i) (P j) (ht i) (ht j) hij
end
end ProximityPrize.SubmissionLower.RCN011
end PackedLegacy_AX

/-! Packed from ProximityPrize.SubmissionLower.DA. -/
section PackedLegacy_DA
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
open scoped BigOperators
set_option linter.constructorNameAsVariable false
local instance concreteFieldChar:
   CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433:=
 charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem derivative_ne_zero_of_pos_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hpos:0 < R.natDegree) (hlt:R.natDegree < p):R.derivative≠0:=by
 intro hzero
 have hc:=congrArg (fun f:K[X] => f.coeff (R.natDegree-1)) hzero
 rw [coeff_derivative] at hc
 have hsucc:R.natDegree-1+1=R.natDegree:=by omega
 rw [hsucc] at hc
 have hcastSucc:((R.natDegree-1:ℕ):K)+1=(R.natDegree:K):=by
   simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ => (z:K)) hsucc
 rw [hcastSucc,coeff_natDegree] at hc
 simp only [coeff_zero] at hc
 have hcast:(R.natDegree:K)≠0:=by
   intro hz
   have hdvd:p∣R.natDegree:=(CharP.cast_eq_zero_iff K p R.natDegree).mp hz
   exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
 have hR:R≠0:=by
   intro hz
   simp [hz] at hpos
 exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) hcast) hc
theorem irreducible_isCoprime_derivative_of_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hirr:Irreducible R) (hpos:0 < R.natDegree) (hlt:R.natDegree < p):
   IsCoprime R R.derivative:=by
 have hdne:=derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
 have hddeg:R.derivative.natDegree < R.natDegree:=
   natDegree_derivative_lt (ne_of_gt hpos)
 have hnotdvd:¬ R∣R.derivative:=by
   intro hdvd
   have hle:=natDegree_le_of_dvd hdvd hdne
   omega
 by_contra hnot
 exact hnotdvd ((hirr.dvd_iff_not_isCoprime).2 hnot)
theorem irreducible_resultant_derivative_ne_zero_of_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hirr:Irreducible R) (hpos:0 < R.natDegree) (hlt:R.natDegree < p):
   R.resultant R.derivative≠0:=by
 intro hz
 have hc:=(Polynomial.resultant_eq_zero_iff.mp hz).2
 exact hc (irreducible_isCoprime_derivative_of_natDegree_lt_char p R hirr hpos hlt)
theorem monic_irreducible_discr_ne_zero_of_natDegree_lt_char
   {K:Type} [Field K] (p:ℕ) [CharP K p] (R:K[X])
   (hmonic:R.Monic) (hirr:Irreducible R)
   (hpos:0 < R.natDegree) (hlt:R.natDegree < p):R.discr≠0:=by
 have hcop:=irreducible_isCoprime_derivative_of_natDegree_lt_char p R hirr hpos hlt
 have hdne:=derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
 have hddeg:R.derivative.natDegree=R.natDegree-1:=by
   apply le_antisymm (Polynomial.natDegree_derivative_le R)
   apply Polynomial.le_natDegree_of_ne_zero
   rw [Polynomial.coeff_derivative]
   have hs:R.natDegree-1+1=R.natDegree:=by omega
   rw [hs]
   have hcastSucc:((R.natDegree-1:ℕ):K)+1=(R.natDegree:K):=by
     simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ => (z:K)) hs
   rw [hcastSucc,Polynomial.coeff_natDegree]
   have hcast:(R.natDegree:K)≠0:=by
     intro hz
     exact (Nat.not_dvd_of_pos_of_lt hpos hlt)
       ((CharP.cast_eq_zero_iff K p R.natDegree).mp hz)
   exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero) hcast
 have hres:R.resultant R.derivative R.natDegree (R.natDegree-1)≠0:=by
   simpa [hddeg] using
     irreducible_resultant_derivative_ne_zero_of_natDegree_lt_char p R hirr hpos hlt
 have hdegree:0 < R.degree:=Polynomial.natDegree_pos_iff_degree_pos.mp hpos
 have hrel:=Polynomial.resultant_deriv (f:=R) hdegree
 rw [hmonic.leadingCoeff,mul_one] at hrel
 intro hz
 rw [hz,mul_zero] at hrel
 exact hres hrel
theorem monic_discr_ne_zero_of_fraction_irreducible
   {A K:Type} [CommRing A] [IsDomain A] [Field K]
   [Algebra A K] [IsFractionRing A K]
   (p:ℕ) [CharP A p] (R:A[X]) (hmonic:R.Monic)
   (hirrK:Irreducible (R.map (algebraMap A K)))
   (hpos:0 < R.natDegree) (hlt:R.natDegree < p):R.discr≠0:=by
 letI:CharP K p:=charP_of_injective_algebraMap (IsFractionRing.injective A K) p
 let f:A →+*K:=algebraMap A K
 let RK:K[X]:=R.map f
 have hdeg:RK.natDegree=R.natDegree:=hmonic.natDegree_map f
 have hposK:0 < RK.natDegree:=by simpa [hdeg]
 have hltK:RK.natDegree < p:=by simpa [hdeg]
 have hcopK:=irreducible_isCoprime_derivative_of_natDegree_lt_char p RK hirrK hposK hltK
 have hresK:RK.resultant RK.derivative≠0:=by
   intro hz
   exact (Polynomial.resultant_eq_zero_iff.mp hz).2 hcopK
 have hddegK:RK.derivative.natDegree=RK.natDegree-1:=by
   apply le_antisymm (Polynomial.natDegree_derivative_le RK)
   apply Polynomial.le_natDegree_of_ne_zero
   rw [Polynomial.coeff_derivative]
   have hs:RK.natDegree-1+1=RK.natDegree:=by omega
   rw [hs]
   have hcastSucc:((RK.natDegree-1:ℕ):K)+1=(RK.natDegree:K):=by
     simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z:ℕ => (z:K)) hs
   rw [hcastSucc,Polynomial.coeff_natDegree]
   have hcast:(RK.natDegree:K)≠0:=by
     intro hz
     exact (Nat.not_dvd_of_pos_of_lt hposK hltK)
       ((CharP.cast_eq_zero_iff K p RK.natDegree).mp hz)
   exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirrK.ne_zero) hcast
 have hresKfixed:RK.resultant RK.derivative R.natDegree (R.natDegree-1)≠0:=by
   simpa [hdeg,hddegK] using hresK
 have hresRaw:R.resultant R.derivative R.natDegree (R.natDegree-1)≠0:=by
   intro hz
   apply hresKfixed
   dsimp [RK]
   rw [Polynomial.derivative_map]
   rw [Polynomial.resultant_map_map]
   simpa using congrArg f hz
 have hdegree:0 < R.degree:=Polynomial.natDegree_pos_iff_degree_pos.mp hpos
 have hrel:=Polynomial.resultant_deriv (f:=R) hdegree
 rw [hmonic.leadingCoeff,mul_one] at hrel
 intro hzero
 rw [hzero,mul_zero] at hrel
 exact hresRaw hrel
theorem degreeX_derivative_le {F:Type} [Field F] (R:F[X][Y]):
   degreeX R.derivative ≤ degreeX R:=by
 classical
 unfold degreeX
 apply Finset.sup_le
 intro j hj
 rw [Polynomial.coeff_derivative]
 calc
   (R.coeff (j+1)*(j+1:F[X])).natDegree ≤
       (R.coeff (j+1)).natDegree+((j+1:F[X])).natDegree:=
     Polynomial.natDegree_mul_le
   _ ≤ degreeX R:=by
     have hn:((j:F[X])+1).natDegree=0:=by
       rw [←Nat.cast_one, ←Nat.cast_add,Polynomial.natDegree_natCast]
     rw [hn,Nat.add_zero]
     exact Polynomial.Bivariate.coeff_natDegree_le_degreeX R (j+1)
theorem discr_natDegree_le {F:Type} [Field F] (R:F[X][Y])
   (hmonic:R.Monic) (hpos:0 < R.natDegree):
   R.discr.natDegree ≤ (2*R.natDegree-1)*degreeX R:=by
 let d:=R.natDegree
 let S:=R.resultant R.derivative d (d-1)
 have hSdeg:S.natDegree ≤ (d-1)*degreeX R+d*degreeX R.derivative:=by
   exact ps_nat_degree_resultant_le R.derivative R (d-1) d
 have hSdeg':S.natDegree ≤ (2*d-1)*degreeX R:=by
   calc
     S.natDegree ≤ (d-1)*degreeX R+d*degreeX R.derivative:=hSdeg
     _ ≤ (d-1)*degreeX R+d*degreeX R:=by
       gcongr
       exact degreeX_derivative_le R
     _=((d-1)+d)*degreeX R:=by ring
     _=(2*d-1)*degreeX R:=by
       congr 1
       dsimp [d]
       omega
 have hdegree:0 < R.degree:=Polynomial.natDegree_pos_iff_degree_pos.mp hpos
 have hrel:=Polynomial.resultant_deriv (f:=R) hdegree
 rw [hmonic.leadingCoeff,mul_one] at hrel
 by_cases hd:R.discr=0
 · simp [hd]
 · have hu:((-1:F[X])^(d*(d-1)/2))≠0:=pow_ne_zero _ (by simp)
   have heqdeg:S.natDegree=R.discr.natDegree:=by
     rw [show S=(-1)^(d*(d-1)/2)*R.discr by simpa [S,d] using hrel,
       Polynomial.natDegree_mul hu hd]
     simp
   rw [←heqdeg]
   exact hSdeg'
theorem sum_discr_natDegree_le {F ρ:Type} [Field F] [DecidableEq ρ]
   (S:Finset ρ) (R:ρ → F[X][Y])
   (hmonic:∀ r∈S,(R r).Monic)
   (hpos:∀ r∈S,0 < (R r).natDegree):
   (∑ r∈S,(R r).discr.natDegree) ≤
     ∑ r∈S,(2*(R r).natDegree-1)*degreeX (R r):=by
 apply Finset.sum_le_sum
 intro r hr
 exact discr_natDegree_le (R r) (hmonic r hr) (hpos r hr)
theorem exists_good_x_of_discriminants
   {F ρ:Type} [Field F] [Fintype F] [DecidableEq ρ]
   (S:Finset ρ) (R:ρ → F[X][Y])
   (hne:∀ r∈S,(R r).discr≠0)
   (hdeg:(∑ r∈S,(R r).discr.natDegree) < Fintype.card F):
   ∃ x₀:F,∀ r∈S,Polynomial.eval x₀ (R r).discr≠0:=by
 classical
 let P:F[X]:=∏ r∈S,(R r).discr
 have hPne:P≠0:=by
   change (∏ r∈S,(R r).discr)≠0
   rw [Finset.prod_ne_zero_iff]
   exact hne
 have hPdeg:P.natDegree < Fintype.card F:=by
   exact (Polynomial.natDegree_prod_le S (fun r => (R r).discr)).trans_lt hdeg
 by_contra hgood
 push Not at hgood
 have hPeval:∀ x:F,P.eval x=0:=by
   intro x
   obtain ⟨r,hr,hz⟩:=hgood x
   change Polynomial.eval x (∏ r∈S,(R r).discr)=0
   rw [Polynomial.eval_prod]
   exact Finset.prod_eq_zero hr hz
 have hzero:=Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
   P Function.injective_id hPeval hPdeg
 exact hPne hzero
end ProximityPrize.SubmissionLower
end PackedLegacy_DA

/-! Packed from ProximityPrize.SubmissionLower.X8. -/
section PackedLegacy_X8
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate
variable {F:Type} [Field F]
theorem bivariate_resultant_eval (B H:F[X][Y]) (n m:ℕ) (z:F):
   (Polynomial.resultant B H n m).eval z=
     Polynomial.resultant (B.map (Polynomial.evalRingHom z))
       (H.map (Polynomial.evalRingHom z)) n m:=by
 simp
theorem bivariate_resultant_eval_fixed_original_degrees (B H:F[X][Y]) (z:F):
   (Polynomial.resultant B H).eval z=
     Polynomial.resultant (B.map (Polynomial.evalRingHom z))
       (H.map (Polynomial.evalRingHom z)) B.natDegree H.natDegree:=by
 exact bivariate_resultant_eval B H B.natDegree H.natDegree z
theorem resultant_eq_zero_of_common_root {p q:F[X]} {t:F}
   (hne:p≠0∨q≠0) (hp:p.eval t=0) (hq:q.eval t=0):
   Polynomial.resultant p q=0:=by
 rw [Polynomial.resultant_eq_zero_iff]
 refine ⟨hne,?_⟩
 rintro ⟨a,b,hab⟩
 have heval:=congrArg (fun r:F[X] => r.eval t) hab
 simp [Polynomial.eval_add,Polynomial.eval_mul,hp,hq] at heval
theorem resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
   {p q:F[X]} {m n:ℕ} {t:F}
   (hpdeg:p.natDegree ≤ m) (hqmonic:q.Monic) (hqdeg:q.natDegree=n)
   (hp:p.eval t=0) (hq:q.eval t=0):
   Polynomial.resultant p q m n=0:=by
 have hstd:Polynomial.resultant p q=0:=
   resultant_eq_zero_of_common_root (Or.inr hqmonic.ne_zero) hp hq
 have hm:p.natDegree+(m-p.natDegree)=m:=Nat.add_sub_of_le hpdeg
 rw [←hm, ←hqdeg]
 rw [Polynomial.resultant_add_left_deg]
 · simp [hstd]
 · exact le_rfl
theorem resultant_fixed_degree_eq_zero_of_common_root
   {p q:F[X]} {m n:ℕ} {t:F}
   (hpdeg:p.natDegree ≤ m) (hqdeg:q.natDegree ≤ n)
   (hsize:0 < m+n) (hp:p.eval t=0) (hq:q.eval t=0):
   Polynomial.resultant p q m n=0:=by
 by_cases hne:p≠0∨q≠0
 · have hstd:Polynomial.resultant p q=0:=
     resultant_eq_zero_of_common_root hne hp hq
   have hm:p.natDegree+(m-p.natDegree)=m:=Nat.add_sub_of_le hpdeg
   have hn:q.natDegree+(n-q.natDegree)=n:=Nat.add_sub_of_le hqdeg
   rw [←hm, ←hn]
   rw [Polynomial.resultant_add_left_deg]
   · rw [Polynomial.resultant_add_right_deg]
     · simp [hstd]
     · exact le_rfl
   · exact le_rfl
 · push Not at hne
   rcases hne with ⟨rfl,rfl⟩
   rcases m with _ | m <;> rcases n with _ | n <;> simp_all
theorem bivariate_resultant_eval_eq_zero_of_common_root
   (B H:F[X][Y]) (n m:ℕ) (z t:F)
   (hBdeg:(B.map (Polynomial.evalRingHom z)).natDegree ≤ n)
   (hHdeg:(H.map (Polynomial.evalRingHom z)).natDegree ≤ m)
   (hsize:0 < n+m)
   (hBroot:(B.map (Polynomial.evalRingHom z)).eval t=0)
   (hHroot:(H.map (Polynomial.evalRingHom z)).eval t=0):
   (Polynomial.resultant B H n m).eval z=0:=by
 rw [bivariate_resultant_eval]
 exact resultant_fixed_degree_eq_zero_of_common_root hBdeg hHdeg hsize hBroot hHroot
theorem bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
   (B H:F[X][Y]) (z t:F)
   (hsize:0 < B.natDegree+H.natDegree)
   (hBroot:(B.map (Polynomial.evalRingHom z)).eval t=0)
   (hHroot:(H.map (Polynomial.evalRingHom z)).eval t=0):
   (Polynomial.resultant B H).eval z=0:=by
 rw [bivariate_resultant_eval_fixed_original_degrees]
 exact resultant_fixed_degree_eq_zero_of_common_root
   Polynomial.natDegree_map_le Polynomial.natDegree_map_le hsize hBroot hHroot
theorem bivariate_resultant_natDegree_le (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*degreeX B+n*degreeX H:=by
 exact ps_nat_degree_resultant_le H B m n
theorem bivariate_resultant_natDegree_le_of_declared_Y_degrees
   (B H:F[X][Y]) (n m:ℕ)
   (hBY:B.natDegree=n) (hHY:H.natDegree=m):
   (Polynomial.resultant B H).natDegree ≤
     m*degreeX B+n*degreeX H:=by
 simpa [hBY,hHY] using bivariate_resultant_natDegree_le B H n m
theorem irreducible_dvd_of_resultant_eq_zero
   (B H:F[X][Y]) (hHmonic:H.Monic) (hHirreducible:Irreducible H)
   (hres:Polynomial.resultant B H=0):H∣B:=by
 classical
 let K:=FractionRing F[X]
 let f:F[X] →+*K:=algebraMap F[X] K
 have hf:Function.Injective f:=IsFractionRing.injective F[X] K
 have hBdeg:(B.map f).natDegree=B.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf B
 have hHdeg:(H.map f).natDegree=H.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf H
 have hresFixed:
     Polynomial.resultant (B.map f) (H.map f) B.natDegree H.natDegree=0:=by
   rw [Polynomial.resultant_map_map]
   rw [hres]
   exact map_zero f
 have hresK:Polynomial.resultant (B.map f) (H.map f)=0:=by
   simpa only [hBdeg,hHdeg] using hresFixed
 have hnotCoprime:¬ IsCoprime (B.map f) (H.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hresK).2
 have hHirreducibleK:Irreducible (H.map f):=by
   exact (hHmonic.irreducible_iff_irreducible_map_fraction_map).mp hHirreducible
 have hdvdK:H.map f∣B.map f:=
   (Irreducible.dvd_iff_not_isCoprime hHirreducibleK).2 fun hc =>
     hnotCoprime hc.symm
 exact hHmonic.isPrimitive.dvd_of_fraction_map_dvd_fraction_map hdvdK
theorem irreducible_dvd_of_many_bivariate_common_roots
   (B H:F[X][Y]) (n m:ℕ) (S:Finset F) (t:F → F)
   (hBY:B.natDegree=n) (hHY:H.natDegree=m)
   (hHmonic:H.Monic) (hHirreducible:Irreducible H)
   (hmany:m*degreeX B+n*degreeX H < S.card)
   (hroots:∀ z∈S,
     (B.map (Polynomial.evalRingHom z)).eval (t z)=0∧
     (H.map (Polynomial.evalRingHom z)).eval (t z)=0):
   H∣B:=by
 let R:F[X]:=Polynomial.resultant B H n m
 have hReval:∀ z∈S,R.eval z=0:=by
   intro z hz
   rw [bivariate_resultant_eval]
   exact resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
     (Polynomial.natDegree_map_le.trans hBY.le)
     (hHmonic.map (Polynomial.evalRingHom z))
     ((hHmonic.natDegree_map (Polynomial.evalRingHom z)).trans hHY)
     (hroots z hz).1 (hroots z hz).2
 have hRdeg:R.natDegree ≤ m*degreeX B+n*degreeX H:=by
   exact bivariate_resultant_natDegree_le B H n m
 have hRzero:R=0:=
   Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S hReval
     (hRdeg.trans_lt hmany)
 apply irreducible_dvd_of_resultant_eq_zero B H hHmonic hHirreducible
 simpa only [R,hBY,hHY] using hRzero
theorem quotient_mk_eq_zero_of_many_bivariate_common_roots
   (B H:F[X][Y]) (n m:ℕ) (S:Finset F) (t:F → F)
   (hBY:B.natDegree=n) (hHY:H.natDegree=m)
   (hHmonic:H.Monic) (hHirreducible:Irreducible H)
   (hmany:m*degreeX B+n*degreeX H < S.card)
   (hroots:∀ z∈S,
     (B.map (Polynomial.evalRingHom z)).eval (t z)=0∧
     (H.map (Polynomial.evalRingHom z)).eval (t z)=0):
   Ideal.Quotient.mk (Ideal.span {H}) B=0:=by
 rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
 exact irreducible_dvd_of_many_bivariate_common_roots B H n m S t hBY hHY
   hHmonic hHirreducible hmany hroots
theorem exists_common_specialization_eval_C_ne_zero
   [Fintype F] {ρ:Type} [DecidableEq ρ]
   (S:Finset ρ) (p:ρ → F[X][Y])
   (hp:∀ r∈S,p r≠0)
   (hdeg:(∑ r∈S,(p r).natDegree) < Fintype.card F):
   ∃ x₀:F,∀ r∈S,Polynomial.eval (Polynomial.C x₀) (p r)≠0:=by
 classical
 let P:F[X][Y]:=∏ r∈S,p r
 have hPne:P≠0:=by
   change (∏ r∈S,p r)≠0
   rw [Finset.prod_ne_zero_iff]
   exact hp
 have hPdeg:P.natDegree < Fintype.card F:=by
   exact (Polynomial.natDegree_prod_le S p).trans_lt hdeg
 by_contra hgood
 push Not at hgood
 have hPeval:∀ x:F,P.eval (Polynomial.C x)=0:=by
   intro x
   obtain ⟨r,hrS,hrzero⟩:=hgood x
   change Polynomial.eval (Polynomial.C x) (∏ r∈S,p r)=0
   rw [Polynomial.eval_prod]
   exact Finset.prod_eq_zero hrS hrzero
 have hPzero:P=0:=
   Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
     P Polynomial.C_injective hPeval hPdeg
 exact hPne hPzero
theorem exists_common_specialization_eval_C_ne_zero_univ
   [Fintype F] {ρ:Type} [Fintype ρ] [DecidableEq ρ]
   (p:ρ → F[X][Y]) (hp:∀ r,p r≠0)
   (hdeg:(∑ r,(p r).natDegree) < Fintype.card F):
   ∃ x₀:F,∀ r,Polynomial.eval (Polynomial.C x₀) (p r)≠0:=by
 simpa only [Finset.mem_univ,forall_const] using
   exists_common_specialization_eval_C_ne_zero (F:=F) Finset.univ p
     (fun r _ => hp r) hdeg
end ProximityPrize.SubmissionLower
end PackedLegacy_X8

/-! Packed from ProximityPrize.SubmissionLower.W2. -/
section PackedLegacy_W2
namespace ProximityPrize.SubmissionLower.RCN355
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_eval_columns_eq_zero
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (columns:Finset ι)
   (hzero:∀ j∈columns,∀ i,(M i j).eval alpha=0):
   (Polynomial.X-Polynomial.C alpha)^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ j∈columns,(Polynomial.X-Polynomial.C alpha))∣
       ∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:
     (Polynomial.X-Polynomial.C alpha)^columns.card∣
       ∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K):
   (Polynomial.X-Polynomial.C alpha)^
       (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)∣
     M.det:=by
 classical
 let evalMatrix:Matrix ι ι (Polynomial K) →+*Matrix ι ι K:=
   (Polynomial.evalRingHom alpha).mapMatrix
 let constMatrix:Matrix ι ι K →+*Matrix ι ι (Polynomial K):=
   (Polynomial.C:K →+*Polynomial K).mapMatrix
 let evaluated:Matrix ι ι K:=evalMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form evaluated
 let transformed:Matrix ι ι (Polynomial K):=constMatrix V*M*constMatrix U
 have heval_const (B:Matrix ι ι K):evalMatrix (constMatrix B)=B:=by
   ext i j
   simp [evalMatrix,constMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
 have heval:evalMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change evalMatrix (constMatrix V*M*constMatrix U)=_
   rw [map_mul,map_mul,heval_const,heval_const]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-evaluated.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-evaluated.rank:=by
   simp [zeroColumns]
 have hzero:∀ j∈zeroColumns,∀ i,(transformed i j).eval alpha=0:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   change evalMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [heval]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:IsUnit (constMatrix V).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
 have hUdet:IsUnit (constMatrix U).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
 have hdiv:=pow_card_dvd_det_of_eval_columns_eq_zero
   transformed alpha zeroColumns hzero
 rw [hcard] at hdiv
 change (Polynomial.X-Polynomial.C alpha)^
     (Fintype.card ι-evaluated.rank)∣
       (constMatrix V*M*constMatrix U).det at hdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdiv
 exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)
theorem corank_le_rootMultiplicity_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (hdet:M.det≠0):
   Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
     M.det.rootMultiplicity alpha:=by
 exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
   (pow_corank_dvd_det M alpha)
theorem sum_rootMultiplicity_le_natDegree
   (P:Polynomial K) (points:Finset K):
   (∑ alpha∈points,P.rootMultiplicity alpha) ≤ P.natDegree:=by
 classical
 have hselected:
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤ P.roots.card:=by
   let all:=points ∪ P.roots.toFinset
   calc
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤
         ∑ alpha∈all,Multiset.count alpha P.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ alpha∈P.roots.toFinset,Multiset.count alpha P.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro alpha _ hnot
       exact Multiset.count_eq_zero.mpr (by simpa using hnot)
     _=P.roots.card:=Multiset.toFinset_sum_count_eq P.roots
 calc
   (∑ alpha∈points,P.rootMultiplicity alpha)=
       ∑ alpha∈points,Multiset.count alpha P.roots:=by
     apply Finset.sum_congr rfl
     intro alpha _
     exact (Polynomial.count_roots P).symm
   _ ≤ P.roots.card:=hselected
   _ ≤ P.natDegree:=Polynomial.card_roots' P
theorem sum_coranks_le_natDegree_det
   (M:Matrix ι ι (Polynomial K)) (points:Finset K) (hdet:M.det≠0):
   (∑ alpha∈points,
     (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)) ≤
     M.det.natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,M.det.rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ => corank_le_rootMultiplicity_det M alpha hdet
   _ ≤ M.det.natDegree:=sum_rootMultiplicity_le_natDegree M.det points
theorem sylvester_corank_le_rootMultiplicity_resultant
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
     (Polynomial.resultant P Q m n).rootMultiplicity alpha:=by
 simpa only [Fintype.card_fin,Polynomial.resultant,
   ←Polynomial.sylvester_map_map] using
   corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant
theorem sum_sylvester_coranks_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(Polynomial.resultant P Q m n).rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ =>
       sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
   _ ≤ (Polynomial.resultant P Q m n).natDegree:=
     sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points
theorem sum_sylvester_coranks_le_bidegree_bound
   {F:Type} [Field F] [DecidableEq F]
   (P Q:Polynomial (Polynomial F)) (m n:ℕ) (points:Finset F)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 have hdegree:=bivariate_resultant_natDegree_le (F:=F) P Q m n
 exact Nat.le_trans
   (sum_sylvester_coranks_le_resultant_natDegree P Q m n points hresultant) hdegree
end
end ProximityPrize.SubmissionLower.RCN355
end PackedLegacy_W2

/-! Packed from ProximityPrize.SubmissionLower.G5. -/
section PackedLegacy_G5
namespace ProximityPrize.SubmissionLower.RCN363
open scoped BigOperators
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
def evaluationOn (N:ℕ) (roots:Finset K):
   Polynomial.degreeLT K N →ₗ[K] (roots → K) where
 toFun P x:=(P:Polynomial K).eval (x:K)
 map_add' _ _:=funext fun _ => Polynomial.eval_add
 map_smul' _ _:=funext <| by simp
theorem evaluationOn_surjective (N:ℕ) (roots:Finset K)
   (hcard:roots.card ≤ N):Function.Surjective (evaluationOn N roots):=by
 let E:=Lagrange.funEquivDegreeLT (s:=roots) (v:=fun x:K => x)
   (Set.injOn_id (roots:Set K))
 intro values
 let small:=E.symm values
 have hsmall:(small:Polynomial K).degree < (roots.card:WithBot ℕ):=
   Polynomial.mem_degreeLT.mp small.property
 have hlarge:(small:Polynomial K).degree < (N:WithBot ℕ):=
   hsmall.trans_le (by exact_mod_cast hcard)
 refine ⟨⟨(small:Polynomial K),Polynomial.mem_degreeLT.mpr hlarge⟩,?_⟩
 change E small=values
 exact E.apply_symm_apply values
theorem finrank_degreeLT (N:ℕ):
   Module.finrank K (Polynomial.degreeLT K N)=N:=by
 simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial K) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank K (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd K m n)
     (Polynomial.degreeLT.basis K (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis K (m+n)) (Polynomial.degreeLT.basisProd K m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_roots_card_le_cap
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n:=by
 rcases hnonzero with hp0 | hq0
 · have hcard:roots.card ≤ p.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hp0).mpr (hroots x hx).1
   omega
 · have hcard:roots.card ≤ q.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hq0).mpr (hroots x hx).2
   omega
theorem common_roots_card_le_sylvester_corank
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let E:=evaluationOn (m+n) roots
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective E:=
   evaluationOn_surjective (m+n) roots
     (common_roots_card_le_cap p q m n roots hp hq hnonzero hroots)
 have hcontain:LinearMap.range L ≤ LinearMap.ker E:=by
   rintro P ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   ext x
   change (p*(input.2:Polynomial K)+q*(input.1:Polynomial K)).eval
     (x:K)=0
   simp only [Polynomial.eval_add,Polynomial.eval_mul,
     (hroots x x.property).1,(hroots x x.property).2,zero_mul,zero_add]
 have hevalrank:Module.finrank K (LinearMap.range E)=roots.card:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,
     Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
 have hnull:=LinearMap.finrank_range_add_finrank_ker E
 rw [hevalrank,finrank_degreeLT] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank K (LinearMap.range L) at hmatrix
 omega
theorem common_fiber_card_le_sylvester_corank
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K) (roots:Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hnonzero:P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ beta∈roots,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   roots.card ≤ m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank:=by
 apply common_roots_card_le_sylvester_corank
 · exact Polynomial.natDegree_map_le.trans hP
 · exact Polynomial.natDegree_map_le.trans hQ
 · exact hnonzero
 · exact hroots
theorem sum_common_fiber_cards_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(m+n-(Polynomial.sylvester
       (P.map (Polynomial.evalRingHom alpha))
       (Q.map (Polynomial.evalRingHom alpha)) m n).rank):=by
     apply Finset.sum_le_sum
     intro alpha halpha
     exact common_fiber_card_le_sylvester_corank P Q m n alpha (fibers alpha)
       hP hQ (hnonzero alpha halpha) (hroots alpha halpha)
   _ ≤ _:=RCN355.sum_sylvester_coranks_le_resultant_natDegree
     P Q m n points hresultant
theorem sum_common_fiber_cards_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 exact Nat.le_trans
   (sum_common_fiber_cards_le_resultant_natDegree P Q m n points fibers
     hP hQ hresultant hnonzero hroots)
   (bivariate_resultant_natDegree_le (F:=K) P Q m n)
def pointFiber (points:Finset (K × K)) (alpha:K):Finset K:=
 (points.filter (fun point => point.1=alpha)).image Prod.snd
theorem card_eq_sum_pointFiber (points:Finset (K × K)):
   points.card=∑ alpha∈points.image Prod.fst,(pointFiber points alpha).card:=by
 rw [Finset.card_eq_sum_card_image Prod.fst points]
 apply Finset.sum_congr rfl
 intro alpha _
 change (points.filter (fun point => point.1=alpha)).card=
   ((points.filter (fun point => point.1=alpha)).image Prod.snd).card
 symm
 apply Finset.card_image_of_injOn
 intro u hu v hv huv
 apply Prod.ext
 · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
 · exact huv
theorem common_points_card_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset (K × K))
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ point∈points,
     P.map (Polynomial.evalRingHom point.1)≠0∨
     Q.map (Polynomial.evalRingHom point.1)≠0)
   (hroots:∀ point∈points,
     (P.map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     (Q.map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 rw [card_eq_sum_pointFiber points]
 apply sum_common_fiber_cards_le_bidegree_bound P Q m n
   (points.image Prod.fst) (pointFiber points) hP hQ hresultant
 · intro alpha halpha
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp halpha
   exact hnonzero point hpoint
 · intro alpha _ beta hbeta
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp hbeta
   obtain ⟨hpoint,hfirst⟩:=Finset.mem_filter.mp hpoint
   simpa only [hfirst] using hroots point hpoint
end
end ProximityPrize.SubmissionLower.RCN363
end PackedLegacy_G5

/-! Packed from ProximityPrize.SubmissionLower.W6. -/
section PackedLegacy_W6
namespace ProximityPrize.SubmissionLower.RCN362
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
theorem inner_linear_C_dvd_of_specialization_eq_zero
   (P:Polynomial (Polynomial K)) (alpha:K)
   (hzero:P.map (Polynomial.evalRingHom alpha)=0):
   Polynomial.C (Polynomial.X-Polynomial.C alpha)∣P:=by
 rw [Polynomial.C_dvd_iff_dvd_coeff]
 intro i
 apply Polynomial.dvd_iff_isRoot.mpr
 have hcoeff:=congrArg (fun Q:Polynomial K => Q.coeff i) hzero
 simpa using hcoeff
theorem primitive_specialization_ne_zero
   (P:Polynomial (Polynomial K)) (hprimitive:P.IsPrimitive) (alpha:K):
   P.map (Polynomial.evalRingHom alpha)≠0:=by
 intro hzero
 exact Polynomial.not_isUnit_X_sub_C alpha
   (hprimitive _ (inner_linear_C_dvd_of_specialization_eq_zero P alpha hzero))
theorem irreducible_specialization_ne_zero
   (P:Polynomial (Polynomial K)) (hirreducible:Irreducible P)
   (hdegree:0 < P.natDegree) (alpha:K):
   P.map (Polynomial.evalRingHom alpha)≠0:=by
 exact primitive_specialization_ne_zero P
   (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) alpha
theorem primitive_irreducible_dvd_of_resultant_eq_zero
   (P Q:Polynomial (Polynomial K))
   (hprimitive:P.IsPrimitive) (hirreducible:Irreducible P)
   (hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree=0):P∣Q:=by
 classical
 let F:=FractionRing (Polynomial K)
 let f:Polynomial K →+*F:=algebraMap (Polynomial K) F
 have hf:Function.Injective f:=IsFractionRing.injective (Polynomial K) F
 have hPdegree:(P.map f).natDegree=P.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf P
 have hQdegree:(Q.map f).natDegree=Q.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf Q
 have hfixed:Polynomial.resultant (P.map f) (Q.map f)
     P.natDegree Q.natDegree=0:=by
   rw [Polynomial.resultant_map_map,hresultant,map_zero]
 have hresF:Polynomial.resultant (P.map f) (Q.map f)=0:=by
   simpa only [hPdegree,hQdegree] using hfixed
 have hnotCoprime:¬ IsCoprime (P.map f) (Q.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hresF).2
 have hirreducibleF:Irreducible (P.map f):=
   hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirreducible
 have hdivF:P.map f∣Q.map f:=
   (Irreducible.dvd_iff_not_isCoprime hirreducibleF).mpr hnotCoprime
 exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdivF
theorem irreducible_resultant_ne_zero_of_not_dvd
   (P Q:Polynomial (Polynomial K)) (hirreducible:Irreducible P)
   (hdegree:0 < P.natDegree) (hproper:¬ P∣Q):
   Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
 intro hresultant
 exact hproper (primitive_irreducible_dvd_of_resultant_eq_zero P Q
   (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) hirreducible hresultant)
theorem irreducible_common_points_card_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (points:Finset (K × K))
   (hirreducible:Irreducible P) (hdegree:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (hroots:∀ point∈points,
     (P.map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     (Q.map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 apply RCN363.common_points_card_le_bidegree_bound
   P Q P.natDegree Q.natDegree points le_rfl le_rfl
 · exact irreducible_resultant_ne_zero_of_not_dvd P Q hirreducible hdegree hproper
 · intro point _
   exact Or.inl (irreducible_specialization_ne_zero P hirreducible hdegree point.1)
 · exact hroots
end
end ProximityPrize.SubmissionLower.RCN362
end PackedLegacy_W6

/-! Packed from ProximityPrize.SubmissionLower.IT. -/
section PackedLegacy_IT
section ProximityFlatProofPort
namespace Polynomial
open Ideal
variable {R S:Type*} [Semiring R] [Semiring S] (p:R[X])
def contentIdeal:=span (p.coeffs:Set R)
theorem contentIdeal_def:p.contentIdeal=span (p.coeffs:Set R):=rfl
@[simp]
theorem contentIdeal_zero:(0:R[X]).contentIdeal=⊥:=by
 simp [contentIdeal_def]
@[simp]
theorem contentIdeal_eq_bot_iff:p.contentIdeal=⊥ ↔ p=0:=by
 simp only [contentIdeal_def,span_eq_bot]
 refine ⟨?_,fun h↦by simp [h]⟩
 contrapose!
 exact fun h↦⟨p.leadingCoeff,coeff_mem_coeffs (leadingCoeff_ne_zero.mpr h),
   leadingCoeff_ne_zero.mpr h⟩
theorem coeff_mem_contentIdeal (n:ℕ):p.coeff n∈p.contentIdeal:=by
 letI:DecidableEq R:=Classical.decEq R
 by_cases h:p.coeff n=0
 · simp [h]
 · apply subset_span
   simpa using coeff_mem_coeffs h
@[simp]
theorem contentIdeal_monomial (n:ℕ) (r:R):(monomial n r).contentIdeal=span {r}:=by
 letI:DecidableEq R:=Classical.decEq R
 by_cases h:r=0 <;>
 simp [h,Set.singleton_zero,contentIdeal_def,coeffs_monomial]
@[simp]
theorem contentIdeal_C (r:R):(C r).contentIdeal=span {r}:=by
 rw [←monomial_zero_left]
 exact contentIdeal_monomial 0 r
@[simp]
theorem contentIdeal_one:(1:R[X]).contentIdeal=⊤:=by
 rw [←span_singleton_one, ←contentIdeal_C 1,C_1]
theorem contentIdeal_FG:p.contentIdeal.FG:=⟨p.coeffs,rfl⟩
theorem contentIdeal_map_eq_map_contentIdeal (f:R →+*S):
   (p.map f).contentIdeal=p.contentIdeal.map f:=by
 letI:DecidableEq S:=Classical.decEq S
 suffices span ((map f p).coeffs ∪ {0})=span (f '' p.coeffs ∪ {0}) by
   simpa [contentIdeal_def,map_span]
 congr 1
 ext s
 by_cases hs:s=0
 · simp [hs]
 · aesop (add simp mem_coeffs_iff)
theorem contentIdeal_mul_le_mul_contentIdeal (q:R[X]):
   (p*q).contentIdeal ≤ p.contentIdeal*q.contentIdeal:=by
 rw [contentIdeal_def,span_le]
 simp only [Set.subset_def,Finset.mem_coe,mem_coeffs_iff]
 rintro r ⟨n,_,rfl⟩
 simp [coeff_mul,_root_.sum_mem,Submodule.mul_mem_mul,coeff_mem_contentIdeal]
section CommSemiring
variable {R:Type*} [CommSemiring R] {p q:R[X]}
theorem contentIdeal_le_contentIdeal_of_dvd (hpq:p∣q):q.contentIdeal ≤ p.contentIdeal:=by
 obtain ⟨p',rfl⟩:=hpq
 exact le_trans (p.contentIdeal_mul_le_mul_contentIdeal p') mul_le_right
theorem _root_.Submodule.IsPrincipal.contentIdeal_generator_dvd_coeff
   (h_prin:p.contentIdeal.IsPrincipal) (n:ℕ):h_prin.generator∣p.coeff n:=by
 have:=p.coeff_mem_contentIdeal n
 rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at this
 obtain ⟨_,ha⟩:=this
 simp [ha]
theorem _root_.Submodule.IsPrincipal.contentIdeal_generator_dvd
   (h_prin:p.contentIdeal.IsPrincipal):C h_prin.generator∣p:=by
 rw [C_dvd_iff_dvd_coeff]
 exact fun i↦h_prin.contentIdeal_generator_dvd_coeff i
theorem _root_.Submodule.IsPrincipal.contentIdeal_le_span_iff_dvd
   (h_prin:p.contentIdeal.IsPrincipal) (r:R):
   p.contentIdeal ≤ span {r} ↔ C r∣p:=by
 constructor
 · rw [←p.contentIdeal.span_singleton_generator]
   intro _
   calc
   C r∣C h_prin.generator:=by
     apply _root_.map_dvd C
     rwa [←span_singleton_le_span_singleton]
    _∣p:=h_prin.contentIdeal_generator_dvd
 · rw [←contentIdeal_C r]
   exact fun h↦contentIdeal_le_contentIdeal_of_dvd h
theorem isPrimitive_of_contentIdeal_eq_top (h:p.contentIdeal=⊤):p.IsPrimitive:=by
 have h_prin:p.contentIdeal.IsPrincipal:=by
   rw [h]
   exact top_isPrincipal
 intro r
 simp [←h_prin.contentIdeal_le_span_iff_dvd r,h]
theorem _root_.Submodule.IsPrincipal.isPrimitive_iff_contentIdeal_eq_top
   (h_prin:p.contentIdeal.IsPrincipal):p.IsPrimitive ↔ p.contentIdeal=⊤:=by
 refine ⟨?_,fun h↦isPrimitive_of_contentIdeal_eq_top h⟩
 contrapose!
 simp only [IsPrimitive,not_forall]
 intro _
 use h_prin.generator,h_prin.contentIdeal_generator_dvd
 simp_all [←Ideal.span_singleton_eq_top]
theorem contentIdeal_eq_top_of_contentIdeal_mul_eq_top
   (h:(p*q).contentIdeal=⊤):p.contentIdeal=⊤:=by
 apply le_antisymm le_top
 calc
 ⊤=(p*q).contentIdeal:=h.symm
 _ ≤ p.contentIdeal*q.contentIdeal:=contentIdeal_mul_le_mul_contentIdeal p q
 _ ≤ p.contentIdeal:=mul_le_right
end CommSemiring
section Ring
variable {R:Type*} [CommRing R] {p q:R[X]}
theorem mul_contentIdeal_le_radical_contentIdeal_mul:
   p.contentIdeal*q.contentIdeal ≤ ((p*q).contentIdeal).radical:=by
 rw [radical_eq_sInf,le_sInf_iff]
 intro P ⟨hpq,hPprime⟩
 rw [hPprime.mul_le]
 rw [←Ideal.mk_ker (I:=P)] at hpq ⊢
 simpa only [←map_eq_bot_iff_le_ker, ←contentIdeal_map_eq_map_contentIdeal,Polynomial.map_mul,
   contentIdeal_eq_bot_iff,mul_eq_zero] using hpq
theorem contentIdeal_mul_eq_top_of_contentIdeal_eq_top (hp:p.contentIdeal=⊤)
   (hq:q.contentIdeal=⊤):(p*q).contentIdeal=⊤:=by
 rw [←Ideal.radical_eq_top]
 apply le_antisymm le_top
 calc
   ⊤=p.contentIdeal*q.contentIdeal:=by simp [hp,hq]
   _ ≤ ((p*q).contentIdeal).radical:=mul_contentIdeal_le_radical_contentIdeal_mul
end Ring
section NormalizedGCDMonoid
variable {R:Type*} [CommRing R] [NormalizedGCDMonoid R] {p:R[X]}
theorem contentIdeal_le_span_content:p.contentIdeal ≤ span {p.content}:=by
 rw [contentIdeal_def,span_le]
 intro _ h1
 rw [Finset.mem_coe,mem_coeffs_iff] at h1
 obtain ⟨n,_,h2⟩:=h1
 rw [SetLike.mem_coe,h2,mem_span_singleton]
 exact content_dvd_coeff n
theorem _root_.Submodule.IsPrincipal.contentIdeal_eq_span_content_of_isPrincipal
   (h_prin:p.contentIdeal.IsPrincipal):p.contentIdeal=span {p.content}:=by
 apply le_antisymm contentIdeal_le_span_content
 rw [←p.contentIdeal.span_singleton_generator,span_singleton_le_span_singleton,content,
   Finset.dvd_gcd_iff]
 exact fun n _↦h_prin.contentIdeal_generator_dvd_coeff n
end NormalizedGCDMonoid
section IsBezout
variable {R:Type*} [CommSemiring R] [IsBezout R] (p:R[X])
theorem isPrimitive_iff_contentIdeal_eq_top:p.IsPrimitive ↔ p.contentIdeal=⊤:=
 (IsBezout.isPrincipal_of_FG _ p.contentIdeal_FG).isPrimitive_iff_contentIdeal_eq_top
end IsBezout
end Polynomial
end ProximityFlatProofPort
end PackedLegacy_IT

/-! Packed from ProximityPrize.SubmissionLower.G3. -/
section PackedLegacy_G3
namespace ProximityPrize.SubmissionLower.RCN360
noncomputable section
variable {K L:Type} [Field K] [Field L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
def bimap (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial (Polynomial L):=P.map (Polynomial.mapRingHom f)
theorem bimap_primitive (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive):
   (bimap f P).IsPrimitive:=by
 apply Polynomial.isPrimitive_of_contentIdeal_eq_top
 rw [bimap,Polynomial.contentIdeal_map_eq_map_contentIdeal,
   (Polynomial.isPrimitive_iff_contentIdeal_eq_top P).mp hP,Ideal.map_top]
theorem bimap_natDegree_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   (bimap f P).natDegree ≤ P.natDegree:=
 Polynomial.natDegree_map_le
theorem bimap_degreeX_le (f:K →+*L) (P:Polynomial (Polynomial K)):
   Polynomial.Bivariate.degreeX (bimap f P) ≤ Polynomial.Bivariate.degreeX P:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bimap f P).coeff j=(P.coeff j).map f by simp [bimap]]
 exact Polynomial.natDegree_map_le.trans
   (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j)
theorem bimap_specialization (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)=
     P.map (Polynomial.eval₂RingHom f x):=by
 ext j
 simp [bimap,Polynomial.eval_map]
theorem bimap_eval_natural (f:K →+*L)
   (P:Polynomial (Polynomial K)) (x y:K):
   ((bimap f P).map (Polynomial.evalRingHom (f x))).eval (f y)=
     f ((P.map (Polynomial.evalRingHom x)).eval y):=by
 have h:(bimap f P).map (Polynomial.evalRingHom (f x))=
     (P.map (Polynomial.evalRingHom x)).map f:=by
   ext j
   simp [bimap,Polynomial.eval_map,Polynomial.eval₂_at_apply]
 rw [h,Polynomial.eval_map_apply]
theorem bimap_comp {M:Type} [Field M]
   (f:K →+*L) (g:L →+*M) (P:Polynomial (Polynomial K)):
   bimap g (bimap f P)=bimap (g.comp f) P:=by
 ext j i
 simp [bimap]
theorem bimap_resultant_ne_zero (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hres:Polynomial.resultant P Q m n≠0):
   Polynomial.resultant (bimap f P) (bimap f Q) m n≠0:=by
 unfold bimap
 rw [Polynomial.resultant_map_map]
 intro hzero
 apply hres
 apply Polynomial.map_injective f f.injective
 simpa only [Polynomial.coe_mapRingHom,Polynomial.map_zero] using hzero
theorem bimap_specialization_ne_zero (f:K →+*L)
   (P:Polynomial (Polynomial K)) (hP:P.IsPrimitive) (x:L):
   (bimap f P).map (Polynomial.evalRingHom x)≠0:=by
 classical
 exact RCN362.primitive_specialization_ne_zero
   (bimap f P) (bimap_primitive f P hP) x
theorem common_points_card_le_after_extension (f:K →+*L)
   (P Q:Polynomial (Polynomial K)) (points:Finset (L × L))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (hroots:∀ point∈points,
     ((bimap f P).map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     ((bimap f Q).map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hcount:=RCN363.common_points_card_le_bidegree_bound
   (bimap f P) (bimap f Q) P.natDegree Q.natDegree points
   (bimap_natDegree_le f P) (bimap_natDegree_le f Q)
   (bimap_resultant_ne_zero f P Q P.natDegree Q.natDegree
     (RCN362.irreducible_resultant_ne_zero_of_not_dvd
       P Q hP hdeg hproper))
   (fun point _ => Or.inl (bimap_specialization_ne_zero f P
     (hP.isPrimitive (Nat.ne_of_gt hdeg)) point.1)) hroots
 exact hcount.trans (Nat.add_le_add
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f P))
   (Nat.mul_le_mul_left _ (bimap_degreeX_le f Q)))
end
end ProximityPrize.SubmissionLower.RCN360
end PackedLegacy_G3

/-! Packed from ProximityPrize.SubmissionLower.G6. -/
section PackedLegacy_G6
namespace ProximityPrize.SubmissionLower.RCN364
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
theorem integral_and_separable_of_small_annihilator
   (p:ℕ) [CharP K p] (f:Polynomial K) (x:L)
   (hf:f≠0) (hx:Polynomial.aeval x f=0) (hdegree:f.natDegree < p):
   IsIntegral K x∧IsSeparable K x:=by
 have hint:IsIntegral K x:=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
 have hmin:(minpoly K x).natDegree ≤ f.natDegree:=
   Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hf
 refine ⟨hint,?_⟩
 change (minpoly K x).Separable
 apply (Polynomial.separable_def _).mpr
 exact irreducible_isCoprime_derivative_of_natDegree_lt_char p (minpoly K x)
   (minpoly.irreducible hint) (minpoly.natDegree_pos hint) (hmin.trans_lt hdegree)
theorem resultant_aeval_eq_zero_of_common_root
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPdegree:P.natDegree ≤ m) (hQdegree:Q.natDegree ≤ n)
   (hpositive:m≠0∨n≠0) (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0):
   Polynomial.aeval y (Polynomial.resultant P Q m n)=0:=by
 obtain ⟨U,V,_,_,hidentity⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   P Q hPdegree hQdegree hpositive
 have heval:=congrArg
   (fun F:Polynomial (Polynomial K) =>
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r F) hidentity
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
   hP,hQ,zero_mul,zero_add] at heval
 exact heval.symm
theorem finite_separable_of_two_generators (y r:L)
   (hy:IsSeparable K y) (hr:IsSeparable K r)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 letI:FiniteDimensional K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.finiteDimensional_adjoin_pair hy.isIntegral hr.isIntegral
 letI:Algebra.IsSeparable K (IntermediateField.adjoin K ({y,r}:Set L)):=
   IntermediateField.isSeparable_adjoin_pair_of_isSeparable K L hy hr
 letI:FiniteDimensional K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hsepTop:Algebra.IsSeparable K (⊤:IntermediateField K L):=by
   rw [←hgenerate]
   infer_instance
 have hfinite:FiniteDimensional K L:=Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K) (E:=L)).toLinearMap
   (IntermediateField.topEquiv (F:=K) (E:=L)).surjective
 exact ⟨hfinite,(IntermediateField.isSeparable_top (F:=K) (E:=L)).mp hsepTop⟩
theorem finite_separable_of_proper_plane_roots
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:L)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
   FiniteDimensional K L∧Algebra.IsSeparable K L:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=resultant_aeval_eq_zero_of_common_root P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
 obtain ⟨_,hySeparable⟩:=integral_and_separable_of_small_annihilator p
   (Polynomial.resultant P Q P.natDegree Q.natDegree) y hresne hresroot hresultantDegree
 let S:IntermediateField K L:=IntermediateField.adjoin K {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
 letI:DecidableEq S:=Classical.decEq S
 letI:CharP S p:=charP_of_injective_algebraMap (algebraMap K S).injective p
 let g:Polynomial K →+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
   exact h
 have hPydegree:Py.natDegree < p:=Polynomial.natDegree_map_le.trans_lt hRdegree
 have hcoefficient:(algebraMap S L).comp g=
     Polynomial.eval₂RingHom (algebraMap K L) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K S L c).symm
   · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K L) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S L) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 obtain ⟨_,hrSeparable⟩:=integral_and_separable_of_small_annihilator p
   Py r hPyne hPyroot hPydegree
 letI:Algebra.IsSeparable K S:=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr hySeparable
 have hrOverK:IsSeparable K r:=
   IsSeparable.of_algebra_isSeparable_of_isSeparable K hrSeparable
 exact finite_separable_of_two_generators y r hySeparable hrOverK hgenerate
end
end ProximityPrize.SubmissionLower.RCN364
end PackedLegacy_G6

/-! Packed from ProximityPrize.SubmissionLower.G4. -/
section PackedLegacy_G4
namespace ProximityPrize.SubmissionLower.RCN361
open RCN360
noncomputable section
section Evaluation
variable (K E:Type) [Field K] [Field E] [Algebra K E]
def planeEval (y r:E):Polynomial (Polynomial K) →+*E:=
 (Polynomial.evalRingHom r).comp
   (Polynomial.mapRingHom (Polynomial.eval₂RingHom (algebraMap K E) y))
def relationIdeal (y r:E):Ideal (Polynomial (Polynomial K)):=
 RingHom.ker (planeEval K E y r)
theorem planeEval_eq (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     ((bimap (algebraMap K E) P).map (Polynomial.evalRingHom y)).eval r:=by
 simp only [planeEval,RingHom.comp_apply,Polynomial.coe_mapRingHom,
   Polynomial.coe_evalRingHom]
 rw [bimap_specialization]
variable (Ω:Type) [Field Ω] [Algebra K Ω]
theorem algHom_planeEval (φ:E →ₐ[K] Ω) (y r:E)
   (P:Polynomial (Polynomial K)):
   φ (planeEval K E y r P)=planeEval K Ω (φ y) (φ r) P:=by
 rw [planeEval_eq,planeEval_eq]
 have h:=bimap_eval_natural φ.toRingHom
   (bimap (algebraMap K E) P) y r
 have hcomp:φ.toRingHom.comp (algebraMap K E)=algebraMap K Ω:=by
   ext a
   exact φ.commutes a
 rw [bimap_comp,hcomp] at h
 exact h.symm
theorem algHom_eq_of_generating_pair (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (φ ψ:E →ₐ[K] Ω) (hy:φ y=ψ y) (hr:φ r=ψ r):φ=ψ:=by
 apply AlgHom.ext
 intro x
 have hx:x∈IntermediateField.adjoin K ({y,r}:Set E):=by
   rw [hgen]
   trivial
 exact IntermediateField.adjoin_induction K
   (p:=fun a _ => φ a=ψ a)
   (fun a ha => by
     rcases Set.mem_insert_iff.mp ha with h | h
     · simpa only [h] using hy
     · simpa only [Set.mem_singleton_iff.mp h] using hr)
   (fun a => by rw [φ.commutes,ψ.commutes])
   (fun a b _ _ ha hb => by simp only [map_add,ha,hb])
   (fun a _ ha => by simp only [map_inv₀,ha])
   (fun a b _ _ ha hb => by simp only [map_mul,ha,hb]) hx
theorem embedding_pair_injective (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤):
   Function.Injective (fun φ:E →ₐ[K] Ω => (φ y,φ r)):=by
 intro φ ψ h
 exact algHom_eq_of_generating_pair K E Ω y r hgen φ ψ
   (congrArg Prod.fst h) (congrArg Prod.snd h)
variable (E':Type) [Field E'] [Algebra K E']
theorem relationIdeal_eq_of_embedding_pairs_eq
   (y r:E) (y' r':E') (φ:E →ₐ[K] Ω) (ψ:E' →ₐ[K] Ω)
   (hy:φ y=ψ y') (hr:φ r=ψ r'):
   relationIdeal K E y r=relationIdeal K E' y' r':=by
 apply Ideal.ext
 intro P
 change planeEval K E y r P=0 ↔ planeEval K E' y' r' P=0
 have heq:φ (planeEval K E y r P)=ψ (planeEval K E' y' r' P):=by
   rw [algHom_planeEval,algHom_planeEval,hy,hr]
 constructor
 · intro h
   apply ψ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq.symm
 · intro h
   apply φ.injective
   simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,h,map_zero] using heq
end Evaluation
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
 [FiniteDimensional K E] [Algebra.IsSeparable K E]
theorem finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:E) (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hPy:planeEval K E y r P=0) (hQy:planeEval K E y r Q=0):
   Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
     P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure E
 letI:Fintype (E →ₐ[K] Ω):=Fintype.ofFinite _
 let points:Finset (Ω × Ω):=Finset.univ.image (fun φ:E →ₐ[K] Ω => (φ y,φ r))
 have hcard:points.card=Module.finrank K E:=by
   rw [Finset.card_image_of_injective _ (embedding_pair_injective K E Ω y r hgen),
     Finset.card_univ,Fintype.card_eq_nat_card]
   exact Field.finSepDegree_eq_finrank_of_isSeparable K E
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨φ,_,rfl⟩:=Finset.mem_image.mp hp
 constructor
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r P,hPy,map_zero]
 · rw [←planeEval_eq]
   rw [←algHom_planeEval K E Ω φ y r Q,hQy,map_zero]
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)] [∀ i,Algebra.IsSeparable K (E i)]
theorem sum_finrank_le_planar_bound
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hdeg:0 < P.natDegree) (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hPy:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQy:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 let Ω:=AlgebraicClosure K
 letI:∀ i,Fintype (E i →ₐ[K] Ω):=fun i => Fintype.ofFinite _
 let pair:(Σ i,E i →ₐ[K] Ω) → Ω × Ω:=
   fun a => (a.2 (y a.1),a.2 (r a.1))
 have hinj:Function.Injective pair:=by
   rintro ⟨i,φ⟩ ⟨j,ψ⟩ h
   have hij:i=j:=hkernels
     (relationIdeal_eq_of_embedding_pairs_eq K (E i) Ω (E j)
       (y i) (r i) (y j) (r j) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h))
   subst j
   have heq:φ=ψ:=algHom_eq_of_generating_pair K (E i) Ω
     (y i) (r i) (hgen i) φ ψ (congrArg Prod.fst h) (congrArg Prod.snd h)
   exact congrArg (Sigma.mk i) heq
 let points:Finset (Ω × Ω):=Finset.univ.image pair
 have hcard:points.card=∑ i,Module.finrank K (E i):=by
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_sigma]
   apply Finset.sum_congr rfl
   intro i _
   rw [Fintype.card_eq_nat_card,
     ←Field.finSepDegree_eq_of_isAlgClosed K (E i) Ω,
     Field.finSepDegree_eq_finrank_of_isSeparable]
 rw [←hcard]
 apply common_points_card_le_after_extension (algebraMap K Ω) P Q points hP hdeg hproper
 intro point hp
 obtain ⟨⟨i,φ⟩,_,rfl⟩:=Finset.mem_image.mp hp
 change
   ((bimap (algebraMap K Ω) P).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0∧
   ((bimap (algebraMap K Ω) Q).map (Polynomial.evalRingHom (φ (y i)))).eval (φ (r i))=0
 constructor
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) P,hPy i,map_zero]
 · rw [←planeEval_eq, ←algHom_planeEval K (E i) Ω φ (y i) (r i) Q,hQy i,map_zero]
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN361
end PackedLegacy_G4

/-! Packed from ProximityPrize.SubmissionLower.W7. -/
section PackedLegacy_W7
namespace ProximityPrize.SubmissionLower.RCN365
open RCN361
noncomputable section
section SingleField
variable (K E:Type) [Field K] [Field E] [Algebra K E]
theorem planeEval_eq_eval₂ (y r:E) (P:Polynomial (Polynomial K)):
   planeEval K E y r P=
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K E) y) r P:=by
 change (P.map (Polynomial.eval₂RingHom (algebraMap K E) y)).eval r=_
 rw [Polynomial.eval_map]
theorem finite_separable_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:E)
   (hgenerate:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hP:planeEval K E y r P=0) (hQ:planeEval K E y r Q=0):
   FiniteDimensional K E∧Algebra.IsSeparable K E∧
     Module.finrank K E ≤ Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hPeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r P=0:=by
   rw [←planeEval_eq_eval₂]
   exact hP
 have hQeval:Polynomial.eval₂
     (Polynomial.eval₂RingHom (algebraMap K E) y) r Q=0:=by
   rw [←planeEval_eq_eval₂]
   exact hQ
 have hfields:=RCN364.finite_separable_of_proper_plane_roots
   p P Q hirreducible hpositive hproper hRdegree hresultantDegree y r hPeval hQeval hgenerate
 letI:FiniteDimensional K E:=hfields.1
 letI:Algebra.IsSeparable K E:=hfields.2
 exact ⟨hfields.1,hfields.2,
   RCN361.finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hP hQ⟩
end SingleField
section FiniteFamily
variable (K:Type) [Field K]
 {I:Type} [Fintype I] (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
theorem finite_separable_sum_finrank_le_planar_bound
   (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
   (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
   (y r:∀ i,E i)
   (hgenerate:∀ i,IntermediateField.adjoin K ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i => relationIdeal K (E i) (y i) (r i)))
   (hP:∀ i,planeEval K (E i) (y i) (r i) P=0)
   (hQ:∀ i,planeEval K (E i) (y i) (r i) Q=0):
   (∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i))∧
     (∑ i,Module.finrank K (E i)) ≤
       Q.natDegree*Polynomial.Bivariate.degreeX P+
         P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 have hfields:∀ i,FiniteDimensional K (E i)∧Algebra.IsSeparable K (E i):=by
   intro i
   have h:=finite_separable_finrank_le_planar_bound K (E i)
     p P Q hirreducible hpositive hproper hRdegree hresultantDegree
     (y i) (r i) (hgenerate i) (hP i) (hQ i)
   exact ⟨h.1,h.2.1⟩
 letI:∀ i,FiniteDimensional K (E i):=fun i => (hfields i).1
 letI:∀ i,Algebra.IsSeparable K (E i):=fun i => (hfields i).2
 exact ⟨hfields,
   RCN361.sum_finrank_le_planar_bound K E P Q
     hirreducible hpositive hproper y r hgenerate hkernels hP hQ⟩
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN365
end PackedLegacy_W7

/-! Packed from ProximityPrize.SubmissionLower.X4. -/
section PackedLegacy_X4
namespace ProximityPrize.SubmissionLower.RCN010
open RCN002 RCN005
 RCN371 RCN011
noncomputable section
theorem order_cover (order:Fin 3 ≃ Fin 3) (l:Fin 3):
   l=order 0∨l=order 2∨l=order 1:=by
 have h:∀ i:Fin 3,i=0∨i=2∨i=1:=by decide
 rcases h (order.symm l) with hl | hl | hl
 · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl)
 · exact Or.inr (Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
 · exact Or.inr (Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
variable (K:Type) [Field K]
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem actual_generators:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P (order 2),coordinate K P (order 1)}:Set (CoordinateField K P))=⊤:=
 adjoin_two_coordinates_over_ratFunc_eq_top K P (order 0) (order 2) (order 1) ht
   (order_cover order)
theorem planeEval_eq_actual:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1))=
       actualPlaneEvaluation K order P ht:=rfl
theorem relationIdeal_eq_actual:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   RCN361.relationIdeal (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1))=
       actualRelationKernel K order P ht:=rfl
theorem actual_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
 letI:CharP (RatFunc K) p:=
   charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
 have hirr:=planeMap_irreducible_of_component
   (K:=K) (order:=order) (P:=P) (ht:=ht) G hG hGmem
 have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_component
     (K:=K) (order:=order) (P:=P) (ht:=ht) G H hG hGmem).mp h)
 have hGroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order G)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order G)=0
   exact (actualPlane_root_iff K order P ht G).mpr hGmem
 have hHroots:RCN361.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order H)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order H)=0
   exact (actualPlane_root_iff K order P ht H).mpr hHmem
 exact RCN365.finite_separable_finrank_le_planar_bound
   (RatFunc K) (CoordinateField K P) p (planeMap K order G) (planeMap K order H)
   hirr hpositive hproperPlane hRdegree hresultantDegree
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (actual_generators K order P ht) hGroots hHroots
end Component
section FiniteFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   letI:CharP (RatFunc K) p:=
     charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
   have hirr:=planeMap_irreducible_of_component
     (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro h
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G H hG (hGmem i₀)).mp h)
   have hkernels:Function.Injective (fun i =>
       RCN361.relationIdeal (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i => actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   exact RCN365.finite_separable_sum_finrank_le_planar_bound
     (RatFunc K) (fun i => CoordinateField K (P i)) p
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     hRdegree hresultantDegree
     (fun i => coordinate K (P i) (order 2)) (fun i => coordinate K (P i) (order 1))
     (fun i => actual_generators K order (P i) (ht i)) hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN010
end PackedLegacy_X4

/-! Packed from ProximityPrize.SubmissionLower.H1. -/
section PackedLegacy_H1
namespace ProximityPrize.SubmissionLower.RCN009
open RCN371 RCN011
noncomputable section
variable (K:Type) [Field K]
section FirstCoordinate
variable {A:Type} [Field A]
def firstMap (φ:Polynomial K →+*A):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 2) A:=
 (MvPolynomial.map φ).comp (collectFirst K).toRingHom
@[simp] theorem firstMap_C (φ:Polynomial K →+*A) (a:K):
   firstMap K φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_zero (φ:Polynomial K →+*A):
   firstMap K φ (MvPolynomial.X (0:Fin 3))=MvPolynomial.C (φ Polynomial.X):=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
@[simp] theorem firstMap_X_succ (φ:Polynomial K →+*A) (i:Fin 2):
   firstMap K φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
 simp [firstMap,collectFirst,MvPolynomial.renameEquiv_apply]
theorem firstMap_eq_eval₂Hom (φ:Polynomial K →+*A):
   firstMap K φ=
     MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
       (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem firstMap_monomial (φ:Polynomial K →+*A)
   (d:Fin 3 →₀ ℕ) (a:K):
   firstMap K φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [firstMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,map_mul,map_pow]
 ring
theorem support_firstMap_subset (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K):
   (firstMap K φ F).support ⊆ F.support.image Finsupp.tail:=by
 classical
 have hsum:firstMap K φ F=
     ∑ d∈F.support,firstMap K φ (MvPolynomial.monomial d (MvPolynomial.coeff d F)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [firstMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem firstMap_degreeOf_le (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K) (i:Fin 2):
   (firstMap K φ F).degreeOf i ≤ F.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_firstMap_subset K φ F he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
end FirstCoordinate
theorem rationalMap_eq_firstMap (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=firstMap K (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F):=rfl
theorem rationalMap_degreeOf_le (order:Fin 3 ≃ Fin 3) (F:Original K) (i:Fin 2):
   (rationalMap K order F).degreeOf i ≤ F.degreeOf (order i.succ):=by
 rw [rationalMap_eq_firstMap]
 calc
   _ ≤ (MvPolynomial.rename order.symm F).degreeOf i.succ:=
     firstMap_degreeOf_le K _ _ i
   _=F.degreeOf (order i.succ):=by
     simpa only [Equiv.symm_apply_apply] using
       (MvPolynomial.degreeOf_rename_of_injective (p:=F) order.symm.injective
         (order i.succ))
section NestedDegrees
variable (A:Type) [Field A]
theorem bivariateEquiv_natDegree (f:MvPolynomial (Fin 2) A):
   (bivariateEquiv A f).natDegree=f.degreeOf 0:=by
 change (Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   (MvPolynomial.finSuccEquiv A 1 f)).natDegree=f.degreeOf 0
 rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective]
 exact MvPolynomial.natDegree_finSuccEquiv f
theorem uniqueAlgEquiv_natDegree_le (f:MvPolynomial (Fin 1) A):
   (MvPolynomial.uniqueAlgEquiv A (Fin 1) f).natDegree ≤ f.degreeOf 0:=by
 classical
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 rw [MvPolynomial.coeff_uniqueAlgEquiv]
 by_contra hne
 have hd:=MvPolynomial.monomial_le_degreeOf (0:Fin 1)
   (MvPolynomial.mem_support_iff.mpr hne)
 have hdefault:(default:Fin 1)=0:=Subsingleton.elim _ _
 simp only [hdefault,Finsupp.single_eq_same] at hd
 omega
theorem bivariateEquiv_degreeX_le (f:MvPolynomial (Fin 2) A):
   Polynomial.Bivariate.degreeX (bivariateEquiv A f) ≤ f.degreeOf 1:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bivariateEquiv A f).coeff j=
   MvPolynomial.uniqueAlgEquiv A (Fin 1) ((MvPolynomial.finSuccEquiv A 1 f).coeff j) by
   simp [bivariateEquiv]]
 exact (uniqueAlgEquiv_natDegree_le A _).trans
   (MvPolynomial.degreeOf_coeff_finSuccEquiv f (0:Fin 1) j)
end NestedDegrees
theorem planeMap_natDegree_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K order F).natDegree ≤ F.degreeOf (order 1):=by
 change (bivariateEquiv (RatFunc K) (rationalMap K order F)).natDegree ≤ _
 rw [bivariateEquiv_natDegree]
 exact rationalMap_degreeOf_le K order F (0:Fin 2)
theorem planeMap_degreeX_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   Polynomial.Bivariate.degreeX (planeMap K order F) ≤ F.degreeOf (order 2):=by
 exact (bivariateEquiv_degreeX_le (RatFunc K) (rationalMap K order F)).trans
   (rationalMap_degreeOf_le K order F (1:Fin 2))
theorem planeMap_resultant_natDegree_le (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree ≤
     H.degreeOf (order 1)*G.degreeOf (order 2)+
       G.degreeOf (order 1)*H.degreeOf (order 2):=by
 exact (bivariate_resultant_natDegree_le (planeMap K order G) (planeMap K order H)
   (planeMap K order G).natDegree (planeMap K order H).natDegree).trans
     (Nat.add_le_add
       (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
       (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H)))
theorem original_characteristic_gates (order:Fin 3 ≃ Fin 3) (G H:Original K) (p:ℕ)
   (houter:G.degreeOf (order 1) < p)
   (hmixed:H.degreeOf (order 1)*G.degreeOf (order 2)+
     G.degreeOf (order 1)*H.degreeOf (order 2) < p):
   (planeMap K order G).natDegree < p∧
     (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree < p:=
 ⟨(planeMap_natDegree_le K order G).trans_lt houter,
   (planeMap_resultant_natDegree_le K order G H).trans_lt hmixed⟩
end
end ProximityPrize.SubmissionLower.RCN009
end PackedLegacy_H1

/-! Packed from ProximityPrize.SubmissionLower.X5. -/
section PackedLegacy_X5
namespace ProximityPrize.SubmissionLower.RCN013
open RCN002 RCN371 RCN011 RCN009
noncomputable section
variable (K:Type) [Field K]
def swapOtherOrder (order:Fin 3 ≃ Fin 3):Fin 3 ≃ Fin 3:=
 (Equiv.swap (1:Fin 3) 2).trans order
@[simp] theorem swapOtherOrder_zero (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 0=order 0:=by
 simp [swapOtherOrder,Equiv.swap_apply_def]
@[simp] theorem swapOtherOrder_one (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 1=order 2:=by
 simp [swapOtherOrder]
@[simp] theorem swapOtherOrder_two (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 2=order 1:=by
 simp [swapOtherOrder]
theorem rationalMap_first (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 0))=
     MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):=by
 simp [rationalMap]
theorem rationalMap_outer (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 1))=MvPolynomial.X 0:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [rationalMap,h]
theorem rationalMap_inner (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 2))=MvPolynomial.X 1:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [rationalMap,h]
theorem rationalMap_swapOtherOrder (order:Fin 3 ≃ Fin 3):
   rationalMap K (swapOtherOrder order)=
     (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)).toRingHom.comp
       (rationalMap K order):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp [rationalMap]
 · intro j
   obtain ⟨i,rfl⟩:=order.surjective j
   have hi:i=0∨i=1∨i=2:=by omega
   rcases hi with rfl | rfl | rfl
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 0)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
         MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) by
       simpa only [swapOtherOrder_zero] using rationalMap_first K (swapOtherOrder order)]
     rw [rationalMap_first]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 1)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
         MvPolynomial.X 1 by
       simpa only [swapOtherOrder_two] using rationalMap_inner K (swapOtherOrder order)]
     rw [rationalMap_outer]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 2)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
         MvPolynomial.X 0 by
       simpa only [swapOtherOrder_one] using rationalMap_outer K (swapOtherOrder order)]
     rw [rationalMap_inner]
     simp
theorem swapped_outer_degree (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K (swapOtherOrder order) F).natDegree=
     (rationalMap K order F).degreeOf 1:=by
 change (bivariateEquiv (RatFunc K) (rationalMap K (swapOtherOrder order) F)).natDegree=_
 rw [bivariateEquiv_natDegree,rationalMap_swapOtherOrder]
 change (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1) (rationalMap K order F)).degreeOf 0=_
 simpa only [Equiv.swap_apply_right] using
   (MvPolynomial.degreeOf_rename_of_injective (p:=rationalMap K order F)
     (Equiv.swap (0:Fin 2) 1).injective (1:Fin 2))
theorem positive_degree_of_irreducible {A:Type} [Field A]
   (f:MvPolynomial (Fin 2) A) (hf:Irreducible f):
   0 < f.degreeOf 0∨0 < f.degreeOf 1:=by
 classical
 by_cases h0:0 < f.degreeOf 0
 · exact Or.inl h0
 by_cases h1:0 < f.degreeOf 1
 · exact Or.inr h1
 exfalso
 have hdeg:∀ i:Fin 2,f.degreeOf i=0:=by
   intro i
   have hi:i=0∨i=1:=by omega
   rcases hi with rfl | rfl <;> omega
 have hconst:f=MvPolynomial.C (MvPolynomial.coeff 0 f):=by
   apply MvPolynomial.ext
   intro d
   by_cases hd:d=0
   · subst d
     simp
   · have hzero:MvPolynomial.coeff d f=0:=by
       by_contra hne
       have hm:d∈f.support:=MvPolynomial.mem_support_iff.mpr hne
       apply hd
       apply Finsupp.ext
       intro i
       have hle:=MvPolynomial.monomial_le_degreeOf i hm
       rw [hdeg i] at hle
       exact Nat.eq_zero_of_le_zero hle
     simp [hzero,Ne.symm hd]
 have ha:MvPolynomial.coeff 0 f≠0:=by
   intro h
   apply hf.ne_zero
   rw [hconst,h,map_zero]
 apply hf.not_isUnit
 rw [hconst]
 exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
theorem exists_positive_outer_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G:Original K)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   ∃ order':Fin 3 ≃ Fin 3,
     (order'=order∨order'=swapOtherOrder order)∧
     order' 0=order 0∧0 < (planeMap K order' G).natDegree:=by
 have hirr:=rationalMap_irreducible_of_component K order P G hG hmem ht
 rcases positive_degree_of_irreducible (rationalMap K order G) hirr with h0 | h1
 · refine ⟨order,Or.inl rfl,rfl,?_⟩
   change 0 < (bivariateEquiv (RatFunc K) (rationalMap K order G)).natDegree
   rwa [bivariateEquiv_natDegree]
 · exact ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
     by rwa [swapped_outer_degree]⟩
def originalMixedDegree (order:Fin 3 ≃ Fin 3) (G H:Original K):ℕ:=
 H.degreeOf (order 1)*G.degreeOf (order 2)+
   G.degreeOf (order 1)*H.degreeOf (order 2)
@[simp] theorem originalMixedDegree_swap (order:Fin 3 ≃ Fin 3) (G H:Original K):
   originalMixedDegree K (swapOtherOrder order) G H=originalMixedDegree K order G H:=by
 simp only [originalMixedDegree,swapOtherOrder_one,swapOtherOrder_two]
 ring
theorem exists_positive_characteristic_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G H:Original K) (p:ℕ)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   ∃ order':Fin 3 ≃ Fin 3,
     order' 0=order 0∧
     originalMixedDegree K order' G H=originalMixedDegree K order G H∧
     0 < (planeMap K order' G).natDegree∧
     (planeMap K order' G).natDegree < p∧
     (Polynomial.resultant (planeMap K order' G) (planeMap K order' H)).natDegree < p:=by
 obtain ⟨order',hor,hbase,hpos⟩:=exists_positive_outer_order K order P G hG hmem ht
 have hbudget:originalMixedDegree K order' G H=originalMixedDegree K order G H:=by
   rcases hor with rfl | rfl
   · rfl
   · exact originalMixedDegree_swap K order G H
 have hout:G.degreeOf (order' 1) < p:=by
   rcases hor with rfl | rfl
   · exact h1
   · simpa only [swapOtherOrder_one] using h2
 have hmix':H.degreeOf (order' 1)*G.degreeOf (order' 2)+
     G.degreeOf (order' 1)*H.degreeOf (order' 2) < p:=by
   change originalMixedDegree K order' G H < p
   rwa [hbudget]
 exact ⟨order',hbase,hbudget,hpos,
   original_characteristic_gates K order' G H p hout hmix'⟩
end
end ProximityPrize.SubmissionLower.RCN013
end PackedLegacy_X5

/-! Packed from ProximityPrize.SubmissionLower.G9. -/
section PackedLegacy_G9
namespace ProximityPrize.SubmissionLower.RCN004
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
noncomputable section
variable (K:Type) [Field K]
theorem rationalBaseAlgebra_congr (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
private def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
private def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
private def familySummary {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
     (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H) ≤
       originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H))
section Single
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem original_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
   exists_positive_characteristic_order K order P G H p hG hGmem ht h1 h2 hmixed
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,hbudget] at hresult
 exact hresult
end Single
section Family
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
     exists_positive_characteristic_order K order (P i₀) G H p
       hG (hGmem i₀) (ht i₀) h1 h2 hmixed
   have ht':∀ i,Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
         Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfields,hbound⟩:=actual_finite_separable_sum_finrank_bound
       K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
     exact ⟨hfields,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:(fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0) hbase (ht' i) (ht i)
   change familySummary K P (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end Family
theorem all_transcendental_coordinates_finite_separable
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 intro i hi
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hneq:order 1≠order 2:=by
   intro h
   have heq:=order.injective h
   exact (by decide:(1:Fin 3)≠2) heq
 have hbudget:originalMixedDegree K order G H < p:=
   hmixed (order 1) (order 2) hneq
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hbudget
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.RCN004
end PackedLegacy_G9

/-! Packed from ProximityPrize.SubmissionLower.AV. -/
section PackedLegacy_AV
namespace ProximityPrize.SubmissionLower.RCN001
open RCN002 RCN005
 RCN371 RCN007 RCN013
 RCN004
noncomputable section
variable (K:Type) [Field K]
section Family
variable {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem sum_actualCoordinateDegree_le_original
   (order:Fin 3 ≃ Fin 3) (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤ originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s => P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i) ≤ originalMixedDegree K order G H:=by
   have h:=original_finite_separable_sum_finrank_bound K order (fun i:s => P i)
     (fun i => i.2) hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper h1 h2 hmixed
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
theorem weighted_sum_actualCoordinateDegree_le (weight bound:Fin 3 → ℕ)
   (hbound:∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤ bound j):
   (∑ i,∑ j,weight j*actualCoordinateDegree K (P i) j) ≤
     ∑ j,weight j*bound j:=by
 rw [Finset.sum_comm]
 apply Finset.sum_le_sum
 intro j _
 rw [←Finset.mul_sum]
 exact Nat.mul_le_mul_left (weight j) (hbound j)
end Family
def coordinateMixedDegree (G H:Original K) (i:Fin 3):ℕ:=
 originalMixedDegree K (Equiv.swap 0 i) G H
@[simp] theorem coordinateMixedDegree_zero (G H:Original K):
   coordinateMixedDegree K G H 0=
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_one (G H:Original K):
   coordinateMixedDegree K G H 1=
     H.degreeOf 0*G.degreeOf 2+G.degreeOf 0*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_two (G H:Original K):
   coordinateMixedDegree K G H 2=
     H.degreeOf 0*G.degreeOf 1+G.degreeOf 0*H.degreeOf 1:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def] <;> ring
theorem sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (hinj:Function.Injective P) (j:Fin 3) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ k:Fin 3,G.degreeOf k < p)
   (hmixed:coordinateMixedDegree K G H j < p):
   (∑ i,actualCoordinateDegree K (P i) j) ≤ coordinateMixedDegree K G H j:=by
 have h:=sum_actualCoordinateDegree_le_original K P (Equiv.swap 0 j) hinj p G H
   hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
     (hdegree ((Equiv.swap 0 j) 2)) hmixed
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using h
theorem projectionsFiniteSeparable_of_original_gates
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ProjectionsFiniteSeparable K P:=
 all_transcendental_coordinates_finite_separable K P p G H
   hG hGmem hHmem hproper hdegree hmixed
end
end ProximityPrize.SubmissionLower.RCN001
end PackedLegacy_AV

/-! Packed from ProximityPrize.SubmissionLower.F. -/
section PackedLegacy_F
namespace ProximityPrize.SubmissionLower.RCN243
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def regularitySurface (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)
theorem selectedPoint_evaluation (selected:K → Polynomial K) (γ:K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem noLargeSelectedPencil_mono
   (selected:K → Polynomial K) (Γ Δ:Finset K) (w e:ℕ)
   (hsub:Δ ⊆ Γ) (hno:NoLargeSelectedPencil selected Γ w e):
   NoLargeSelectedPencil selected Δ w e:=by
 intro P₀ P₁ h₀ h₁
 apply le_trans (Finset.card_le_card ?_) (hno P₀ P₁ h₀ h₁)
 intro γ hγ
 obtain ⟨hΔ,hp⟩:=Finset.mem_filter.mp hγ
 exact Finset.mem_filter.mpr ⟨hsub hΔ,hp⟩
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem proper_cut_seed_bound_of_projection_sum
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i):
   Γ.card*(a-w) ≤ (nodes.card-w)*(∑ i,cap i*budget i)+
     (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have htmem:=regularComponent_T_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Ω C.1:=
     all_transcendental_coordinates_finite_separable Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hcutDegree
   have hcount:=prime_seed_incidence_sharp φ C.1 hproj
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolution γ (hsub hγ))
     (fun γ hγ => hregular γ (hsub hγ))
     (fun γ hγ => componentSeeds_on_prime Ω G T H Γ (selectedPoint φ selected) C γ hγ)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
   exact hcount
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem regularComponents_degree_budget
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬ G∣T)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p):
   ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 intro i
 letI:∀ C:RegularComponent Ω G T (regularitySurface φ F),C.1.IsPrime:=
   fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
 have hneq:(Equiv.swap (0:Fin 3) i) 1≠(Equiv.swap (0:Fin 3) i) 2:=
   (Equiv.swap (0:Fin 3) i).injective.ne (by decide)
 have hmixed:coordinateMixedDegree Ω G T i < p:=
   hcutDegree ((Equiv.swap (0:Fin 3) i) 1) ((Equiv.swap (0:Fin 3) i) 2) hneq
 exact sum_actualCoordinateDegree_at_le Ω
   (fun C:RegularComponent Ω G T (regularitySurface φ F) => C.1)
   Subtype.val_injective i p G T hG
   (regularComponent_G_mem Ω G T (regularitySurface φ F))
   (regularComponent_T_mem Ω G T (regularitySurface φ F))
   hproper hGdegree hmixed
theorem proper_cut_seed_bound
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,cap i*coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=
 proper_cut_seed_bound_of_projection_sum φ F G T hG hdiv hproper selected Γ
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hcutDegree
   hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
   (coordinateMixedDegree Ω G T) hcap
   (regularComponents_degree_budget φ F G T p hG hproper hGdegree hcutDegree)
end
end ProximityPrize.SubmissionLower.RCN243
end PackedLegacy_F

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier08 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.AI. -/
section PackedLegacy_AI
namespace ProximityPrize.SubmissionLower.RCN301
open RCN174 RCN256
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def agreements:ℕ:=182807
def errors:ℕ:=n-agreements
def gap:ℕ:=agreements-w
structure Profile where
 multiplicity:ℕ
 seedCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq
def profileA:Profile:=⟨25,5263,7⟩
def profileB:Profile:=⟨47,598,14⟩
def profileC:Profile:=⟨27,579299,6⟩
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
def coefficients (P:Profile):ℕ:=
 coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P:Profile):ℕ:=
 localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P:Profile):ℕ:=n*P.localRank
def nullity (P:Profile):ℕ:=P.coefficients-P.totalRank
end Profile
theorem coefficientCount_eq_sum_range_of_weighted_cutoff
   (D w L s t:ℕ) (ht:t ≤ L+1) (hD:D ≤ w*t):
   coefficientCount D w L s=
     ∑ i∈Finset.range t,
       ∑ j∈Finset.range (s+1),
         (L+1-i)*(D-w*i-(w-1)*j):=by
 have hsplit:L+1=t+(L+1-t):=by omega
 unfold coefficientCount
 rw [hsplit,Finset.sum_range_add]
 have htail:
     (∑ x∈Finset.range (L+1-t),
       ∑ j∈Finset.range (s+1),
         (t+(L+1-t)-(t+x))*
           (D-w*(t+x)-(w-1)*j))=0:=by
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   have hti:t ≤ t+i:=by omega
   have hzero:D-w*(t+i)=0:=
     Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
   simp [hzero]
 rw [htail,add_zero]
theorem base_values:
   errors=79337∧gap=51736:=by
 norm_num [errors,gap,n,agreements,w]
theorem profileA_coefficients_exact:
   profileA.coefficients=2811431653128:=by
 change coefficientCount (25*182807) 131071 5263 7=2811431653128
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (25*182807) 131071 5263 7 35 (by norm_num) (by norm_num)]
 decide
theorem profileA_localRank_exact:profileA.localRank=10724760:=by
 change localRankBound 25 5263 7=10724760
 decide
theorem profileA_values:
   profileA.weightedCap=4570175∧profileA.yCap=34∧
     profileA.localRank=10724760∧
     profileA.coefficients=2811431653128∧
     profileA.nullity=167688:=by
 refine ⟨by norm_num [Profile.weightedCap,profileA,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileA,agreements,w],
   profileA_localRank_exact,profileA_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,
   profileA_localRank_exact]
 norm_num [n]
theorem profileB_coefficients_exact:
   profileB.coefficients=1997482954410:=by
 change coefficientCount (47*182807) 131071 598 14=1997482954410
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (47*182807) 131071 598 14 66 (by norm_num) (by norm_num)]
 decide
theorem profileB_localRank_exact:profileB.localRank=7619680:=by
 change localRankBound 47 598 14=7619680
 decide
theorem profileB_values:
   profileB.weightedCap=8591929∧profileB.yCap=65∧
     profileB.localRank=7619680∧
     profileB.coefficients=1997482954410∧
     profileB.nullity=29560490:=by
 refine ⟨by norm_num [Profile.weightedCap,profileB,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileB,agreements,w],
   profileB_localRank_exact,profileB_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,
   profileB_localRank_exact]
 norm_num [n]
theorem profileC_coefficients_exact:
   profileC.coefficients=329531914715570:=by
 change coefficientCount (27*182807) 131071 579299 6=329531914715570
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (27*182807) 131071 579299 6 38 (by norm_num) (by norm_num)]
 decide
theorem profileC_localRank_exact:profileC.localRank=1257064494:=by
 change localRankBound 27 579299 6=1257064494
 decide
theorem profileC_values:
   profileC.weightedCap=4935789∧profileC.yCap=37∧
     profileC.localRank=1257064494∧
     profileC.coefficients=329531914715570∧
     profileC.nullity=434:=by
 refine ⟨by norm_num [Profile.weightedCap,profileC,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileC,agreements,w],
   profileC_localRank_exact,profileC_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileC_coefficients_exact,
   profileC_localRank_exact]
 norm_num [n]
theorem interpolation_gates:
     profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 simp only [Profile.totalRank]
 rw [profileA_coefficients_exact,profileA_localRank_exact,
   profileB_coefficients_exact,profileB_localRank_exact,
   profileC_coefficients_exact,profileC_localRank_exact]
 norm_num [n]
theorem characteristic_gates:
   profileA.characteristicCap < prime∧
     (2*profileA.slopeCap-1)*profileA.seedCap < prime∧
     profileA.slopeCap < prime∧
   profileB.characteristicCap < prime∧
     (2*profileB.slopeCap-1)*profileB.seedCap < prime∧
     profileB.slopeCap < prime∧
   profileC.characteristicCap < prime∧
     (2*profileC.slopeCap-1)*profileC.seedCap < prime∧
     profileC.slopeCap < prime:=by
 norm_num [Profile.characteristicCap,Profile.weightedCap,profileA,profileB,
   profileC,agreements,prime]
theorem meet_caps:
   (min profileA.multiplicity profileB.multiplicity,
       min profileA.seedCap profileB.seedCap,
       min profileA.slopeCap profileB.slopeCap)=(25,598,7)∧
     (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
       min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
       min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap)=
         (25,598,6):=by
 norm_num [profileA,profileB,profileC]
end ProximityPrize.SubmissionLower.RCN301
end PackedLegacy_AI

/-! Packed from ProximityPrize.SubmissionLower.H. -/
section PackedLegacy_H
namespace ProximityPrize.SubmissionLower.RCN213
open scoped BigOperators
theorem identity_degree_weight_cross_le
   (n a w k:ℕ) (hk:k ≤ w) (hwa:w < a) (han:a ≤ n):
   (n-k)*(a-w)*(w-k)*a ≤
     n*(a-w)*w*(a-k):=by
 have hka:k ≤ a:=hk.trans hwa.le
 have hkn:k ≤ n:=hka.trans han
 let d:=w-k
 let g:=a-w
 let c:=n-w
 have hdw:d ≤ w:=by dsimp [d];omega
 have haw:a=w+g:=by dsimp [g];omega
 have hnw:n=w+c:=by dsimp [c];omega
 have hak:a-k=d+g:=by dsimp [d,g];omega
 have hnk:n-k=d+c:=by dsimp [d,c];omega
 change (n-k)*g*d*a ≤ n*g*w*(a-k)
 rw [hnk,hak,haw,hnw]
 calc
   (d+c)*g*d*(w+g) ≤
       (d+c)*g*d*(w+g)+
         g*(w-d)*(w*d+g*(w+d)+c*g):=by omega
   _=(w+c)*g*w*(d+g):=by
     let t:=w-d
     have hwt:w=t+d:=by
       dsimp [t]
       omega
     rw [hwt]
     have hsub:t+d-d=t:=by omega
     simp only [hsub]
     ring
theorem identity_unit_weight_le
   (n a w k:ℕ) (hk:k ≤ w) (hwa:w < a) (han:a ≤ n):
   (n-k)*(a-w) ≤ (n-w)*(a-k):=by
 have hka:k ≤ a:=hk.trans hwa.le
 have hkn:k ≤ n:=hka.trans han
 have hak:a-k=(w-k)+(a-w):=by omega
 have hnk:n-k=(w-k)+(n-w):=by omega
 rw [hak,hnk]
 have hgap:a-w ≤ n-w:=Nat.sub_le_sub_right han w
 nlinarith [Nat.zero_le (w-k),Nat.zero_le (a-w),Nat.zero_le (n-w)]
theorem stratified_incidence_linear
   (q n a w k degreeCost unitCost U V:ℕ)
   (hk:k ≤ w) (hwa:w < a)
   (hraw:q*(a-k) ≤
     (n-k)*((w-k)*degreeCost+unitCost))
   (hdegree:(n-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:(n-k)*(a-w) ≤ V*(a-k)):
   q*(a-w) ≤ U*degreeCost+V*unitCost:=by
 have hak:0 < a-k:=by omega
 refine Nat.le_of_mul_le_mul_right ?_ hak
 calc
   q*(a-w)*(a-k)=(q*(a-k))*(a-w):=by ring
   _ ≤ ((n-k)*((w-k)*degreeCost+unitCost))*(a-w):=
     Nat.mul_le_mul_right (a-w) hraw
   _=((n-k)*(a-w)*(w-k))*degreeCost+
       ((n-k)*(a-w))*unitCost:=by ring
   _ ≤ (U*(a-k))*degreeCost+
       (V*(a-k))*unitCost:=
     Nat.add_le_add (Nat.mul_le_mul_right degreeCost hdegree)
       (Nat.mul_le_mul_right unitCost hunit)
   _=(U*degreeCost+V*unitCost)*(a-k):=by ring
def n:ℕ:=262144
def errors:ℕ:=78958
def agreements:ℕ:=n-errors
def w:ℕ:=131071
def gap:ℕ:=agreements-w
def degreeIncidence:ℕ:=9775005205
def unitIncidence:ℕ:=n-w
theorem parameter_values:
   agreements=183186∧gap=52115∧unitIncidence=131073:=by
 norm_num [agreements,gap,unitIncidence,n,errors,w]
theorem degreeIncidence_is_ceiling:
   degreeIncidence*agreements-n*gap*w=69370∧
     n*gap*w ≤ degreeIncidence*agreements:=by
 norm_num [degreeIncidence,agreements,gap,n,errors,w]
theorem degree_part_bound (k:ℕ) (hk:k ≤ w):
   (n-k)*gap*(w-k) ≤ degreeIncidence*(agreements-k):=by
 have hcross:=identity_degree_weight_cross_le n agreements w k hk
   (by norm_num [agreements,n,errors,w])
   (by norm_num [agreements,n,errors])
 have hceil:=degreeIncidence_is_ceiling.2
 have ha:0 < agreements:=by norm_num [agreements,n,errors]
 have hmul:=Nat.mul_le_mul_right (agreements-k) hceil
 have htotal:
     ((n-k)*gap*(w-k))*agreements ≤
       (degreeIncidence*(agreements-k))*agreements:=by
   calc
     ((n-k)*gap*(w-k))*agreements=
         (n-k)*(agreements-w)*(w-k)*agreements:=by
           rfl
     _ ≤ n*(agreements-w)*w*(agreements-k):=hcross
     _ ≤ (degreeIncidence*agreements)*(agreements-k):=by
       simpa only [gap] using hmul
     _=(degreeIncidence*(agreements-k))*agreements:=by ring
 exact Nat.le_of_mul_le_mul_right htotal ha
theorem unit_part_bound (k:ℕ) (hk:k ≤ w):
   (n-k)*gap ≤ unitIncidence*(agreements-k):=by
 simpa only [gap,unitIncidence] using
   identity_unit_weight_le n agreements w k hk
     (by norm_num [agreements,n,errors,w])
     (by norm_num [agreements,n,errors])
theorem stratified_incidence_quadratic
   (q k A B C:ℕ) (hk:k ≤ w)
   (hraw:(q*gap)*(agreements-k) ≤
     (n-k)*((w-k)*
       (A*degreeIncidence+B*unitIncidence)+
       (B*degreeIncidence+C*unitIncidence))):
   q*gap^2 ≤
     A*degreeIncidence^2+
       2*B*degreeIncidence*unitIncidence+
       C*unitIncidence^2:=by
 have hlinear:=stratified_incidence_linear
   (q*gap) n agreements w k
   (A*degreeIncidence+B*unitIncidence)
   (B*degreeIncidence+C*unitIncidence)
   degreeIncidence unitIncidence hk
   (by norm_num [agreements,n,errors,w]) hraw
   (degree_part_bound k hk) (unit_part_bound k hk)
 calc
   q*gap^2=(q*gap)*gap:=by ring
   _ ≤ degreeIncidence*(A*degreeIncidence+B*unitIncidence)+
       unitIncidence*(B*degreeIncidence+C*unitIncidence):=hlinear
   _=A*degreeIncidence^2+
       2*B*degreeIncidence*unitIncidence+
       C*unitIncidence^2:=by ring
def mixedQuadratic:ℕ:=3425875
def mixedLinear:ℕ:=15465
def mixedUnit:ℕ:=8
def zLinear:ℕ:=1205
def zUnit:ℕ:=8
def stratifiedPrimary:ℕ:=
 mixedQuadratic*degreeIncidence^2+
   2*mixedLinear*degreeIncidence*unitIncidence+
   mixedUnit*unitIncidence^2
def stratifiedZTail:ℕ:=
 (errors+1)*gap*
   (zLinear*degreeIncidence+zUnit*unitIncidence)
def retainedSingularContribution:ℕ:=6714916701272010710818955
def stratifiedTotalNumerator:ℕ:=
 stratifiedPrimary+stratifiedZTail+retainedSingularContribution
def gapSquared:ℕ:=gap^2
def ledgerCeiling:ℕ:=
 (stratifiedTotalNumerator+gapSquared-1)/gapSquared
def alignmentBudget:ℕ:=137490364055697543
theorem stratified_primary_exact:
   stratifiedPrimary=327344885660029958859664957:=by
 norm_num [stratifiedPrimary,mixedQuadratic,mixedLinear,mixedUnit,
   degreeIncidence,unitIncidence,n,w]
theorem stratified_z_tail_exact:
   stratifiedZTail=48469491604406824705565:=by
 norm_num [stratifiedZTail,zLinear,zUnit,degreeIncidence,unitIncidence,
   errors,gap,agreements,n,w]
theorem stratified_total_exact:
   stratifiedTotalNumerator=334108271852906376395189477:=by
 rw [show stratifiedTotalNumerator=
     stratifiedPrimary+stratifiedZTail+retainedSingularContribution by rfl,
   stratified_primary_exact,stratified_z_tail_exact]
 norm_num [retainedSingularContribution]
theorem gap_squared_exact:gapSquared=2715973225:=by
 norm_num [gapSquared,gap,agreements,n,errors,w]
theorem ledger_ceiling_exact:ledgerCeiling=123016040356180749:=by
 norm_num [ledgerCeiling,stratified_total_exact,gap_squared_exact]
theorem strict_budget:stratifiedTotalNumerator < alignmentBudget*gapSquared:=by
 rw [stratified_total_exact,gap_squared_exact]
 norm_num [alignmentBudget]
theorem budget_slack:alignmentBudget-ledgerCeiling=14474323699516794:=by
 rw [ledger_ceiling_exact]
 norm_num [alignmentBudget]
end ProximityPrize.SubmissionLower.RCN213
end PackedLegacy_H

/-! Packed from ProximityPrize.SubmissionLower.R. -/
section PackedLegacy_R
namespace ProximityPrize.SubmissionLower.RCN223
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def alignmentBudget:ℕ:=137490364055697543
def errors:ℕ:=78958
def agreements:ℕ:=n-errors
def multiplicity:ℕ:=31
def seedTotalCap:ℕ:=495
def slopeCap:ℕ:=8
def weightedCap:ℕ:=multiplicity*agreements
def yCap:ℕ:=(weightedCap-1)/w
def gap:ℕ:=agreements-w
def algebraicCap:ℕ:=(2*slopeCap-1)*seedTotalCap
def implicitWeightedCap:ℕ:=(2*slopeCap-1)*weightedCap
def implicitYCap:ℕ:=(implicitWeightedCap-1)/w
def coefficientCount:ℕ:=
 ∑ i∈range (seedTotalCap+1),
   ∑ j∈range (slopeCap+1),
     (seedTotalCap+1-i)*
       (weightedCap-w*i-(w-1)*j)
def contactExponent (r:ℕ):ℕ:=min (r+1) (multiplicity-r)
def localContactRank:ℕ:=
 ∑ r∈range multiplicity,
   (((slopeCap+1)*
       (∑ f∈range (min r seedTotalCap+1),
         (seedTotalCap+1-f)))-
     ((slopeCap+1-contactExponent r)*
       (∑ f∈range (min r seedTotalCap+1-contactExponent r),
         (seedTotalCap+1-contactExponent r-f))))
def totalContactRank:ℕ:=n*localContactRank
def rankMargin:ℕ:=coefficientCount-totalContactRank
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
 a.r*b.y*c.z+a.r*b.z*c.y+
 a.z*b.y*c.r+a.z*b.r*c.y
def unitZ:DegreeVector:=⟨0,0,1⟩
def liftedSurface:DegreeVector:=⟨implicitYCap,1,algebraicCap⟩
def implicitCut:DegreeVector:=⟨implicitYCap,0,algebraicCap⟩
def liftedLast:DegreeVector:=
 ⟨1+2*implicitWeightedCap*implicitYCap,
   implicitWeightedCap,
   2*implicitWeightedCap*algebraicCap⟩
def liftedAgreement:DegreeVector:=
 ⟨1+2*w*implicitYCap,
   w,
   2*w*algebraicCap+1⟩
def retainedSingularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
     mixed liftedSurface implicitCut liftedLast+
     (errors+1)*mixed liftedSurface implicitCut unitZ)+
   (n-w)*mixed liftedSurface implicitCut liftedAgreement
def retainedSingularContribution:ℕ:=gap*retainedSingularNumerator
theorem parameter_values:
   agreements=183186∧weightedCap=5678766∧yCap=43∧
   gap=52115∧algebraicCap=7425∧
   implicitWeightedCap=85181490∧implicitYCap=649:=by
 norm_num [agreements,n,errors,weightedCap,multiplicity,yCap,w,
   gap,algebraicCap,slopeCap,seedTotalCap,implicitWeightedCap,
   implicitYCap]
theorem coefficient_count_exact:coefficientCount=453847251690:=by
 rfl
theorem local_contact_rank_exact:localContactRank=1731288:=by
 rfl
theorem total_contact_rank_exact:totalContactRank=453846761472:=by
 rw [show totalContactRank=n*localContactRank by rfl,
   local_contact_rank_exact]
 norm_num [n]
theorem rank_margin_exact:rankMargin=490218:=by
 rw [show rankMargin=coefficientCount-totalContactRank by rfl,
   coefficient_count_exact,total_contact_rank_exact]
theorem interpolation_gate:totalContactRank < coefficientCount:=by
 rw [coefficient_count_exact,total_contact_rank_exact]
 norm_num
theorem characteristic_gates:
   weightedCap < prime∧implicitWeightedCap < prime∧
     algebraicCap < prime∧slopeCap < prime:=by
 norm_num [weightedCap,multiplicity,agreements,n,errors,
   implicitWeightedCap,algebraicCap,slopeCap,seedTotalCap,prime]
theorem retained_singular_numerator_exact:
   retainedSingularNumerator=128848061043308274217:=by
 norm_num [retainedSingularNumerator,liftedSurface,implicitCut,
   liftedLast,liftedAgreement,unitZ,mixed,implicitYCap,
   implicitWeightedCap,algebraicCap,yCap,weightedCap,multiplicity,
   agreements,n,errors,w,gap,slopeCap,seedTotalCap]
theorem retained_singular_contribution_exact:
   retainedSingularContribution=6714916701272010710818955:=by
 rw [show retainedSingularContribution=
     gap*retainedSingularNumerator by rfl,
   retained_singular_numerator_exact]
 norm_num [gap,agreements,n,errors,w]
theorem retained_singular_matches_residual_ledger:
   retainedSingularContribution=
     RCN213.retainedSingularContribution:=by
 rw [retained_singular_contribution_exact]
 rfl
theorem exact_stratified_ledger:
   RCN213.stratifiedTotalNumerator=
       334108271852906376395189477∧
     RCN213.ledgerCeiling=
       123016040356180749∧
     RCN213.alignmentBudget-
         RCN213.ledgerCeiling=
       14474323699516794:=by
 exact ⟨RCN213.stratified_total_exact,
   RCN213.ledger_ceiling_exact,
   RCN213.budget_slack⟩
theorem strict_alignment_budget:
   RCN213.stratifiedTotalNumerator <
     alignmentBudget*gap^2:=by
 rw [RCN213.stratified_total_exact]
 norm_num [alignmentBudget,gap,agreements,n,errors,w]
end ProximityPrize.SubmissionLower.RCN223
end PackedLegacy_R

/-! Packed from ProximityPrize.SubmissionLower.CB. -/
section PackedLegacy_CB
namespace ProximityPrize.SubmissionLower.RCN294
open scoped BigOperators
open RCN223
def sumVector {I:Type} [Fintype I] (v:I-> DegreeVector):DegreeVector:=
 ⟨∑ i,(v i).y,∑ i,(v i).r,∑ i,(v i).z⟩
def vectorLE (a b:DegreeVector):Prop:=
 a.y ≤ b.y∧a.r ≤ b.r∧a.z ≤ b.z
def dot (a b:DegreeVector):Nat:=
 a.y*b.y+a.r*b.r+a.z*b.z
theorem dot_mono_left {a b:DegreeVector} (c:DegreeVector)
   (h:vectorLE a b):dot a c ≤ dot b c:=
 Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
     (Nat.mul_le_mul_right c.r h.2.1))
   (Nat.mul_le_mul_right c.z h.2.2)
theorem dot_sum_left {I:Type} [Fintype I]
   (v:I-> DegreeVector) (a:DegreeVector):
   dot (sumVector v) a=∑ i,dot (v i) a:=by
 simp only [dot,sumVector,Finset.sum_add_distrib,Finset.sum_mul]
def implicitAggregateCost:DegreeVector:=
 ⟨algebraicCap,2*implicitYCap*algebraicCap,implicitYCap⟩
def implicitCoefficients:DegreeVector:=
 ⟨(n-w)*liftedAgreement.y,
   (n-w)*liftedAgreement.r,
   (n-w)*liftedAgreement.z+(errors+1)*gap⟩
def implicitCoreNumerator:Nat:=
 (n-w)*mixed liftedSurface implicitCut liftedAgreement+
   (errors+1)*gap*mixed liftedSurface implicitCut unitZ
theorem implicit_bound_eq_dot (v:DegreeVector):
   (n-w)*dot liftedAgreement v+(errors+1)*gap*v.z=
     dot v implicitCoefficients:=by
 simp only [implicitCoefficients,dot]
 ring
theorem implicit_aggregate_eq_core:
   dot implicitAggregateCost implicitCoefficients=implicitCoreNumerator:=by
 simp only [implicitAggregateCost,implicitCoefficients,
   implicitCoreNumerator,dot,mixed,liftedSurface,implicitCut,unitZ]
 ring
theorem sum_implicit_counts_bound {I:Type} [Fintype I]
   (count:I-> Nat) (cost:I-> DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:forall i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z):
   (∑ i,count i)*gap ≤ implicitCoreNumerator:=by
 calc
   _=∑ i,count i*gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) implicitCoefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←implicit_bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) implicitCoefficients:=
     (dot_sum_left cost implicitCoefficients).symm
   _ ≤ dot implicitAggregateCost implicitCoefficients:=
     dot_mono_left implicitCoefficients ⟨hy,hr,hz⟩
   _=implicitCoreNumerator:=implicit_aggregate_eq_core
theorem retained_singular_padding:
   retainedSingularNumerator=
     implicitCoreNumerator+
       gap*(algebraicCap+2*algebraicCap^2+
         mixed liftedSurface implicitCut liftedLast):=by
 simp only [retainedSingularNumerator,implicitCoreNumerator]
 ring
theorem implicit_with_exceptions_bound {I:Type} [Fintype I]
   (count:I-> Nat) (cost:I-> DegreeVector) (exceptions:Nat)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:forall i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap ≤ retainedSingularNumerator:=by
 have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
   _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
   _ ≤ retainedSingularNumerator:=by
     rw [retained_singular_padding]
     apply Nat.add_le_add_left
     calc
       2*algebraicCap^2*gap=gap*(2*algebraicCap^2):=by ring
       _ ≤ gap*(algebraicCap+2*algebraicCap^2+
           mixed liftedSurface implicitCut liftedLast):=
         Nat.mul_le_mul_left gap (by omega)
theorem implicit_with_exceptions_scaled_bound {I:Type} [Fintype I]
   (count:I-> Nat) (cost:I-> DegreeVector) (exceptions:Nat)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:forall i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap^2 ≤
     retainedSingularContribution:=by
 have h:=implicit_with_exceptions_bound count cost exceptions
   hy hr hz hcount hexceptions
 calc
   ((∑ i,count i)+exceptions)*gap^2=
       (((∑ i,count i)+exceptions)*gap)*gap:=by ring
   _ ≤ retainedSingularNumerator*gap:=Nat.mul_le_mul_right gap h
   _=retainedSingularContribution:=by
     simp only [retainedSingularContribution]
     ring
end ProximityPrize.SubmissionLower.RCN294
end PackedLegacy_CB

/-! Packed from ProximityPrize.SubmissionLower.AK. -/
section PackedLegacy_AK
namespace ProximityPrize.SubmissionLower.RCN318
open scoped BigOperators
open RCN223 RCN294
theorem implicit_with_exceptions_tight_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap ≤
     implicitCoreNumerator+2*algebraicCap^2*gap:=by
 have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
   _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
theorem implicit_with_exceptions_tight_scaled_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap^2 ≤
     (implicitCoreNumerator+2*algebraicCap^2*gap)*gap:=by
 have h:=implicit_with_exceptions_tight_bound count cost exceptions
   hy hr hz hcount hexceptions
 calc
   ((∑ i,count i)+exceptions)*gap^2=
       (((∑ i,count i)+exceptions)*gap)*gap:=by ring
   _ ≤ (implicitCoreNumerator+2*algebraicCap^2*gap)*gap:=
     Nat.mul_le_mul_right gap h
structure TightParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 D:ℕ
 L:ℕ
 s:ℕ
 deriving DecidableEq
namespace TightParameters
def errors (P:TightParameters):ℕ:=P.n-P.a
def gap (P:TightParameters):ℕ:=P.a-P.w
def kappa (P:TightParameters):ℕ:=2*P.s-1
def implicitYCap (P:TightParameters):ℕ:=(P.kappa*P.D-1)/P.w
def algebraicCap (P:TightParameters):ℕ:=P.kappa*P.L
def agreement (P:TightParameters):DegreeVector:=
 ⟨1+2*P.w*P.implicitYCap,
   P.w,
   2*P.w*P.algebraicCap+1⟩
def aggregateCost (P:TightParameters):DegreeVector:=
 ⟨P.algebraicCap,
   2*P.implicitYCap*P.algebraicCap,
   P.implicitYCap⟩
def coefficients (P:TightParameters):DegreeVector:=
 ⟨(P.n-P.w)*P.agreement.y,
   (P.n-P.w)*P.agreement.r,
   (P.n-P.w)*P.agreement.z+(P.errors+1)*P.gap⟩
def coreNumerator (P:TightParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.aggregateCost+
   (P.errors+1)*P.gap*P.implicitYCap
def tightNumerator (P:TightParameters):ℕ:=
 P.coreNumerator+2*P.algebraicCap^2*P.gap
def countCap (P:TightParameters):ℕ:=P.tightNumerator/P.gap
theorem bound_eq_dot (P:TightParameters) (v:DegreeVector):
   (P.n-P.w)*dot P.agreement v+
       (P.errors+1)*P.gap*v.z=
     dot v P.coefficients:=by
 simp only [coefficients,errors,gap,dot]
 ring
theorem aggregate_eq_core (P:TightParameters):
   dot P.aggregateCost P.coefficients=P.coreNumerator:=by
 simp only [aggregateCost,coefficients,coreNumerator,dot]
 ring
theorem sum_counts_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z):
   (∑ i,count i)*P.gap ≤ P.coreNumerator:=by
 calc
   _=∑ i,count i*P.gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) P.coefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←P.bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) P.coefficients:=
     (dot_sum_left cost P.coefficients).symm
   _ ≤ dot P.aggregateCost P.coefficients:=
     dot_mono_left P.coefficients ⟨hy,hr,hz⟩
   _=P.coreNumerator:=P.aggregate_eq_core
theorem with_exceptions_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*P.algebraicCap^2):
   ((∑ i,count i)+exceptions)*P.gap ≤ P.tightNumerator:=by
 have hmain:=P.sum_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*P.gap+exceptions*P.gap:=Nat.add_mul _ _ _
   _ ≤ P.coreNumerator+2*P.algebraicCap^2*P.gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
   _=P.tightNumerator:=rfl
theorem count_le_countCap (P:TightParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.tightNumerator):
   count ≤ P.countCap:=by
 exact (Nat.le_div_iff_mul_le hgap).mpr hcount
end TightParameters
def maximalResidualQA:TightParameters:=
 ⟨262144,131071,182807,4570175,5263,7⟩
def maximalResidualH:TightParameters:=
 ⟨262144,131071,182807,4570175,598,7⟩
theorem maximal_residual_values:
   maximalResidualQA.implicitYCap=453∧
     maximalResidualQA.algebraicCap=68419∧
     maximalResidualH.implicitYCap=453∧
     maximalResidualH.algebraicCap=7774:=by
 norm_num [maximalResidualQA,maximalResidualH,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa]
theorem maximal_residual_count_caps:
   maximalResidualQA.countCap=61761704341773∧
     maximalResidualH.countCap=7016664323606:=by
 norm_num [maximalResidualQA,maximalResidualH,TightParameters.countCap,
   TightParameters.tightNumerator,TightParameters.coreNumerator,
   TightParameters.aggregateCost,TightParameters.agreement,
   TightParameters.implicitYCap,TightParameters.algebraicCap,
   TightParameters.kappa,TightParameters.errors,TightParameters.gap,dot]
theorem maximal_residual_total_below_budget:
   96129765351580058+maximalResidualQA.countCap+
       maximalResidualH.countCap < 100000000000000000:=by
 rw [maximal_residual_count_caps.1,maximal_residual_count_caps.2]
 norm_num
end ProximityPrize.SubmissionLower.RCN318
end PackedLegacy_AK

/-! Packed from ProximityPrize.SubmissionLower.N5. -/
section PackedLegacy_N5
namespace ProximityPrize.SubmissionLower.RCN260
open scoped BigOperators
open RCN318 RCN223 RCN294
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
structure UnequalParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 leftY:ℕ
 leftR:ℕ
 leftZ:ℕ
 rightY:ℕ
 rightR:ℕ
 rightZ:ℕ
 deriving DecidableEq
namespace UnequalParameters
def errors (P:UnequalParameters):ℕ:=P.n-P.a
def gap (P:UnequalParameters):ℕ:=P.a-P.w
def leftAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.leftY,
   P.w*(2*P.leftR-1),
   2*P.w*P.leftZ+1⟩
def rightAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.rightY,
   P.w*(2*P.rightR-1),
   2*P.w*P.rightZ+1⟩
def agreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨max P.leftAgreement.y P.rightAgreement.y,
   max P.leftAgreement.r P.rightAgreement.r,
   max P.leftAgreement.z P.rightAgreement.z⟩
def mixedCost (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨P.leftR*P.rightZ+P.leftZ*P.rightR,
   P.leftY*P.rightZ+P.leftZ*P.rightY,
   P.leftY*P.rightR+P.leftR*P.rightY⟩
def regularNumerator (P:UnequalParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.mixedCost+
   (P.errors+1)*P.gap*P.mixedCost.z
def regularCountCap (P:UnequalParameters):ℕ:=P.regularNumerator/P.gap
theorem regular_count_le (P:UnequalParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.regularNumerator):
   count ≤ P.regularCountCap:=
 (Nat.le_div_iff_mul_le hgap).mpr hcount
end UnequalParameters
theorem complete_stage_count_lt
   (R:UnequalParameters) (S:TightParameters)
   (hgap:0 < R.gap) (hgapEq:S.gap=R.gap)
   {I:Type} [Fintype I]
   (total regular exceptions:ℕ) (count:I → ℕ)
   (cost:I → RCN223.DegreeVector)
   (hcover:total ≤ regular+((∑ i,count i)+exceptions))
   (hregular:regular*R.gap ≤ R.regularNumerator)
   (hy:(∑ i,(cost i).y) ≤ S.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*S.implicitYCap*S.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ S.implicitYCap)
   (hcount:∀ i,count i*S.gap ≤
     (S.n-S.w)*dot S.agreement (cost i)+
       (S.errors+1)*S.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*S.algebraicCap^2):
   total < R.regularCountCap+S.countCap+1:=by
 have hregularCap:regular ≤ R.regularCountCap:=
   R.regular_count_le regular hgap hregular
 have hsingularScaled:=
   S.with_exceptions_bound count cost exceptions hy hr hz hcount hexceptions
 have hsingularGap:0 < S.gap:=by
   rw [hgapEq]
   exact hgap
 have hsingularCap:(∑ i,count i)+exceptions ≤ S.countCap:=by
   exact S.count_le_countCap _ hsingularGap hsingularScaled
 omega
def residualStageOne:UnequalParameters:=
 ⟨262144,131071,182807,34,7,5263,65,14,598⟩
def residualStageTwo:UnequalParameters:=
 ⟨262144,131071,182807,34,7,598,37,6,579299⟩
theorem residual_stage_values:
   residualStageOne.agreement=⟨17039231,3538917,1379653347⟩∧
     residualStageOne.mixedCost=⟨77868,362427,931⟩∧
     residualStageOne.regularCountCap=9865174615710∧
     residualStageTwo.agreement=⟨9699255,1703923,151858598459⟩∧
     residualStageTwo.mixedCost=⟨4058681,19718292,463⟩∧
     residualStageTwo.regularCountCap=362987233541405:=by
 norm_num [residualStageOne,residualStageTwo,UnequalParameters.agreement,
   UnequalParameters.leftAgreement,UnequalParameters.rightAgreement,
   UnequalParameters.mixedCost,UnequalParameters.regularCountCap,
   UnequalParameters.regularNumerator,UnequalParameters.errors,
   UnequalParameters.gap,dot]
theorem residual_stage_ceilings:
   residualStageOne.regularCountCap+maximalResidualQA.countCap+1=
       9865174615710+61761704341774∧
     residualStageTwo.regularCountCap+maximalResidualH.countCap+1=
       362987233541405+7016664323607:=by
 rw [residual_stage_values.2.2.1,residual_stage_values.2.2.2.2.2,
   maximal_residual_count_caps.1,maximal_residual_count_caps.2]
 norm_num
theorem residual_stage_one_count_lt
   {I:Type} [Fintype I]
   (total regular exceptions:ℕ) (count:I → ℕ)
   (cost:I → RCN223.DegreeVector)
   (hcover:total ≤ regular+((∑ i,count i)+exceptions))
   (hregular:regular*residualStageOne.gap ≤ residualStageOne.regularNumerator)
   (hy:(∑ i,(cost i).y) ≤ maximalResidualQA.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤
     2*maximalResidualQA.implicitYCap*maximalResidualQA.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ maximalResidualQA.implicitYCap)
   (hcount:∀ i,count i*maximalResidualQA.gap ≤
     (maximalResidualQA.n-maximalResidualQA.w)*
         dot maximalResidualQA.agreement (cost i)+
       (maximalResidualQA.errors+1)*maximalResidualQA.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*maximalResidualQA.algebraicCap^2):
   total < 9865174615710+61761704341774:=by
 have h:=complete_stage_count_lt residualStageOne maximalResidualQA
   (by norm_num [residualStageOne,UnequalParameters.gap])
   (by norm_num [residualStageOne,maximalResidualQA,UnequalParameters.gap,
     TightParameters.gap]) total regular exceptions count cost hcover hregular
     hy hr hz hcount hexceptions
 rw [residual_stage_ceilings.1] at h
 exact h
theorem residual_stage_two_count_lt
   {I:Type} [Fintype I]
   (total regular exceptions:ℕ) (count:I → ℕ)
   (cost:I → RCN223.DegreeVector)
   (hcover:total ≤ regular+((∑ i,count i)+exceptions))
   (hregular:regular*residualStageTwo.gap ≤ residualStageTwo.regularNumerator)
   (hy:(∑ i,(cost i).y) ≤ maximalResidualH.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤
     2*maximalResidualH.implicitYCap*maximalResidualH.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ maximalResidualH.implicitYCap)
   (hcount:∀ i,count i*maximalResidualH.gap ≤
     (maximalResidualH.n-maximalResidualH.w)*
         dot maximalResidualH.agreement (cost i)+
       (maximalResidualH.errors+1)*maximalResidualH.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*maximalResidualH.algebraicCap^2):
   total < 362987233541405+7016664323607:=by
 have h:=complete_stage_count_lt residualStageTwo maximalResidualH
   (by norm_num [residualStageTwo,UnequalParameters.gap])
   (by norm_num [residualStageTwo,maximalResidualH,UnequalParameters.gap,
     TightParameters.gap]) total regular exceptions count cost hcover hregular
     hy hr hz hcount hexceptions
 rw [residual_stage_ceilings.2] at h
 exact h
end ProximityPrize.SubmissionLower.RCN260
end PackedLegacy_N5

/-! Packed from ProximityPrize.SubmissionLower.C. -/
section PackedLegacy_C
namespace ProximityPrize.SubmissionLower.RCN081
open RCN174
noncomputable section
def weightEmbed (weights:Fin 4 → ℕ):(Fin 4 →₀ ℕ) →+(Fin 5 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+
   Finsupp.single 4 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ) (i:Fin 4):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   weightEmbed weights d (4:Fin 5)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 5 →₀ ℕ => a i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
variable {K:Type*} [Field K]
def weightedLift (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 5) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightedLift K weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem weightedLift_ne_zero (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (hP:P≠0):weightedLift K weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift_injective weights
 simpa only [map_zero] using hzero
theorem coeff_weightedLift_at (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (d:Fin 4 →₀ ℕ):
   MvPolynomial.coeff (weightEmbed weights d) (weightedLift K weights P)=
     MvPolynomial.coeff d P:=by
 change Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)
   (weightEmbed weights d)=(AddMonoidAlgebra.coeff P) d
 exact Finsupp.mapDomain_apply (weightEmbed_injective weights) _ d
theorem support_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).support=P.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).degreeOf (4:Fin 5)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift K weights P).degreeOf (4:Fin 5)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact weightEmbed_last weights d
theorem weightedTotalDegree_mul (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift K weights (P*Q)).degreeOf (4:Fin 5):=
     (degree_weightedLift weights (P*Q)).symm
   _=(weightedLift K weights P*weightedLift K weights Q).degreeOf (4:Fin 5):=by
     rw [map_mul]
   _=(weightedLift K weights P).degreeOf (4:Fin 5)+
       (weightedLift K weights Q).degreeOf (4:Fin 5):=
     MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
     rw [degree_weightedLift,degree_weightedLift]
theorem weightedTotalDegree_le_of_dvd (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_le_iff (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (cap:ℕ):
   MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
     ∀ d∈P.support,Finsupp.weight weights d ≤ cap:=by
 simp only [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
theorem weight_fin4 (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2+d 3*weights 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 calc
   Finsupp.weight weights d=Finsupp.weight weights
       (Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
         Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)):=congrArg _ hd
   _=_:=by simp only [map_add,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id]
def seedWeights:Fin 4 → ℕ:=![0,1,0,1]
def slopeWeights:Fin 4 → ℕ:=![0,0,1,0]
def contactWeights (w:ℕ):Fin 4 → ℕ:=![1,w,w-1,0]
theorem seed_weight (d:Fin 4 →₀ ℕ):Finsupp.weight seedWeights d=d 1+d 3:=by
 rw [weight_fin4]
 simp [seedWeights]
theorem slope_weight (d:Fin 4 →₀ ℕ):Finsupp.weight slopeWeights d=d 2:=by
 rw [weight_fin4]
 simp [slopeWeights]
theorem contact_weight (w:ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight (contactWeights w) d=d 0+w*d 1+(w-1)*d 2:=by
 rw [weight_fin4]
 simp [contactWeights,Nat.mul_comm]
theorem mem_globalCoefficientBox_iff (P:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hD:0 < D):
   P∈globalCoefficientBox K D w L s ↔
     MvPolynomial.weightedTotalDegree seedWeights P ≤ L∧
     MvPolynomial.weightedTotalDegree slopeWeights P ≤ s∧
     MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D-1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff seedWeights P L).mpr
     intro d hd
     rw [seed_weight]
     exact (h hd).1
   · apply (weightedTotalDegree_le_iff slopeWeights P s).mpr
     intro d hd
     rw [slope_weight]
     exact (h hd).2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) P (D-1)).mpr
     intro d hd
     rw [contact_weight]
     have hh:=(h hd).2.2
     omega
 · rintro ⟨hseed,hslope,hcontact⟩ d hd
   have hs:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hseed
   have hr:=(MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hslope
   have hc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hcontact
   rw [seed_weight] at hs
   rw [slope_weight] at hr
   rw [contact_weight] at hc
   exact ⟨hs,hr,by omega⟩
theorem mem_globalCoefficientBox_of_dvd
   (F Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hdiv:F∣Q)
   (hbox:Q∈globalCoefficientBox K D w L s):
   F∈globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_globalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd seedWeights F Q hdiv hQ).trans hcaps.1,
   (weightedTotalDegree_le_of_dvd slopeWeights F Q hdiv hQ).trans hcaps.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hcaps.2.2⟩
theorem degreeOf_le_of_dvd (i:Fin 4) (F Q:MvPolynomial (Fin 4) K)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem sum_degreeOf_le_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q) (i:Fin 4):
   (∑ j∈I,(f j).degreeOf i) ≤ Q.degreeOf i:=by
 classical
 have hprod:(∏ j∈I,f j)≠0:=by
   intro hz
   rcases hdiv with ⟨G,hG⟩
   apply hQ
   rw [hG,hz,zero_mul]
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 calc
   (∑ j∈I,(f j).degreeOf i)=(∏ j∈I,f j).degreeOf i:=
     (MvPolynomial.degreeOf_prod_eq (n:=i) I f hf).symm
   _ ≤ Q.degreeOf i:=degreeOf_le_of_dvd i _ Q hdiv hQ
theorem separated_degree_budgets_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ Q.degreeOf (1:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ Q.degreeOf (2:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ Q.degreeOf (3:Fin 4):=
 ⟨sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 1,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 2,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 3⟩
theorem degreeOf_eq_sum_of_scalar_factorization {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (c:K) (hQ:Q≠0) (hfactor:Q=MvPolynomial.C c*∏ j∈I,f j) (i:Fin 4):
   Q.degreeOf i=∑ j∈I,(f j).degreeOf i:=by
 classical
 have hnonzero:MvPolynomial.C c*(∏ j∈I,f j)≠0:=by
   rw [←hfactor]
   exact hQ
 rcases mul_ne_zero_iff.mp hnonzero with ⟨hc,hprod⟩
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [hfactor,MvPolynomial.degreeOf_mul_eq hc hprod,MvPolynomial.degreeOf_C,
   Nat.zero_add,MvPolynomial.degreeOf_prod_eq I f hf]
theorem degreeOf_Y_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 apply (Nat.le_div_iff_mul_le hw).mpr
 have hc:=(hbox hd).2.2
 have hm:d 1*w=w*d 1:=Nat.mul_comm _ _
 omega
theorem degreeOf_R_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (2:Fin 4) ≤ s:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hbox hd).2.1
theorem degreeOf_Z_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (3:Fin 4) ≤ L:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=(hbox hd).1
 omega
theorem degree_bounds_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w∧
   Q.degreeOf (2:Fin 4) ≤ s∧Q.degreeOf (3:Fin 4) ≤ L:=
 ⟨degreeOf_Y_le_of_mem_box Q D w L s hw hbox,
   degreeOf_R_le_of_mem_box Q D w L s hbox,
   degreeOf_Z_le_of_mem_box Q D w L s hbox⟩
theorem separated_factor_caps_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w L s) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ (D-1)/w∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ s∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ L:=by
 have hsum:=separated_degree_budgets_of_prod_dvd I f Q hQ hdiv
 have hcaps:=degree_bounds_of_mem_box Q D w L s hw hbox
 exact ⟨hsum.1.trans hcaps.1,hsum.2.1.trans hcaps.2.1,hsum.2.2.trans hcaps.2.2⟩
end
end ProximityPrize.SubmissionLower.RCN081
end PackedLegacy_C

/-! Packed from ProximityPrize.SubmissionLower.J1. -/
section PackedLegacy_J1
namespace ProximityPrize.SubmissionLower.RCN082
open UniqueFactorizationMonoid RCN136 RCN174
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def activeFactors (Q:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (normalizedFactors Q).toFinset.filter
   (fun F => 0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
theorem activeFactors_spec (Q F:MvPolynomial (Fin 4) K)
   (hF:F∈activeFactors Q):
   Irreducible F∧F∣Q∧0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 classical
 obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hF
 have hmem:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hm
 exact ⟨irreducible_of_normalized_factor F hmem,
   dvd_of_mem_normalizedFactors hmem,hp⟩
theorem exists_normalized_factor_of_map_zero
   {A:Type*} [CommRing A] [IsDomain A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactors Q,ψ F=0:=by
 have hassoc:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at hassoc
 have hp:ψ (normalizedFactors Q).prod=0:=
   (associated_zero_iff_eq_zero _).mp hassoc
 rw [map_multiset_prod] at hp
 exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
theorem eq_C_of_all_degreeOf_zero (P:MvPolynomial (Fin 3) L)
   (h:∀ i,P.degreeOf i=0):P=MvPolynomial.C (P.coeff 0):=by
 classical
 apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
 apply Nat.eq_zero_of_le_zero
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro d hd
 have hd0:d=0:=by
   ext i
   have hi:=MvPolynomial.monomial_le_degreeOf i hd
   rw [h i] at hi
   exact Nat.eq_zero_of_le_zero hi
 simp [hd0]
theorem pureX_nonvanishing (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (v:Fin 3 → L) (P:Polynomial K)
   (hpure:collectX K F=MvPolynomial.C P):
   MvPolynomial.eval v (surfaceMap φ F)≠0:=by
 have hP:P≠0:=by
   intro h
   apply hF
   apply (collectX K).injective
   simpa only [h,map_zero] using hpure
 have hφP:φ P≠0:=by
   intro h
   apply hP
   apply hφ
   simpa only [map_zero] using h
 change MvPolynomial.eval v (MvPolynomial.map φ (collectX K F))≠0
 rw [hpure,MvPolynomial.map_C,MvPolynomial.eval_C]
 exact hφP
theorem positive_seed_degree_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 by_contra hn
 have hy:F.degreeOf 1 ≤ 0:=by omega
 have hr:F.degreeOf 2 ≤ 0:=by omega
 have hz:F.degreeOf 3 ≤ 0:=by omega
 have hc:=surfaceMap_separated_caps φ F 0 0 0 hy hr hz
 have hconst:surfaceMap φ F=MvPolynomial.C ((surfaceMap φ F).coeff 0):=by
   apply eq_C_of_all_degreeOf_zero
   intro i
   fin_cases i
   · exact Nat.eq_zero_of_le_zero hc.1
   · exact Nat.eq_zero_of_le_zero hc.2.1
   · exact Nat.eq_zero_of_le_zero hc.2.2
 have hvalue:=hzero
 rw [hconst,MvPolynomial.eval_C] at hvalue
 apply surfaceMap_ne_zero φ hφ F hF
 rw [hconst,hvalue,map_zero]
theorem exists_active_factor_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   ∃ F∈activeFactors Q,MvPolynomial.eval v (surfaceMap φ F)=0:=by
 classical
 obtain ⟨F,hmem,hz⟩:=exists_normalized_factor_of_map_zero
   ((MvPolynomial.eval v).comp (surfaceMap φ)) Q hQ hzero
 have hF:=ne_zero_of_mem_normalizedFactors hmem
 have hpos:=positive_seed_degree_of_surface_zero φ hφ F hF v hz
 exact ⟨F,Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem,hpos⟩,hz⟩
theorem activeFactors_product_dvd (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (∏ F∈activeFactors Q,F)∣Q:=by
 classical
 apply (Finset.prod_dvd_prod_of_subset (activeFactors Q)
   (normalizedFactors Q).toFinset id (Finset.filter_subset _ _)).trans
 exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
theorem activeFactors_mem_box (Q F:MvPolynomial (Fin 4) K)
   (D w zcap s:ℕ) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w zcap s) (hF:F∈activeFactors Q):
   F∈globalCoefficientBox K D w zcap s:=
 RCN081.mem_globalCoefficientBox_of_dvd F Q D w zcap s hQ
   (activeFactors_spec Q F hF).2.1 hbox
theorem activeFactors_degree_budgets (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (∑ F∈activeFactors Q,F.degreeOf (1:Fin 4)) ≤ Q.degreeOf 1∧
   (∑ F∈activeFactors Q,F.degreeOf (2:Fin 4)) ≤ Q.degreeOf 2∧
   (∑ F∈activeFactors Q,F.degreeOf (3:Fin 4)) ≤ Q.degreeOf 3:=
 RCN081.separated_degree_budgets_of_prod_dvd (activeFactors Q) id Q hQ
   (activeFactors_product_dvd Q hQ)
theorem activeFactors_input_budgets (Q:MvPolynomial (Fin 4) K)
   (D w zcap s:ℕ) (hw:0 < w) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w zcap s):
   (∑ F∈activeFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
   (∑ F∈activeFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
   (∑ F∈activeFactors Q,F.degreeOf (3:Fin 4)) ≤ zcap:=
 RCN081.separated_factor_caps_of_prod_dvd (activeFactors Q) id Q
   D w zcap s hw hQ hbox (activeFactors_product_dvd Q hQ)
theorem activeFactors_card_le (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (activeFactors Q).card ≤ Q.degreeOf 1+Q.degreeOf 2+Q.degreeOf 3:=by
 classical
 have hsum:(activeFactors Q).card ≤
     ∑ F∈activeFactors Q,(F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):=by
   calc
     (activeFactors Q).card=∑ _F∈activeFactors Q,(1:ℕ):=by simp
     _ ≤ _:=Finset.sum_le_sum fun F hF => (activeFactors_spec Q F hF).2.2
 rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
 have hb:=activeFactors_degree_budgets Q hQ
 omega
theorem exists_active_irreducible_box_factor
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (D w zcap s:ℕ) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w zcap s)
   (v:Fin 3 → L) (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   ∃ F∈activeFactors Q,Irreducible F∧F∣Q∧
     F∈globalCoefficientBox K D w zcap s∧
     MvPolynomial.eval v (surfaceMap φ F)=0:=by
 obtain ⟨F,hF,hz⟩:=exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
 have hs:=activeFactors_spec Q F hF
 exact ⟨F,hF,hs.1,hs.2.1,activeFactors_mem_box Q F D w zcap s hQ hbox hF,hz⟩
end
end ProximityPrize.SubmissionLower.RCN082
end PackedLegacy_J1

/-! Packed from ProximityPrize.SubmissionLower.BH. -/
section PackedLegacy_BH
namespace ProximityPrize.SubmissionLower.RCN132
open RCN136 RCN082
noncomputable section
variable (K:Type*) [Field K]
abbrev Collected:=MvPolynomial (Fin 3) (Polynomial K)
abbrev RationalCoefficients:=FractionRing (Polynomial K)
abbrev RationalPolynomials:=MvPolynomial (Fin 3) (RationalCoefficients K)
attribute [local instance] MvPolynomial.algebraMvPolynomial
def coefficientDenominators:Submonoid (Collected K):=
 (nonZeroDivisors (Polynomial K)).map MvPolynomial.C
local instance:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RationalCoefficients K)
def rationalSurfaceMap:
   MvPolynomial (Fin 4) K →+*RationalPolynomials K:=
 surfaceMap (algebraMap (Polynomial K) (RationalCoefficients K))
theorem rationalSurfaceMap_eq (F:MvPolynomial (Fin 4) K):
   rationalSurfaceMap K F=
     algebraMap (Collected K) (RationalPolynomials K) (collectX K F):=rfl
def xLift (P:Polynomial K):MvPolynomial (Fin 4) K:=
 (collectX K).symm (MvPolynomial.C P)
theorem xLift_add (P Q:Polynomial K):xLift K (P+Q)=xLift K P+xLift K Q:=by
 simp [xLift]
theorem xLift_monomial (n:ℕ) (a:K):
   xLift K (Polynomial.monomial n a)=
     MvPolynomial.C a*MvPolynomial.X (0:Fin 4)^n:=by
 apply (collectX K).injective
 simp [xLift, ←Polynomial.C_mul_X_pow_eq_monomial]
theorem xLift_ne_zero (P:Polynomial K) (hP:P≠0):xLift K P≠0:=by
 intro h
 have hh:=congrArg (collectX K) h
 have hc:(MvPolynomial.C P:Collected K)=0:=by
   simpa only [xLift,AlgEquiv.apply_symm_apply,map_zero] using hh
 apply hP
 apply MvPolynomial.C_injective
 simpa only [map_zero] using hc
theorem xLift_degreeOf_succ (P:Polynomial K) (i:Fin 3):
   (xLift K P).degreeOf i.succ=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>
     rw [xLift_add]
     apply Nat.eq_zero_of_le_zero
     simpa only [hP,hQ,max_self] using
       MvPolynomial.degreeOf_add_le i.succ (xLift K P) (xLift K Q)
 | monomial n a =>
     rw [xLift_monomial]
     have hx:(MvPolynomial.X (0:Fin 4):MvPolynomial (Fin 4) K).degreeOf i.succ=0:=by
       simp [MvPolynomial.degreeOf_X,Fin.succ_ne_zero]
     have hp:=MvPolynomial.degreeOf_pow_le i.succ
       (MvPolynomial.X (0:Fin 4):MvPolynomial (Fin 4) K) n
     rw [hx,Nat.mul_zero] at hp
     have hm:=MvPolynomial.degreeOf_mul_le i.succ
       (MvPolynomial.C a:MvPolynomial (Fin 4) K) (MvPolynomial.X (0:Fin 4)^n)
     rw [MvPolynomial.degreeOf_C,Nat.zero_add] at hm
     exact Nat.eq_zero_of_le_zero (hm.trans hp)
theorem not_dvd_xLift_of_positive_degree
   (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (hP:P≠0)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   ¬ F∣xLift K P:=by
 intro hdiv
 have hi:∃ i:Fin 3,0 < F.degreeOf i.succ:=by
   by_cases hy:0 < F.degreeOf 1
   · exact ⟨0,hy⟩
   by_cases hr:0 < F.degreeOf 2
   · exact ⟨1,hr⟩
   exact ⟨2,by change 0 < F.degreeOf (3:Fin 4);omega⟩
 obtain ⟨i,hi⟩:=hi
 have hb:=RCN081.degreeOf_le_of_dvd i.succ F (xLift K P)
   hdiv (xLift_ne_zero K P hP)
 rw [xLift_degreeOf_succ] at hb
 omega
theorem collected_principal_isPrime (F:MvPolynomial (Fin 4) K) (hF:Irreducible F):
   (Ideal.span ({collectX K F}:Set (Collected K))).IsPrime:=by
 have hi:Irreducible (collectX K F):=(MulEquiv.irreducible_iff (collectX K)).mpr hF
 exact Ideal.isPrime_span_singleton_of_prime hi.prime
theorem coefficientDenominators_disjoint (F:MvPolynomial (Fin 4) K)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collectX K F}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨P,hP,rfl⟩:=Submonoid.mem_map.mp ha
 have hP0:P≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hP
 obtain ⟨G,hG⟩:=Ideal.mem_span_singleton.mp hI
 have hdiv:F∣xLift K P:=by
   refine ⟨(collectX K).symm G,?_⟩
   apply (collectX K).injective
   simpa only [xLift,AlgEquiv.apply_symm_apply,map_mul] using hG
 exact not_dvd_xLift_of_positive_degree K F P hP0 hpos hdiv
theorem localized_principal_isPrime (F:MvPolynomial (Fin 4) K)
   (hF:Irreducible F) (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   (Ideal.span ({rationalSurfaceMap K F}:Set (RationalPolynomials K))).IsPrime:=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collectX K F}:Set (Collected K)))
   (collected_principal_isPrime K F hF) (coefficientDenominators_disjoint K F hpos)
 simpa only [Ideal.map_span,Set.image_singleton, ←rationalSurfaceMap_eq] using hp
theorem rationalSurfaceMap_irreducible (F:MvPolynomial (Fin 4) K)
   (hF:Irreducible F) (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   Irreducible (rationalSurfaceMap K F):=by
 have hne:rationalSurfaceMap K F≠0:=
   surfaceMap_ne_zero (algebraMap (Polynomial K) (RationalCoefficients K))
     (IsFractionRing.injective (Polynomial K) (RationalCoefficients K)) F hF.ne_zero
 exact ((Ideal.span_singleton_prime hne).mp
   (localized_principal_isPrime K F hF hpos)).irreducible
theorem rationalSurfaceMap_dvd_iff
   (F M:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3):
   rationalSurfaceMap K F∣rationalSurfaceMap K M ↔ F∣M:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collectX K M)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collectX K F}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalSurfaceMap_eq] using hdiv
   have hu:collectX K M∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collectX K F}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K F hF)
     (coefficientDenominators_disjoint K F hpos)] at hu
   obtain ⟨G,hG⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collectX K).symm G,?_⟩
   apply (collectX K).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hG
 · intro hdiv
   exact map_dvd (rationalSurfaceMap K) hdiv
theorem activeFactor_rational_irreducible
   (Q F:MvPolynomial (Fin 4) K) (hF:F∈activeFactors Q):
   Irreducible (rationalSurfaceMap K F):=by
 have hs:=activeFactors_spec Q F hF
 exact rationalSurfaceMap_irreducible K F hs.1 hs.2.2
theorem activeFactor_rational_dvd_iff
   (Q F M:MvPolynomial (Fin 4) K) (hF:F∈activeFactors Q):
   rationalSurfaceMap K F∣rationalSurfaceMap K M ↔ F∣M:=by
 have hs:=activeFactors_spec Q F hF
 exact rationalSurfaceMap_dvd_iff K F M hs.1 hs.2.2
end
end ProximityPrize.SubmissionLower.RCN132
end PackedLegacy_BH

/-! Packed from ProximityPrize.SubmissionLower.R6. -/
section PackedLegacy_R6
namespace ProximityPrize.SubmissionLower.RCN350
noncomputable section
section FlatPrincipal
variable {A B:Type*} [CommRing A] [IsDomain A]
 [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B]
 [Module.Flat A B]
theorem prime_eq_span_of_le (g:B) (hg:Prime g)
   (Q:Ideal B) [Q.IsPrime] (hQ:Q≠⊥)
   (hle:Q ≤ Ideal.span {g}):Q=Ideal.span {g}:=by
 let P:Ideal B:=Ideal.span {g}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 have hheight:P.height ≤ 1:=Ideal.height_span_singleton_le_one hg.not_unit
 by_contra hne
 have hlt:Q < P:=lt_of_le_of_ne hle hne
 have hsmall:=(Ideal.height_le_iff (p:=P) (n:=1)).mp hheight Q
   inferInstance hlt
 have hzero:Q.height=0:=Order.lt_one_iff.mp hsmall
 exact hQ (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
theorem under_prime_factor_eq
   (hinjective:Function.Injective (algebraMap A B))
   (F:A) (hF:Prime F) (g:B) (hg:Prime g)
   (hdiv:g∣algebraMap A B F):
   (Ideal.span {g}).under A=Ideal.span {F}:=by
 let P:Ideal B:=Ideal.span {g}
 let p:Ideal A:=Ideal.span {F}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 haveI:p.IsPrime:=(Ideal.span_singleton_prime hF.ne_zero).mpr hF
 have hp:p ≤ P.under A:=by
   apply Ideal.span_le.mpr
   intro x hx
   obtain rfl:=Set.mem_singleton_iff.mp hx
   exact Ideal.mem_span_singleton.mpr hdiv
 obtain ⟨Q,hQP,hQprime,hQover⟩:=
   P.exists_ideal_le_liesOver_of_le (p:=p) (q:=P.under A) hp
 letI:Q.IsPrime:=hQprime
 letI:Q.LiesOver p:=hQover
 have hFQ:algebraMap A B F∈Q:=by
   change F∈Q.under A
   rw [←Q.over_def p]
   exact Ideal.subset_span (Set.mem_singleton F)
 have hQ:Q≠⊥:=by
   intro hbot
   rw [hbot,Ideal.mem_bot] at hFQ
   exact hF.ne_zero (hinjective (by simpa only [map_zero] using hFQ))
 have heq:Q=P:=prime_eq_span_of_le g hg Q hQ hQP
 have hover:Q.under A=p:=(Q.over_def p).symm
 simpa only [heq] using hover
theorem dvd_of_prime_factor_dvd
   (hinjective:Function.Injective (algebraMap A B))
   (F M:A) (hF:Prime F) (g:B) (hg:Prime g)
   (hdivF:g∣algebraMap A B F) (hdivM:g∣algebraMap A B M):
   F∣M:=by
 have hm:M∈(Ideal.span {g}).under A:=
   Ideal.mem_span_singleton.mpr hdivM
 rw [under_prime_factor_eq hinjective F hF g hg hdivF] at hm
 exact Ideal.mem_span_singleton.mp hm
end FlatPrincipal
section CoefficientExtension
variable {K L σ:Type*} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem coefficient_extension_flat:
   Module.Flat (MvPolynomial σ K) (MvPolynomial σ L):=by
 exact Module.Flat.of_linearEquiv
   (Algebra.IsPushout.equiv K (MvPolynomial σ K) L
     (MvPolynomial σ L)).symm.toLinearEquiv
variable [Finite σ]
theorem geometric_factor_contraction
   (F:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdiv:g∣MvPolynomial.map (algebraMap K L) F):
   Ideal.comap (MvPolynomial.map (algebraMap K L)) (Ideal.span {g})=
     Ideal.span {F}:=by
 letI:=coefficient_extension_flat (K:=K) (L:=L) (σ:=σ)
 have hinj:Function.Injective
     (algebraMap (MvPolynomial σ K) (MvPolynomial σ L)):=
   MvPolynomial.map_injective _ (algebraMap K L).injective
 exact under_prime_factor_eq hinj F hF.prime g hg.prime hdiv
theorem original_dvd_of_geometric_factor_dvd
   (F M:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdivF:g∣MvPolynomial.map (algebraMap K L) F)
   (hdivM:g∣MvPolynomial.map (algebraMap K L) M):
   F∣M:=by
 have hm:M∈Ideal.comap (MvPolynomial.map (algebraMap K L))
     (Ideal.span {g}):=Ideal.mem_span_singleton.mpr hdivM
 rw [geometric_factor_contraction F hF g hg hdivF] at hm
 exact Ideal.mem_span_singleton.mp hm
theorem geometric_factor_not_dvd_of_original_not_dvd
   (F M:MvPolynomial σ K) (hF:Irreducible F) (hnot:¬ F∣M)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdivF:g∣MvPolynomial.map (algebraMap K L) F):
   ¬ g∣MvPolynomial.map (algebraMap K L) M:=by
 intro hdivM
 exact hnot (original_dvd_of_geometric_factor_dvd F M hF g hg hdivF hdivM)
end CoefficientExtension
end
end ProximityPrize.SubmissionLower.RCN350
end PackedLegacy_R6

/-! Packed from ProximityPrize.SubmissionLower.CG. -/
section PackedLegacy_CG
namespace ProximityPrize.SubmissionLower.RCN311
open RCN077 RCN313 RCN047 RCN269 RCN233 RCN139 RCN347 RCN174 RCN319
noncomputable section
variable (K:Type*) [CommRing K]
theorem cleared_vector_field_annihilates (F:Poly4 K):
   (polyH K F)^2*MvPolynomial.pderiv (0:Fin 4) F+
     MvPolynomial.X (2:Fin 4)*(polyH K F)^2*
       MvPolynomial.pderiv (1:Fin 4) F+
     polyG K F*polyH K F*MvPolynomial.pderiv (2:Fin 4) F=0:=by
 unfold polyG polyH
 ring
theorem numeratorStep_mul_equation (F A:Poly4 K) (b:ℕ):
   numeratorStep K F b (F*A)=F*numeratorStep K F b A:=by
 unfold numeratorStep clearedStep
 simp only [leibniz_product]
 unfold polyG polyH
 ring
theorem equation_dvd_numeratorStep (F M:Poly4 K) (b:ℕ) (h:F∣M):
   F∣numeratorStep K F b M:=by
 rcases h with ⟨A,rfl⟩
 rw [numeratorStep_mul_equation]
 exact dvd_mul_right F _
theorem equation_dvd_all_later_numerators (F:Poly4 K) (b:ℕ)
   (h:F∣numerator K F b):
   ∀ j,b ≤ j → F∣numerator K F j:=by
 intro j hbj
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hbj
 clear hbj
 induction d with
 | zero => simpa using h
 | succ d ih =>
     simpa only [Nat.add_succ,numerator_succ] using
       equation_dvd_numeratorStep K F (numerator K F (b+d)) (b+d) ih
variable {L:Type*} [CommRing L]
theorem all_later_numerators_vanish (coefficients:K →+*L)
   (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (b:ℕ) (h:F∣numerator K F b):
   ∀ j,b ≤ j →
     MvPolynomial.eval₂Hom coefficients v (numerator K F j)=0:=by
 intro j hbj
 rcases equation_dvd_all_later_numerators K F b h j hbj with ⟨A,hA⟩
 rw [hA,map_mul,hF,zero_mul]
end
section PolynomialFamily
variable {K L:Type*} [Field K] [Field L]
theorem all_tail_jets_zero_of_first_tail_dvd
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hdiv:F∣numerator K F (w+1)):
   ∀ j,w < j →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hreg)
       (contactCoordinate K F (1:Fin 4)) j=0:=by
 intro j hj
 rw [jetCoefficient_eq_evaluated_numerator coefficients F v hF hreg]
 rw [all_later_numerators_vanish K coefficients F v hF (w+1) hdiv j (by omega)]
 simp
theorem exists_global_polynomial_of_first_tail_dvd
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1 ≤ w) (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   ∃ P:Polynomial L,P.natDegree ≤ w∧
     specialization L P (v 3) (MvPolynomial.map coefficients F)=0∧
     P.eval (v 0)=v 1∧P.derivative.eval (v 0)=v 2:=by
 apply exists_global_polynomial_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end PolynomialFamily
end ProximityPrize.SubmissionLower.RCN311
end PackedLegacy_CG

/-! Packed from ProximityPrize.SubmissionLower.EK. -/
section PackedLegacy_EK
namespace ProximityPrize.SubmissionLower.RCN135
open RCN077 RCN269 RCN233 RCN231 RCN229 RCN139 RCN313 RCN319
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable (K:Type*) [Field K]
abbrev RationalBase:=FractionRing (Polynomial K)
abbrev GenericField:=AlgebraicClosure (RationalBase K)
def polynomialEmbedding:Polynomial K →+*GenericField K:=
 (algebraMap (RationalBase K) (GenericField K)).comp
   (algebraMap (Polynomial K) (RationalBase K))
def coefficientEmbedding:K →+*GenericField K:=
 (polynomialEmbedding K).comp Polynomial.C
def initialCoordinate:GenericField K:=polynomialEmbedding K Polynomial.X
theorem polynomialEmbedding_injective:Function.Injective (polynomialEmbedding K):=
 (algebraMap (RationalBase K) (GenericField K)).injective.comp
   (IsFractionRing.injective (Polynomial K) (RationalBase K))
theorem coefficientEmbedding_injective:Function.Injective (coefficientEmbedding K):=
 (coefficientEmbedding K).injective
theorem genericField_isAlgClosed:IsAlgClosed (GenericField K):=by
 infer_instance
theorem genericField_charP (p:ℕ) [CharP K p]:CharP (GenericField K) p:=by
 infer_instance
theorem generic_eval_eq (P:Polynomial K):
   P.eval₂ (coefficientEmbedding K) (initialCoordinate K)=polynomialEmbedding K P:=by
 have hhom:Polynomial.eval₂RingHom (coefficientEmbedding K) (initialCoordinate K)=
     polynomialEmbedding K:=by
   apply Polynomial.ringHom_ext
   · intro a
     simp [coefficientEmbedding,RingHom.comp_apply]
   · simp [initialCoordinate]
 exact DFunLike.congr_fun hhom P
@[simp] theorem polynomialEmbedding_eq_zero_iff (P:Polynomial K):
   polynomialEmbedding K P=0 ↔ P=0:=by
 constructor
 · intro h
   apply polynomialEmbedding_injective K
   simpa only [map_zero] using h
 · rintro rfl
   exact map_zero _
theorem generic_eval_eq_zero_iff (P:Polynomial K):
   P.eval₂ (coefficientEmbedding K) (initialCoordinate K)=0 ↔ P=0:=by
 rw [generic_eval_eq,polynomialEmbedding_eq_zero_iff]
theorem generic_eval_ne_zero (P:Polynomial K) (hP:P≠0):
   P.eval₂ (coefficientEmbedding K) (initialCoordinate K)≠0:=
 (generic_eval_eq_zero_iff K P).not.mpr hP
def initialPoint (P:Polynomial K) (γ:K):Fin 4 → GenericField K:=
 polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)
@[simp] theorem initialPoint_X (P:Polynomial K) (γ:K):
   initialPoint K P γ 0=initialCoordinate K:=rfl
@[simp] theorem initialPoint_Y (P:Polynomial K) (γ:K):
   initialPoint K P γ 1=polynomialEmbedding K P:=by
 exact generic_eval_eq K P
@[simp] theorem initialPoint_R (P:Polynomial K) (γ:K):
   initialPoint K P γ 2=polynomialEmbedding K P.derivative:=by
 exact generic_eval_eq K P.derivative
@[simp] theorem initialPoint_Z (P:Polynomial K) (γ:K):
   initialPoint K P γ 3=coefficientEmbedding K γ:=rfl
theorem evaluation_at_initialPoint (P:Polynomial K) (γ:K) (Q:Poly4 K):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) Q=
     polynomialEmbedding K (specialization K P γ Q):=by
 change MvPolynomial.eval₂Hom (coefficientEmbedding K)
     (polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)) Q=_
 rw [eval_polynomialPoint_eq_specialization,generic_eval_eq]
theorem initialPoint_relation (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) F=0:=by
 rw [evaluation_at_initialPoint,hsolution,map_zero]
theorem initialPoint_regular_iff (F:Poly4 K) (P:Polynomial K) (γ:K):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
       (MvPolynomial.pderiv (2:Fin 4) F)≠0 ↔
     specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
 simp only [evaluation_at_initialPoint,ne_eq,polynomialEmbedding_eq_zero_iff]
def valueSeedProjection (pair:Polynomial K × K):GenericField K × GenericField K:=
 (initialPoint K pair.1 pair.2 1,initialPoint K pair.1 pair.2 3)
theorem valueSeedProjection_injective:Function.Injective (valueSeedProjection K):=by
 intro a b hab
 have hy:=congrArg Prod.fst hab
 have hz:=congrArg Prod.snd hab
 simp only [valueSeedProjection,initialPoint_Y,initialPoint_Z] at hy hz
 exact Prod.ext (polynomialEmbedding_injective K hy) (coefficientEmbedding_injective K hz)
theorem initialPoint_injective:
   Function.Injective (fun pair:Polynomial K × K => initialPoint K pair.1 pair.2):=by
 intro a b hab
 apply valueSeedProjection_injective K
 exact Prod.ext (congrFun hab 1) (congrFun hab 3)
theorem selectedProjection_injective {ι:Type*} (seed:ι → K)
   (hseed:Function.Injective seed) (P:ι → Polynomial K):
   Function.Injective (fun i => valueSeedProjection K (P i,seed i)):=by
 intro a b hab
 have hpair:=valueSeedProjection_injective K hab
 exact hseed (congrArg Prod.snd hpair)
theorem initialPoint_all_tail_numerators_zero
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (w:ℕ) (hdegree:P.natDegree ≤ w):
   ∀ b,w < b →
     MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
       (numerator K F b)=0:=by
 intro b hb
 exact polynomialPoint_numerator_zero (coefficientEmbedding K) F P γ
   (initialCoordinate K) hsolution b (hdegree.trans_lt hb)
theorem global_recovery_at_initialPoint
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0)
   (hregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP K p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   globalPolynomial (coefficientEmbedding K) F (initialPoint K P γ)
     (initialPoint_relation K F P γ hsolution)
     ((initialPoint_regular_iff K F P γ).mpr hregular) w=
     P.map (coefficientEmbedding K):=by
 letI:CharP (GenericField K) p:=genericField_charP K p
 exact globalPolynomial_eq_map_of_solution (coefficientEmbedding K) F P γ
   (initialCoordinate K) hsolution ((initialPoint_regular_iff K F P γ).mpr hregular)
   p w hchar hdegree
end
end ProximityPrize.SubmissionLower.RCN135
end PackedLegacy_EK

/-! Packed from ProximityPrize.SubmissionLower.EM. -/
section PackedLegacy_EM
namespace ProximityPrize.SubmissionLower.RCN138
open RCN136 RCN132 RCN313 RCN311 RCN174 RCN319 RCN135
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
def geometricPolynomialEmbedding:Polynomial K →+*L:=
 (algebraMap (RationalCoefficients K) L).comp
   (algebraMap (Polynomial K) (RationalCoefficients K))
def geometricSurfaceMap:MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map (algebraMap (RationalCoefficients K) L)).comp (rationalSurfaceMap K)
theorem geometricSurfaceMap_eq_surfaceMap:
   geometricSurfaceMap K L=surfaceMap (geometricPolynomialEmbedding K L):=by
 apply RingHom.ext
 intro F
 change MvPolynomial.map (algebraMap (RationalCoefficients K) L)
     (MvPolynomial.map (algebraMap (Polynomial K) (RationalCoefficients K)) (collectX K F))=
   MvPolynomial.map ((algebraMap (RationalCoefficients K) L).comp
     (algebraMap (Polynomial K) (RationalCoefficients K))) (collectX K F)
 exact MvPolynomial.map_map _ _ _
theorem geometricSurfaceMap_separated_caps
   (F:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
   (hy:F.degreeOf 1 ≤ ell) (hr:F.degreeOf 2 ≤ s) (hz:F.degreeOf 3 ≤ zcap):
   (geometricSurfaceMap K L F).degreeOf 0 ≤ ell∧
     (geometricSurfaceMap K L F).degreeOf 1 ≤ s∧
     (geometricSurfaceMap K L F).degreeOf 2 ≤ zcap:=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_separated_caps _ F ell s zcap hy hr hz
theorem geometricSurfaceMap_joint_seed_cap
   (F:MvPolynomial (Fin 4) K) (cap:ℕ)
   (hcap:∀ d∈F.support,d 1+d 3 ≤ cap):
   ∀ e∈(geometricSurfaceMap K L F).support,e 0+e 2 ≤ cap:=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_joint_seed_cap _ F cap hcap
theorem geometric_factor_dvd_iff
   (F M:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   g∣geometricSurfaceMap K L M ↔ F∣M:=by
 constructor
 · intro hdivM
   have hfrac:rationalSurfaceMap K F∣rationalSurfaceMap K M:=
     RCN350.original_dvd_of_geometric_factor_dvd
       (rationalSurfaceMap K F) (rationalSurfaceMap K M)
       (rationalSurfaceMap_irreducible K F hF hpos) g hg hdivF hdivM
   exact (rationalSurfaceMap_dvd_iff K F M hF hpos).mp hfrac
 · intro hdiv
   exact hdivF.trans (map_dvd (geometricSurfaceMap K L) hdiv)
theorem all_later_tails_of_geometric_first_tail
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F) (w:ℕ)
   (hfirst:g∣geometricSurfaceMap K L (numerator K F (w+1))):
   ∀ j,w < j → F∣numerator K F j:=by
 have hbase:=(geometric_factor_dvd_iff K L F (numerator K F (w+1))
   hF hpos g hg hdivF).mp hfirst
 intro j hj
 exact equation_dvd_all_later_numerators K F (w+1) hbase j (by omega)
theorem first_tail_dichotomy
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3) (w:ℕ):
   (F∣numerator K F (w+1)∧∀ j,w < j → F∣numerator K F j)∨
     (∀ g:MvPolynomial (Fin 3) L,Irreducible g →
       g∣geometricSurfaceMap K L F →
       ¬ g∣geometricSurfaceMap K L (numerator K F (w+1))):=by
 by_cases h:F∣numerator K F (w+1)
 · left
   refine ⟨h,?_⟩
   intro j hj
   exact equation_dvd_all_later_numerators K F (w+1) h j (by omega)
 · right
   intro g hg hdivF hdivM
   exact h ((geometric_factor_dvd_iff K L F (numerator K F (w+1))
     hF hpos g hg hdivF).mp hdivM)
theorem polynomiality_of_geometric_first_tail
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F)
   (v:Fin 4 → L)
   (hv:MvPolynomial.eval₂Hom
     ((geometricPolynomialEmbedding K L).comp Polynomial.C) v F=0)
   (hreg:MvPolynomial.eval₂Hom
     ((geometricPolynomialEmbedding K L).comp Polynomial.C) v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1 ≤ w) (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hfirst:g∣geometricSurfaceMap K L (numerator K F (w+1))):
   ∃ P:Polynomial L,P.natDegree ≤ w∧
     specialization L P (v 3)
       (MvPolynomial.map ((geometricPolynomialEmbedding K L).comp Polynomial.C) F)=0∧
     P.eval (v 0)=v 1∧P.derivative.eval (v 0)=v 2:=by
 apply exists_global_polynomial_of_first_tail_dvd
   ((geometricPolynomialEmbedding K L).comp Polynomial.C) F v hv hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 exact (geometric_factor_dvd_iff K L F (numerator K F (w+1))
   hF hpos g hg hdivF).mp hfirst
section CanonicalGenericField
theorem canonical_geometricPolynomialEmbedding:
   geometricPolynomialEmbedding K (GenericField K)=polynomialEmbedding K:=rfl
theorem canonical_geometricSurfaceMap:
   geometricSurfaceMap K (GenericField K)=surfaceMap (polynomialEmbedding K):=by
 rw [geometricSurfaceMap_eq_surfaceMap,canonical_geometricPolynomialEmbedding]
theorem eval_at_actual_generic_initial_point
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=
     polynomialEmbedding K (specialization K P γ F):=by
 rw [canonical_geometricSurfaceMap,eval_surfaceMap]
 change MvPolynomial.eval₂Hom (coefficientEmbedding K)
     (Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)) F=_
 have hv:Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)=
     initialPoint K P γ:=by
   funext i
   refine Fin.cases ?_ (fun j => ?_) i <;> rfl
 rw [hv]
 exact evaluation_at_initialPoint K P γ F
theorem actual_generic_initial_zero_iff
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=0 ↔ specialization K P γ F=0:=by
 rw [eval_at_actual_generic_initial_point,polynomialEmbedding_eq_zero_iff]
theorem canonical_first_tail_dichotomy
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3) (w:ℕ):
   (F∣numerator K F (w+1)∧∀ j,w < j → F∣numerator K F j)∨
     (∀ g:MvPolynomial (Fin 3) (GenericField K),Irreducible g →
       g∣surfaceMap (polynomialEmbedding K) F →
       ¬ g∣surfaceMap (polynomialEmbedding K) (numerator K F (w+1))):=by
 simpa only [canonical_geometricSurfaceMap] using
   first_tail_dichotomy K (GenericField K) F hF hpos w
end CanonicalGenericField
end
end ProximityPrize.SubmissionLower.RCN138
end PackedLegacy_EM

/-! Packed from ProximityPrize.SubmissionLower.EL. -/
section PackedLegacy_EL
namespace ProximityPrize.SubmissionLower.RCN137
open UniqueFactorizationMonoid RCN136 RCN082 RCN135 RCN138 RCN174 RCN319
noncomputable section
section ArbitraryVariables
variable {σ A:Type*} [Field A]
local instance:StrongNormalizationMonoid (MvPolynomial σ A):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def normalizedFactorSet (Q:MvPolynomial σ A):Finset (MvPolynomial σ A):=by
 classical
 exact (normalizedFactors Q).toFinset
theorem normalizedFactorSet_spec (Q F:MvPolynomial σ A)
   (hF:F∈normalizedFactorSet Q):Irreducible F∧F∣Q:=by
 classical
 have hm:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hF
 exact ⟨irreducible_of_normalized_factor F hm,dvd_of_mem_normalizedFactors hm⟩
theorem normalizedFactorSet_product_dvd (Q:MvPolynomial σ A) (hQ:Q≠0):
   (∏ F∈normalizedFactorSet Q,F)∣Q:=by
 classical
 exact (normalizedFactors Q).toFinset_prod_dvd_prod.trans (prod_normalizedFactors hQ).dvd
theorem coordinate_degree_le_of_dvd (i:σ) (F Q:MvPolynomial σ A)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem sum_coordinate_degrees_le_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial σ A) (Q:MvPolynomial σ A)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q) (i:σ):
   (∑ j∈I,(f j).degreeOf i) ≤ Q.degreeOf i:=by
 classical
 have hprod:(∏ j∈I,f j)≠0:=by
   intro hz
   rcases hdiv with ⟨G,hG⟩
   apply hQ
   rw [hG,hz,zero_mul]
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 calc
   (∑ j∈I,(f j).degreeOf i)=(∏ j∈I,f j).degreeOf i:=
     (MvPolynomial.degreeOf_prod_eq (n:=i) I f hf).symm
   _ ≤ Q.degreeOf i:=coordinate_degree_le_of_dvd i _ Q hdiv hQ
theorem normalizedFactorSet_degree_budget
   (Q:MvPolynomial σ A) (hQ:Q≠0) (i:σ):
   (∑ F∈normalizedFactorSet Q,F.degreeOf i) ≤ Q.degreeOf i:=
 sum_coordinate_degrees_le_of_prod_dvd (normalizedFactorSet Q) id Q hQ
   (normalizedFactorSet_product_dvd Q hQ) i
theorem exists_normalizedFactorSet_zero
   {B:Type*} [CommRing B] [IsDomain B]
   (ψ:MvPolynomial σ A →+*B) (Q:MvPolynomial σ A)
   (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactorSet Q,ψ F=0:=by
 classical
 have ha:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at ha
 have hp:ψ (normalizedFactors Q).prod=0:=(associated_zero_iff_eq_zero _).mp ha
 rw [map_multiset_prod] at hp
 obtain ⟨F,hm,hz⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
 exact ⟨F,Multiset.mem_toFinset.mpr hm,hz⟩
end ArbitraryVariables
section SurfaceFamilies
variable {K L:Type*} [Field K] [Field L]
def surfaceFactors (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   Finset (MvPolynomial (Fin 3) L):=normalizedFactorSet (surfaceMap φ F)
theorem surfaceFactors_spec (φ:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K) (g:MvPolynomial (Fin 3) L)
   (hg:g∈surfaceFactors φ F):Irreducible g∧g∣surfaceMap φ F:=
 normalizedFactorSet_spec (surfaceMap φ F) g hg
theorem exists_surfaceFactor_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   ∃ g∈surfaceFactors φ F,MvPolynomial.eval v g=0:=
 exists_normalizedFactorSet_zero (MvPolynomial.eval v) (surfaceMap φ F)
   (surfaceMap_ne_zero φ hφ F hF) hzero
theorem surfaceFactors_degree_budget
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g∈surfaceFactors φ F,g.degreeOf i) ≤ F.degreeOf i.succ:=
 (normalizedFactorSet_degree_budget (surfaceMap φ F)
   (surfaceMap_ne_zero φ hφ F hF) i).trans (surfaceMap_degreeOf_le φ F i)
theorem exists_geometric_component_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   ∃ F∈activeFactors Q,∃ g∈surfaceFactors φ F,
     Irreducible F∧Irreducible g∧F∣Q∧g∣surfaceMap φ F∧
     MvPolynomial.eval v g=0:=by
 obtain ⟨F,hF,hzF⟩:=exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
 have hsF:=activeFactors_spec Q F hF
 obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero φ hφ F hsF.1.ne_zero v hzF
 have hsg:=surfaceFactors_spec φ F g hg
 exact ⟨F,hF,g,hg,hsF.1,hsg.1,hsF.2.1,hsg.2,hzg⟩
theorem surfaceFactor_family_degree_budget
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (i:Fin 3):
   (∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf i) ≤
     Q.degreeOf i.succ:=by
 classical
 calc
   (∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf i) ≤
       ∑ F∈activeFactors Q,F.degreeOf i.succ:=by
     apply Finset.sum_le_sum
     intro F hF
     exact surfaceFactors_degree_budget φ hφ F (activeFactors_spec Q F hF).1.ne_zero i
   _ ≤ Q.degreeOf i.succ:=
     sum_coordinate_degrees_le_of_prod_dvd (activeFactors Q) id Q hQ
       (activeFactors_product_dvd Q hQ) i.succ
theorem surfaceFactor_family_input_budgets
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (D w zcap s:ℕ) (hw:0 < w) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w zcap s):
   (∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (0:Fin 3)) ≤ (D-1)/w∧
   (∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (1:Fin 3)) ≤ s∧
   (∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (2:Fin 3)) ≤ zcap:=by
 have hc:=RCN081.degree_bounds_of_mem_box Q D w zcap s hw hbox
 exact ⟨(surfaceFactor_family_degree_budget φ hφ Q hQ 0).trans hc.1,
   (surfaceFactor_family_degree_budget φ hφ Q hQ 1).trans hc.2.1,
   (surfaceFactor_family_degree_budget φ hφ Q hQ 2).trans hc.2.2⟩
theorem irreducible_positive_surface_degree
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g):
   0 < g.degreeOf 0+g.degreeOf 1+g.degreeOf 2:=by
 by_contra h
 have heq:g=MvPolynomial.C (g.coeff 0):=by
   apply eq_C_of_all_degreeOf_zero
   intro i
   fin_cases i
   · change g.degreeOf (0:Fin 3)=0
     omega
   · change g.degreeOf (1:Fin 3)=0
     omega
   · change g.degreeOf (2:Fin 3)=0
     omega
 have hc:g.coeff 0≠0:=by
   intro hzero
   apply hg.ne_zero
   rw [heq,hzero,map_zero]
 apply hg.not_isUnit
 rw [heq]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem surfaceFactor_card_le_degree_sum
   (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   (surfaceFactors φ F).card ≤
     ∑ g∈surfaceFactors φ F,(g.degreeOf 0+g.degreeOf 1+g.degreeOf 2):=by
 classical
 calc
   (surfaceFactors φ F).card=∑ _g∈surfaceFactors φ F,(1:ℕ):=by simp
   _ ≤ _:=Finset.sum_le_sum fun g hg =>
     irreducible_positive_surface_degree g (surfaceFactors_spec φ F g hg).1
theorem surfaceFactor_family_card_budget
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):
   (∑ F∈activeFactors Q,(surfaceFactors φ F).card) ≤
     Q.degreeOf 1+Q.degreeOf 2+Q.degreeOf 3:=by
 classical
 have hcount:=Finset.sum_le_sum
   (s:=activeFactors Q) (fun F _ => surfaceFactor_card_le_degree_sum φ F)
 simp only [Finset.sum_add_distrib] at hcount
 have h0:(∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (0:Fin 3)) ≤
     Q.degreeOf (1:Fin 4):=surfaceFactor_family_degree_budget φ hφ Q hQ 0
 have h1:(∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (1:Fin 3)) ≤
     Q.degreeOf (2:Fin 4):=surfaceFactor_family_degree_budget φ hφ Q hQ 1
 have h2:(∑ F∈activeFactors Q,∑ g∈surfaceFactors φ F,g.degreeOf (2:Fin 3)) ≤
     Q.degreeOf (3:Fin 4):=surfaceFactor_family_degree_budget φ hφ Q hQ 2
 omega
end SurfaceFamilies
section CanonicalPoints
variable (K:Type*) [Field K]
theorem exists_component_at_actual_initial_point
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ Q=0):
   ∃ F∈activeFactors Q,∃ g∈surfaceFactors (polynomialEmbedding K) F,
     Irreducible F∧Irreducible g∧F∣Q∧
     g∣surfaceMap (polynomialEmbedding K) F∧
     MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ) g=0:=by
 have hz:=(actual_generic_initial_zero_iff K P γ Q).mpr hsolution
 rw [canonical_geometricSurfaceMap] at hz
 exact exists_geometric_component_of_surface_zero
   (polynomialEmbedding K) (polynomialEmbedding_injective K) Q hQ
   (fun i:Fin 3 => initialPoint K P γ i.succ) hz
end CanonicalPoints
end
end ProximityPrize.SubmissionLower.RCN137
end PackedLegacy_EL

/-! Packed from ProximityPrize.SubmissionLower.AD. -/
section PackedLegacy_AD
namespace ProximityPrize.SubmissionLower.RCN267
open RCN136 RCN313 RCN138 RCN132 RCN137
noncomputable section
section PartialDerivatives
variable {σ K:Type*} [Field K]
theorem pderiv_zero_of_degree_zero (i:σ) (F:MvPolynomial σ K)
   (hdegree:F.degreeOf i=0):MvPolynomial.pderiv i F=0:=by
 apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
 intro hmem
 exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hmem) hdegree
theorem pderiv_zero_iff_degree_zero_below_char
   (i:σ) (F:MvPolynomial σ K) (p:ℕ) [CharP K p]
   (hdegree:F.degreeOf i < p):
   MvPolynomial.pderiv i F=0 ↔ F.degreeOf i=0:=by
 classical
 constructor
 · intro hzero
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   by_contra hn
   have hpos:0 < d i:=by omega
   have hsmall:d i < p:=(MvPolynomial.monomial_le_degreeOf i hd).trans_lt hdegree
   let e:σ →₀ ℕ:=d-Finsupp.single i 1
   have he:e+Finsupp.single i 1=d:=
     Finsupp.sub_add_single_one_cancel (by omega:d i≠0)
   have hnat:e i+1=d i:=by
     have hh:=congrArg (fun f:σ →₀ ℕ => f i) he
     simpa only [Finsupp.add_apply,Finsupp.single_eq_same] using hh
   have hcast:(d i:K)≠0:=
     (CharP.cast_eq_zero_iff K p (d i)).not.mpr (Nat.not_dvd_of_pos_of_lt hpos hsmall)
   have hcoef:(e i:K)+1≠0:=by
     simpa only [←hnat,Nat.cast_add,Nat.cast_one] using hcast
   have hz:MvPolynomial.coeff e (MvPolynomial.pderiv i F)=0:=by
     rw [hzero,MvPolynomial.coeff_zero]
   rw [MvPolynomial.coeff_pderiv,he] at hz
   exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcoef hz
 · exact pderiv_zero_of_degree_zero i F
end PartialDerivatives
section SurfaceCommutation
variable {K L:Type*} [Field K] [Field L]
theorem surfaceMap_pderiv_X (φ:Polynomial K →+*L) (i:Fin 4) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ (MvPolynomial.X i))=
     surfaceMap φ (MvPolynomial.pderiv j.succ (MvPolynomial.X i)):=by
 classical
 refine Fin.cases ?_ (fun k => ?_) i
 · simp [MvPolynomial.pderiv_X,Pi.single_apply,Fin.succ_ne_zero]
 · by_cases h:k=j
   · subst k
     simp
   · simp [MvPolynomial.pderiv_X,Pi.single_apply,h,Fin.succ_inj,apply_ite]
theorem surfaceMap_pderiv (φ:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K) (j:Fin 3):
   MvPolynomial.pderiv j (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv j.succ F):=by
 classical
 induction F using MvPolynomial.induction_on with
 | C a => simp [MvPolynomial.pderiv_C]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     simp only [map_mul,map_add,MvPolynomial.pderiv_mul,hP,surfaceMap_pderiv_X]
theorem surfaceMap_pderiv_R (φ:Polynomial K →+*L) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (surfaceMap φ F)=
     surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F):=
 surfaceMap_pderiv φ F 1
end SurfaceCommutation
section BaseRegularity
variable {K:Type*} [Field K]
theorem R_derivative_nonzero (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   MvPolynomial.pderiv (2:Fin 4) F≠0:=by
 intro hzero
 have hd:=(pderiv_zero_iff_degree_zero_below_char (2:Fin 4) F p hsmall).mp hzero
 omega
theorem R_derivative_degree_lt (F:MvPolynomial (Fin 4) K) (hpos:0 < F.degreeOf 2):
   (MvPolynomial.pderiv (2:Fin 4) F).degreeOf 2 < F.degreeOf 2:=by
 have hb:=pderiv_same_degree_bound (2:Fin 4) F (F.degreeOf 2) le_rfl
 omega
theorem equation_not_dvd_R_derivative
   (F:MvPolynomial (Fin 4) K) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p):
   ¬ F∣MvPolynomial.pderiv (2:Fin 4) F:=by
 intro hdiv
 have hle:=RCN081.degreeOf_le_of_dvd (2:Fin 4) F _ hdiv
   (R_derivative_nonzero F p hpos hsmall)
 have hlt:=R_derivative_degree_lt F hpos
 omega
end BaseRegularity
section GeometricRegularity
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
theorem geometricSurfaceMap_pderiv_R (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F)=
     geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_pderiv_R _ F
theorem H_proper_on_every_geometric_factor
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 intro hdivH
 apply equation_not_dvd_R_derivative F p hpos hsmall
 exact (geometric_factor_dvd_iff K L F (MvPolynomial.pderiv (2:Fin 4) F)
   hF (by omega) g hg hdivF).mp hdivH
theorem geometric_factor_R_derivative_nonzero
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   MvPolynomial.pderiv (1:Fin 3) g≠0:=by
 intro hgzero
 have hdivH:g∣MvPolynomial.pderiv (1:Fin 3) (geometricSurfaceMap K L F):=by
   obtain ⟨G,hG⟩:=hdivF
   refine ⟨MvPolynomial.pderiv (1:Fin 3) G,?_⟩
   rw [hG,MvPolynomial.pderiv_mul,hgzero,zero_mul,zero_add]
 rw [geometricSurfaceMap_pderiv_R] at hdivH
 exact H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF hdivH
theorem geometric_factor_R_degree_positive
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3):=by
 apply Nat.pos_of_ne_zero
 intro hzero
 exact geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF
   (pderiv_zero_of_degree_zero (1:Fin 3) g hzero)
theorem geometric_factor_R_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (g:MvPolynomial (Fin 3) L) (hdivF:g∣geometricSurfaceMap K L F):
   g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
 have hφ:Function.Injective (geometricPolynomialEmbedding K L):=
   (algebraMap (RationalCoefficients K) L).injective.comp
     (IsFractionRing.injective (Polynomial K) (RationalCoefficients K))
 have hne:geometricSurfaceMap K L F≠0:=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_ne_zero _ hφ F hF
 have hc:(geometricSurfaceMap K L F).degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4):=by
   rw [geometricSurfaceMap_eq_surfaceMap]
   exact surfaceMap_degreeOf_le _ F 1
 exact (coordinate_degree_le_of_dvd (1:Fin 3) g _ hdivF hne).trans hc
theorem geometric_factor_regular_gate
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hpos:0 < F.degreeOf 2) (hsmall:F.degreeOf 2 < p)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   0 < g.degreeOf (1:Fin 3)∧g.degreeOf (1:Fin 3) ≤ F.degreeOf (2:Fin 4)∧
     g.degreeOf (1:Fin 3) < p∧MvPolynomial.pderiv (1:Fin 3) g≠0∧
     ¬ g∣geometricSurfaceMap K L (MvPolynomial.pderiv (2:Fin 4) F):=by
 have hle:=geometric_factor_R_degree_le K L F hF.ne_zero g hdivF
 exact ⟨geometric_factor_R_degree_positive K L F hF p hpos hsmall g hg hdivF,
   hle,hle.trans_lt hsmall,
   geometric_factor_R_derivative_nonzero K L F hF p hpos hsmall g hg hdivF,
   H_proper_on_every_geometric_factor K L F hF p hpos hsmall g hg hdivF⟩
end GeometricRegularity
end
end ProximityPrize.SubmissionLower.RCN267
end PackedLegacy_AD

/-! Packed from ProximityPrize.SubmissionLower.P5. -/
section PackedLegacy_P5
namespace ProximityPrize.SubmissionLower.RCN290
open RCN082 RCN136 RCN267
noncomputable section
section GenericResultant
variable {A:Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]
theorem primitive_irreducible_dvd_of_resultant_zero
   (P Q:Polynomial A) (hprimitive:P.IsPrimitive) (hP:Irreducible P)
   (hzero:Polynomial.resultant P Q P.natDegree Q.natDegree=0):P∣Q:=by
 classical
 let T:=FractionRing A
 let f:A →+*T:=algebraMap A T
 have hf:Function.Injective f:=IsFractionRing.injective A T
 have hPd:(P.map f).natDegree=P.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf P
 have hQd:(Q.map f).natDegree=Q.natDegree:=
   Polynomial.natDegree_map_eq_of_injective hf Q
 have hfixed:Polynomial.resultant (P.map f) (Q.map f)
     P.natDegree Q.natDegree=0:=by
   rw [Polynomial.resultant_map_map,hzero,map_zero]
 have hres:Polynomial.resultant (P.map f) (Q.map f)=0:=by
   simpa only [hPd,hQd] using hfixed
 have hnot:¬ IsCoprime (P.map f) (Q.map f):=
   (Polynomial.resultant_eq_zero_iff.mp hres).2
 have hi:Irreducible (P.map f):=
   hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hP
 exact hprimitive.dvd_of_fraction_map_dvd_fraction_map
   ((Irreducible.dvd_iff_not_isCoprime hi).mpr hnot)
theorem irreducible_resultant_nonzero
   (P Q:Polynomial A) (hP:Irreducible P) (hpos:0 < P.natDegree)
   (hproper:¬ P∣Q):
   Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=by
 intro hz
 exact hproper (primitive_irreducible_dvd_of_resultant_zero P Q
   (hP.isPrimitive (Nat.ne_of_gt hpos)) hP hz)
end GenericResultant
section Construction
variable {K:Type*} [Field K]
abbrev RemainingCoordinates:={i:Fin 4//i≠2}
abbrev CoefficientRing (K:Type*) [Field K]:=
 MvPolynomial RemainingCoordinates K
def collectR (K:Type*) [Field K]:
   MvPolynomial (Fin 4) K ≃ₐ[K] Polynomial (CoefficientRing K):=
 (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe (2:Fin 4)).symm).trans
   (MvPolynomial.optionEquivLeft K RemainingCoordinates)
theorem collectR_natDegree (F:MvPolynomial (Fin 4) K):
   (collectR K F).natDegree=F.degreeOf 2:=by
 exact (MvPolynomial.degreeOf_eq_natDegree (2:Fin 4) F).symm
def eliminateR (F G:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 (collectR K).symm (Polynomial.C
   (Polynomial.resultant (collectR K F) (collectR K G)))
theorem eliminateR_R_degree (F G:MvPolynomial (Fin 4) K):
   (eliminateR F G).degreeOf 2=0:=by
 rw [←collectR_natDegree,eliminateR,AlgEquiv.apply_symm_apply,
   Polynomial.natDegree_C]
theorem eliminateR_nonzero
   (F G:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 2) (hproper:¬ F∣G):eliminateR F G≠0:=by
 have hi:Irreducible (collectR K F):=(MulEquiv.irreducible_iff (collectR K)).mpr hF
 have hdegree:0 < (collectR K F).natDegree:=by
   rw [collectR_natDegree]
   exact hpos
 have hnot:¬ collectR K F∣collectR K G:=by
   intro hd
   apply hproper
   obtain ⟨T,hT⟩:=hd
   refine ⟨(collectR K).symm T,?_⟩
   apply (collectR K).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hT
 have hres:=irreducible_resultant_nonzero (collectR K F) (collectR K G)
   hi hdegree hnot
 intro hz
 have hh:=congrArg (collectR K) hz
 have hc:Polynomial.C (Polynomial.resultant (collectR K F) (collectR K G))=0:=by
   simpa only [eliminateR,AlgEquiv.apply_symm_apply,map_zero] using hh
 exact hres (Polynomial.C_eq_zero.mp hc)
theorem eliminateR_bezout (F G:MvPolynomial (Fin 4) K)
   (hpos:0 < F.degreeOf 2):
   ∃ A B:MvPolynomial (Fin 4) K,F*A+G*B=eliminateR F G:=by
 obtain ⟨A,B,_,_,hab⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
   (collectR K F) (collectR K G) le_rfl le_rfl
     (Or.inl (by rw [collectR_natDegree];omega))
 refine ⟨(collectR K).symm A,(collectR K).symm B,?_⟩
 apply (collectR K).injective
 simpa only [map_add,map_mul,AlgEquiv.apply_symm_apply,eliminateR] using hab
theorem eliminateR_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (F G:MvPolynomial (Fin 4) K) (hpos:0 < F.degreeOf 2)
   (hF:ψ F=0) (hG:ψ G=0):ψ (eliminateR F G)=0:=by
 obtain ⟨U,V,huv⟩:=eliminateR_bezout F G hpos
 rw [←huv,map_add,map_mul,map_mul,hF,hG,zero_mul,zero_mul,zero_add]
def singularContribution (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 if F.degreeOf 2=0 then F else eliminateR F (MvPolynomial.pderiv (2:Fin 4) F)
def singularAuxiliary (Q:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 ∏ F∈activeFactors Q,singularContribution F
theorem singularContribution_nonzero
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (p:ℕ) [CharP K p]
   (hsmall:F.degreeOf 2 < p):singularContribution F≠0:=by
 unfold singularContribution
 split_ifs with h
 · exact hF.ne_zero
 · have hp:0 < F.degreeOf 2:=Nat.pos_of_ne_zero h
   exact eliminateR_nonzero F _ hF hp (equation_not_dvd_R_derivative F p hp hsmall)
theorem singularContribution_R_degree (F:MvPolynomial (Fin 4) K):
   (singularContribution F).degreeOf 2=0:=by
 unfold singularContribution
 split_ifs with h
 · exact h
 · exact eliminateR_R_degree F _
theorem singularAuxiliary_nonzero
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (p:ℕ) [CharP K p]
   (hsmall:Q.degreeOf 2 < p):singularAuxiliary Q≠0:=by
 classical
 apply Finset.prod_ne_zero_iff.mpr
 intro F hF
 have hs:=activeFactors_spec Q F hF
 apply singularContribution_nonzero F hs.1 p
 exact (RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q hs.2.1 hQ).trans_lt hsmall
theorem singularAuxiliary_R_degree
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (p:ℕ) [CharP K p]
   (hsmall:Q.degreeOf 2 < p):(singularAuxiliary Q).degreeOf 2=0:=by
 classical
 have hne:∀ F∈activeFactors Q,singularContribution F≠0:=by
   intro F hF
   have hs:=activeFactors_spec Q F hF
   exact singularContribution_nonzero F hs.1 p
     ((RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q hs.2.1 hQ).trans_lt hsmall)
 change (∏ F∈activeFactors Q,singularContribution F).degreeOf 2=0
 rw [MvPolynomial.degreeOf_prod_eq (n:=(2:Fin 4)) _ _ hne]
 simp only [singularContribution_R_degree,Finset.sum_const_zero]
theorem singularContribution_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A) (F:MvPolynomial (Fin 4) K)
   (hF:ψ F=0) (hsingular:F.degreeOf 2=0∨ψ (MvPolynomial.pderiv 2 F)=0):
   ψ (singularContribution F)=0:=by
 unfold singularContribution
 split_ifs with h
 · exact hF
 · exact eliminateR_map_zero ψ F _ (Nat.pos_of_ne_zero h) hF
     (hsingular.resolve_left h)
theorem singularAuxiliary_map_zero {A:Type*} [CommRing A]
   (ψ:MvPolynomial (Fin 4) K →+*A) (Q F:MvPolynomial (Fin 4) K)
   (hmem:F∈activeFactors Q) (hF:ψ F=0)
   (hsingular:F.degreeOf 2=0∨ψ (MvPolynomial.pderiv 2 F)=0):
   ψ (singularAuxiliary Q)=0:=by
 classical
 change ψ (∏ G∈activeFactors Q,singularContribution G)=0
 rw [map_prod]
 apply Finset.prod_eq_zero hmem
 exact singularContribution_map_zero ψ F hF hsingular
end Construction
section ActualCoverage
variable {K L:Type*} [Field K] [Field L]
theorem surface_zero_singular_or_regular
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (v:Fin 3 → L) (hzero:MvPolynomial.eval v (surfaceMap φ Q)=0):
   MvPolynomial.eval v (surfaceMap φ (singularAuxiliary Q))=0∨
     ∃ F∈activeFactors Q,Irreducible F∧0 < F.degreeOf 2∧
       MvPolynomial.eval v (surfaceMap φ F)=0∧
       MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F))≠0:=by
 classical
 obtain ⟨F,hF,hz⟩:=exists_active_factor_of_surface_zero φ hφ Q hQ v hzero
 by_cases hr:F.degreeOf 2=0
 · exact Or.inl (singularAuxiliary_map_zero
     ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inl hr))
 · rcases eq_or_ne (MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv 2 F))) 0 with hh | hh
   · exact Or.inl (singularAuxiliary_map_zero
       ((MvPolynomial.eval v).comp (surfaceMap φ)) Q F hF hz (Or.inr hh))
   · exact Or.inr ⟨F,hF,(activeFactors_spec Q F hF).1,Nat.pos_of_ne_zero hr,hz,hh⟩
end ActualCoverage
end
end ProximityPrize.SubmissionLower.RCN290
end PackedLegacy_P5

/-! Packed from ProximityPrize.SubmissionLower.CA. -/
section PackedLegacy_CA
namespace ProximityPrize.SubmissionLower.RCN293
open RCN290 RCN081 RCN082
noncomputable section
variable {K:Type*} [Field K]
def embedCoefficients (K:Type*) [Field K]:
   CoefficientRing K →+*MvPolynomial (Fin 4) K:=
 (collectR K).symm.toRingHom.comp Polynomial.C
theorem collectR_X_other (i:RemainingCoordinates):
   collectR K (MvPolynomial.X (i:Fin 4))=Polynomial.C (MvPolynomial.X i):=by
 simp [collectR,MvPolynomial.renameEquiv_apply,
   Equiv.optionSubtypeNe_symm_apply,i.property]
theorem collectR_rename_remaining (P:CoefficientRing K):
   collectR K (MvPolynomial.rename Subtype.val P)=Polynomial.C P:=by
 induction P using MvPolynomial.induction_on with
 | C a => simp [collectR,MvPolynomial.renameEquiv_apply]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     simp only [map_mul,MvPolynomial.rename_X,hP,collectR_X_other]
theorem embedCoefficients_eq_rename (P:CoefficientRing K):
   embedCoefficients K P=MvPolynomial.rename Subtype.val P:=by
 apply (collectR K).injective
 rw [collectR_rename_remaining]
 exact (collectR K).apply_symm_apply (Polynomial.C P)
def liftedCoefficient (F:MvPolynomial (Fin 4) K) (n:ℕ):
   MvPolynomial (Fin 4) K:=embedCoefficients K ((collectR K F).coeff n)
theorem liftedCoefficient_R_degree (F:MvPolynomial (Fin 4) K) (n:ℕ):
   (liftedCoefficient F n).degreeOf 2=0:=by
 rw [←collectR_natDegree]
 change ((collectR K) ((collectR K).symm (Polynomial.C ((collectR K F).coeff n)))).natDegree=0
 rw [AlgEquiv.apply_symm_apply,Polynomial.natDegree_C]
theorem liftedCoefficient_support
   (F:MvPolynomial (Fin 4) K) (n:ℕ) (e:Fin 4 →₀ ℕ)
   (he:e∈(liftedCoefficient F n).support):
   ∃ d∈F.support,∀ i,e i ≤ d i:=by
 classical
 have heR:e 2=0:=by
   have hh:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) he
   rw [liftedCoefficient_R_degree] at hh
   omega
 change e∈(embedCoefficients K ((collectR K F).coeff n)).support at he
 rw [embedCoefficients_eq_rename,
   MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
 obtain ⟨u,hu,heu⟩:=Finset.mem_image.mp he
 have hopt:u.optionElim n∈
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm F).support:=
   (MvPolynomial.mem_support_coeff_optionEquivLeft (R:=K)).mp hu
 rw [MvPolynomial.support_rename_of_injective
   (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at hopt
 obtain ⟨d,hd,hdu⟩:=Finset.mem_image.mp hopt
 refine ⟨d,hd,?_⟩
 intro i
 by_cases hi:i=2
 · subst i
   rw [heR]
   exact Nat.zero_le _
 · have hev:e i=u ⟨i,hi⟩:=by
     rw [←heu]
     exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i,hi⟩
   have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm i)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i=some ⟨i,hi⟩:=by
     simp [Equiv.optionSubtypeNe_symm_apply,hi]
   rw [hindex,Finsupp.optionElim_apply_some] at huv
   exact le_of_eq (hev.trans huv.symm)
theorem weight_mono_fin4 (weights:Fin 4 → ℕ) (e d:Fin 4 →₀ ℕ)
   (h:∀ i,e i ≤ d i):Finsupp.weight weights e ≤ Finsupp.weight weights d:=by
 rw [weight_fin4,weight_fin4]
 gcongr <;> exact h _
theorem liftedCoefficient_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (n:ℕ):
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient F n) ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro e he
 obtain ⟨d,hd,hed⟩:=liftedCoefficient_support F n e he
 exact (weight_mono_fin4 weights e d hed).trans (MvPolynomial.le_weightedTotalDegree weights hd)
theorem pderiv_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (i:Fin 4):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i F) ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro e he
 have hd:=RCN313.support_before_pderiv i F e he
 have hle:Finsupp.weight weights e ≤
     Finsupp.weight weights (e+Finsupp.single i 1):=by
   rw [map_add]
   exact Nat.le_add_right _ _
 exact hle.trans (MvPolynomial.le_weightedTotalDegree weights hd)
theorem degreeOf_det_le_uniform (N a:ℕ)
   (M:Matrix (Fin N) (Fin N) (MvPolynomial (Fin 5) K))
   (hM:∀ i j,(M i j).degreeOf 4 ≤ a):M.det.degreeOf 4 ≤ N*a:=by
 classical
 rw [Matrix.det_apply']
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) Finset.univ _).trans
 apply Finset.sup_le_iff.mpr
 intro σ _
 have hprod:(∏ i,M (σ i) i).degreeOf (4:Fin 5) ≤ N*a:=by
   calc
     _ ≤ ∑ i:Fin N,(M (σ i) i).degreeOf (4:Fin 5):=
       MvPolynomial.degreeOf_prod_le (4:Fin 5) Finset.univ _
     _ ≤ ∑ _i:Fin N,a:=Finset.sum_le_sum fun i _ => hM (σ i) i
     _=N*a:=by simp
 have hsign:(((Equiv.Perm.sign σ:ℤ):MvPolynomial (Fin 5) K)).degreeOf 4 ≤ 0:=by
   simpa only [map_intCast] using
     (MvPolynomial.degreeOf_C (((Equiv.Perm.sign σ:ℤ):K)) (4:Fin 5)).le
 exact (MvPolynomial.degreeOf_mul_le (4:Fin 5) _ _).trans
   ((Nat.add_le_add hsign hprod).trans_eq (zero_add _))
def weightedCoefficientEmbedding (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   CoefficientRing K →+*MvPolynomial (Fin 5) K:=
 (weightedLift K weights).comp (embedCoefficients K)
theorem degree_weightedCoefficient (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (n:ℕ):
   (weightedCoefficientEmbedding K weights ((collectR K F).coeff n)).degreeOf 4 ≤
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift K weights (liftedCoefficient F n)).degreeOf 4 ≤ _
 rw [degree_weightedLift]
 exact liftedCoefficient_weight_le weights F n
theorem eliminateR_weight_le (weights:Fin 4 → ℕ)
   (F G:MvPolynomial (Fin 4) K) (a:ℕ)
   (hF:MvPolynomial.weightedTotalDegree weights F ≤ a)
   (hG:MvPolynomial.weightedTotalDegree weights G ≤ a):
   MvPolynomial.weightedTotalDegree weights (eliminateR F G) ≤
     (F.degreeOf 2+G.degreeOf 2)*a:=by
 let ψ:=weightedCoefficientEmbedding K weights
 let M:=Polynomial.sylvester (collectR K F) (collectR K G)
   (collectR K F).natDegree (collectR K G).natDegree
 have hentry:∀ i j,((ψ.mapMatrix M) i j).degreeOf (4:Fin 5) ≤ a:=by
   intro i j
   induction j using Fin.addCases with
   | «left» j =>
       simp only [RingHom.mapMatrix_apply,Matrix.map_apply,M,Polynomial.sylvester,
         Matrix.of_apply,Fin.addCases_left]
       split_ifs
       · exact (degree_weightedCoefficient weights G _).trans hG
       · simp
   | «right» j =>
       simp only [RingHom.mapMatrix_apply,Matrix.map_apply,M,Polynomial.sylvester,
         Matrix.of_apply,Fin.addCases_right]
       split_ifs
       · exact (degree_weightedCoefficient weights F _).trans hF
       · simp
 have hdet:=degreeOf_det_le_uniform
   ((collectR K F).natDegree+(collectR K G).natDegree) a (ψ.mapMatrix M) hentry
 rw [←ψ.map_det] at hdet
 change (weightedLift K weights (eliminateR F G)).degreeOf 4 ≤ _ at hdet
 rw [degree_weightedLift,collectR_natDegree,collectR_natDegree] at hdet
 exact hdet
theorem weightedTotalDegree_prod_le {ι:Type*} (weights:Fin 4 → ℕ)
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (∏ i∈I,f i) ≤
     ∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i):=by
 rw [←degree_weightedLift,map_prod]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_prod_le (4:Fin 5) I (fun i => weightedLift K weights (f i)))
theorem sum_weighted_degrees_le_of_prod_dvd {ι:Type*} (weights:Fin 4 → ℕ)
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ i∈I,f i)∣Q):
   (∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈I,f i)≠0:=by
   intro hz
   obtain ⟨T,hT⟩:=hdiv
   exact hQ (by rw [hT,hz,zero_mul])
 have hf:∀ i∈I,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 have hmap:(∏ i∈I,weightedLift K weights (f i))∣weightedLift K weights Q:=by
   obtain ⟨T,hT⟩:=hdiv
   refine ⟨weightedLift K weights T,?_⟩
   rw [hT,map_mul,map_prod]
 calc
   (∑ i∈I,MvPolynomial.weightedTotalDegree weights (f i))=
       ∑ i∈I,(weightedLift K weights (f i)).degreeOf (4:Fin 5):=by
     simp only [degree_weightedLift]
   _=(∏ i∈I,weightedLift K weights (f i)).degreeOf (4:Fin 5):=
     (MvPolynomial.degreeOf_prod_eq I _
       (fun i hi => weightedLift_ne_zero weights (f i) (hf i hi))).symm
   _ ≤ (weightedLift K weights Q).degreeOf (4:Fin 5):=
     RCN137.coordinate_degree_le_of_dvd (4:Fin 5) _ _ hmap
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights Q:=degree_weightedLift weights Q
theorem singularContribution_weight_le (weights:Fin 4 → ℕ)
   (F:MvPolynomial (Fin 4) K) (s:ℕ) (hs:1 ≤ s) (hR:F.degreeOf 2 ≤ s):
   MvPolynomial.weightedTotalDegree weights (singularContribution F) ≤
     (2*s-1)*MvPolynomial.weightedTotalDegree weights F:=by
 unfold singularContribution
 split_ifs with h
 · have hfactor:1 ≤ 2*s-1:=by omega
   simpa only [one_mul] using
     (Nat.mul_le_mul_right (MvPolynomial.weightedTotalDegree weights F) hfactor)
 · have hpos:0 < F.degreeOf 2:=Nat.pos_of_ne_zero h
   have hder:=RCN267.R_derivative_degree_lt F hpos
   have hfactor:F.degreeOf 2+(MvPolynomial.pderiv (2:Fin 4) F).degreeOf 2 ≤
       2*s-1:=by omega
   exact (eliminateR_weight_le weights F (MvPolynomial.pderiv (2:Fin 4) F)
     (MvPolynomial.weightedTotalDegree weights F) le_rfl (pderiv_weight_le weights F 2)).trans
     (Nat.mul_le_mul_right _ hfactor)
theorem singularAuxiliary_weight_le (weights:Fin 4 → ℕ)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (s:ℕ) (hs:1 ≤ s) (hR:Q.degreeOf 2 ≤ s):
   MvPolynomial.weightedTotalDegree weights (singularAuxiliary Q) ≤
     (2*s-1)*MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 calc
   _ ≤ ∑ F∈activeFactors Q,
       MvPolynomial.weightedTotalDegree weights (singularContribution F):=
     weightedTotalDegree_prod_le weights (activeFactors Q) singularContribution
   _ ≤ ∑ F∈activeFactors Q,
       (2*s-1)*MvPolynomial.weightedTotalDegree weights F:=by
     apply Finset.sum_le_sum
     intro F hF
     exact singularContribution_weight_le weights F s hs
       ((RCN081.degreeOf_le_of_dvd (2:Fin 4) F Q
         (activeFactors_spec Q F hF).2.1 hQ).trans hR)
   _=(2*s-1)*∑ F∈activeFactors Q,MvPolynomial.weightedTotalDegree weights F:=by
     rw [Finset.mul_sum]
   _ ≤ (2*s-1)*MvPolynomial.weightedTotalDegree weights Q:=
     Nat.mul_le_mul_left _ (sum_weighted_degrees_le_of_prod_dvd weights
       (activeFactors Q) id Q hQ (activeFactors_product_dvd Q hQ))
theorem singularAuxiliary_input_caps
   (Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hs:1 ≤ s)
   (hbox:Q∈RCN174.globalCoefficientBox K D w L s):
   MvPolynomial.weightedTotalDegree seedWeights (singularAuxiliary Q) ≤ (2*s-1)*L∧
     MvPolynomial.weightedTotalDegree (contactWeights w) (singularAuxiliary Q) <
       (2*s-1)*D:=by
 have hD:0 < D:=by
   obtain ⟨d,hd⟩:=MvPolynomial.support_nonempty.mpr hQ
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 have hR:Q.degreeOf 2 ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hpositive:0 < 2*s-1:=by omega
 refine ⟨(singularAuxiliary_weight_le seedWeights Q hQ s hs hR).trans
   (Nat.mul_le_mul_left _ hcaps.1),?_⟩
 have hle:=(singularAuxiliary_weight_le (contactWeights w) Q hQ s hs hR).trans
   (Nat.mul_le_mul_left _ hcaps.2.2)
 exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (by omega:D-1 < D) hpositive)
theorem singularAuxiliary_nonzero_mem_box
   (Q:MvPolynomial (Fin 4) K) (D w L s p:ℕ) [CharP K p]
   (hQ:Q≠0) (hs:1 ≤ s) (hsmall:s < p)
   (hbox:Q∈RCN174.globalCoefficientBox K D w L s):
   singularAuxiliary Q≠0∧
     singularAuxiliary Q∈RCN174.globalCoefficientBox K
       ((2*s-1)*D) w ((2*s-1)*L) 0:=by
 have hR:Q.degreeOf 2 ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hjR:=singularAuxiliary_R_degree Q hQ p (hR.trans_lt hsmall)
 have hc:=singularAuxiliary_input_caps Q D w L s hQ hs hbox
 refine ⟨singularAuxiliary_nonzero Q hQ p (hR.trans_lt hsmall),?_⟩
 intro d hd
 have hseed:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hc.1
 have hcontact:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans_lt hc.2
 have hslope:=MvPolynomial.monomial_le_degreeOf (f:=singularAuxiliary Q) (2:Fin 4) hd
 rw [hjR] at hslope
 rw [seed_weight] at hseed
 rw [contact_weight] at hcontact
 exact ⟨hseed,hslope,hcontact⟩
end
end ProximityPrize.SubmissionLower.RCN293
end PackedLegacy_CA

/-! Packed from ProximityPrize.SubmissionLower.BS. -/
section PackedLegacy_BS
namespace ProximityPrize.SubmissionLower.RCN167
open RCN081 RCN082 RCN293 RCN267 RCN313 RCN136 RCN319 RCN231
noncomputable section
variable {K:Type*} [Field K]
def implicitLift (A:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 MvPolynomial.pderiv (0:Fin 4) A+
   MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A
theorem implicitLift_R_derivative (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0):
   MvPolynomial.pderiv (2:Fin 4) (implicitLift A)=MvPolynomial.pderiv (1:Fin 4) A:=by
 have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 0 2 A 0 (by omega)
 have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 1 2 A 0 (by omega)
 have hx0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hX
 have hy0:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) _ hY
 simp only [implicitLift,map_add,MvPolynomial.pderiv_mul,hx0,hy0,
   MvPolynomial.pderiv_X_self,one_mul,mul_zero,add_zero,zero_add]
theorem implicitLift_nonzero (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
   implicitLift A≠0:=by
 intro h
 apply hY
 rw [←implicitLift_R_derivative A hR,h,map_zero]
theorem implicitLift_R_degree_le (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0):(implicitLift A).degreeOf 2 ≤ 1:=by
 have hX:(MvPolynomial.pderiv (0:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 0 2 A 0 (by omega)
 have hY:(MvPolynomial.pderiv (1:Fin 4) A).degreeOf 2 ≤ 0:=
   pderiv_degree_bound 1 2 A 0 (by omega)
 have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf 2 ≤ 1:=by simp
 have hm:=degree_mul_bound (2:Fin 4) hvar hY
 exact degree_add_bound (2:Fin 4) (hX.trans (by omega)) (by simpa using hm)
theorem implicitLift_other_degree_le (A:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i≠2):(implicitLift A).degreeOf i ≤ A.degreeOf i:=by
 have hX:=pderiv_degree_bound 0 i A (A.degreeOf i) le_rfl
 have hY:=pderiv_degree_bound 1 i A (A.degreeOf i) le_rfl
 have hvar:(MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K).degreeOf i ≤ 0:=by
   simp [MvPolynomial.degreeOf_X,hi]
 have hm:=degree_mul_bound i hvar hY
 exact degree_add_bound i hX (by simpa using hm)
theorem implicitLift_solution (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (P:Polynomial K) (γ:K)
   (hA:specialization K P γ A=0):specialization K P γ (implicitLift A)=0:=by
 have hchain:=derivative_specialization K P γ A
 rw [hA,Polynomial.derivative_zero,pderiv_zero_of_degree_zero (2:Fin 4) A hR,
   map_zero,mul_zero,add_zero] at hchain
 have hspec:specialization K P γ (implicitLift A)=
     specialization K P γ (MvPolynomial.pderiv (0:Fin 4) A)+
       P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A):=by
   simp [implicitLift,specialization]
 exact hspec.trans hchain.symm
theorem weighted_mul_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P*Q) ≤
     MvPolynomial.weightedTotalDegree weights P+MvPolynomial.weightedTotalDegree weights Q:=by
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_mul_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_add_le (weights:Fin 4 → ℕ) (P Q:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree weights (P+Q) ≤
     max (MvPolynomial.weightedTotalDegree weights P) (MvPolynomial.weightedTotalDegree weights Q):=by
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   (MvPolynomial.degreeOf_add_le (4:Fin 5) (weightedLift K weights P) (weightedLift K weights Q))
theorem weighted_X (weights:Fin 4 → ℕ) (i:Fin 4):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.X i:MvPolynomial (Fin 4) K)=weights i:=by
 simp [MvPolynomial.weightedTotalDegree,MvPolynomial.support_X,Finsupp.weight_single]
theorem pderiv_weight_sub_bound (weights:Fin 4 → ℕ)
   (A:MvPolynomial (Fin 4) K) (i:Fin 4) (B:ℕ)
   (hA:MvPolynomial.weightedTotalDegree weights A ≤ B):
   MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i A) ≤ B-weights i:=by
 apply (weightedTotalDegree_le_iff weights _ _).mpr
 intro d hd
 have hh:=(MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i A d hd)).trans hA
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 omega
theorem implicitLift_seed_weight_le (A:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree seedWeights (implicitLift A) ≤
     MvPolynomial.weightedTotalDegree seedWeights A:=by
 have hX:=pderiv_weight_le seedWeights A 0
 have hY:=pderiv_weight_le seedWeights A 1
 have hvar:MvPolynomial.weightedTotalDegree seedWeights
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=0:=by
   rw [weighted_X]
   simp [seedWeights]
 have hm:=weighted_mul_le seedWeights (MvPolynomial.X (2:Fin 4))
   (MvPolynomial.pderiv (1:Fin 4) A)
 rw [hvar,zero_add] at hm
 exact (weighted_add_le seedWeights _ _).trans (max_le hX (hm.trans hY))
theorem implicitLift_contact_weight_le
   (A:MvPolynomial (Fin 4) K) (D w:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hA:MvPolynomial.weightedTotalDegree (contactWeights w) A ≤ D-1):
   MvPolynomial.weightedTotalDegree (contactWeights w) (implicitLift A) ≤ D-2:=by
 have hX:=pderiv_weight_sub_bound (contactWeights w) A 0 (D-1) hA
 have hY:=pderiv_weight_sub_bound (contactWeights w) A 1 (D-1) hA
 change MvPolynomial.weightedTotalDegree (contactWeights w)
   (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-1-1 at hX
 change MvPolynomial.weightedTotalDegree (contactWeights w)
   (MvPolynomial.pderiv (1:Fin 4) A) ≤ D-1-w at hY
 have hx:MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.pderiv (0:Fin 4) A) ≤ D-2:=by omega
 have hvar:MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K)=w-1:=by
   rw [weighted_X]
   simp [contactWeights]
 have hm:=weighted_mul_le (contactWeights w) (MvPolynomial.X (2:Fin 4))
   (MvPolynomial.pderiv (1:Fin 4) A)
 rw [hvar] at hm
 have hm':MvPolynomial.weightedTotalDegree (contactWeights w)
     (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) A) ≤ D-2:=by omega
 exact (weighted_add_le (contactWeights w) _ _).trans (max_le hx hm')
theorem implicitLift_mem_box
   (A:MvPolynomial (Fin 4) K) (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:A∈RCN174.globalCoefficientBox K D w L 0):
   implicitLift A∈RCN174.globalCoefficientBox K D w L 1:=by
 have hD:0 < D:=by omega
 have hcaps:=(mem_globalCoefficientBox_iff A D w L 0 hD).mp hbox
 have hR:A.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hs:=(implicitLift_seed_weight_le A).trans hcaps.1
 have hc:=implicitLift_contact_weight_le A D w hw hDw hcaps.2.2
 have hr:=implicitLift_R_degree_le A hR
 intro d hd
 have hseed:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hs
 have hcontact:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
 have hslope:=(MvPolynomial.monomial_le_degreeOf (f:=implicitLift A) (2:Fin 4) hd).trans hr
 rw [seed_weight] at hseed
 rw [contact_weight] at hcontact
 exact ⟨hseed,hslope,by omega⟩
def positiveRFactors (F:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors F).filter (fun G => 0 < G.degreeOf 2)
theorem positiveRFactors_spec (F G:MvPolynomial (Fin 4) K)
   (hG:G∈positiveRFactors F):Irreducible G∧G∣F∧0 < G.degreeOf 2:=by
 classical
 obtain ⟨hmem,hpos⟩:=Finset.mem_filter.mp hG
 have hh:=activeFactors_spec F G hmem
 exact ⟨hh.1,hh.2.1,hpos⟩
theorem positiveRFactors_product_dvd (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∏ G∈positiveRFactors F,G)∣F:=by
 classical
 exact (Finset.prod_dvd_prod_of_subset (positiveRFactors F) (activeFactors F) id
   (Finset.filter_subset _ _)).trans (activeFactors_product_dvd F hF)
theorem factor_derivative_regular_at_zero {B:Type*} [CommRing B]
   (ψ:MvPolynomial (Fin 4) K →+*B) (F G:MvPolynomial (Fin 4) K)
   (hdiv:G∣F) (hG:ψ G=0)
   (hregular:ψ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   ψ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
 intro hz
 obtain ⟨T,hT⟩:=hdiv
 apply hregular
 rw [hT,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,hG,
   zero_mul,zero_mul,zero_add]
theorem lift_positive_factor_budgets (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
   (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
 have hF:=implicitLift_nonzero A hR hY
 have hprod:=positiveRFactors_product_dvd (implicitLift A) hF
 have hb:=RCN081.sum_degreeOf_le_of_prod_dvd
   (positiveRFactors (implicitLift A)) id (implicitLift A) hF hprod
 exact ⟨(hb 2).trans (implicitLift_R_degree_le A hR),
   (hb 1).trans (implicitLift_other_degree_le A 1 (by decide)),
   (hb 3).trans (implicitLift_other_degree_le A 3 (by decide))⟩
theorem lift_positive_factor_card_le_one (A:MvPolynomial (Fin 4) K)
   (hR:A.degreeOf 2=0) (hY:MvPolynomial.pderiv (1:Fin 4) A≠0):
   (positiveRFactors (implicitLift A)).card ≤ 1:=by
 classical
 have hc:(positiveRFactors (implicitLift A)).card ≤
     ∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4):=by
   calc
     _=∑ _G∈positiveRFactors (implicitLift A),(1:ℕ):=by simp
     _ ≤ _:=Finset.sum_le_sum fun G hG => (positiveRFactors_spec _ G hG).2.2
 exact hc.trans (lift_positive_factor_budgets A hR hY).1
section SurfacePoints
variable {T:Type*} [Field T]
theorem exists_regular_lift_factor_at_surface
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (A:MvPolynomial (Fin 4) K) (hA:A≠0) (hR:A.degreeOf 2=0)
   (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0)
   (hregular:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0):
   ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G∣implicitLift A∧
     G.degreeOf 2=1∧MvPolynomial.eval v (surfaceMap φ G)=0∧
     MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) G))≠0∧¬ G∣A:=by
 classical
 let ψ:MvPolynomial (Fin 4) K →+*T:=(MvPolynomial.eval v).comp (surfaceMap φ)
 have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
   intro hz
   apply hregular
   rw [hz,map_zero,map_zero]
 have hF:=implicitLift_nonzero A hR hY
 obtain ⟨G,hG,hz⟩:=exists_active_factor_of_surface_zero φ hφ (implicitLift A) hF v hzero
 have hspec:=activeFactors_spec (implicitLift A) G hG
 have hFregular:ψ (MvPolynomial.pderiv (2:Fin 4) (implicitLift A))≠0:=by
   rw [implicitLift_R_derivative A hR]
   exact hregular
 have hGreg:=factor_derivative_regular_at_zero ψ (implicitLift A) G hspec.2.1 hz hFregular
 have hpos:0 < G.degreeOf 2:=by
   apply Nat.pos_of_ne_zero
   intro hn
   apply hGreg
   rw [pderiv_zero_of_degree_zero (2:Fin 4) G hn,map_zero]
 have hdeg:G.degreeOf 2=1:=by
   have hh:=(RCN081.degreeOf_le_of_dvd (2:Fin 4) G (implicitLift A)
     hspec.2.1 hF).trans (implicitLift_R_degree_le A hR)
   omega
 have hproper:¬ G∣A:=by
   intro hd
   have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) G A hd hA
   omega
 exact ⟨G,Finset.mem_filter.mpr ⟨hG,hpos⟩,hspec.1,hspec.2.1,hdeg,hz,hGreg,hproper⟩
end SurfacePoints
theorem exists_regular_lift_factor_of_solution
   (A:MvPolynomial (Fin 4) K) (hA:A≠0) (P:Polynomial K) (γ:K)
   (D w L:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:A∈RCN174.globalCoefficientBox K D w L 0)
   (hsolution:specialization K P γ A=0)
   (hregular:specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0):
   ∃ G∈positiveRFactors (implicitLift A),Irreducible G∧G.degreeOf 2=1∧
     G∈RCN174.globalCoefficientBox K D w L 1∧
     specialization K P γ G=0∧
     specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0∧¬ G∣A:=by
 have hR:A.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hFsolution:=implicitLift_solution A hR P γ hsolution
 let φ:=RCN135.polynomialEmbedding K
 let v:Fin 3 → RCN135.GenericField K:=
   fun i => RCN135.initialPoint K P γ i.succ
 have hzero:MvPolynomial.eval v (surfaceMap φ (implicitLift A))=0:=by
   have hh:=(RCN138.actual_generic_initial_zero_iff K P γ (implicitLift A)).mpr hFsolution
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
 have hreg:MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
   intro hz
   apply hregular
   apply (RCN138.actual_generic_initial_zero_iff K P γ _).mp
   simpa only [RCN138.canonical_geometricSurfaceMap] using hz
 obtain ⟨G,hG,hi,hd,hdeg,hpoint,hGreg,hproper⟩:=
   exists_regular_lift_factor_at_surface φ (RCN135.polynomialEmbedding_injective K)
     A hA hR v hzero hreg
 have hY:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
   intro hz
   exact hregular (by rw [hz,map_zero])
 have hGbox:=RCN081.mem_globalCoefficientBox_of_dvd G (implicitLift A)
   D w L 1 (implicitLift_nonzero A hR hY) hd (implicitLift_mem_box A D w L hw hDw hbox)
 have hGsol:specialization K P γ G=0:=by
   apply (RCN138.actual_generic_initial_zero_iff K P γ G).mp
   simpa only [RCN138.canonical_geometricSurfaceMap] using hpoint
 have hGregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
   intro hz
   apply hGreg
   have hh:=(RCN138.actual_generic_initial_zero_iff K P γ _).mpr hz
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
 exact ⟨G,hG,hi,hdeg,hGbox,hGsol,hGregular,hproper⟩
end
end ProximityPrize.SubmissionLower.RCN167
end PackedLegacy_BS

/-! Packed from ProximityPrize.SubmissionLower.I9. -/
section PackedLegacy_I9
namespace ProximityPrize.SubmissionLower.RCN079
open RCN136 RCN082 RCN290 RCN293 RCN081 RCN319
noncomputable section
variable {K:Type*} [Field K]
def swapYR (K:Type*) [Field K]:MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K:=
 MvPolynomial.renameEquiv K (Equiv.swap (1:Fin 4) 2)
@[simp] theorem swapYR_twice (F:MvPolynomial (Fin 4) K):swapYR K (swapYR K F)=F:=by
 simp [swapYR,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_rename,Function.comp_def]
 exact MvPolynomial.rename_id_apply F
theorem swapYR_ne_zero (F:MvPolynomial (Fin 4) K) (hF:F≠0):swapYR K F≠0:=by
 intro h
 apply hF
 apply (swapYR K).injective
 simpa only [map_zero] using h
theorem swapYR_degree_Y (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 1=F.degreeOf 2:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (2:Fin 4))
theorem swapYR_degree_R (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 2=F.degreeOf 1:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (1:Fin 4))
theorem swapYR_degree_Z (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 3=F.degreeOf 3:=by
 have hfix:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 simpa only [swapYR,MvPolynomial.renameEquiv_apply,hfix] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (3:Fin 4))
theorem swapYR_pderiv_Y (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 4) (swapYR K F)=
     swapYR K (MvPolynomial.pderiv (2:Fin 4) F):=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.pderiv_rename (Equiv.swap (1:Fin 4) 2).injective (2:Fin 4) F)
theorem coordinate_weight_degree (F:MvPolynomial (Fin 4) K) (i:Fin 4):
   MvPolynomial.weightedTotalDegree (Pi.single i 1) F=F.degreeOf i:=by
 rw [MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => F.support.sup f)
 funext d
 exact Finsupp.weight_single_one_apply i d
def exceptionalAuxiliary (J:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 swapYR K (singularAuxiliary (swapYR K J))
theorem exceptionalAuxiliary_nonzero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):exceptionalAuxiliary J≠0:=by
 apply swapYR_ne_zero
 apply singularAuxiliary_nonzero (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_Y_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):(exceptionalAuxiliary J).degreeOf 1=0:=by
 rw [exceptionalAuxiliary,swapYR_degree_Y]
 apply singularAuxiliary_R_degree (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_R_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):(exceptionalAuxiliary J).degreeOf 2=0:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (1:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Y,hR,mul_zero] at hb
 rw [exceptionalAuxiliary,swapYR_degree_R]
 exact Nat.eq_zero_of_le_zero hb
theorem exceptionalAuxiliary_Z_degree_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):
   (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*J.degreeOf 3:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (3:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Z] at hb
 rw [exceptionalAuxiliary,swapYR_degree_Z]
 exact hb
theorem exceptionalAuxiliary_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j):
   exceptionalAuxiliary J≠0∧(exceptionalAuxiliary J).degreeOf 1=0∧
     (exceptionalAuxiliary J).degreeOf 2=0∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*j∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ 2*j^2:=by
 have hz:=(exceptionalAuxiliary_Z_degree_le J hJ j hj hY).trans (Nat.mul_le_mul_left _ hZ)
 refine ⟨exceptionalAuxiliary_nonzero J hJ j p hY hsmall,
   exceptionalAuxiliary_Y_degree_zero J hJ j p hY hsmall,
   exceptionalAuxiliary_R_degree_zero J hJ hR j hj hY,hz,?_⟩
 calc
   _ ≤ (2*j-1)*j:=hz
   _ ≤ (2*j)*j:=Nat.mul_le_mul_right j (Nat.sub_le _ _)
   _=2*j^2:=by ring
def originalImplicitFactors (J:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors (swapYR K J)).image (swapYR K)
theorem swapYR_dvd_swapYR_iff (F J:MvPolynomial (Fin 4) K):
   swapYR K F∣swapYR K J ↔ F∣J:=by
 constructor
 · rintro ⟨T,hT⟩
   refine ⟨swapYR K T,?_⟩
   have hh:=congrArg (swapYR K) hT
   simpa only [map_mul,swapYR_twice] using hh
 · rintro ⟨T,hT⟩
   exact ⟨swapYR K T,by rw [hT,map_mul]⟩
theorem originalImplicitFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hA:A∈originalImplicitFactors J):Irreducible A∧A∣J:=by
 classical
 obtain ⟨F,hF,rfl⟩:=Finset.mem_image.mp hA
 have hf:=activeFactors_spec (swapYR K J) F hF
 refine ⟨(MulEquiv.irreducible_iff (swapYR K)).mpr hf.1,?_⟩
 have hh:=(swapYR_dvd_swapYR_iff F (swapYR K J)).mpr hf.2.1
 simpa only [swapYR_twice] using hh
theorem originalImplicitFactors_product_dvd (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∏ A∈originalImplicitFactors J,A)∣J:=by
 classical
 have hi:Set.InjOn (swapYR K) (activeFactors (swapYR K J)):=(swapYR K).injective.injOn
 have heq:(∏ A∈originalImplicitFactors J,A)=
     swapYR K (∏ F∈activeFactors (swapYR K J),F):=by
   rw [originalImplicitFactors,Finset.prod_image hi,map_prod]
 rw [heq]
 have hh:=(swapYR_dvd_swapYR_iff (∏ F∈activeFactors (swapYR K J),F) (swapYR K J)).mpr
   (activeFactors_product_dvd (swapYR K J) (swapYR_ne_zero J hJ))
 simpa only [swapYR_twice] using hh
theorem originalImplicitFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈originalImplicitFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈originalImplicitFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 have hh:=RCN081.sum_degreeOf_le_of_prod_dvd
   (originalImplicitFactors J) id J hJ (originalImplicitFactors_product_dvd J hJ)
 exact ⟨hh 1,hh 3⟩
section SurfaceCoverage
variable {T:Type*} [Field T]
def swapSurfacePoint (v:Fin 3 → T):Fin 3 → T:=![v 1,v 0,v 2]
@[simp] theorem swapSurfacePoint_twice (v:Fin 3 → T):
   swapSurfacePoint (swapSurfacePoint v)=v:=by
 funext i
 fin_cases i <;> simp [swapSurfacePoint]
theorem eval_surface_swap (φ:Polynomial K →+*T) (v:Fin 3 → T)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ (swapYR K F))=
     MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ F):=by
 have hfix0:Equiv.swap (1:Fin 4) 2 (0:Fin 4)=0:=by decide
 have hfix3:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 have hs1:surfaceMap φ (MvPolynomial.X (1:Fin 4))=MvPolynomial.X (0:Fin 3):=
   surfaceMap_X_succ φ 0
 have hs2:surfaceMap φ (MvPolynomial.X (2:Fin 4))=MvPolynomial.X (1:Fin 3):=
   surfaceMap_X_succ φ 1
 have hs3:surfaceMap φ (MvPolynomial.X (3:Fin 4))=MvPolynomial.X (2:Fin 3):=
   surfaceMap_X_succ φ 2
 have hh:((MvPolynomial.eval v).comp (surfaceMap φ)).comp (swapYR K).toRingHom=
     (MvPolynomial.eval (swapSurfacePoint v)).comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply,
         hfix0,hfix3,hs1,hs2,hs3,swapSurfacePoint]
 exact RingHom.congr_fun hh F
theorem surface_zero_exceptional_or_implicit_regular
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ J)=0):
   MvPolynomial.eval v (surfaceMap φ (exceptionalAuxiliary J))=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧
       MvPolynomial.eval v (surfaceMap φ A)=0∧
       MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
 classical
 have hswap:MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ (swapYR K J))=0:=by
   rw [eval_surface_swap,swapSurfacePoint_twice]
   exact hzero
 obtain haux | ⟨F,hF,hi,hpos,hz,hreg⟩:=surface_zero_singular_or_regular
   φ hφ (swapYR K J) (swapYR_ne_zero J hJ) (swapSurfacePoint v) hswap
 · left
   rw [exceptionalAuxiliary,eval_surface_swap]
   exact haux
 · right
   have hmem:swapYR K F∈originalImplicitFactors J:=Finset.mem_image.mpr ⟨F,hF,rfl⟩
   have hs:=originalImplicitFactors_spec J (swapYR K F) hmem
   have hAR:(swapYR K F).degreeOf 2=0:=by
     have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) (swapYR K F) J hs.2 hJ
     omega
   refine ⟨swapYR K F,hmem,hs.1,hs.2,hAR,?_,?_,?_⟩
   · rw [swapYR_degree_Y]
     exact hpos
   · rw [eval_surface_swap]
     exact hz
   · rw [swapYR_pderiv_Y,eval_surface_swap]
     exact hreg
end SurfaceCoverage
theorem solution_exceptional_or_implicit_regular
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧specialization K P γ A=0∧
       specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0:=by
 let φ:=RCN135.polynomialEmbedding K
 let v:Fin 3 → RCN135.GenericField K:=
   fun i => RCN135.initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [RCN138.canonical_geometricSurfaceMap] using
     (RCN138.actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨A,hA,hi,hd,hAR,hAY,hz,hreg⟩:=
   surface_zero_exceptional_or_implicit_regular φ
     (RCN135.polynomialEmbedding_injective K) J hJ hR v ((heval J).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨A,hA,hi,hd,hAR,hAY,(heval _).mp hz,(heval _).not.mp hreg⟩
end
end ProximityPrize.SubmissionLower.RCN079
end PackedLegacy_I9

/-! Packed from ProximityPrize.SubmissionLower.J0. -/
section PackedLegacy_J0
namespace ProximityPrize.SubmissionLower.RCN080
open RCN136 RCN079 RCN319
noncomputable section
section SeedProjection
variable {T:Type*} [Field T]
def seedProjection (T:Type*) [Field T]:MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![0,0,Polynomial.X]
def seedEmbedding (T:Type*) [Field T]:Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2:Fin 3))
theorem seed_only_vars (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0)
   (i:Fin 3) (hi:i∈S.vars):i=2:=by
 fin_cases i
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hY)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · rfl
theorem seedProjection_reconstruct (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):
   seedEmbedding T (seedProjection T S)=S:=by
 change ((seedEmbedding T).comp (seedProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedEmbedding,seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedEmbedding,seedProjection]
 · rfl
theorem seedProjection_nonzero (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):seedProjection T S≠0:=by
 intro hz
 apply hS
 rw [←seedProjection_reconstruct S hY hR,hz,map_zero]
theorem monomial_fin3 (d:Fin 3 →₀ ℕ) (a:T):
   MvPolynomial.monomial d a=MvPolynomial.C a*MvPolynomial.X 0^d 0*
     MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem seedProjection_monomial (d:Fin 3 →₀ ℕ) (a:T):
   seedProjection T (MvPolynomial.monomial d a)=
     Polynomial.C a*0^d 0*0^d 1*Polynomial.X^d 2:=by
 rw [monomial_fin3]
 simp [seedProjection]
theorem seedProjection_monomial_natDegree_le (d:Fin 3 →₀ ℕ) (a:T):
   (seedProjection T (MvPolynomial.monomial d a)).natDegree ≤ d 2:=by
 rw [seedProjection_monomial]
 have hc:(Polynomial.C a).natDegree ≤ 0:=by simp
 have h0:((0:Polynomial T)^d 0).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 0)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have h1:((0:Polynomial T)^d 1).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 1)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have hx:((Polynomial.X:Polynomial T)^d 2).natDegree ≤ d 2:=by simp
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc h0) h1) hx
 simpa using hh
theorem seedProjection_natDegree_le (S:MvPolynomial (Fin 3) T):
   (seedProjection T S).natDegree ≤ S.degreeOf 2:=by
 classical
 have hsum:seedProjection T S=
     ∑ d∈S.support,seedProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 exact Polynomial.natDegree_sum_le_of_forall_le S.support _ (fun d hd =>
   (seedProjection_monomial_natDegree_le d (S.coeff d)).trans (MvPolynomial.monomial_le_degreeOf 2 hd))
theorem seedProjection_eval (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0) (v:Fin 3 → T):
   (seedProjection T S).eval (v 2)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 2)).comp (seedProjection T)) S=(MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedProjection]
 · rfl
end SeedProjection
section GenericSurface
variable {K T:Type*} [Field K] [Field T]
def auxiliarySeedPolynomial (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):Polynomial T:=
 seedProjection T (surfaceMap φ H)
theorem surface_seed_only (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):
   (surfaceMap φ H).degreeOf 0=0∧(surfaceMap φ H).degreeOf 1=0:=
 ⟨Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 0).trans_eq hY),
   Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 1).trans_eq hR)⟩
theorem auxiliarySeedPolynomial_nonzero
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):auxiliarySeedPolynomial φ H≠0:=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_nonzero (surfaceMap φ H) (surfaceMap_ne_zero φ hφ H hH) hs.1 hs.2
theorem auxiliarySeedPolynomial_natDegree_le
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):
   (auxiliarySeedPolynomial φ H).natDegree ≤ H.degreeOf 3:=
 (seedProjection_natDegree_le (surfaceMap φ H)).trans (surfaceMap_degreeOf_le φ H 2)
theorem auxiliarySeedPolynomial_eval
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (v:Fin 3 → T):
   (auxiliarySeedPolynomial φ H).eval (v 2)=MvPolynomial.eval v (surfaceMap φ H):=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_eval (surfaceMap φ H) hs.1 hs.2 v
theorem card_surface_seeds_le
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ v:Fin 3 → T,
     v 2=φ (Polynomial.C γ)∧MvPolynomial.eval v (surfaceMap φ H)=0):
   seeds.card ≤ H.degreeOf 3:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq T:=Classical.decEq T
 let q:Polynomial T:=auxiliarySeedPolynomial φ H
 let c:K →+*T:=φ.comp Polynomial.C
 have hq:q≠0:=auxiliarySeedPolynomial_nonzero φ hφ H hH hY hR
 have hroots:∀ z∈seeds.image c,z∈q.roots:=by
   intro z hz
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
   obtain ⟨v,hv,hzero⟩:=hsolutions γ hγ
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (φ (Polynomial.C γ))=0
   rw [←hv]
   exact (auxiliarySeedPolynomial_eval φ H hY hR v).trans hzero
 calc
   seeds.card=(seeds.image c).card:=(Finset.card_image_of_injOn c.injective.injOn).symm
   _ ≤ q.natDegree:=Polynomial.card_le_degree_of_subset_roots hroots
   _ ≤ H.degreeOf 3:=auxiliarySeedPolynomial_natDegree_le φ H
end GenericSurface
section ActualSolutions
variable {K:Type*} [Field K]
theorem card_actual_solution_seeds_le
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,specialization K P γ H=0):
   seeds.card ≤ H.degreeOf 3:=by
 apply card_surface_seeds_le (RCN135.polynomialEmbedding K)
   (RCN135.polynomialEmbedding_injective K) H hH hY hR seeds
 intro γ hγ
 obtain ⟨P,hP⟩:=hsolutions γ hγ
 refine ⟨fun i => RCN135.initialPoint K P γ i.succ,?_,?_⟩
 · rfl
 · have hh:=(RCN138.actual_generic_initial_zero_iff K P γ H).mpr hP
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
theorem exceptional_solution_seed_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,
     specialization K P γ (exceptionalAuxiliary J)=0):seeds.card ≤ 2*j^2:=by
 have hd:=exceptionalAuxiliary_data J hJ hR j p hj hsmall hY hZ
 exact (card_actual_solution_seeds_le (exceptionalAuxiliary J) hd.1 hd.2.1 hd.2.2.1
   seeds hsolutions).trans hd.2.2.2.2
end ActualSolutions
end
end ProximityPrize.SubmissionLower.RCN080
end PackedLegacy_J0

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier09 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BU. -/
section PackedLegacy_BU
namespace ProximityPrize.SubmissionLower.RCN169
open RCN079 RCN167 RCN081 RCN267 RCN174
noncomputable section
variable {K:Type*} [Field K]
def implicitBaseFactors (J:MvPolynomial (Fin 4) K):
   Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (originalImplicitFactors J).filter
   (fun A => MvPolynomial.pderiv (1:Fin 4) A≠0)
theorem implicitBaseFactors_subset (J:MvPolynomial (Fin 4) K):
   implicitBaseFactors J ⊆ originalImplicitFactors J:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitBaseFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0) (hA:A∈implicitBaseFactors J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0:=by
 classical
 obtain ⟨hm,hy⟩:=Finset.mem_filter.mp hA
 have hs:=originalImplicitFactors_spec J A hm
 have hr:=RCN081.degreeOf_le_of_dvd (2:Fin 4) A J hs.2 hJ
 exact ⟨hs.1,hs.2,by omega,hy⟩
theorem implicitBaseFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 classical
 have hb:=originalImplicitFactors_degree_budgets J hJ
 exact ⟨(Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.1,
   (Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.2⟩
def implicitPairSet (J:MvPolynomial (Fin 4) K):
   Finset ((A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):=
 (implicitBaseFactors J).sigma (fun A => positiveRFactors (implicitLift A))
theorem mem_implicitPairSet (J A G:MvPolynomial (Fin 4) K):
   (⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
       implicitPairSet J ↔
     A∈implicitBaseFactors J∧G∈positiveRFactors (implicitLift A):=by
 classical
 exact Finset.mem_sigma
theorem implicitPair_spec (J A G:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0)
   (hpair:(⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
     implicitPairSet J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0∧
     Irreducible G∧G∣implicitLift A∧G.degreeOf 2=1∧¬ G∣A:=by
 obtain ⟨hA,hG⟩:=(mem_implicitPairSet J A G).mp hpair
 obtain ⟨hiA,hdA,hrA,hyA⟩:=implicitBaseFactors_spec J A hJ hR hA
 obtain ⟨hiG,hdG,hrG⟩:=positiveRFactors_spec (implicitLift A) G hG
 have hF:=implicitLift_nonzero A hrA hyA
 have hgcap:=(RCN081.degreeOf_le_of_dvd (2:Fin 4)
   G (implicitLift A) hdG hF).trans (implicitLift_R_degree_le A hrA)
 refine ⟨hiA,hdA,hrA,hyA,hiG,hdG,by omega,?_⟩
 intro hd
 have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) G A hd hiA.ne_zero
 omega
theorem sum_products_le_product_sums {ι:Type*} (I:Finset ι) (f g:ι → ℕ):
   (∑ i∈I,f i*g i) ≤ (∑ i∈I,f i)*(∑ i∈I,g i):=by
 calc
   _ ≤ ∑ i∈I,f i*(∑ j∈I,g j):=by
     apply Finset.sum_le_sum
     intro i hi
     exact Nat.mul_le_mul_left (f i) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
   _=_:=(Finset.sum_mul I f (∑ j∈I,g j)).symm
theorem implicitBaseFactors_product_degree_budget
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)) ≤
     J.degreeOf 1*J.degreeOf 3:=by
 have hb:=implicitBaseFactors_degree_budgets J hJ
 exact (sum_products_le_product_sums (implicitBaseFactors J)
   (fun A => A.degreeOf 1) (fun A => A.degreeOf 3)).trans (Nat.mul_le_mul hb.1 hb.2)
def pairYCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 3
def pairRCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 1*q.1.degreeOf 3+q.2.degreeOf 3*q.1.degreeOf 1
def pairZCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 1
theorem implicitPair_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*J.degreeOf 1*J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ J.degreeOf 1:=by
 classical
 have hlocal (A:MvPolynomial (Fin 4) K) (hA:A∈implicitBaseFactors J):
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
   obtain ⟨_,_,hr,hy⟩:=implicitBaseFactors_spec J A hJ hR hA
   exact lift_positive_factor_budgets A hr hy
 have hb:=implicitBaseFactors_degree_budgets J hJ
 have hy:(∑ q∈implicitPairSet J,pairYCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 3) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 3) (hlocal A hA).1
 have hz:(∑ q∈implicitPairSet J,pairZCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 1) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 1) (hlocal A hA).1
 have hr:(∑ q∈implicitPairSet J,pairRCost q) ≤
     ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),
     (G.degreeOf 1*A.degreeOf 3+G.degreeOf 3*A.degreeOf 1)) ≤ _
   rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.sum_mul]
   calc
     _ ≤ A.degreeOf 1*A.degreeOf 3+A.degreeOf 3*A.degreeOf 1:=
       Nat.add_le_add (Nat.mul_le_mul_right _ (hlocal A hA).2.1)
         (Nat.mul_le_mul_right _ (hlocal A hA).2.2)
     _=_:=by ring
 refine ⟨hy.trans hb.2,?_,hz.trans hb.1⟩
 calc
   _ ≤ ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=hr
   _=2*(∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=
     (Finset.mul_sum _ _ _).symm
   _ ≤ 2*(J.degreeOf 1*J.degreeOf 3):=
     Nat.mul_le_mul_left 2 (implicitBaseFactors_product_degree_budget J hJ)
   _=_:=by ring
theorem implicitPair_input_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:0 < w) (hbox:J∈globalCoefficientBox K D w j 0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ j∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*((D-1)/w)*j∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ (D-1)/w:=by
 have hR:J.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hcaps:=degree_bounds_of_mem_box J D w j 0 hw hbox
 have hy:J.degreeOf 1 ≤ (D-1)/w:=hcaps.1
 have hz:J.degreeOf 3 ≤ j:=hcaps.2.2
 have hb:=implicitPair_degree_budgets J hJ hR
 exact ⟨hb.1.trans hz,
   hb.2.1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hy) hz),hb.2.2.trans hy⟩
end
end ProximityPrize.SubmissionLower.RCN169
end PackedLegacy_BU

/-! Packed from ProximityPrize.SubmissionLower.V. -/
section PackedLegacy_V
namespace ProximityPrize.SubmissionLower.RCN286
open RCN169 RCN167 RCN079 RCN080 RCN290 RCN293 RCN135 RCN136 RCN138 RCN082 RCN081 RCN174 RCN319
noncomputable section
variable {K:Type*} [Field K]
def RegularSolution (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ F=0∧
   specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0
def LiftedSolutionPair
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ q.1=0∧
   specialization K P γ (MvPolynomial.pderiv (1:Fin 4) q.1)≠0∧
   RegularSolution q.2 P γ
theorem solution_regular_or_auxiliary
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ Q=0):
   specialization K P γ (singularAuxiliary Q)=0∨
     ∃ F∈positiveRFactors Q,RegularSolution F P γ:=by
 classical
 let φ:=polynomialEmbedding K
 let v:Fin 3 → GenericField K:=fun i => initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [canonical_geometricSurfaceMap] using (actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨F,hF,_hi,hpos,hz,hregular⟩:=
   surface_zero_singular_or_regular φ (polynomialEmbedding_injective K)
     Q hQ v ((heval Q).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨F,Finset.mem_filter.mpr ⟨hF,hpos⟩,
     (heval F).mp hz,(heval _).not.mp hregular⟩
theorem directFactor_data
   (Q F:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s)
   (hF:F∈positiveRFactors Q):
   Irreducible F∧0 < F.degreeOf 2∧F∈globalCoefficientBox K D w L s:=by
 obtain ⟨hi,hd,hr⟩:=positiveRFactors_spec Q F hF
 exact ⟨hi,hr,mem_globalCoefficientBox_of_dvd F Q D w L s hQ hd hbox⟩
theorem directFactor_input_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w) (hbox:Q∈globalCoefficientBox K D w L s):
   (∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
     (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
     (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L:=
 separated_factor_caps_of_prod_dvd (positiveRFactors Q) id Q D w L s hw hQ hbox
   (positiveRFactors_product_dvd Q hQ)
theorem implicitPair_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:J∈globalCoefficientBox K D w j 0)
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (hq:q∈implicitPairSet J):
   Irreducible q.1∧Irreducible q.2∧q.2.degreeOf 2=1∧
     q.1∈globalCoefficientBox K D w j 0∧
     q.2∈globalCoefficientBox K D w j 1∧¬ q.2∣q.1:=by
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain ⟨hiA,hdA,hrA,hyA,hiG,hdG,hrG,hproper⟩:=
   implicitPair_spec J q.1 q.2 hJ hR hq
 have hAbox:=mem_globalCoefficientBox_of_dvd q.1 J D w j 0 hJ hdA hbox
 have hGbox:=mem_globalCoefficientBox_of_dvd q.2 (implicitLift q.1) D w j 1
   (implicitLift_nonzero q.1 hrA hyA) hdG
   (implicitLift_mem_box q.1 D w j hw hDw hAbox)
 exact ⟨hiA,hiG,hrG,hAbox,hGbox,hproper⟩
theorem solution_implicit_pair_or_exceptional
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (P:Polynomial K) (γ:K) (D w j:ℕ)
   (hw:1 ≤ w) (hDw:w < D) (hbox:J∈globalCoefficientBox K D w j 0)
   (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ q∈implicitPairSet J,LiftedSolutionPair q P γ:=by
 classical
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain haux | ⟨A,hA,hi,hd,_hAR,_hAY,hsolA,hregA⟩:=
   solution_exceptional_or_implicit_regular J hJ hR P γ hsolution
 · exact Or.inl haux
 · have hy:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
     intro hz
     exact hregA (by rw [hz,map_zero])
   have hAmem:A∈implicitBaseFactors J:=Finset.mem_filter.mpr ⟨hA,hy⟩
   have hAbox:=mem_globalCoefficientBox_of_dvd A J D w j 0 hJ hd hbox
   obtain ⟨G,hG,_hiG,_hrG,_hGbox,hsolG,hregG,_hproper⟩:=
     exists_regular_lift_factor_of_solution A hi.ne_zero P γ D w j hw hDw hAbox hsolA hregA
   exact Or.inr ⟨⟨A,G⟩,(mem_implicitPairSet J A G).mpr ⟨hAmem,hG⟩,
     hsolA,hregA,hsolG,hregG⟩
def exceptionalSeeds (J:MvPolynomial (Fin 4) K) (seeds:Finset K)
   (selected:K → Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => specialization K (selected γ) γ (exceptionalAuxiliary J)=0)
theorem exceptionalSeeds_subset (J:MvPolynomial (Fin 4) K)
   (seeds:Finset K) (selected:K → Polynomial K):exceptionalSeeds J seeds selected ⊆ seeds:=by
 classical
 exact Finset.filter_subset _ _
theorem exceptionalSeeds_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j)
   (seeds:Finset K) (selected:K → Polynomial K):
   (exceptionalSeeds J seeds selected).card ≤ 2*j^2:=by
 classical
 apply exceptional_solution_seed_card_le J hJ hR j p hj hsmall hY hZ
 intro γ hγ
 exact ⟨selected γ,(Finset.mem_filter.mp hγ).2⟩
theorem solution_three_way
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ Q=0):
   (∃ F∈positiveRFactors Q,RegularSolution F P γ)∨
     (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q P γ)∨
     specialization K P γ (exceptionalAuxiliary (singularAuxiliary Q))=0:=by
 obtain haux | hregular:=solution_regular_or_auxiliary Q hQ P γ hsolution
 · have hJ:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
   obtain hexceptional | himplicit:=solution_implicit_pair_or_exceptional
     (singularAuxiliary Q) hJ.1 P γ ((2*s-1)*D) w ((2*s-1)*L)
     hw hDw hJ.2 haux
   · exact Or.inr (Or.inr hexceptional)
   · exact Or.inr (Or.inl himplicit)
 · exact Or.inl hregular
theorem selected_seed_decomposition
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (seeds:Finset K) (selected:K → Polynomial K)
   (hsolutions:∀ γ∈seeds,specialization K (selected γ) γ Q=0):
   (exceptionalSeeds (singularAuxiliary Q) seeds selected).card ≤
       2*((2*s-1)*L)^2∧
     (∀ γ∈seeds,γ∉exceptionalSeeds (singularAuxiliary Q) seeds selected →
       (∃ F∈positiveRFactors Q,RegularSolution F (selected γ) γ)∨
         (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q (selected γ) γ))∧
     ((∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
       (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
       (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L)∧
     ((∑ q∈implicitPairSet (singularAuxiliary Q),pairYCost q) ≤ (2*s-1)*L∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairRCost q) ≤
         2*(((2*s-1)*D-1)/w)*((2*s-1)*L)∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairZCost q) ≤
         ((2*s-1)*D-1)/w):=by
 classical
 have hwpos:0 < w:=by omega
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=Nat.eq_zero_of_le_zero
   (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ (2*s-1)*L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:=degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 refine ⟨exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR ((2*s-1)*L)
     p hj hjSmall hJY hJZ seeds selected,?_,
   directFactor_input_budgets Q hQ D w L s hwpos hbox,
   implicitPair_input_budgets (singularAuxiliary Q) hJ ((2*s-1)*D) w
     ((2*s-1)*L) hwpos hJbox⟩
 intro γ hγ hnot
 obtain hregular | himplicit | hexceptional:=solution_three_way
   Q hQ D w L s p hs hsmall hw hDw hbox (selected γ) γ (hsolutions γ hγ)
 · exact Or.inl hregular
 · exact Or.inr himplicit
 · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hγ,hexceptional⟩))
end
end ProximityPrize.SubmissionLower.RCN286
end PackedLegacy_V

/-! Packed from ProximityPrize.SubmissionLower.FS. -/
section PackedLegacy_FS
namespace ProximityPrize.SubmissionLower.RCN242
open RCN051
def surfaceVector:DegreeVector:=⟨yCap,slopeCap,seedTotalCap⟩
theorem first_cut_projection_values:
   mixed surfaceVector firstTail unitY=438304768∧
   mixed surfaceVector firstTail unitR=2283798704∧
   mixed surfaceVector firstTail unitZ=61603845:=by
 norm_num [mixed,surfaceVector,firstTail,tailVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem agreement_cut_projection_values:
   mixed surfaceVector agreementVector unitY=438301429∧
   mixed surfaceVector agreementVector unitR=2283781305∧
   mixed surfaceVector agreementVector unitZ=61603375:=by
 norm_num [mixed,surfaceVector,agreementVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem non_R_projection_caps_below_characteristic:
   mixed surfaceVector firstTail unitY < prime∧
   mixed surfaceVector firstTail unitZ < prime∧
   mixed surfaceVector agreementVector unitY < prime∧
   mixed surfaceVector agreementVector unitZ < prime:=by
 rcases first_cut_projection_values with ⟨h1,h2,h3⟩
 rcases agreement_cut_projection_values with ⟨h4,h5,h6⟩
 rw [h1,h3,h4,h6]
 norm_num [prime]
end ProximityPrize.SubmissionLower.RCN242
end PackedLegacy_FS

/-! Packed from ProximityPrize.SubmissionLower.BT. -/
section PackedLegacy_BT
namespace ProximityPrize.SubmissionLower.RCN168
open RCN051
def implicitWeightedCap:ℕ:=(2*slopeCap-1)*weightedCap
def implicitYCap:ℕ:=(implicitWeightedCap-1)/w
def liftedSurface:DegreeVector:=⟨implicitYCap,1,algebraicCap⟩
def implicitCut:DegreeVector:=⟨implicitYCap,0,algebraicCap⟩
def liftedLastTail:DegreeVector:=
 ⟨1+2*implicitWeightedCap*implicitYCap,
   implicitWeightedCap,2*implicitWeightedCap*algebraicCap⟩
def liftedAgreement:DegreeVector:=
 ⟨1+2*w*implicitYCap,w,2*w*algebraicCap+1⟩
def liftedSingularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
   mixed liftedSurface implicitCut liftedLastTail+
   (errors+1)*mixed liftedSurface implicitCut unitZ)+
 (n-w)*mixed liftedSurface implicitCut liftedAgreement
def liftedTotalNumerator:ℕ:=regularNumerator+gap*liftedSingularNumerator
theorem lifted_parameter_values:
   implicitWeightedCap=29924640∧implicitYCap=228∧
   liftedLastTail=⟨13645635841,29924640,94801259520⟩∧
   liftedAgreement=⟨59768377,131071,415232929⟩:=by
 norm_num [implicitWeightedCap,implicitYCap,liftedLastTail,liftedAgreement,
   algebraicCap,weightedCap,RCN051.multiplicity,agreements,
   w,slopeCap,seedTotalCap]
theorem lifted_projection_values:
   mixed liftedSurface implicitCut unitY=1584∧
   mixed liftedSurface implicitCut unitR=722304∧
   mixed liftedSurface implicitCut unitZ=228:=by
 norm_num [mixed,liftedSurface,implicitCut,implicitYCap,implicitWeightedCap,
   unitY,unitR,unitZ,algebraicCap,weightedCap,
   RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem lifted_projection_characteristic_gates:
   implicitWeightedCap < prime∧
   mixed liftedSurface implicitCut unitY < prime∧
   mixed liftedSurface implicitCut unitR < prime∧
   mixed liftedSurface implicitCut unitZ < prime:=by
 rcases lifted_projection_values with ⟨hY,hR,hZ⟩
 rw [hY,hR,hZ,lifted_parameter_values.1]
 norm_num [prime]
theorem lifted_singular_numerator_exact:
   liftedSingularNumerator=3516047537415780312:=by
 norm_num [liftedSingularNumerator,mixed,liftedSurface,implicitCut,liftedLastTail,
   liftedAgreement,implicitYCap,implicitWeightedCap,unitZ,algebraicCap,
   weightedCap,RCN051.multiplicity,agreements,w,gap,
   errors,n,slopeCap,seedTotalCap]
theorem lifted_total_numerator_exact:
   liftedTotalNumerator=143697127886496891242366373:=by
 rw [liftedTotalNumerator,lifted_singular_numerator_exact]
 norm_num [regularNumerator,cutNumerator,wholeNumerator,mixed,
   firstTail,lastTail,tailVector,agreementVector,unitY,unitR,unitZ,
   yCap,weightedCap,RCN051.multiplicity,agreements,
   w,gap,errors,n,slopeCap,seedTotalCap]
theorem lifted_division_certificate:
   liftedTotalNumerator=49925776167317549*gap^2+2316504024∧
   2316504024 < gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num
theorem lifted_ceiling_exact:
   49925776167317549*gap^2 < liftedTotalNumerator∧
     liftedTotalNumerator ≤ 49925776167317550*gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num
theorem lifted_strict_budget:
   liftedTotalNumerator < alignmentBudget*gap^2:=by
 rw [lifted_total_numerator_exact,denominator_exact]
 norm_num [alignmentBudget]
end ProximityPrize.SubmissionLower.RCN168
end PackedLegacy_BT

/-! Packed from ProximityPrize.SubmissionLower.P4. -/
section PackedLegacy_P4
namespace ProximityPrize.SubmissionLower.RCN289
open RCN174 RCN081 RCN313
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem polyH_Y_degree_pred_of_mem_box
   (F:Poly4 K) (D w L s c:ℕ) (hw:0 < w)
   (hD:D ≤ w*c+(w-1))
   (hbox:F∈globalCoefficientBox K D w L s):
   (polyH K F).degreeOf (1:Fin 4) ≤ c-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=support_before_pderiv (2:Fin 4) F d hd
 have hc:=(hbox hs).2.2
 let e:Fin 4 →₀ ℕ:=d+Finsupp.single (2:Fin 4) 1
 have he:e=d+Finsupp.single (2:Fin 4) 1:=rfl
 change e∈F.support at hs
 change e 0+w*e 1+(w-1)*e 2 < D at hc
 have h0:e (0:Fin 4)=d 0:=by simp [he]
 have h1:e (1:Fin 4)=d 1:=by simp [he]
 have h2:e (2:Fin 4)=d 2+1:=by simp [he]
 rw [h0,h1,h2] at hc
 have hcontact:w*d 1+(w-1) < D:=by
   have hr:(w-1)*1 ≤ (w-1)*(d 2+1):=
     Nat.mul_le_mul_left (w-1) (by omega)
   calc
     w*d 1+(w-1) ≤
         d 0+w*d 1+(w-1)*(d 2+1):=by omega
     _ < D:=hc
 have hadd:w*d 1+(w-1) < w*c+(w-1):=
   hcontact.trans_le hD
 have hmul:w*d 1 < w*c:=Nat.add_lt_add_iff_right.mp hadd
 have hlt:d 1 < c:=(Nat.mul_lt_mul_left hw).mp hmul
 omega
theorem numeratorStep_Y_degree_bound
   (F M:Poly4 K) (b a c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (hM:M.degreeOf (1:Fin 4) ≤ a):
   (numeratorStep K F b M).degreeOf (1:Fin 4) ≤ a+(2*c-1):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 change H.degreeOf (1:Fin 4) ≤ c-1 at hH
 have hR:R.degreeOf (1:Fin 4) ≤ 0:=by
   simp [R,MvPolynomial.degreeOf_X_of_ne
     (by decide:(1:Fin 4)≠(2:Fin 4))]
 have hG:G.degreeOf (1:Fin 4) ≤ c:=by
   simpa only [Nat.add_zero] using
     polyG_degree_bound (1:Fin 4) F c 0 hF hR
 have hH2:=degree_pow_bound (1:Fin 4) 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) (1:Fin 4) M a hM
 have hMY:=pderiv_same_degree_bound (1:Fin 4) M a hM
 have hMR:=pderiv_degree_bound (2:Fin 4) (1:Fin 4) M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) (1:Fin 4) H (c-1) hH
 have hHY:=pderiv_same_degree_bound (1:Fin 4) H (c-1) hH
 have hHR:=pderiv_degree_bound (2:Fin 4) (1:Fin 4) H (c-1) hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4) hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hG hH) hMR
   omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4) hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4) hG hHR
   omega
 have hbrace:=degree_add_bound (1:Fin 4)
   (degree_add_bound (1:Fin 4) hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf (1:Fin 4) ≤ 0:=
   le_of_eq (degree_natCast_eq_zero (1:Fin 4) (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf (1:Fin 4) ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound (1:Fin 4) hn hM
 have h4:=degree_mul_bound (1:Fin 4) hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf (1:Fin 4) ≤
       a+(2*c-1)
 exact degree_sub_bound (1:Fin 4)
   (degree_add_bound (1:Fin 4) (degree_add_bound (1:Fin 4) h1 h2) h3) h4
theorem numerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (b:ℕ):
   (numerator K F b).degreeOf (1:Fin 4) ≤ 1+b*(2*c-1):=by
 induction b with
 | zero => simp [numerator_zero]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_Y_degree_bound F (numerator K F b) b
       (1+b*(2*c-1)) c hc hF hH ih
     simpa only [Nat.add_mul,Nat.one_mul,add_assoc] using hh
theorem commonNumeratorTerm_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w j:ℕ) (hj:j ≤ w) (coeffs:ℕ → K) (x:K):
   (commonNumeratorTerm F w coeffs x j).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 have hM:=numerator_Y_degree_bound F c hc hF hH j
 have hCM:(MvPolynomial.C (coeffs j)*numerator K F j).degreeOf (1:Fin 4) ≤
     1+j*(2*c-1):=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) (1:Fin 4) (coeffs j)).trans hM
 have hHP:=degree_pow_bound (1:Fin 4) (2*(w-j)) hH
 have hXP:MvPolynomial.degreeOf (1:Fin 4)
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   simpa only [Nat.mul_zero] using degree_pow_bound (1:Fin 4) j
     (shiftedX_degree_bound (1:Fin 4) (by decide) x)
 have hterm:=degree_mul_bound (1:Fin 4)
   (degree_mul_bound (1:Fin 4) hCM hHP) hXP
 have hwj:j+(w-j)=w:=by omega
 have hcap:(1+j*(2*c-1))+2*(w-j)*(c-1)+0 ≤
     1+w*(2*c-1):=by
   have hdelta:2*c-1=2*(c-1)+1:=by omega
   rw [hdelta]
   calc
     (1+j*(2*(c-1)+1))+2*(w-j)*(c-1)+0=
         1+2*(j+(w-j))*(c-1)+j:=by ring
     _=1+2*w*(c-1)+j:=by rw [hwj]
     _ ≤ 1+2*w*(c-1)+w:=Nat.add_le_add_left hj _
     _=1+w*(2*(c-1)+1):=by ring
 simpa only [commonNumeratorTerm] using hterm.trans hcap
theorem clearedTaylorNumerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w:ℕ) (coeffs:ℕ → K) (x:K):
   (clearedTaylorNumerator F w coeffs x).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound (1:Fin 4)
 intro j hj
 exact commonNumeratorTerm_Y_degree_bound F c hc hF hH w j
   (by have:=Finset.mem_range.mp hj;omega) coeffs x
theorem agreementNumerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   (agreementNumerator F w coeffs x u₀ u₁).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 unfold agreementNumerator
 apply degree_sub_bound (1:Fin 4)
 · exact clearedTaylorNumerator_Y_degree_bound F c hc hF hH w coeffs x
 · have ha:=affineSeedPolynomial_degree_bound (1:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 4)≠3)]) u₀ u₁
   have hp:=degree_pow_bound (1:Fin 4) (2*w) hH
   have hm:=degree_mul_bound (1:Fin 4) ha hp
   have hdelta:2*c-1=2*(c-1)+1:=by omega
   apply hm.trans
   rw [hdelta]
   calc
     0+2*w*(c-1) ≤ 1+2*w*(c-1)+w:=by omega
     _=1+w*(2*(c-1)+1):=by ring
theorem sharp_Y_bounds_of_mem_box
   (F:Poly4 K) (D w L s c:ℕ) (hw:0 < w) (hc:1 ≤ c)
   (hD:D ≤ w*c+(w-1))
   (hbox:F∈globalCoefficientBox K D w L s)
   (b t:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   (numerator K F b).degreeOf (1:Fin 4) ≤ 1+b*(2*c-1)∧
     (agreementNumerator F t coeffs x u₀ u₁).degreeOf (1:Fin 4) ≤
       1+t*(2*c-1):=by
 have hY:=degreeOf_Y_le_of_mem_box F D w L s hw hbox
 have hcapped:F.degreeOf (1:Fin 4) ≤ c:=by
   apply hY.trans
   apply Nat.le_of_lt_succ
   apply (Nat.div_lt_iff_lt_mul hw).mpr
   have hwsub:w-1 < w:=Nat.sub_lt hw (by norm_num)
   calc
     D-1 ≤ D:=Nat.sub_le D 1
     _ ≤ w*c+(w-1):=hD
     _ < w*c+w:=Nat.add_lt_add_left hwsub _
     _=(c+1)*w:=by ring
 have hH:=polyH_Y_degree_pred_of_mem_box F D w L s c hw hD hbox
 exact ⟨numerator_Y_degree_bound F c hc hcapped hH b,
   agreementNumerator_Y_degree_bound F c hc hcapped hH t coeffs x u₀ u₁⟩
end
end ProximityPrize.SubmissionLower.RCN289
end PackedLegacy_P4

/-! Packed from ProximityPrize.SubmissionLower.Y4. -/
section PackedLegacy_Y4
namespace ProximityPrize.SubmissionLower.RCN068
open scoped Classical
open RCN051 RCN313 RCN136 RCN174 RCN231 RCN238 RCN289
noncomputable section
def capAt (v:DegreeVector):Fin 3 → ℕ:=![v.y,v.r,v.z]
def numeratorCaps (ell s L b:ℕ):DegreeVector:=
 ⟨1+2*b*ell,b*(2*s-1),2*b*L⟩
def agreementCaps (ell s L w:ℕ):DegreeVector:=
 ⟨1+2*w*ell,w*(2*s-1),2*w*L+1⟩
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def HasCaps (Q:MvPolynomial (Fin 3) Ω) (v:DegreeVector):Prop:=
 ∀ i,Q.degreeOf i ≤ capAt v i
variable (φ:Polynomial K →+*Ω)
def firstTailSurface (F:MvPolynomial (Fin 4) K) (w:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (numerator K F (w+1))
theorem surface_numerator_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (b:ℕ):HasCaps (surfaceMap φ (numerator K F b)) (numeratorCaps ell s L b):=by
 obtain ⟨hy,hr,hz⟩:=numerator_degree_bounds F ell s L hs hY hR hZ b
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem surface_agreement_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   HasCaps (surfaceMap φ (agreementNumerator F w c x u₀ u₁))
     (agreementCaps ell s L w):=by
 obtain ⟨hy,hr,hz⟩:=agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem fixed_firstTail_caps (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap):
   HasCaps (firstTailSurface φ F w) firstTail:=by
 have hold:=surface_numerator_caps φ F yCap slopeCap seedTotalCap (by decide)
   hY hR hZ (w+1)
 have hsharp:=sharp_Y_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap yCap
   (by norm_num [w]) (by norm_num [yCap,weightedCap,RCN051.multiplicity,
     agreements,w])
   (by norm_num [weightedCap,RCN051.multiplicity,agreements,
     w,yCap]) hbox (w+1) 0 (fun _ => 0) 0 0 0
 intro i
 fin_cases i
 · have hy:=(surfaceMap_degreeOf_le φ _ 0).trans hsharp.1
   simpa [firstTailSurface,firstTail,tailVector,capAt] using hy
 · simpa [firstTailSurface,firstTail,tailVector,numeratorCaps,capAt] using hold 1
 · simpa [firstTailSurface,firstTail,tailVector,numeratorCaps,capAt] using hold 2
theorem fixed_agreement_caps (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap) (x u₀ u₁:K):
   HasCaps (agreementPolynomial φ F w x u₀ u₁) agreementVector:=by
 have hold:=surface_agreement_caps φ F yCap slopeCap seedTotalCap (by decide)
   hY hR hZ w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 have hsharp:=sharp_Y_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap yCap
   (by norm_num [w]) (by norm_num [yCap,weightedCap,RCN051.multiplicity,
     agreements,w])
   (by norm_num [weightedCap,RCN051.multiplicity,agreements,
     w,yCap]) hbox 0 w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 intro i
 fin_cases i
 · have hy:=(surfaceMap_degreeOf_le φ _ 0).trans hsharp.2
   simpa [agreementPolynomial,agreementVector,capAt] using hy
 · simpa [agreementPolynomial,agreementVector,agreementCaps,capAt] using hold 1
 · simpa [agreementPolynomial,agreementVector,agreementCaps,capAt] using hold 2
theorem selected_firstTail_zero
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (firstTailSurface φ F w)=0:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (numerator K F (w+1)))=0
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
   (φ Polynomial.X) hsolution (w+1) (Nat.lt_succ_of_le hdegree)
theorem fixed_implicit_agreement_caps (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ RCN168.implicitYCap)
   (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
   (x u₀ u₁:K):
   HasCaps (agreementPolynomial φ F w x u₀ u₁)
     RCN168.liftedAgreement:=by
 have h:=surface_agreement_caps φ F RCN168.implicitYCap 1
   algebraicCap (by decide) hY hR hZ w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 simpa [agreementPolynomial,agreementCaps,RCN168.liftedAgreement] using h
section MixedGates
variable (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
theorem actual_pair_degree_le (hG:HasCaps G g) (hT:HasCaps T t) (j k:Fin 3):
   T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k ≤
     capAt t j*capAt g k+capAt g j*capAt t k:=
 Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))
theorem pair_caps_below_of_mixed (p:ℕ)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   ∀ j k:Fin 3,j≠k →
     capAt t j*capAt g k+capAt g j*capAt t k < p:=by
 intro j k hne
 fin_cases j <;> fin_cases k
 all_goals try exact (hne rfl).elim
 all_goals first
   | simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
   | simpa [capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using hR
   | simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem actual_characteristic_gates (p:ℕ)
   (hG:HasCaps G g) (hT:HasCaps T t)
   (hg:∀ j,capAt g j < p)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   (∀ j,G.degreeOf j < p)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p:=by
 refine ⟨fun j↦(hG j).trans_lt (hg j),?_⟩
 intro j k hjk
 exact (actual_pair_degree_le G T g t hG hT j k).trans_lt
   (pair_caps_below_of_mixed g t p hY hR hZ j k hjk)
end MixedGates
theorem fixed_surface_caps_below_characteristic:
   ∀ j,capAt RCN242.surfaceVector j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,RCN242.surfaceVector,yCap,weightedCap,
     RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap,prime]
theorem fixed_firstTail_nonR_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN242.surfaceVector) (hT:HasCaps T firstTail):
   (∀ j,G.degreeOf j < prime)∧
     T.degreeOf 1*G.degreeOf 2+G.degreeOf 1*T.degreeOf 2 < prime∧
     T.degreeOf 0*G.degreeOf 1+G.degreeOf 0*T.degreeOf 1 < prime:=by
 rcases RCN242.non_R_projection_caps_below_characteristic with
   ⟨hY,hZ,_,_⟩
 refine ⟨fun j => (hG j).trans_lt (fixed_surface_caps_below_characteristic j),
   (actual_pair_degree_le G T _ _ hG hT 1 2).trans_lt ?_,
   (actual_pair_degree_le G T _ _ hG hT 0 1).trans_lt ?_⟩
 · simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
 · simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem fixed_agreement_nonR_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN242.surfaceVector) (hT:HasCaps T agreementVector):
   (∀ j,G.degreeOf j < prime)∧
     T.degreeOf 1*G.degreeOf 2+G.degreeOf 1*T.degreeOf 2 < prime∧
     T.degreeOf 0*G.degreeOf 1+G.degreeOf 0*T.degreeOf 1 < prime:=by
 rcases RCN242.non_R_projection_caps_below_characteristic with
   ⟨_,_,hY,hZ⟩
 refine ⟨fun j => (hG j).trans_lt (fixed_surface_caps_below_characteristic j),
   (actual_pair_degree_le G T _ _ hG hT 1 2).trans_lt ?_,
   (actual_pair_degree_le G T _ _ hG hT 0 1).trans_lt ?_⟩
 · simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
 · simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem fixed_implicit_surface_caps_below_characteristic:
   ∀ j,capAt RCN168.liftedSurface j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,RCN168.liftedSurface,
     RCN168.implicitYCap,RCN168.implicitWeightedCap,
     algebraicCap,weightedCap,RCN051.multiplicity,agreements,
     w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN168.liftedSurface)
   (hT:HasCaps T RCN168.implicitCut):
   (∀ j,G.degreeOf j < prime)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
 rcases RCN168.lifted_projection_characteristic_gates with
   ⟨_,hY,hR,hZ⟩
 exact actual_characteristic_gates G T _ _ prime hG hT
   fixed_implicit_surface_caps_below_characteristic hY hR hZ
end
end ProximityPrize.SubmissionLower.RCN068
end PackedLegacy_Y4

/-! Packed from ProximityPrize.SubmissionLower.B2. -/
section PackedLegacy_B2
namespace ProximityPrize.SubmissionLower.RCN070
open RCN051 RCN168
open scoped BigOperators
def addVector (a b:DegreeVector):DegreeVector:=
 ⟨a.y+b.y,a.r+b.r,a.z+b.z⟩
def scaleVector (c:ℕ) (v:DegreeVector):DegreeVector:=
 ⟨c*v.y,c*v.r,c*v.z⟩
def sumVector {I:Type} [Fintype I] (v:I → DegreeVector):DegreeVector:=
 ⟨∑ i,(v i).y,∑ i,(v i).r,∑ i,(v i).z⟩
def vectorLE (a b:DegreeVector):Prop:=a.y ≤ b.y∧a.r ≤ b.r∧a.z ≤ b.z
def dot (a b:DegreeVector):ℕ:=a.y*b.y+a.r*b.r+a.z*b.z
theorem dot_comm (a b:DegreeVector):dot a b=dot b a:=by
 simp only [dot]
 ring
theorem dot_mono_left {a b:DegreeVector} (c:DegreeVector) (h:vectorLE a b):
   dot a c ≤ dot b c:=
 Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1) (Nat.mul_le_mul_right c.r h.2.1))
   (Nat.mul_le_mul_right c.z h.2.2)
theorem dot_mono_right (a:DegreeVector) {b c:DegreeVector} (h:vectorLE b c):
   dot a b ≤ dot a c:=by
 rw [dot_comm a b,dot_comm a c]
 exact dot_mono_left a h
theorem dot_sum_left {I:Type} [Fintype I] (v:I → DegreeVector) (a:DegreeVector):
   dot (sumVector v) a=∑ i,dot (v i) a:=by
 simp only [dot,sumVector,Finset.sum_add_distrib,Finset.sum_mul]
theorem dot_sum_right {I:Type} [Fintype I] (v:I → DegreeVector) (a:DegreeVector):
   dot a (sumVector v)=∑ i,dot a (v i):=by
 rw [dot_comm,dot_sum_left]
 apply Finset.sum_congr rfl
 intro i _
 exact dot_comm (v i) a
theorem mixed_first_decomposition (v a b:DegreeVector):
   mixed v a b=v.y*mixed unitY a b+v.r*mixed unitR a b+v.z*mixed unitZ a b:=by
 simp only [mixed,unitY,unitR,unitZ]
 ring
theorem mixed_add_left (u v a b:DegreeVector):
   mixed (addVector u v) a b=mixed u a b+mixed v a b:=by
 simp only [mixed,addVector]
 ring
theorem mixed_scale_left (c:ℕ) (v a b:DegreeVector):
   mixed (scaleVector c v) a b=c*mixed v a b:=by
 simp only [mixed,scaleVector]
 ring
theorem mixed_sum_left {I:Type} [Fintype I] (v:I → DegreeVector) (a b:DegreeVector):
   mixed (sumVector v) a b=∑ i,mixed (v i) a b:=by
 calc
   _=dot (sumVector v) ⟨mixed unitY a b,mixed unitR a b,mixed unitZ a b⟩:=
     mixed_first_decomposition _ _ _
   _=∑ i,dot (v i) ⟨mixed unitY a b,mixed unitR a b,mixed unitZ a b⟩:=dot_sum_left _ _
   _=_:=by
     apply Finset.sum_congr rfl
     intro i _
     exact (mixed_first_decomposition (v i) a b).symm
def cutCoefficients:DegreeVector:=
 ⟨cutNumerator unitY,cutNumerator unitR,cutNumerator unitZ⟩
def wholeCoefficients:DegreeVector:=
 ⟨wholeNumerator unitY,wholeNumerator unitR,wholeNumerator unitZ⟩
def envelopeCoefficients:DegreeVector:=
 ⟨max (cutNumerator unitY) (wholeNumerator unitY),
   max (cutNumerator unitR) (wholeNumerator unitR),
   max (cutNumerator unitZ) (wholeNumerator unitZ)⟩
def regularSurface:DegreeVector:=⟨yCap,slopeCap,seedTotalCap⟩
theorem cut_eq_dot (v:DegreeVector):cutNumerator v=dot v cutCoefficients:=by
 simp only [cutNumerator,cutCoefficients,dot,mixed,unitY,unitR,unitZ]
 ring
theorem whole_eq_dot (v:DegreeVector):wholeNumerator v=dot v wholeCoefficients:=by
 simp only [wholeNumerator,wholeCoefficients,dot,mixed,unitY,unitR,unitZ]
 ring
theorem cut_add (u v:DegreeVector):
   cutNumerator (addVector u v)=cutNumerator u+cutNumerator v:=by
 rw [cut_eq_dot,cut_eq_dot,cut_eq_dot]
 simp only [dot,addVector]
 ring
theorem whole_add (u v:DegreeVector):
   wholeNumerator (addVector u v)=wholeNumerator u+wholeNumerator v:=by
 rw [whole_eq_dot,whole_eq_dot,whole_eq_dot]
 simp only [dot,addVector]
 ring
theorem cut_scale (c:ℕ) (v:DegreeVector):
   cutNumerator (scaleVector c v)=c*cutNumerator v:=by
 rw [cut_eq_dot,cut_eq_dot]
 simp only [dot,scaleVector]
 ring
theorem whole_scale (c:ℕ) (v:DegreeVector):
   wholeNumerator (scaleVector c v)=c*wholeNumerator v:=by
 rw [whole_eq_dot,whole_eq_dot]
 simp only [dot,scaleVector]
 ring
theorem cut_sum {I:Type} [Fintype I] (v:I → DegreeVector):
   cutNumerator (sumVector v)=∑ i,cutNumerator (v i):=by
 rw [cut_eq_dot,dot_sum_left]
 apply Finset.sum_congr rfl
 intro i _
 exact (cut_eq_dot (v i)).symm
theorem whole_sum {I:Type} [Fintype I] (v:I → DegreeVector):
   wholeNumerator (sumVector v)=∑ i,wholeNumerator (v i):=by
 rw [whole_eq_dot,dot_sum_left]
 apply Finset.sum_congr rfl
 intro i _
 exact (whole_eq_dot (v i)).symm
theorem cut_le_envelope (v:DegreeVector):cutNumerator v ≤ dot v envelopeCoefficients:=by
 rw [cut_eq_dot]
 exact dot_mono_right v ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _⟩
theorem whole_le_envelope (v:DegreeVector):wholeNumerator v ≤ dot v envelopeCoefficients:=by
 rw [whole_eq_dot]
 exact dot_mono_right v ⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩
theorem max_branch_le_envelope (v:DegreeVector):
   max (cutNumerator v) (wholeNumerator v) ≤ dot v envelopeCoefficients:=
 max_le (cut_le_envelope v) (whole_le_envelope v)
theorem regularNumerator_eq_dot:regularNumerator=dot regularSurface wholeCoefficients:=rfl
theorem sum_regular_max_bound {I:Type} [Fintype I]
   (count:I → ℕ) (v:I → DegreeVector)
   (hy:(∑ i,(v i).y) ≤ yCap) (hr:(∑ i,(v i).r) ≤ slopeCap)
   (hz:(∑ i,(v i).z) ≤ seedTotalCap)
   (hcount:∀ i,count i*gap^2 ≤ wholeNumerator (v i)):
   (∑ i,count i)*gap^2 ≤ regularNumerator:=by
 calc
   _=∑ i,count i*gap^2:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (v i) wholeCoefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←whole_eq_dot]
     exact hcount i
   _=dot (sumVector v) wholeCoefficients:=(dot_sum_left _ _).symm
   _ ≤ dot regularSurface wholeCoefficients:=dot_mono_left _ ⟨hy,hr,hz⟩
   _=regularNumerator:=rfl
theorem sum_regular_branch_bound {I:Type} [Fintype I]
   (count:I → ℕ) (v:I → DegreeVector)
   (hy:(∑ i,(v i).y) ≤ yCap) (hr:(∑ i,(v i).r) ≤ slopeCap)
   (hz:(∑ i,(v i).z) ≤ seedTotalCap)
   (hcount:∀ i,count i*gap^2 ≤ wholeNumerator (v i)):
   (∑ i,count i)*gap^2 ≤ regularNumerator:=by
 apply sum_regular_max_bound count v hy hr hz
 exact hcount
theorem sum_regular_numeric_caps {I:Type} [Fintype I]
   (count:I → ℕ) (v:I → DegreeVector)
   (hy:(∑ i,(v i).y) ≤ 25) (hr:(∑ i,(v i).r) ≤ 5)
   (hz:(∑ i,(v i).z) ≤ 176)
   (hcount:∀ i,count i*gap^2 ≤ wholeNumerator (v i)):
   (∑ i,count i)*gap^2 ≤ regularNumerator:=by
 exact sum_regular_branch_bound count v
   (by simpa only [parameter_values.2.1] using hy)
   (by simpa only [slopeCap] using hr)
   (by simpa only [seedTotalCap] using hz) hcount
def implicitAggregateCost:DegreeVector:=
 ⟨algebraicCap,2*implicitYCap*algebraicCap,implicitYCap⟩
def implicitCoefficients:DegreeVector:=
 ⟨(n-w)*liftedAgreement.y,(n-w)*liftedAgreement.r,
   (n-w)*liftedAgreement.z+(errors+1)*gap⟩
def implicitCoreNumerator:ℕ:=
 (n-w)*mixed liftedSurface implicitCut liftedAgreement+
   (errors+1)*gap*mixed liftedSurface implicitCut unitZ
theorem implicit_bound_eq_dot (v:DegreeVector):
   (n-w)*dot liftedAgreement v+(errors+1)*gap*v.z=
     dot v implicitCoefficients:=by
 simp only [implicitCoefficients,dot]
 ring
theorem implicit_aggregate_eq_core:
   dot implicitAggregateCost implicitCoefficients=implicitCoreNumerator:=by
 simp only [implicitAggregateCost,implicitCoefficients,implicitCoreNumerator,
   dot,mixed,liftedSurface,implicitCut,unitZ]
 ring
theorem sum_implicit_counts_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z):
   (∑ i,count i)*gap ≤ implicitCoreNumerator:=by
 calc
   _=∑ i,count i*gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) implicitCoefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←implicit_bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) implicitCoefficients:=(dot_sum_left _ _).symm
   _ ≤ dot implicitAggregateCost implicitCoefficients:=dot_mono_left _ ⟨hy,hr,hz⟩
   _=implicitCoreNumerator:=implicit_aggregate_eq_core
theorem lifted_singular_padding:
   liftedSingularNumerator=
     (implicitCoreNumerator+2*algebraicCap^2*gap)+
       gap*(algebraicCap+mixed liftedSurface implicitCut liftedLastTail):=by
 simp only [liftedSingularNumerator,implicitCoreNumerator]
 ring
theorem implicit_with_exceptions_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap ≤ liftedSingularNumerator:=by
 have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
   _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
   _ ≤ liftedSingularNumerator:=by
     rw [lifted_singular_padding]
     exact Nat.le_add_right _ _
theorem combined_scaled_bound (regularCount implicitCount exceptions:ℕ)
   (hregular:regularCount*gap^2 ≤ regularNumerator)
   (himplicit:(implicitCount+exceptions)*gap ≤ liftedSingularNumerator):
   (regularCount+implicitCount+exceptions)*gap^2 ≤ liftedTotalNumerator:=by
 calc
   _=regularCount*gap^2+((implicitCount+exceptions)*gap)*gap:=by ring
   _ ≤ regularNumerator+liftedSingularNumerator*gap:=
     Nat.add_le_add hregular (Nat.mul_le_mul_right gap himplicit)
   _=liftedTotalNumerator:=by
     simp only [liftedTotalNumerator]
     ring
theorem below_budget_of_lifted_scaled_bound (cardinality:ℕ)
   (h:cardinality*gap^2 ≤ liftedTotalNumerator):cardinality < alignmentBudget:=by
 exact Nat.lt_of_mul_lt_mul_right (h.trans_lt lifted_strict_budget)
theorem final_family_ledger {I J:Type} [Fintype I] [Fintype J]
   (regularCount:I → ℕ) (v:I → DegreeVector)
   (implicitCount:J → ℕ) (cost:J → DegreeVector) (exceptions cardinality:ℕ)
   (hregularY:(∑ i,(v i).y) ≤ 25) (hregularR:(∑ i,(v i).r) ≤ 5)
   (hregularZ:(∑ i,(v i).z) ≤ 176)
   (hregular:∀ i,regularCount i*gap^2 ≤ wholeNumerator (v i))
   (hcostY:(∑ i,(cost i).y) ≤ algebraicCap)
   (hcostR:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hcostZ:(∑ i,(cost i).z) ≤ implicitYCap)
   (himplicit:∀ i,implicitCount i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2)
   (hcover:cardinality ≤ (∑ i,regularCount i)+(∑ i,implicitCount i)+exceptions):
   cardinality < alignmentBudget:=by
 have hreg:=sum_regular_numeric_caps regularCount v hregularY hregularR hregularZ hregular
 have himp:=implicit_with_exceptions_bound implicitCount cost exceptions
   hcostY hcostR hcostZ himplicit hexceptions
 have hscaled:=combined_scaled_bound (∑ i,regularCount i) (∑ i,implicitCount i)
   exceptions hreg himp
 exact below_budget_of_lifted_scaled_bound cardinality
   ((Nat.mul_le_mul_right (gap^2) hcover).trans hscaled)
end ProximityPrize.SubmissionLower.RCN070
end PackedLegacy_B2

/-! Packed from ProximityPrize.SubmissionLower.BV. -/
section PackedLegacy_BV
namespace ProximityPrize.SubmissionLower.RCN170
open scoped Classical BigOperators
open RCN051 RCN168 RCN068 RCN070 RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def pairCost (A G:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨pairYCost ⟨A,G⟩,pairRCost ⟨A,G⟩,pairZCost ⟨A,G⟩⟩
def geometricPairCost (A:MvPolynomial (Fin 4) K)
   (g:MvPolynomial (Fin 3) Ω):DegreeVector:=
 ⟨g.degreeOf 1*A.degreeOf 3,
   g.degreeOf 0*A.degreeOf 3+g.degreeOf 2*A.degreeOf 1,
   g.degreeOf 1*A.degreeOf 1⟩
theorem capAt_dot (a b:DegreeVector):
   (∑ i:Fin 3,capAt a i*capAt b i)=dot a b:=by
 simp [Fin.sum_univ_three,capAt,dot]
theorem coordinateMixedDegree_le_geometricPairCost
   (φ:Polynomial K →+*Ω) (A:MvPolynomial (Fin 4) K)
   (hAR:A.degreeOf 2=0) (g:MvPolynomial (Fin 3) Ω) (i:Fin 3):
   coordinateMixedDegree Ω g (surfaceMap φ A) i ≤ capAt (geometricPairCost A g) i:=by
 have hTY:(surfaceMap φ A).degreeOf (0:Fin 3) ≤ A.degreeOf (1:Fin 4):=
   surfaceMap_degreeOf_le φ A (0:Fin 3)
 have hTRle:(surfaceMap φ A).degreeOf (1:Fin 3) ≤ A.degreeOf (2:Fin 4):=
   surfaceMap_degreeOf_le φ A (1:Fin 3)
 rw [hAR] at hTRle
 have hTR:(surfaceMap φ A).degreeOf (1:Fin 3)=0:=
   Nat.eq_zero_of_le_zero hTRle
 have hTZ:(surfaceMap φ A).degreeOf (2:Fin 3) ≤ A.degreeOf (3:Fin 4):=
   surfaceMap_degreeOf_le φ A (2:Fin 3)
 fin_cases i
 · simpa [coordinateMixedDegree_zero,hTR,capAt,geometricPairCost] using
     Nat.mul_le_mul_left (g.degreeOf 1) hTZ
 · have h:=Nat.add_le_add
     (Nat.mul_le_mul_right (g.degreeOf 2) hTY)
     (Nat.mul_le_mul_left (g.degreeOf 0) hTZ)
   simpa [coordinateMixedDegree_one,capAt,geometricPairCost,
     Nat.mul_comm,Nat.add_comm] using h
 · simpa [coordinateMixedDegree_two,hTR,capAt,geometricPairCost,Nat.mul_comm] using
     Nat.mul_le_mul_right (g.degreeOf 1) hTY
theorem sum_geometricPairCost_le
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (A G:MvPolynomial (Fin 4) K) (hG:G≠0) (i:Fin 3):
   (∑ g∈surfaceFactors φ G,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=by
 have hY:=surfaceFactors_degree_budget φ hφ G hG (0:Fin 3)
 have hR:=surfaceFactors_degree_budget φ hφ G hG (1:Fin 3)
 have hZ:=surfaceFactors_degree_budget φ hφ G hG (2:Fin 3)
 fin_cases i
 · simpa [capAt,geometricPairCost,pairCost,pairYCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 3) hR
 · simpa [capAt,geometricPairCost,pairCost,pairRCost,
     Finset.sum_add_distrib, ←Finset.sum_mul] using
     Nat.add_le_add (Nat.mul_le_mul_right (A.degreeOf 3) hY)
       (Nat.mul_le_mul_right (A.degreeOf 1) hZ)
 · simpa [capAt,geometricPairCost,pairCost,pairZCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 1) hR
theorem canonical_selectedPoint_surface_evaluation
   (selected:K → Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_evaluation]
 exact evaluation_at_initialPoint K (selected γ) γ F
theorem geometric_factor_proper_cut
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) G):
   ¬ g∣surfaceMap (polynomialEmbedding K) A:=by
 obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec (polynomialEmbedding K) G g hg
 have hpos:0 < G.degreeOf 1+G.degreeOf 2+G.degreeOf 3:=by omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) G:=by
   simpa only [canonical_geometricSurfaceMap] using hdiv
 intro h
 apply hproper
 apply (geometric_factor_dvd_iff K (GenericField K) G A hG hpos g hgi hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using h
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound_fixed
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (hAbox:A∈globalCoefficientBox K implicitWeightedCap w algebraicCap 0)
   (hGbox:G∈globalCoefficientBox K implicitWeightedCap w algebraicCap 1)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
     (errors+1)*gap*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitWeightedCap w algebraicCap 0
   (by norm_num [w]) hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitWeightedCap w algebraicCap 1
   (by norm_num [w]) hGbox
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) implicitCut:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [canonical_selectedPoint_surface_evaluation,hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [canonical_selectedPoint_surface_evaluation,hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ (polynomialEmbedding_injective K)
     G hG.ne_zero (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*gap ≤
       (n-w)*(∑ i:Fin 3,
         capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
         (errors+1)*gap*capAt (geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g liftedSurface:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGGcaps.1
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
   have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (RCN231.polynomialPoint (φ.comp Polynomial.C)
         (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
       liftedAgreement:=
     fixed_implicit_agreement_caps φ G hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (geometric_factor_proper_cut A G hG hGR hproper g hg) selected (seedsFor g)
     nodes x u₀ u₁ hinj prime w agreements errors
     (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,agreements])
     (by rw [hnodes];norm_num [agreements,n]) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
     (capAt liftedAgreement) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=coordinateMixedDegree_le_geometricPairCost φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hδ i))))
     (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=
   sum_geometricPairCost_le φ (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt liftedAgreement i*capAt (geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt liftedAgreement i*
         (∑ g∈factors,capAt (geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=Nat.mul_le_mul_right gap hcard
   _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
         (errors+1)*gap*capAt (geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt liftedAgreement i*
       (∑ g∈factors,capAt (geometricPairCost A g) i))+
         (errors+1)*gap*(∑ g∈factors,capAt (geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*
       (∑ i:Fin 3,capAt liftedAgreement i*capAt (pairCost A G) i)+
       (errors+1)*gap*capAt (pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hbudget i))))
       (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
   _=(n-w)*dot liftedAgreement (pairCost A G)+
       (errors+1)*gap*pairZCost ⟨A,G⟩:=by
     rw [capAt_dot]
     rfl
end
end ProximityPrize.SubmissionLower.RCN170
end PackedLegacy_BV

/-! Packed from ProximityPrize.SubmissionLower.BW. -/
section PackedLegacy_BW
namespace ProximityPrize.SubmissionLower.RCN172
open scoped Classical BigOperators
open RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001 RCN068
noncomputable section
variable {K:Type} [Field K]
 {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (implicitD w jY jZ p n a e:ℕ)
   (hAbox:A∈globalCoefficientBox K implicitD w jZ 0)
   (hGbox:G∈globalCoefficientBox K implicitD w jZ 1)
   (hjY:(implicitD-1)/w=jY)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K p]
   (hw:1 ≤ w) (hchar:w < p) (hwa:w < a) (han:a ≤ n)
   (hjYsmall:jY < p) (hjZsmall:jZ < p)
   (hmixedSmall:2*jY*jZ < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):
   Γ.card*(a-w) ≤
     (n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 let surfaceCap:RCN051.DegreeVector:=⟨jY,1,jZ⟩
 let cutCap:RCN051.DegreeVector:=⟨jY,0,jZ⟩
 let agreementCap:RCN051.DegreeVector:=
   ⟨1+2*w*jY,w,2*w*jZ+1⟩
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
 have hAY:A.degreeOf 1 ≤ jY:=hAGcaps.1.trans_eq hjY
 have hGY:G.degreeOf 1 ≤ jY:=hGGcaps.1.trans_eq hjY
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) cutCap:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ
     (polynomialEmbedding_injective K) G hG.ne_zero
     (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*(a-w) ≤
       (n-w)*(∑ i:Fin 3,
         capAt agreementCap i*
           capAt (RCN170.geometricPairCost A g) i)+
         (e+1)*(a-w)*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g surfaceCap:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGY
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hsurfaceSmall:∀ j,capAt surfaceCap j < p:=by
     intro j
     fin_cases j
     · simpa [surfaceCap,capAt] using hjYsmall
     · simpa [surfaceCap,capAt] using lt_of_le_of_lt hw hchar
     · simpa [surfaceCap,capAt] using hjZsmall
   have hgates:=actual_characteristic_gates g (surfaceMap φ A)
     surfaceCap cutCap p hgcaps hAcaps hsurfaceSmall
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitY] using hjZsmall)
     (by
       simp [RCN051.mixed,surfaceCap,cutCap,
         RCN051.unitR]
       rw [show jY*jZ+jZ*jY=2*jY*jZ by ring]
       exact hmixedSmall)
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitZ] using hjYsmall)
   have hreg:∀ γ∈seedsFor g,
       MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
         (RCN231.polynomialPoint (φ.comp Polynomial.C)
           (selected γ) γ (φ Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr
       (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps
       (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap:=by
     have h:=surface_agreement_caps φ G jY 1 jZ (by decide)
       hGY hGGcaps.2.1 hGGcaps.2.2 w
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     simpa [agreementPolynomial,agreementCaps,agreementCap] using h
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut
       A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
     (by simpa [hnodes] using han) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w e (hsub g) hnoPencil)
     (capAt agreementCap) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost
       φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hδ i))))
     (Nat.mul_le_mul_left ((e+1)*(a-w)) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt agreementCap i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*(a-w) ≤ (∑ g∈factors,(seedsFor g).card)*(a-w):=
     Nat.mul_le_mul_right (a-w) hcard
   _=∑ g∈factors,(seedsFor g).card*(a-w):=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)+
       (e+1)*(a-w)*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt agreementCap i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (e+1)*(a-w)*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt agreementCap i*
       capAt (RCN170.pairCost A G) i)+
       (e+1)*(a-w)*
         capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hbudget i))))
       (Nat.mul_le_mul_left ((e+1)*(a-w)) (hbudget 2))
   _=(n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,capAt,agreementCap,
       RCN170.pairCost]
end
end ProximityPrize.SubmissionLower.RCN172
end PackedLegacy_BW

/-! Packed from ProximityPrize.SubmissionLower.CD. -/
section PackedLegacy_CD
namespace ProximityPrize.SubmissionLower.RCN306
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def unitAt:Fin 3 → DegreeVector:=![unitY,unitR,unitZ]
def degreeVector (G:MvPolynomial (Fin 3) Ω):DegreeVector:=
 ⟨G.degreeOf 0,G.degreeOf 1,G.degreeOf 2⟩
theorem degreeVector_hasCaps (G:MvPolynomial (Fin 3) Ω):
   HasCaps G (degreeVector G):=by
 intro i
 fin_cases i <;> exact le_rfl
theorem coordinateMixedDegree_le_caps
   (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
   (hG:HasCaps G g) (hT:HasCaps T t) (i:Fin 3):
   coordinateMixedDegree Ω G T i ≤ mixed g t (unitAt i):=by
 fin_cases i
 · simpa [unitAt,capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using
     actual_pair_degree_le G T g t hG hT 1 2
 · simpa [unitAt,capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using
     actual_pair_degree_le G T g t hG hT 0 2
 · simpa [unitAt,capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using
     actual_pair_degree_le G T g t hG hT 0 1
theorem mixed_cap_sum (g t e:DegreeVector):
   (∑ i:Fin 3,capAt e i*mixed g t (unitAt i))=mixed g t e:=by
 simp [Fin.sum_univ_three,capAt,unitAt,mixed,unitY,unitR,unitZ]
 ring
def fiberNumerator (n w a e:ℕ) (g E:DegreeVector):ℕ:=
 (n-w)*mixed g E E+(e+1)*(a-w)*mixed g E unitZ
theorem scaled_sharp_incidence_bound
   {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
   (relation:Seed → Node → Prop) [∀ seed node,Decidable (relation seed node)]
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card*(a-w) ≤ M):
   seeds.card*(a-w)^2 ≤ (nodes.card-w)*M:=by
 have hcount:=RCN173.sharp_incidence_bound relation seeds nodes identities
   a w (M/(a-w)) hidentities hcard hwa han hagreement
   (fun node hnode => (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hwa)).mpr
     (hfiber node hnode))
 calc
   seeds.card*(a-w)^2=(seeds.card*(a-w))*(a-w):=by ring
   _ ≤ ((nodes.card-w)*(M/(a-w)))*(a-w):=
     Nat.mul_le_mul_right _ hcount
   _=(nodes.card-w)*((M/(a-w))*(a-w)):=Nat.mul_assoc _ _ _
   _ ≤ (nodes.card-w)*M:=
     Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem whole_surface_seed_bound
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F)
   (hr:0 < G.degreeOf 1)
   (hHproper:¬ G∣surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ i∈nodes,∀ j k:Fin 3,j≠k →
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j*G.degreeOf k+
       G.degreeOf j*(agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (E:DegreeVector)
   (hcap:∀ i∈nodes,HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) E):
   Γ.card*(a-w)^2 ≤
     (nodes.card-w)*fiberNumerator nodes.card w a e (degreeVector G) E:=by
 classical
 let P:Ideal (MvPolynomial (Fin 3) Ω):=Ideal.span {G}
 letI:P.IsPrime:=Ideal.isPrime_span_singleton_of_prime hG.prime
 have hFmem:surfaceMap φ F∈P:=Ideal.mem_span_singleton.mpr hdiv
 have hHmem:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P:=by
   intro h
   exact hHproper (Ideal.mem_span_singleton.mp h)
 let identities:=identityNodes φ P F nodes x u₀ u₁ w
 have hidentities:identities ⊆ nodes:=identityNodes_subset φ P F nodes x u₀ u₁ w
 have hicard:identities.card ≤ w:=
   identityNodes_card_le_of_r_dependent_principal φ P F hFmem hHmem
     nodes x u₀ u₁ w hw hinj G rfl hr
 apply scaled_sharp_incidence_bound
   (fun γ i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
   Γ nodes identities a w (fiberNumerator nodes.card w a e (degreeVector G) E)
   hidentities hicard hwa han hagreement
 intro i hi
 obtain ⟨hinode,hnotid⟩:=Finset.mem_sdiff.mp hi
 let T:=agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
 have hproper:¬ G∣T:=by
   intro hd
   apply hnotid
   exact Finset.mem_filter.mpr ⟨hinode,Ideal.mem_span_singleton.mpr hd⟩
 let fiber:=Γ.filter (fun γ => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
 have hsub:fiber ⊆ Γ:=Finset.filter_subset _ _
 have hTpoint:∀ γ∈fiber,MvPolynomial.eval (selectedPoint φ selected γ) T=0:=by
   intro γ hγ
   have hΓ:=hsub hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) (x i) (u₀ i) (u₁ i)).mpr
       (Finset.mem_filter.mp hγ).2
 have hcount:=proper_cut_seed_bound φ F G T hG hdiv hproper selected fiber
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree (hcutDegree i hinode)
   (fun γ hγ => hdegree γ (hsub hγ))
   (fun γ hγ => hsolution γ (hsub hγ))
   (fun γ hγ => hregular γ (hsub hγ))
   (fun γ hγ => hGpoint γ (hsub hγ)) hTpoint
   (fun γ hγ => hagreement γ (hsub hγ))
   (noLargeSelectedPencil_mono selected Γ fiber w e hsub hnoPencil) (capAt E) hcap
 have hδ (j:Fin 3):coordinateMixedDegree Ω G T j ≤ mixed (degreeVector G) E (unitAt j):=
   coordinateMixedDegree_le_caps G T (degreeVector G) E (degreeVector_hasCaps G)
     (hcap i hinode) j
 have hsum:(∑ j,capAt E j*coordinateMixedDegree Ω G T j) ≤
     mixed (degreeVector G) E E:=by
   calc
     _ ≤ ∑ j,capAt E j*mixed (degreeVector G) E (unitAt j):=by
       apply Finset.sum_le_sum
       intro j _
       exact Nat.mul_le_mul_left _ (hδ j)
     _=_:=mixed_cap_sum (degreeVector G) E E
 exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hsum)
   (Nat.mul_le_mul_left _ (hδ 2)))
end
end ProximityPrize.SubmissionLower.RCN306
end PackedLegacy_CD

/-! Packed from ProximityPrize.SubmissionLower.DB. -/
section PackedLegacy_DB
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators
variable {F:Type} [Field F]
private theorem natDegree_det_le_of_perm_products_le
   {ι:Type} [Fintype ι] [DecidableEq ι]
   (M:Matrix ι ι F[X]) {N:ℕ}
   (h:∀ σ:Equiv.Perm ι,(∏ i:ι,M (σ i) i).natDegree ≤ N):
   M.det.natDegree ≤ N:=by
 classical
 rw [Matrix.det_apply']
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 exact (Polynomial.natDegree_C_mul_le
   ((Equiv.Perm.sign σ:ℤ):F) (∏ i:ι,M (σ i) i)).trans (h σ)
theorem bivariate_resultant_natDegree_le_of_coefficient_heights
   (B H:F[X][Y]) (n m:ℕ)
   (heightB heightH:ℕ → ℕ) (C:ℕ)
   (hB:∀ i,(B.coeff i).natDegree ≤ heightB i)
   (hH:∀ i,(H.coeff i).natDegree ≤ heightH i)
   (hassignment:∀ σ:Equiv.Perm (Fin (n+m)),
     (∀ j:Fin n,
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m)) →
     (∀ j:Fin m,
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n)) →
     (∑ j:Fin n,
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
       (∑ j:Fin m,
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))) ≤ C):
   (Polynomial.resultant B H n m).natDegree ≤ C:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ C
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):
       (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree ≤
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     rw [hentry]
     exact hH _
   have hright (j:Fin m):
       (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree ≤
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     rw [hentry]
     exact hB _
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,
           (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree)+
         (∑ j:Fin m,
           (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree):=by
     simpa using (Fin.sum_univ_add
       (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,
           (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree)+
         (∑ j:Fin m,
           (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree):=
       hsum_deg_split
     _ ≤ (∑ j:Fin n,
           heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
         (∑ j:Fin m,
           heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))):=
       Nat.add_le_add
         (Finset.sum_le_sum (fun j _ => hleft j))
         (Finset.sum_le_sum (fun j _ => hright j))
     _ ≤ C:=hassignment σ hleft_Icc hright_Icc
theorem bivariate_resultant_natDegree_le_of_sylvester_dual
   (B H:F[X][Y]) (n m:ℕ)
   (heightB heightH:ℕ → ℕ) (C:ℕ)
   (hB:∀ i,(B.coeff i).natDegree ≤ heightB i)
   (hH:∀ i,(H.coeff i).natDegree ≤ heightH i)
   (rowPotential:Fin (n+m) → ℤ)
   (leftPotential:Fin n → ℤ) (rightPotential:Fin m → ℤ)
   (hleft:∀ (row:Fin (n+m)) (j:Fin n),
     (row:ℕ)∈Set.Icc (j:ℕ) ((j:ℕ)+m) →
     (heightH ((row:ℕ)-(j:ℕ)):ℤ) ≤
       rowPotential row+leftPotential j)
   (hright:∀ (row:Fin (n+m)) (j:Fin m),
     (row:ℕ)∈Set.Icc (j:ℕ) ((j:ℕ)+n) →
     (heightB ((row:ℕ)-(j:ℕ)):ℤ) ≤
       rowPotential row+rightPotential j)
   (hbudget:(∑ row,rowPotential row)+
     (∑ j,leftPotential j)+(∑ j,rightPotential j) ≤ (C:ℤ)):
   (Polynomial.resultant B H n m).natDegree ≤ C:=by
 apply bivariate_resultant_natDegree_le_of_coefficient_heights
   B H n m heightB heightH C hB hH
 intro σ hleft_Icc hright_Icc
 have hleft_sum:
     (∑ j:Fin n,
         (heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)) ≤
       (∑ j:Fin n,
         (rowPotential (σ (Fin.castAdd m j))+leftPotential j)):=by
   exact Finset.sum_le_sum (fun j _ => hleft _ j (hleft_Icc j))
 have hright_sum:
     (∑ j:Fin m,
         (heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)) ≤
       (∑ j:Fin m,
         (rowPotential (σ (Fin.natAdd n j))+rightPotential j)):=by
   exact Finset.sum_le_sum (fun j _ => hright _ j (hright_Icc j))
 have hperm_sum:
     (∑ row:Fin (n+m),rowPotential (σ row))=
       ∑ row:Fin (n+m),rowPotential row:=by
   simpa using (Equiv.sum_comp σ rowPotential)
 have hrows_split:
     (∑ row:Fin (n+m),rowPotential (σ row))=
       (∑ j:Fin n,rowPotential (σ (Fin.castAdd m j)))+
         (∑ j:Fin m,rowPotential (σ (Fin.natAdd n j))):=by
   simpa using Fin.sum_univ_add
     (fun row:Fin (n+m) => rowPotential (σ row))
 have hrow_sum:
     (∑ j:Fin n,rowPotential (σ (Fin.castAdd m j)))+
         (∑ j:Fin m,rowPotential (σ (Fin.natAdd n j)))=
       ∑ row:Fin (n+m),rowPotential row:=by
   rw [←hrows_split,hperm_sum]
 have hcast:
     (((∑ j:Fin n,
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
       (∑ j:Fin m,
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))):ℕ):ℤ) ≤
       (C:ℤ):=by
   calc
     _=(∑ j:Fin n,
           (heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ))+
         (∑ j:Fin m,
           (heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)):=by
       simp
     _ ≤ (∑ j:Fin n,
           (rowPotential (σ (Fin.castAdd m j))+leftPotential j))+
         (∑ j:Fin m,
           (rowPotential (σ (Fin.natAdd n j))+rightPotential j)):=
       add_le_add hleft_sum hright_sum
     _=(∑ row:Fin (n+m),rowPotential row)+
         (∑ j:Fin n,leftPotential j)+
         (∑ j:Fin m,rightPotential j):=by
       rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
       linear_combination hrow_sum
     _ ≤ (C:ℤ):=hbudget
 exact_mod_cast hcast
namespace CornerStaircase
def surfaceHeight (i:ℕ):ℕ:=
 if i ≤ 24 then 178-i else if i=25 then 5 else 0
def tailHeight (K j:ℕ):ℕ:=
 if j=0 then 178*K
 else if j ≤ 24*K+1 then 178*K+1-j
 else if j ≤ 25*K+1 then 3730*K+149-149*j
 else 0
def rowPrice (K r:ℕ):ℤ:=
 178-((r-1:ℕ):ℤ)-
   148*((r-(24*K+25):ℕ):ℤ)
def rowPotential (K:ℕ) (r:Fin (25+(25*K+1))):ℤ:=
 rowPrice K r
def scaledColumnPotential (K:ℕ) (b:Fin 25):ℤ:=
 178*(K:ℤ)-178+(b:ℕ)
def surfaceColumnPrice (K a:ℕ):ℤ:=
 ((a-1:ℕ):ℤ)+
   148*((a-(24*K+1):ℕ):ℤ)
def surfaceColumnPotential (K:ℕ) (a:Fin (25*K+1)):ℤ:=
 surfaceColumnPrice K a
theorem tailHeight_le_potentials (K:ℕ) (hK:1 ≤ K)
   (row:Fin (25+(25*K+1))) (b:Fin 25)
   (hrow:(row:ℕ)∈Set.Icc (b:ℕ) ((b:ℕ)+(25*K+1))):
   (tailHeight K ((row:ℕ)-(b:ℕ)):ℤ) ≤
     rowPotential K row+scaledColumnPotential K b:=by
 rcases Set.mem_Icc.mp hrow with ⟨hbr,hrb⟩
 have hb:(b:ℕ) ≤ 24:=Nat.le_pred_of_lt b.isLt
 unfold tailHeight rowPotential rowPrice scaledColumnPotential
 split_ifs with hzero hfirst hsecond
 · push_cast
   omega
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem surfaceHeight_le_potentials (K:ℕ) (hK:1 ≤ K)
   (row:Fin (25+(25*K+1))) (a:Fin (25*K+1))
   (hrow:(row:ℕ)∈Set.Icc (a:ℕ) ((a:ℕ)+25)):
   (surfaceHeight ((row:ℕ)-(a:ℕ)):ℤ) ≤
     rowPotential K row+surfaceColumnPotential K a:=by
 rcases Set.mem_Icc.mp hrow with ⟨har,hra⟩
 unfold surfaceHeight rowPotential rowPrice surfaceColumnPotential surfaceColumnPrice
 split_ifs with hfirst hlast
 · push_cast
   omega
 · push_cast
   omega
 · omega
private theorem sum_fin_natSub_cast (A L:ℕ):
   (∑ i:Fin (A+L+1),(((i:ℕ)-A:ℕ):ℤ))=
     ∑ i∈Finset.range (L+1),(i:ℤ):=by
 calc
   _=∑ i∈Finset.range (A+L+1),
         (((i:ℕ)-A:ℕ):ℤ):=by
     simpa using (Fin.sum_univ_eq_sum_range (n:=A+L+1)
       (fun i:ℕ => (((i:ℕ)-A:ℕ):ℤ)))
   _=_:=by
     have hp:
         (∑ x∈Finset.range A,(((x-A:ℕ):ℤ)))=0:=by
       apply Finset.sum_eq_zero
       intro x hx
       rw [Nat.sub_eq_zero_of_le
         (Nat.le_of_lt (Finset.mem_range.mp hx))]
       simp
     rw [show A+L+1=A+(L+1) by omega]
     rw [Finset.sum_range_add]
     rw [hp]
     simp
theorem potentialBudget (K:ℕ) (hK:1 ≤ K):
   (∑ row,rowPotential K row)+
       (∑ b,scaledColumnPotential K b)+
       (∑ a,surfaceColumnPotential K a)=(8127*K+178:ℕ):=by
 have hrowBase:
     (∑ r:Fin (25+(25*K+1)),
         ((((r:ℕ)-1:ℕ):ℤ)))=
       ∑ i∈Finset.range (25*K+25),(i:ℤ):=by
   have hcard:25+(25*K+1)=1+(25*K+24)+1:=by omega
   rw [hcard]
   simpa only [show 25*K+24+1=25*K+25 by omega] using
     sum_fin_natSub_cast 1 (25*K+24)
 have hrowTail:
     (∑ r:Fin (25+(25*K+1)),
         ((((r:ℕ)-(24*K+25):ℕ):ℤ)))=
       ∑ i∈Finset.range (K+1),(i:ℤ):=by
   have hcard:25+(25*K+1)=(24*K+25)+K+1:=by omega
   rw [hcard]
   exact sum_fin_natSub_cast (24*K+25) K
 have hcolumnBase:
     (∑ a:Fin (25*K+1),
         ((((a:ℕ)-1:ℕ):ℤ)))=
       ∑ i∈Finset.range (25*K),(i:ℤ):=by
   have hcard:25*K+1=1+(25*K-1)+1:=by omega
   rw [hcard]
   simpa only [show 25*K-1+1=25*K by omega] using
     sum_fin_natSub_cast 1 (25*K-1)
 have hcolumnTail:
     (∑ a:Fin (25*K+1),
         ((((a:ℕ)-(24*K+1):ℕ):ℤ)))=
       ∑ i∈Finset.range K,(i:ℤ):=by
   have hcard:25*K+1=(24*K+1)+(K-1)+1:=by omega
   rw [hcard]
   simpa only [show K-1+1=K by omega] using
     sum_fin_natSub_cast (24*K+1) (K-1)
 have hlongDifference:
     (∑ i∈Finset.range (25*K+25),(i:ℤ))=
       (∑ i∈Finset.range (25*K),(i:ℤ))+
         (625*K+300):=by
   rw [Finset.sum_range_add]
   norm_num [Finset.sum_range_succ]
   ring
 have htailDifference:
     (∑ i∈Finset.range (K+1),(i:ℤ))=
       (∑ i∈Finset.range K,(i:ℤ))+K:=by
   rw [Finset.sum_range_succ]
 unfold rowPotential rowPrice scaledColumnPotential surfaceColumnPotential surfaceColumnPrice
 simp only [Finset.sum_sub_distrib, ←Finset.mul_sum,Finset.sum_add_distrib,
   Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
 rw [hrowBase,hrowTail,hcolumnBase,hcolumnTail,
   hlongDifference,htailDifference]
 norm_num [Fin.sum_univ_succ]
 ring
def partialBudget (K m:ℕ):ℤ:=
 (∑ row:Fin (25+m),rowPrice K row)+
   (∑ b:Fin 25,scaledColumnPotential K b)+
   (∑ a:Fin m,surfaceColumnPrice K a)
def rowPotentialUpTo (K m:ℕ) (row:Fin (25+m)):ℤ:=
 rowPrice K row
def surfaceColumnPotentialUpTo (K m:ℕ) (a:Fin m):ℤ:=
 surfaceColumnPrice K a
private def basePotential (K:ℕ):ℤ:=
 (∑ row∈Finset.range 25,rowPrice K row)+
   ∑ b:Fin 25,scaledColumnPotential K b
private def pairPotential (K a:ℕ):ℤ:=
 rowPrice K (25+a)+surfaceColumnPrice K a
private theorem partialBudget_eq_base_add_pairs (K m:ℕ):
   partialBudget K m=basePotential K+
     ∑ a∈Finset.range m,pairPotential K a:=by
 unfold partialBudget basePotential pairPotential rowPrice surfaceColumnPrice
 rw [show (∑ row:Fin (25+m),
     (178-(((row:ℕ)-1:ℕ):ℤ)-
       148*(((row:ℕ)-(24*K+25):ℕ):ℤ)))=
     ∑ row∈Finset.range (25+m),
     (178-(((row:ℕ)-1:ℕ):ℤ)-
       148*(((row:ℕ)-(24*K+25):ℕ):ℤ)) by
   simpa using (Fin.sum_univ_eq_sum_range (n:=25+m)
     (fun row:ℕ => (178:ℤ)-((row-1:ℕ):ℤ)-
       148*((row-(24*K+25):ℕ):ℤ)))]
 rw [show (∑ a:Fin m,
     ((((a:ℕ)-1:ℕ):ℤ)+
       148*(((a:ℕ)-(24*K+1):ℕ):ℤ)))=
     ∑ a∈Finset.range m,
     ((((a:ℕ)-1:ℕ):ℤ)+
       148*(((a:ℕ)-(24*K+1):ℕ):ℤ)) by
   simpa using (Fin.sum_univ_eq_sum_range (n:=m)
     (fun a:ℕ => (((a-1:ℕ):ℤ)+
       148*((a-(24*K+1):ℕ):ℤ))))]
 rw [Finset.sum_range_add]
 simp only [Finset.sum_add_distrib]
 ring
theorem pairPotential_nonnegative (K a:ℕ)
   (ha:a < 25*K+1):0 ≤ pairPotential K a:=by
 unfold pairPotential rowPrice surfaceColumnPrice
 push_cast
 omega
theorem partialBudget_le (K m:ℕ) (hm:m ≤ 25*K+1) (hK:1 ≤ K):
   partialBudget K m ≤ (8127*K+178:ℕ):=by
 rw [partialBudget_eq_base_add_pairs]
 calc
   _ ≤ basePotential K+
       ∑ a∈Finset.range (25*K+1),pairPotential K a:=by
     gcongr
     intro a ha _
     exact pairPotential_nonnegative K a (Finset.mem_range.mp ha)
   _=partialBudget K (25*K+1):=
     (partialBudget_eq_base_add_pairs K (25*K+1)).symm
   _=(8127*K+178:ℕ):=by
     simpa [partialBudget,rowPotential,surfaceColumnPotential] using
       potentialBudget K hK
theorem tailHeight_le_potentials_upTo (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1) (row:Fin (25+m)) (b:Fin 25)
   (hrow:(row:ℕ)∈Set.Icc (b:ℕ) ((b:ℕ)+m)):
   (tailHeight K ((row:ℕ)-(b:ℕ)):ℤ) ≤
     rowPotentialUpTo K m row+scaledColumnPotential K b:=by
 rcases Set.mem_Icc.mp hrow with ⟨hbr,hrb⟩
 have hb:(b:ℕ) ≤ 24:=Nat.le_pred_of_lt b.isLt
 unfold tailHeight rowPotentialUpTo rowPrice scaledColumnPotential
 split_ifs with hzero hfirst hsecond
 · push_cast
   omega
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem surfaceHeight_le_potentials_upTo (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1) (row:Fin (25+m)) (a:Fin m)
   (hrow:(row:ℕ)∈Set.Icc (a:ℕ) ((a:ℕ)+25)):
   (surfaceHeight ((row:ℕ)-(a:ℕ)):ℤ) ≤
     rowPotentialUpTo K m row+surfaceColumnPotentialUpTo K m a:=by
 rcases Set.mem_Icc.mp hrow with ⟨har,hra⟩
 unfold surfaceHeight rowPotentialUpTo rowPrice
   surfaceColumnPotentialUpTo surfaceColumnPrice
 split_ifs with hfirst hlast
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem resultant_natDegree_le_actual_tail
   (B H:F[X][Y]) (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H 25 m).natDegree ≤ 8127*K+178:=by
 apply bivariate_resultant_natDegree_le_of_sylvester_dual
   B H 25 m surfaceHeight (tailHeight K) (8127*K+178)
   hB hH (rowPotentialUpTo K m) (scaledColumnPotential K)
     (surfaceColumnPotentialUpTo K m)
 · exact tailHeight_le_potentials_upTo K m hK hm
 · exact surfaceHeight_le_potentials_upTo K m hK hm
 · exact partialBudget_le K m hm hK
theorem ordinary_resultant_natDegree_le
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K) (hHne:H≠0)
   (hBouter:B.natDegree ≤ 25)
   (hHouter:H.natDegree ≤ 25*K+1)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H).natDegree ≤ 8127*K+178:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=resultant_natDegree_le_actual_tail
     B H K H.natDegree hK hHouter hB hH
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:F[X]:=
     (-1)^(H.natDegree*(25-B.natDegree))*
       H.coeff H.natDegree^(25-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=25-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(25-B.natDegree)=25:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H 25 H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree ≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H 25 H.natDegree).natDegree:=by
       rw [hpad]
     _ ≤ 8127*K+178:=hfixed
theorem resultant_natDegree_le_of_budget
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i)
   (hbudget:(∑ row,rowPotential K row)+
       (∑ b,scaledColumnPotential K b)+
       (∑ a,surfaceColumnPotential K a) ≤ (8127*K+178:ℕ)):
   (Polynomial.resultant B H 25 (25*K+1)).natDegree ≤
     8127*K+178:=by
 apply bivariate_resultant_natDegree_le_of_sylvester_dual
   B H 25 (25*K+1) surfaceHeight (tailHeight K) (8127*K+178)
   hB hH (rowPotential K) (scaledColumnPotential K)
     (surfaceColumnPotential K)
 · exact tailHeight_le_potentials K hK
 · exact surfaceHeight_le_potentials K hK
 · exact hbudget
theorem resultant_natDegree_le
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H 25 (25*K+1)).natDegree ≤
     8127*K+178:=by
 apply resultant_natDegree_le_of_budget B H K hK hB hH
 exact (potentialBudget K hK).le
end CornerStaircase
theorem bivariate_resultant_natDegree_le_of_index_sum_height_bound
   (B H:F[X][Y]) (n m:ℕ)
   (heightB heightH:ℕ → ℕ) (C:ℕ)
   (hB:∀ i,(B.coeff i).natDegree ≤ heightB i)
   (hH:∀ i,(H.coeff i).natDegree ≤ heightH i)
   (htransport:∀ (lidx:Fin n → ℕ) (ridx:Fin m → ℕ),
     (∀ j,lidx j ≤ m) → (∀ j,ridx j ≤ n) →
     (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n →
     (∑ j:Fin n,heightH (lidx j))+
       (∑ j:Fin m,heightB (ridx j)) ≤ C):
   (Polynomial.resultant B H n m).natDegree ≤ C:=by
 apply bivariate_resultant_natDegree_le_of_coefficient_heights
   B H n m heightB heightH C hB hH
 intro σ hleft_Icc hright_Icc
 let lidx:Fin n → ℕ:=fun j =>
   ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
 let ridx:Fin m → ℕ:=fun j =>
   ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
 have hleft_le (j:Fin n):lidx j ≤ m:=by
   dsimp [lidx]
   have hh:=Set.mem_Icc.mp (hleft_Icc j)
   omega
 have hright_le (j:Fin m):ridx j ≤ n:=by
   dsimp [ridx]
   have hh:=Set.mem_Icc.mp (hright_Icc j)
   omega
 have hidxsum:
     (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
   have hleft_row (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
     dsimp [lidx]
     have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
     omega
   have hright_row (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
     dsimp [ridx]
     have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
     omega
   have hsum_left_rows:
       (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
         (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
     calc
       _=∑ j:Fin n,((j:ℕ)+lidx j):=
         Finset.sum_congr rfl (fun j _ => hleft_row j)
       _=_:=Finset.sum_add_distrib
   have hsum_right_rows:
       (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
         (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
     calc
       _=∑ j:Fin m,((j:ℕ)+ridx j):=
         Finset.sum_congr rfl (fun j _ => hright_row j)
       _=_:=Finset.sum_add_distrib
   have hperm_sum:
       (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
         ∑ i:Fin (n+m),(i:ℕ):=by
     simpa using (Equiv.sum_comp σ (fun i:Fin (n+m) => (i:ℕ)))
   have hrows_split:
       (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
           (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
     simpa using (Fin.sum_univ_add
       (fun i:Fin (n+m) => ((σ i:Fin (n+m)):ℕ)))
   have hcols_split:
       (∑ i:Fin (n+m),(i:ℕ))=
         (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
     simpa using (Fin.sum_univ_add (fun i:Fin (n+m) => (i:ℕ)))
   have hright_cols:
       (∑ j:Fin m,(n+(j:ℕ)))=
         m*n+∑ j:Fin m,(j:ℕ):=by
     simp [Finset.sum_add_distrib,Finset.sum_const]
   have hmain:
       (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
           (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
         (∑ j:Fin n,(j:ℕ))+
           (m*n+∑ j:Fin m,(j:ℕ)):=by
     rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
   omega
 exact htransport lidx ridx hleft_le hright_le hidxsum
theorem bivariate_resultant_natDegree_le_totalDegree
   (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*totalDegree B+n*totalDegree H-m*n:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ _
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   let lidx:Fin n → ℕ:=fun j =>
     ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
   let ridx:Fin m → ℕ:=fun j =>
     ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
   let ldeg:Fin n → ℕ:=fun j =>
     (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
   let rdeg:Fin m → ℕ:=fun j =>
     (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):lidx j+ldeg j ≤ totalDegree H:=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     have hcoeff:H.coeff (lidx j)≠0:=by
       have hh:=hne (Fin.castAdd m j)
       rw [hentry] at hh
       simpa only [lidx] using hh
     have hsupp:lidx j∈H.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:ldeg j=(H.coeff (lidx j)).natDegree:=by
       dsimp [ldeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
   have hright (j:Fin m):ridx j+rdeg j ≤ totalDegree B:=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     have hcoeff:B.coeff (ridx j)≠0:=by
       have hh:=hne (Fin.natAdd n j)
       rw [hentry] at hh
       simpa only [ridx] using hh
     have hsupp:ridx j∈B.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:rdeg j=(B.coeff (ridx j)).natDegree:=by
       dsimp [rdeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
   have hleft_sum:
       (∑ j:Fin n,(lidx j+ldeg j)) ≤ n*totalDegree H:=by
     calc
       _ ≤ ∑ _j:Fin n,totalDegree H:=
         Finset.sum_le_sum (fun j _ => hleft j)
       _=n*totalDegree H:=by simp
   have hright_sum:
       (∑ j:Fin m,(ridx j+rdeg j)) ≤ m*totalDegree B:=by
     calc
       _ ≤ ∑ _j:Fin m,totalDegree B:=
         Finset.sum_le_sum (fun j _ => hright j)
       _=m*totalDegree B:=by simp
   have hidxsum:
       (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
     have hleft_row (j:Fin n):
         ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
       dsimp [lidx]
       have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
       omega
     have hright_row (j:Fin m):
         ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
       dsimp [ridx]
       have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
       omega
     have hsum_left_rows:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
       calc
         _=∑ j:Fin n,((j:ℕ)+lidx j):=
           Finset.sum_congr rfl (fun j _ => hleft_row j)
         _=_:=Finset.sum_add_distrib
     have hsum_right_rows:
         (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
       calc
         _=∑ j:Fin m,((j:ℕ)+ridx j):=
           Finset.sum_congr rfl (fun j _ => hright_row j)
         _=_:=Finset.sum_add_distrib
     have hperm_sum:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           ∑ i:Fin (n+m),(i:ℕ):=by
       simpa using (Equiv.sum_comp σ (fun i:Fin (n+m) => (i:ℕ)))
     have hrows_split:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
       simpa using (Fin.sum_univ_add
         (fun i:Fin (n+m) => ((σ i:Fin (n+m)):ℕ)))
     have hcols_split:
         (∑ i:Fin (n+m),(i:ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
       simpa using (Fin.sum_univ_add (fun i:Fin (n+m) => (i:ℕ)))
     have hright_cols:
         (∑ j:Fin m,(n+(j:ℕ)))=
           m*n+∑ j:Fin m,(j:ℕ):=by
       simp [Finset.sum_add_distrib,Finset.sum_const]
     have hmain:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+
             (m*n+∑ j:Fin m,(j:ℕ)):=by
       rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
     omega
   have hsum:
       ((∑ j:Fin n,lidx j)+(∑ j:Fin n,ldeg j))+
           ((∑ j:Fin m,ridx j)+(∑ j:Fin m,rdeg j)) ≤
         n*totalDegree H+m*totalDegree B:=by
     simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
   have hdeg_parts:
       (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j) ≤
         m*totalDegree B+n*totalDegree H-m*n:=by
     omega
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=by
     simpa only [ldeg,rdeg] using
       (Fin.sum_univ_add (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=hsum_deg_split
     _ ≤ _:=hdeg_parts
end ProximityPrize.SubmissionLower
end PackedLegacy_DB

/-! Packed from ProximityPrize.SubmissionLower.AY. -/
section PackedLegacy_AY
namespace ProximityPrize.SubmissionLower.RCN012
open Polynomial Polynomial.Bivariate RCN002 RCN005 RCN371 RCN011 RCN009 RCN013
noncomputable section
variable {A:Type} [Field A]
theorem bivariateEquiv_coeff_natDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (height:ℕ → ℕ)
   (hsupport:∀ d∈f.support,d 1 ≤ height (d 0)) (i:ℕ):
   ((bivariateEquiv A f).coeff i).natDegree ≤ height i:=by
 rw [show (bivariateEquiv A f).coeff i=
     MvPolynomial.uniqueAlgEquiv A (Fin 1)
       ((MvPolynomial.finSuccEquiv A 1 f).coeff i) by
   simp [bivariateEquiv]]
 apply (uniqueAlgEquiv_natDegree_le A _).trans
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=hsupport (d.cons i)
   (MvPolynomial.mem_support_coeff_finSuccEquiv.mp hd)
 simpa only [show (1:Fin 2)=(0:Fin 1).succ by decide,
   Finsupp.cons_succ,Finsupp.cons_zero] using hs
theorem bivariateEquiv_totalDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (cap:ℕ)
   (hsupport:∀ d∈f.support,d 0+d 1 ≤ cap):
   totalDegree (bivariateEquiv A f) ≤ cap:=by
 classical
 have houter:f.degreeOf 0 ≤ cap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (Nat.le_add_right (d 0) (d 1)).trans (hsupport d hd)
 unfold totalDegree
 apply Finset.sup_le
 intro i hi
 have hiCap:i ≤ cap:=by
   exact (Polynomial.le_natDegree_of_mem_supp i hi).trans
     ((bivariateEquiv_natDegree A f).trans_le houter)
 have hcoeff:((bivariateEquiv A f).coeff i).natDegree ≤ cap-i:=by
   apply bivariateEquiv_coeff_natDegree_le_of_support f (fun j => cap-j)
   intro d hd
   have hs:=hsupport d hd
   omega
 omega
variable (K:Type) [Field K]
theorem planeMap_coeff_natDegree_le_of_rational_support
   (order:Fin 3 ≃ Fin 3) (F:Original K) (height:ℕ → ℕ)
   (hsupport:∀ d∈(rationalMap K order F).support,
     d 1 ≤ height (d 0)) (i:ℕ):
   ((planeMap K order F).coeff i).natDegree ≤ height i:=by
 exact bivariateEquiv_coeff_natDegree_le_of_support
   (rationalMap K order F) height hsupport i
theorem planeMap_totalDegree_le_of_rational_support
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈(rationalMap K order F).support,
     d 0+d 1 ≤ cap):
   totalDegree (planeMap K order F) ≤ cap:=by
 exact bivariateEquiv_totalDegree_le_of_support
   (rationalMap K order F) cap hsupport
theorem rationalMap_joint_support_of_original
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈F.support,
     d (order 1)+d (order 2) ≤ cap):
   ∀ e∈(rationalMap K order F).support,e 0+e 1 ≤ cap:=by
 classical
 intro e he
 rw [rationalMap_eq_firstMap] at he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp
   (support_firstMap_subset K
     (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F) he)
 rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
 obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hd
 simpa only [Finsupp.tail_apply,Finsupp.mapDomain_equiv_apply,
   Equiv.symm_symm,
   show (0:Fin 2).succ=(1:Fin 3) by decide,
   show (1:Fin 2).succ=(2:Fin 3) by decide] using hsupport u hu
theorem original_joint_support_to_rationalMap
   (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈F.support,d 0+d 2 ≤ cap):
   ∀ e∈(rationalMap K (Equiv.swap 0 1) F).support,
     e 0+e 1 ≤ cap:=by
 apply rationalMap_joint_support_of_original K (Equiv.swap 0 1) F cap
 intro d hd
 simpa [Equiv.swap_apply_def] using hsupport d hd
theorem ordinary_resultant_natDegree_le_totalDegree
   (B H:A[X][Y]) (n mCap totalB totalH cap:ℕ)
   (hHne:H≠0) (hBouter:B.natDegree ≤ n)
   (hHouter:H.natDegree ≤ mCap)
   (hBtotal:totalDegree B ≤ totalB)
   (hHtotal:totalDegree H ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalB+n*totalH-m*n ≤ cap):
   (Polynomial.resultant B H).natDegree ≤ cap:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=bivariate_resultant_natDegree_le_totalDegree
     B H n H.natDegree
   have hdegreeCap:
       H.natDegree*totalDegree B+n*totalDegree H-H.natDegree*n ≤
         H.natDegree*totalB+n*totalH-H.natDegree*n:=by
     exact Nat.sub_le_sub_right
       (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
         (Nat.mul_le_mul_left n hHtotal)) _
   have hfixedCap:
       (Polynomial.resultant B H n H.natDegree).natDegree ≤ cap:=
     hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:A[X]:=
     (-1)^(H.natDegree*(n-B.natDegree))*
       H.coeff H.natDegree^(n-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=n-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(n-B.natDegree)=n:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H n H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree ≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H n H.natDegree).natDegree:=by rw [hpad]
     _ ≤ cap:=hfixedCap
theorem planeMap_trapezoid_resultant_natDegree_le
   (order:Fin 3 ≃ Fin 3) (G T:Original K)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   (Polynomial.resultant (planeMap K order G)
     (planeMap K order T)).natDegree ≤ cap:=by
 apply ordinary_resultant_natDegree_le_totalDegree
   (planeMap K order G) (planeMap K order T)
     n mCap totalG totalT cap
 · intro hzero
   apply hTne
   apply planeMap_injective K order
   simpa only [map_zero] using hzero
 · exact hGouter
 · exact hTouter
 · exact planeMap_totalDegree_le_of_rational_support
     K order G totalG hGsupport
 · exact planeMap_totalDegree_le_of_rational_support
     K order T totalT hTsupport
 · exact hbudget
theorem planeMap_corner_resultant_natDegree_le
   (order:Fin 3 ≃ Fin 3) (G T:Original K) (k:ℕ) (hk:1 ≤ k)
   (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ 25)
   (hTouter:(planeMap K order T).natDegree ≤ 25*k+1)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 1 ≤ CornerStaircase.surfaceHeight (d 0))
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 1 ≤ CornerStaircase.tailHeight k (d 0)):
   (Polynomial.resultant (planeMap K order G) (planeMap K order T)).natDegree ≤
     8127*k+178:=by
 apply CornerStaircase.ordinary_resultant_natDegree_le
   (planeMap K order G) (planeMap K order T) k hk
 · intro hzero
   apply hTne
   apply planeMap_injective K order
   simpa only [map_zero] using hzero
 · exact hGouter
 · exact hTouter
 · exact planeMap_coeff_natDegree_le_of_rational_support
     K order G CornerStaircase.surfaceHeight hGsupport
 · exact planeMap_coeff_natDegree_le_of_rational_support
     K order T (CornerStaircase.tailHeight k) hTsupport
theorem swapped_planeMap_degreeX_le_outer_natDegree
   (order:Fin 3 ≃ Fin 3) (F:Original K):
   degreeX (planeMap K (swapOtherOrder order) F) ≤
     (planeMap K order F).natDegree:=by
 calc
   degreeX (planeMap K (swapOtherOrder order) F) ≤
       (rationalMap K (swapOtherOrder order) F).degreeOf 1:=
     bivariateEquiv_degreeX_le (RatFunc K)
       (rationalMap K (swapOtherOrder order) F)
   _=(rationalMap K order F).degreeOf 0:=by
     rw [rationalMap_swapOtherOrder]
     change (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
       (rationalMap K order F)).degreeOf 1=_
     simpa only [Equiv.swap_apply_left] using
       (MvPolynomial.degreeOf_rename_of_injective
         (p:=rationalMap K order F) (Equiv.swap (0:Fin 2) 1).injective
         (0:Fin 2))
   _=(planeMap K order F).natDegree:=by
     exact (bivariateEquiv_natDegree (RatFunc K)
       (rationalMap K order F)).symm
theorem swapped_resultant_natDegree_le_of_outer_zero
   (order:Fin 3 ≃ Fin 3) (G T:Original K) (gOuter tInner:ℕ)
   (hzero:(planeMap K order G).natDegree=0)
   (hGouter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
   (hTinner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner):
   (Polynomial.resultant (planeMap K (swapOtherOrder order) G)
     (planeMap K (swapOtherOrder order) T)).natDegree ≤ gOuter*tInner:=by
 have hGinner:degreeX (planeMap K (swapOtherOrder order) G)=0:=by
   apply Nat.eq_zero_of_le_zero
   exact (swapped_planeMap_degreeX_le_outer_natDegree K order G).trans_eq hzero
 have hres:=bivariate_resultant_natDegree_le
   (planeMap K (swapOtherOrder order) G)
   (planeMap K (swapOtherOrder order) T)
   (planeMap K (swapOtherOrder order) G).natDegree
   (planeMap K (swapOtherOrder order) T).natDegree
 rw [hGinner,mul_zero,zero_add] at hres
 exact hres.trans (Nat.mul_le_mul hGouter hTinner)
theorem exists_positive_joint_characteristic_order
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (G T:Original K) (p n mCap totalG totalT cap gOuter tInner:ℕ)
   (hG:Irreducible G) (hGmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
   (hTswapInner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner)
   (hnp:n < p) (hgOuterP:gOuter < p)
   (hcapP:cap < p) (hswapP:gOuter*tInner < p)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   ∃ order':Fin 3 ≃ Fin 3,
     (order'=order∨order'=swapOtherOrder order)∧
     order' 0=order 0∧
     originalMixedDegree K order' G T=originalMixedDegree K order G T∧
     0 < (planeMap K order' G).natDegree∧
     (planeMap K order' G).natDegree < p∧
     (Polynomial.resultant (planeMap K order' G)
       (planeMap K order' T)).natDegree < p:=by
 by_cases hpositive:0 < (planeMap K order G).natDegree
 · refine ⟨order,Or.inl rfl,rfl,rfl,hpositive,
     hGouter.trans_lt hnp,?_⟩
   exact (planeMap_trapezoid_resultant_natDegree_le K order G T
     n mCap totalG totalT cap hTne hGouter hTouter hGsupport hTsupport
     hbudget).trans_lt hcapP
 · have hzero:(planeMap K order G).natDegree=0:=
     Nat.eq_zero_of_not_pos hpositive
   obtain ⟨order',hchoice,_hbase,hpos⟩:=
     exists_positive_outer_order K order P G hG hGmem ht
   have hswapPos:0 < (planeMap K (swapOtherOrder order) G).natDegree:=by
     rcases hchoice with hsame | hswap
     · subst order'
       exact (hpositive hpos).elim
     · subst order'
       exact hpos
   refine ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
     originalMixedDegree_swap K order G T,hswapPos,
     hGswapOuter.trans_lt hgOuterP,?_⟩
   exact (swapped_resultant_natDegree_le_of_outer_zero K order G T
     gOuter tInner hzero hGswapOuter hTswapInner).trans_lt hswapP
theorem first_6463_trapezoid_budget (m:ℕ) (hm:m ≤ 6553601):
   m*175+25*45875201-m*25 ≤ 2129920175:=by
 omega
theorem agreement_6463_trapezoid_budget (m:ℕ) (hm:m ≤ 6553551):
   m*175+25*45874851-m*25 ≤ 2129903925:=by
 omega
theorem first_6463_trapezoid_cap_below_characteristic:
   2129920175 < 2130706433:=by norm_num
theorem agreement_6463_trapezoid_cap_below_characteristic:
   2129903925 < 2130706433:=by norm_num
theorem swapped_6463_cap_below_characteristic:
   175*6553601 < 2130706433:=by norm_num
theorem first_6464_sharpY_trapezoid_budget (m:ℕ) (hm:m ≤ 6422529):
   m*176+25*46137345-m*25 ≤ 2123235504:=by
 omega
theorem agreement_6464_sharpY_trapezoid_budget (m:ℕ) (hm:m ≤ 6422480):
   m*176+25*46136993-m*25 ≤ 2123219305:=by
 omega
theorem first_6464_sharpY_trapezoid_cap_below_characteristic:
   2123235504 < 2130706433:=by norm_num
theorem agreement_6464_sharpY_trapezoid_cap_below_characteristic:
   2123219305 < 2130706433:=by norm_num
theorem swapped_6464_sharpY_cap_below_characteristic:
   176*6422529 < 2130706433:=by norm_num
theorem swapped_6464_cap_below_characteristic:
   178*(25*262144+1) < 2130706433:=by
 norm_num
theorem exists_positive_sparse_characteristic_order
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (G T:Original K) (p k gOuter tInner:ℕ)
   (hG:Irreducible G) (hGmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (hTne:T≠0) (hk:1 ≤ k)
   (hGouter:(planeMap K order G).natDegree ≤ 25)
   (hTouter:(planeMap K order T).natDegree ≤ 25*k+1)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 1 ≤ CornerStaircase.surfaceHeight (d 0))
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 1 ≤ CornerStaircase.tailHeight k (d 0))
   (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
   (hTswapInner:degreeX (planeMap K (swapOtherOrder order) T) ≤ tInner)
   (h25p:25 < p) (hgOuterP:gOuter < p)
   (hcornerP:8127*k+178 < p) (hswapP:gOuter*tInner < p):
   ∃ order':Fin 3 ≃ Fin 3,
     (order'=order∨order'=swapOtherOrder order)∧
     order' 0=order 0∧
     0 < (planeMap K order' G).natDegree∧
     (planeMap K order' G).natDegree < p∧
     (Polynomial.resultant (planeMap K order' G)
       (planeMap K order' T)).natDegree < p:=by
 by_cases hpositive:0 < (planeMap K order G).natDegree
 · refine ⟨order,Or.inl rfl,rfl,hpositive,
     hGouter.trans_lt h25p,?_⟩
   exact (planeMap_corner_resultant_natDegree_le K order G T k hk hTne
     hGouter hTouter hGsupport hTsupport).trans_lt hcornerP
 · have hzero:(planeMap K order G).natDegree=0:=
     Nat.eq_zero_of_not_pos hpositive
   obtain ⟨order',hchoice,hbase,hpos⟩:=
     exists_positive_outer_order K order P G hG hGmem ht
   have hswapPos:0 < (planeMap K (swapOtherOrder order) G).natDegree:=by
     rcases hchoice with hsame | hswap
     · subst order'
       exact (hpositive hpos).elim
     · subst order'
       exact hpos
   refine ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
     hswapPos,hGswapOuter.trans_lt hgOuterP,?_⟩
   exact (swapped_resultant_natDegree_le_of_outer_zero K order G T
     gOuter tInner hzero hGswapOuter hTswapInner).trans_lt hswapP
end
end ProximityPrize.SubmissionLower.RCN012
end PackedLegacy_AY

/-! Packed from ProximityPrize.SubmissionLower.Y. -/
section PackedLegacy_Y
namespace ProximityPrize.SubmissionLower.RCN003
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN004 RCN007 RCN001
open RCN012
noncomputable section
variable (K:Type) [Field K]
def JointOrderCertificate (order:Fin 3 ≃ Fin 3)
   (G H:Original K) (p:ℕ):Prop:=
 ∃ order':Fin 3 ≃ Fin 3,
   order' 0=order 0∧
   originalMixedDegree K order' G H=originalMixedDegree K order G H∧
   0 < (planeMap K order' G).natDegree∧
   (planeMap K order' G).natDegree < p∧
   (Polynomial.resultant (planeMap K order' G)
     (planeMap K order' H)).natDegree < p
theorem jointOrderCertificate_of_projection_data
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (G T:Original K) (p n mCap totalG totalT cap gOuter tInner:ℕ)
   (hG:Irreducible G) (hGmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hGswapOuter:(planeMap K (swapOtherOrder order) G).natDegree ≤ gOuter)
   (hTswapInner:Polynomial.Bivariate.degreeX
     (planeMap K (swapOtherOrder order) T) ≤ tInner)
   (hnp:n < p) (hgOuterP:gOuter < p)
   (hcapP:cap < p) (hswapP:gOuter*tInner < p)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   JointOrderCertificate K order G T p:=by
 obtain ⟨order',_hor,hbase,hmixed,hpos,houter,hres⟩:=
   exists_positive_joint_characteristic_order K order P G T p n mCap
     totalG totalT cap gOuter tInner hG hGmem ht hTne hGouter hTouter
     hGsupport hTsupport hGswapOuter hTswapInner hnp hgOuterP hcapP
     hswapP hbudget
 exact ⟨order',hbase,hmixed,hpos,houter,hres⟩
private def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
private def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
private def familySummary {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem finite_separable_finrank_bound_of_joint_certificate
   (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
   (ht:Transcendental K (coordinate K P (order 0)))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=hcertificate
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤
         originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,
   hbudget] at hresult
 exact hresult
theorem finite_separable_sum_finrank_bound_of_joint_certificate
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=hcertificate
 have ht':∀ i,Transcendental K (coordinate K (P i) (order' 0)):=by
   intro i
   simpa only [hbase] using ht i
 have hresult:
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
       (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
         originalMixedDegree K order' G H:=by
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
   obtain ⟨hfields,hbound⟩:=actual_finite_separable_sum_finrank_bound
     K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfields,hbound.trans (plane_budget_le_original K order' G H)⟩
 have halg:
     (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
   funext i
   exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
     hbase (ht' i) (ht i)
 change familySummary K P
   (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
 rw [halg,hbudget] at hresult
 exact hresult
theorem sum_actualCoordinateDegree_le_of_joint_certificate
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (order:Fin 3 ≃ Fin 3)
   (hinj:Function.Injective P) (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hcertificate:JointOrderCertificate K order G H p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤
     originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s => P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i) ≤ originalMixedDegree K order G H:=by
   have h:=finite_separable_sum_finrank_bound_of_joint_certificate
     K order (fun i:s => P i) (fun i => i.2) hinj' p G H hG
     (fun i => hGmem i) (fun i => hHmem i) hproper hcertificate
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s
       (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
theorem finite_separable_at_of_original_coordinate_gate
   (P:Ideal (Original K)) [P.IsPrime] (i:Fin 3)
   (hi:Transcendental K (coordinate K P i))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:coordinateMixedDegree K G H i < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 change fieldsSummary K P (rationalBaseAlgebra K P i hi)
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
theorem projectionsFiniteSeparable_of_joint_R
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ProjectionsFiniteSeparable K P:=by
 intro i hi
 by_cases hiR:i=(1:Fin 3)
 · subst i
   have ht:Transcendental K
       (coordinate K P ((Equiv.swap (0:Fin 3) 1) 0)):=by
     have hbase:(Equiv.swap (0:Fin 3) 1) 0=(1:Fin 3):=by decide
     rw [hbase]
     exact hi
   have h:=finite_separable_finrank_bound_of_joint_certificate K
     (Equiv.swap (0:Fin 3) 1) P ht p G H hG hGmem hHmem hproper hjoint
   exact ⟨h.1,h.2.1⟩
 · have hother:i=(0:Fin 3)∨i=(2:Fin 3):=by
     fin_cases i <;> simp_all
   rcases hother with rfl | rfl
   · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
       hG hGmem hHmem hproper hdegree hmixedY
   · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
       hG hGmem hHmem hproper hdegree hmixedZ
theorem projectionsFiniteSeparable_of_joint_R_provider
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p]
   (G H:Original K) (hG:Irreducible G)
   (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:Transcendental K (coordinate K P 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ProjectionsFiniteSeparable K P:=by
 intro i hi
 by_cases hiR:i=(1:Fin 3)
 · subst i
   exact projectionsFiniteSeparable_of_joint_R K P p G H hG hGmem hHmem
     hproper hdegree hmixedY hmixedZ (hjoint hi) 1 hi
 · have hother:i=(0:Fin 3)∨i=(2:Fin 3):=by
     fin_cases i <;> simp_all
   rcases hother with rfl | rfl
   · exact finite_separable_at_of_original_coordinate_gate K P 0 hi p G H
       hG hGmem hHmem hproper hdegree hmixedY
   · exact finite_separable_at_of_original_coordinate_gate K P 2 hi p G H
       hG hGmem hHmem hproper hdegree hmixedZ
theorem sum_actualCoordinateDegree_at_R_le_of_joint_certificate
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   (∑ i,actualCoordinateDegree K (P i) 1) ≤
     coordinateMixedDegree K G H 1:=by
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using
   (sum_actualCoordinateDegree_le_of_joint_certificate K P
     (Equiv.swap (0:Fin 3) 1) hinj p G H hG hGmem hHmem hproper hjoint)
theorem sum_actualCoordinateDegree_at_R_le_of_joint_provider
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hjoint:∀ i,Transcendental K (coordinate K (P i) 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   (∑ i,actualCoordinateDegree K (P i) 1) ≤
     coordinateMixedDegree K G H 1:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) 1)}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) 1 i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hrewrite:(∑ i,actualCoordinateDegree K (P i) 1)=∑ i:s,D i:=by
   apply Finset.sum_congr_set s
     (fun i => actualCoordinateDegree K (P i) 1) D
   · intro i hi
     exact actualCoordinateDegree_of_transcendental K (P i) 1 hi
   · intro i hi
     change ¬ Transcendental K (coordinate K (P i) 1) at hi
     exact dif_neg hi
 rw [hrewrite]
 by_cases hs:Nonempty s
 · let i₀:s:=Classical.choice hs
   have hcert:=hjoint i₀ i₀.2
   have hinj':Function.Injective (fun i:s => P i):=by
     intro i j h
     apply Subtype.ext
     exact hinj h
   have hbound:=finite_separable_sum_finrank_bound_of_joint_certificate K
     (Equiv.swap (0:Fin 3) 1) (fun i:s => P i)
     (fun i => by
       have hbase:(Equiv.swap (0:Fin 3) 1) 0=(1:Fin 3):=by decide
       rw [hbase]
       exact i.2)
     hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper hcert
   have hbound':=hbound.2
   change (∑ i:s,D i) ≤
     originalMixedDegree K (Equiv.swap (0:Fin 3) 1) G H at hbound'
   simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using hbound'
 · letI:IsEmpty s:=⟨fun i => hs ⟨i⟩⟩
   simp
theorem sum_actualCoordinateDegree_at_le_of_joint_R
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤
     coordinateMixedDegree K G H j:=by
 intro j
 fin_cases j
 · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
     hproper hdegree hmixedY
 · exact sum_actualCoordinateDegree_at_R_le_of_joint_certificate K P hinj p
     G H hG hGmem hHmem hproper hjoint
 · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
     hproper hdegree hmixedZ
theorem sum_actualCoordinateDegree_at_le_of_joint_R_provider
   {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime] (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K) (hG:Irreducible G)
   (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree K G H 0 < p)
   (hmixedZ:coordinateMixedDegree K G H 2 < p)
   (hjoint:∀ i,Transcendental K (coordinate K (P i) 1) →
     JointOrderCertificate K (Equiv.swap 0 1) G H p):
   ∀ j,(∑ i,actualCoordinateDegree K (P i) j) ≤
     coordinateMixedDegree K G H j:=by
 intro j
 fin_cases j
 · exact sum_actualCoordinateDegree_at_le K P hinj 0 p G H hG hGmem hHmem
     hproper hdegree hmixedY
 · exact sum_actualCoordinateDegree_at_R_le_of_joint_provider K P hinj p
     G H hG hGmem hHmem hproper hjoint
 · exact sum_actualCoordinateDegree_at_le K P hinj 2 p G H hG hGmem hHmem
     hproper hdegree hmixedZ
end
end ProximityPrize.SubmissionLower.RCN003
end PackedLegacy_Y

/-! Packed from ProximityPrize.SubmissionLower.K8. -/
section PackedLegacy_K8
namespace ProximityPrize.SubmissionLower.RCN176
open RCN002 RCN007 RCN004 RCN001 RCN003 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
def JointRProvider (G T:MvPolynomial (Fin 3) Ω) (p:ℕ):Prop:=
 ∀ (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime],G∈P →
   Transcendental Ω (coordinate Ω P 1) →
     JointOrderCertificate Ω (Equiv.swap 0 1) G T p
theorem proper_cut_seed_bound_of_projection_sum_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i):
   Γ.card*(a-w) ≤ (nodes.card-w)*(∑ i,cap i*budget i)+
     (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have htmem:=regularComponent_T_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Ω C.1:=
     projectionsFiniteSeparable_of_joint_R_provider Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hmixedY hmixedZ (hjoint C.1 hgmem)
   exact prime_seed_incidence_sharp φ C.1 hproj
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolution γ (hsub hγ))
     (fun γ hγ => hregular γ (hsub hγ))
     (fun γ hγ => componentSeeds_on_prime Ω G T H Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem regularComponents_degree_budget_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬ G∣T)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p):
   ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 letI:∀ C:RegularComponent Ω G T (regularitySurface φ F),C.1.IsPrime:=
   fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
 exact sum_actualCoordinateDegree_at_le_of_joint_R_provider Ω
   (fun C:RegularComponent Ω G T (regularitySurface φ F) => C.1)
   Subtype.val_injective p G T hG
   (regularComponent_G_mem Ω G T (regularitySurface φ F))
   (regularComponent_T_mem Ω G T (regularitySurface φ F))
   hproper hGdegree hmixedY hmixedZ
   (fun C htr => hjoint C.1
     (regularComponent_G_mem Ω G T (regularitySurface φ F) C) htr)
theorem proper_cut_seed_bound_joint_R
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:coordinateMixedDegree Ω G T 0 < p)
   (hmixedZ:coordinateMixedDegree Ω G T 2 < p)
   (hjoint:JointRProvider G T p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,cap i*coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=
 proper_cut_seed_bound_of_projection_sum_joint_R φ F G T hG hdiv hproper
   selected Γ nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree
   hmixedY hmixedZ hjoint hdegree hsolution hregular hGpoint hTpoint
   hagreement hnoPencil cap (coordinateMixedDegree Ω G T) hcap
   (regularComponents_degree_budget_joint_R φ F G T p hG hproper
     hGdegree hmixedY hmixedZ hjoint)
end
end ProximityPrize.SubmissionLower.RCN176
end PackedLegacy_K8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier10 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.K9. -/
section PackedLegacy_K9
namespace ProximityPrize.SubmissionLower.RCN177
open scoped BigOperators
open RCN174 RCN081 RCN313
 RCN136
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def seedDegree (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree seedWeights P
theorem seedDegree_mul_le (P Q:Poly4 K):
   seedDegree (P*Q) ≤ seedDegree P+seedDegree Q:=by
 unfold seedDegree
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_mul_le (4:Fin 5)
     (weightedLift K seedWeights P) (weightedLift K seedWeights Q)
theorem seedDegree_add_le (P Q:Poly4 K):
   seedDegree (P+Q) ≤ max (seedDegree P) (seedDegree Q):=by
 unfold seedDegree
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_add_le (4:Fin 5)
     (weightedLift K seedWeights P) (weightedLift K seedWeights Q)
theorem seedDegree_sub_le (P Q:Poly4 K):
   seedDegree (P-Q) ≤ max (seedDegree P) (seedDegree Q):=by
 unfold seedDegree
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (4:Fin 5)
     (weightedLift K seedWeights P) (weightedLift K seedWeights Q)
@[simp] theorem seedDegree_neg (P:Poly4 K):
   seedDegree (-P)=seedDegree P:=by
 unfold seedDegree
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
theorem seedDegree_pow_le (P:Poly4 K) (n:ℕ):
   seedDegree (P^n) ≤ n*seedDegree P:=by
 unfold seedDegree
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K seedWeights P) n
theorem seedDegree_C (c:K):seedDegree (MvPolynomial.C c:Poly4 K)=0:=by
 unfold seedDegree MvPolynomial.weightedTotalDegree
 simp
theorem seedDegree_X (i:Fin 4):
   seedDegree (MvPolynomial.X i:Poly4 K)=seedWeights i:=by
 unfold seedDegree MvPolynomial.weightedTotalDegree
 simp [MvPolynomial.support_X,Finsupp.weight_single]
theorem seedDegree_natCast (n:ℕ):seedDegree (n:Poly4 K)=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),seedDegree_C]
theorem seedDegree_pderiv_le (P:Poly4 K) (i:Fin 4):
   seedDegree (MvPolynomial.pderiv i P) ≤ seedDegree P:=by
 apply (weightedTotalDegree_le_iff seedWeights _ _).mpr
 intro e he
 have hd:=support_before_pderiv i P e he
 have hmono:Finsupp.weight seedWeights e ≤
     Finsupp.weight seedWeights (e+Finsupp.single i 1):=by
   rw [map_add]
   exact Nat.le_add_right _ _
 exact hmono.trans (MvPolynomial.le_weightedTotalDegree seedWeights hd)
theorem seedDegree_sum_le (I:Finset ℕ) (f:ℕ → Poly4 K) (a:ℕ)
   (hf:∀ i∈I,seedDegree (f i) ≤ a):
   seedDegree (∑ i∈I,f i) ≤ a:=by
 unfold seedDegree
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => weightedLift K seedWeights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem seedDegree_polyH_le (F:Poly4 K):
   seedDegree (polyH K F) ≤ seedDegree F:=
 seedDegree_pderiv_le F 2
theorem seedDegree_polyG_le (F:Poly4 K):
   seedDegree (polyG K F) ≤ seedDegree F:=by
 unfold polyG
 have hX:=seedDegree_pderiv_le F 0
 have hY:=seedDegree_pderiv_le F 1
 have hR:seedDegree (MvPolynomial.X (2:Fin 4):Poly4 K)=0:=by
   simp [seedDegree_X,seedWeights]
 have hm:=seedDegree_mul_le
   (MvPolynomial.X (2:Fin 4):Poly4 K) (MvPolynomial.pderiv 1 F)
 rw [hR,zero_add] at hm
 have hadd:=(seedDegree_add_le (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)).trans
     (max_le hX (hm.trans hY))
 rw [seedDegree_neg]
 exact hadd
theorem numeratorStep_seedDegree_le
   (F M:Poly4 K) (b a L:ℕ)
   (hF:seedDegree F ≤ L) (hM:seedDegree M ≤ a):
   seedDegree (numeratorStep K F b M) ≤ a+2*L:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 have hR:seedDegree R ≤ 0:=by simp [R,seedDegree_X,seedWeights]
 have hH:seedDegree H ≤ L:=(seedDegree_polyH_le F).trans hF
 have hG:seedDegree G ≤ L:=(seedDegree_polyG_le F).trans hF
 have hH2:=(seedDegree_pow_le H 2).trans (Nat.mul_le_mul_left 2 hH)
 have hMX:seedDegree (MvPolynomial.pderiv 0 M) ≤ a:=
   (seedDegree_pderiv_le M 0).trans hM
 have hMY:seedDegree (MvPolynomial.pderiv 1 M) ≤ a:=
   (seedDegree_pderiv_le M 1).trans hM
 have hMR:seedDegree (MvPolynomial.pderiv 2 M) ≤ a:=
   (seedDegree_pderiv_le M 2).trans hM
 have hHX:seedDegree (MvPolynomial.pderiv 0 H) ≤ L:=
   (seedDegree_pderiv_le H 0).trans hH
 have hHY:seedDegree (MvPolynomial.pderiv 1 H) ≤ L:=
   (seedDegree_pderiv_le H 1).trans hH
 have hHR:seedDegree (MvPolynomial.pderiv 2 H) ≤ L:=
   (seedDegree_pderiv_le H 2).trans hH
 have h1:seedDegree (H^2*MvPolynomial.pderiv 0 M) ≤ a+2*L:=by
   have hh:=seedDegree_mul_le (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have h2:seedDegree (R*H^2*MvPolynomial.pderiv 1 M) ≤ a+2*L:=by
   have hh1:=seedDegree_mul_le R (H^2)
   have hh2:=seedDegree_mul_le (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have h3:seedDegree (G*H*MvPolynomial.pderiv 2 M) ≤ a+2*L:=by
   have hh1:=seedDegree_mul_le G H
   have hh2:=seedDegree_mul_le (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hbx:seedDegree (H*MvPolynomial.pderiv 0 H) ≤ 2*L:=by
   have hh:=seedDegree_mul_le H (MvPolynomial.pderiv 0 H)
   omega
 have hby:seedDegree (R*H*MvPolynomial.pderiv 1 H) ≤ 2*L:=by
   have hh1:=seedDegree_mul_le R H
   have hh2:=seedDegree_mul_le (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hbr:seedDegree (G*MvPolynomial.pderiv 2 H) ≤ 2*L:=by
   have hh:=seedDegree_mul_le G (MvPolynomial.pderiv 2 H)
   omega
 have hbrace:seedDegree
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ 2*L:=by
   exact (seedDegree_add_le _ _).trans
     (max_le ((seedDegree_add_le _ _).trans (max_le hbx hby)) hbr)
 have hn:seedDegree (((2*b:ℕ):Poly4 K)) ≤ 0:=by
   rw [seedDegree_natCast]
 have hnM:seedDegree (((2*b:ℕ):Poly4 K)*M) ≤ a:=by
   have hh:=seedDegree_mul_le (((2*b:ℕ):Poly4 K)) M
   omega
 have h4:seedDegree (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ a+2*L:=by
   have hh:=seedDegree_mul_le (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change seedDegree
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ a+2*L
 exact (seedDegree_sub_le _ _).trans
   (max_le ((seedDegree_add_le _ _).trans
     (max_le ((seedDegree_add_le _ _).trans (max_le h1 h2)) h3)) h4)
theorem numerator_seedDegree_le
   (F:Poly4 K) (L:ℕ) (hF:seedDegree F ≤ L) (b:ℕ):
   seedDegree (numerator K F b) ≤ 1+2*b*L:=by
 induction b with
 | zero =>
     simp [numerator_zero,seedDegree_X,seedWeights]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_seedDegree_le F (numerator K F b) b
       (1+2*b*L) L hF ih
     convert hh using 1 <;> ring
theorem numerator_joint_seed_cap
   (F:Poly4 K) (L b:ℕ) (hF:seedDegree F ≤ L):
   ∀ d∈(numerator K F b).support,
     d 1+d 3 ≤ 1+2*b*L:=by
 intro d hd
 rw [←seed_weight]
 exact (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans
   (numerator_seedDegree_le F L hF b)
theorem surfaceMap_numerator_joint_seed_cap
   (φ:Polynomial K →+*Ω) (F:Poly4 K) (L b:ℕ)
   (hF:seedDegree F ≤ L):
   ∀ d∈(surfaceMap φ (numerator K F b)).support,
     d 0+d 2 ≤ 1+2*b*L:=
 surfaceMap_joint_seed_cap φ _ _ (numerator_joint_seed_cap F L b hF)
theorem shiftedX_seedDegree_le (x:K):
   seedDegree (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) ≤ 0:=by
 exact (seedDegree_sub_le _ _).trans (max_le (by simp [seedDegree_C])
   (by simp [seedDegree_X,seedWeights]))
theorem commonNumeratorTerm_seedDegree_le
   (F:Poly4 K) (L w j:ℕ) (hj:j ≤ w)
   (hF:seedDegree F ≤ L) (c:ℕ → K) (x:K):
   seedDegree (commonNumeratorTerm F w c x j) ≤ 1+2*w*L:=by
 have hM:=numerator_seedDegree_le F L hF j
 have hC:seedDegree (MvPolynomial.C (c j):Poly4 K) ≤ 0:=by
   simp [seedDegree_C]
 have hCM:=seedDegree_mul_le (MvPolynomial.C (c j):Poly4 K) (numerator K F j)
 have hH:=(seedDegree_polyH_le F).trans hF
 have hHP:=(seedDegree_pow_le (polyH K F) (2*(w-j))).trans
   (Nat.mul_le_mul_left (2*(w-j)) hH)
 have hXP:=(seedDegree_pow_le
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j).trans
     (Nat.mul_le_mul_left j (shiftedX_seedDegree_le x))
 have h1:=seedDegree_mul_le
   (MvPolynomial.C (c j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=seedDegree_mul_le
   (MvPolynomial.C (c j)*numerator K F j*polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 have hw:j+(w-j)=w:=by omega
 dsimp [commonNumeratorTerm]
 have hCMcap:seedDegree
     (MvPolynomial.C (c j)*numerator K F j) ≤ 1+2*j*L:=by
   exact hCM.trans (Nat.add_le_add hC hM) |>.trans (by omega)
 have h1cap:seedDegree
     (MvPolynomial.C (c j)*numerator K F j*polyH K F^(2*(w-j))) ≤
     (1+2*j*L)+2*(w-j)*L:=
   h1.trans (Nat.add_le_add hCMcap hHP)
 have hterm:=h2.trans (Nat.add_le_add h1cap hXP)
 calc
   seedDegree
       (MvPolynomial.C (c j)*numerator K F j*polyH K F^(2*(w-j))*
         (MvPolynomial.C x-MvPolynomial.X 0)^j) ≤
       ((1+2*j*L)+2*(w-j)*L)+j*0:=hterm
   _=1+2*(j+(w-j))*L:=by ring
   _=1+2*w*L:=by rw [hw]
theorem clearedTaylorNumerator_seedDegree_le
   (F:Poly4 K) (L w:ℕ) (hF:seedDegree F ≤ L)
   (c:ℕ → K) (x:K):
   seedDegree (clearedTaylorNumerator F w c x) ≤ 1+2*w*L:=by
 unfold clearedTaylorNumerator
 apply seedDegree_sum_le
 intro j hj
 exact commonNumeratorTerm_seedDegree_le F L w j
   (by have hh:=Finset.mem_range.mp hj;omega) hF c x
theorem affineSeedPolynomial_seedDegree_le (u₀ u₁:K):
   seedDegree (affineSeedPolynomial u₀ u₁) ≤ 1:=by
 unfold affineSeedPolynomial
 have hC0:seedDegree (MvPolynomial.C u₀:Poly4 K) ≤ 0:=by simp [seedDegree_C]
 have hZ:seedDegree (MvPolynomial.X (3:Fin 4):Poly4 K) ≤ 1:=by
   simp [seedDegree_X,seedWeights]
 have hC1:seedDegree (MvPolynomial.C u₁:Poly4 K) ≤ 0:=by simp [seedDegree_C]
 have hm:=seedDegree_mul_le (MvPolynomial.X (3:Fin 4):Poly4 K)
   (MvPolynomial.C u₁)
 exact (seedDegree_add_le _ _).trans (max_le (hC0.trans (by omega)) (by omega))
theorem agreementNumerator_seedDegree_le
   (F:Poly4 K) (L w:ℕ) (hF:seedDegree F ≤ L)
   (c:ℕ → K) (x u₀ u₁:K):
   seedDegree (agreementNumerator F w c x u₀ u₁) ≤ 1+2*w*L:=by
 unfold agreementNumerator
 have ht:=clearedTaylorNumerator_seedDegree_le F L w hF c x
 have ha:=affineSeedPolynomial_seedDegree_le u₀ u₁
 have hH:=(seedDegree_polyH_le F).trans hF
 have hp:=(seedDegree_pow_le (polyH K F) (2*w)).trans
   (Nat.mul_le_mul_left (2*w) hH)
 have hm:=seedDegree_mul_le (affineSeedPolynomial u₀ u₁) (polyH K F^(2*w))
 exact (seedDegree_sub_le _ _).trans (max_le ht (by omega))
theorem agreementNumerator_joint_seed_cap
   (F:Poly4 K) (L w:ℕ) (hF:seedDegree F ≤ L)
   (c:ℕ → K) (x u₀ u₁:K):
   ∀ d∈(agreementNumerator F w c x u₀ u₁).support,
     d 1+d 3 ≤ 1+2*w*L:=by
 intro d hd
 rw [←seed_weight]
 exact (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans
   (agreementNumerator_seedDegree_le F L w hF c x u₀ u₁)
theorem surfaceMap_agreement_joint_seed_cap
   (φ:Polynomial K →+*Ω) (F:Poly4 K) (L w:ℕ)
   (hF:seedDegree F ≤ L) (c:ℕ → K) (x u₀ u₁:K):
   ∀ d∈(surfaceMap φ (agreementNumerator F w c x u₀ u₁)).support,
     d 0+d 2 ≤ 1+2*w*L:=
 surfaceMap_joint_seed_cap φ _ _
   (agreementNumerator_joint_seed_cap F L w hF c x u₀ u₁)
end
end ProximityPrize.SubmissionLower.RCN177
end PackedLegacy_K9

/-! Packed from ProximityPrize.SubmissionLower.L0. -/
section PackedLegacy_L0
namespace ProximityPrize.SubmissionLower.RCN178
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001 RCN174 RCN306 RCN176 RCN177 RCN003 RCN012 RCN011 RCN009 RCN013 RCN371
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem rationalMap_joint_support_of_dvd
   (G Q:MvPolynomial (Fin 3) Ω) (cap:ℕ)
   (hdiv:G∣Q) (hQne:Q≠0)
   (hQsupport:∀ d∈Q.support,d 0+d 2 ≤ cap):
   ∀ e∈(rationalMap Ω (Equiv.swap 0 1) G).support,
     e 0+e 1 ≤ cap:=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
 let g:=rationalMap Ω order G
 let q:=rationalMap Ω order Q
 have hqne:q≠0:=rationalMap_ne_zero Ω order Q hQne
 have hgdvd:g∣q:=map_dvd (rationalMap Ω order) hdiv
 have hqSupport:∀ e∈q.support,e 0+e 1 ≤ cap:=by
   exact original_joint_support_to_rationalMap Ω Q cap hQsupport
 have hqTotal:q.totalDegree ≤ cap:=by
   unfold MvPolynomial.totalDegree
   apply Finset.sup_le
   intro e he
   simpa [Finsupp.sum_fintype,Fin.sum_univ_two] using hqSupport e he
 have hgTotal:g.totalDegree ≤ cap:=
   (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hgdvd hqne).trans hqTotal
 intro e he
 have hweight:=(MvPolynomial.le_totalDegree he).trans hgTotal
 simpa [Finsupp.sum_fintype,Fin.sum_univ_two] using hweight
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem whole_surface_seed_bound_joint_R
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F)
   (hr:0 < G.degreeOf 1)
   (hHproper:¬ G∣surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:∀ i∈nodes,
     coordinateMixedDegree Ω G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 0 < p)
   (hmixedZ:∀ i∈nodes,
     coordinateMixedDegree Ω G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 2 < p)
   (hjoint:∀ i∈nodes,
     ¬ G∣agreementPolynomial φ F w (x i) (u₀ i) (u₁ i) →
     JointRProvider G (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (E:DegreeVector)
   (hcap:∀ i∈nodes,
     HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) E):
   Γ.card*(a-w)^2 ≤
     (nodes.card-w)*fiberNumerator nodes.card w a e (degreeVector G) E:=by
 classical
 let P:Ideal (MvPolynomial (Fin 3) Ω):=Ideal.span {G}
 letI:P.IsPrime:=Ideal.isPrime_span_singleton_of_prime hG.prime
 have hFmem:surfaceMap φ F∈P:=Ideal.mem_span_singleton.mpr hdiv
 have hHmem:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P:=by
   intro h
   exact hHproper (Ideal.mem_span_singleton.mp h)
 let identities:=identityNodes φ P F nodes x u₀ u₁ w
 have hidentities:identities ⊆ nodes:=identityNodes_subset φ P F nodes x u₀ u₁ w
 have hicard:identities.card ≤ w:=
   identityNodes_card_le_of_r_dependent_principal φ P F hFmem hHmem
     nodes x u₀ u₁ w hw hinj G rfl hr
 apply scaled_sharp_incidence_bound
   (fun γ i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
   Γ nodes identities a w (fiberNumerator nodes.card w a e (degreeVector G) E)
   hidentities hicard hwa han hagreement
 intro i hi
 obtain ⟨hinode,hnotid⟩:=Finset.mem_sdiff.mp hi
 let T:=agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
 have hproper:¬ G∣T:=by
   intro hd
   apply hnotid
   exact Finset.mem_filter.mpr ⟨hinode,Ideal.mem_span_singleton.mpr hd⟩
 let fiber:=Γ.filter (fun γ => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
 have hsub:fiber ⊆ Γ:=Finset.filter_subset _ _
 have hTpoint:∀ γ∈fiber,MvPolynomial.eval (selectedPoint φ selected γ) T=0:=by
   intro γ hγ
   have hΓ:=hsub hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) (x i) (u₀ i) (u₁ i)).mpr
       (Finset.mem_filter.mp hγ).2
 have hcount:=proper_cut_seed_bound_joint_R φ F G T hG hdiv hproper selected fiber
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree
   (hmixedY i hinode) (hmixedZ i hinode) (hjoint i hinode hproper)
   (fun γ hγ => hdegree γ (hsub hγ))
   (fun γ hγ => hsolution γ (hsub hγ))
   (fun γ hγ => hregular γ (hsub hγ))
   (fun γ hγ => hGpoint γ (hsub hγ)) hTpoint
   (fun γ hγ => hagreement γ (hsub hγ))
   (noLargeSelectedPencil_mono selected Γ fiber w e hsub hnoPencil)
   (capAt E) hcap
 have hδ (j:Fin 3):coordinateMixedDegree Ω G T j ≤
     mixed (degreeVector G) E (unitAt j):=
   coordinateMixedDegree_le_caps G T (degreeVector G) E (degreeVector_hasCaps G)
     (hcap i hinode) j
 have hsum:(∑ j,capAt E j*coordinateMixedDegree Ω G T j) ≤
     mixed (degreeVector G) E E:=by
   calc
     _ ≤ ∑ j,capAt E j*mixed (degreeVector G) E (unitAt j):=by
       apply Finset.sum_le_sum
       intro j _
       exact Nat.mul_le_mul_left _ (hδ j)
     _=_:=mixed_cap_sum (degreeVector G) E E
 exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hsum)
   (Nat.mul_le_mul_left _ (hδ 2)))
theorem whole_surface_seed_bound_fixed_joint_R
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F)
   (hr:0 < G.degreeOf 1)
   (hHproper:¬ G∣surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hGcaps:HasCaps G RCN242.surfaceVector)
   (hGjoint:∀ e∈(rationalMap Ω (Equiv.swap 0 1) G).support,
     e 0+e 1 ≤ seedTotalCap)
   (hFseed:seedDegree F ≤ seedTotalCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP Ω prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter
       (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap^2 ≤ wholeNumerator (degreeVector G):=by
 have hcap (i:ι):
     HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) agreementVector:=
   fixed_agreement_caps φ F hbox hY hR hZ (x i) (u₀ i) (u₁ i)
 have hGdegree:∀ j:Fin 3,G.degreeOf j < prime:=
   fun j => (hGcaps j).trans_lt (fixed_surface_caps_below_characteristic j)
 have hmixedY (i:ι):coordinateMixedDegree Ω G
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 0 < prime:=by
   simpa only [coordinateMixedDegree_zero] using
     (fixed_agreement_nonR_characteristic_gates G _ hGcaps (hcap i)).2.1
 have hmixedZ (i:ι):coordinateMixedDegree Ω G
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 2 < prime:=by
   simpa only [coordinateMixedDegree_two] using
     (fixed_agreement_nonR_characteristic_gates G _ hGcaps (hcap i)).2.2
 have hjoint (i:ι)
     (hproper:¬ G∣agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)):
     JointRProvider G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) prime:=by
   intro P _ hGmem ht
   let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
   let T:=agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
   have hTne:T≠0:=by
     intro hzero
     apply hproper
     change G∣T
     rw [hzero]
     exact dvd_zero G
   have hG0:G.degreeOf 0 ≤ 25:=by
     simpa [RCN242.surfaceVector,capAt,yCap,weightedCap,
       RCN051.multiplicity,agreements,w] using hGcaps 0
   have hG2:G.degreeOf 2 ≤ 176:=by
     simpa [RCN242.surfaceVector,capAt,seedTotalCap] using hGcaps 2
   have hT0:T.degreeOf 0 ≤ 6422480:=by
     have h:=hcap i 0
     change T.degreeOf 0 ≤ capAt agreementVector 0 at h
     norm_num [capAt,agreementVector,yCap,weightedCap,
       RCN051.multiplicity,agreements,w] at h
     exact h
   have hGouter:(planeMap Ω order G).natDegree ≤ 25:=by
     exact (planeMap_natDegree_le Ω order G).trans (by simpa [order] using hG0)
   have hTouter:(planeMap Ω order T).natDegree ≤ 6422480:=by
     exact (planeMap_natDegree_le Ω order T).trans (by simpa [order] using hT0)
   have hGsupport:∀ d∈(rationalMap Ω order G).support,
       d 0+d 1 ≤ 176:=by
     simpa [order,seedTotalCap] using hGjoint
   have hTsupport:∀ d∈(rationalMap Ω order T).support,
       d 0+d 1 ≤ 46136993:=by
     have h:=surfaceMap_agreement_joint_seed_cap φ F seedTotalCap w hFseed
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     norm_num [seedTotalCap,w] at h
     simpa [order,T,agreementPolynomial] using
       (original_joint_support_to_rationalMap Ω T 46136993 (by
         simpa [T,agreementPolynomial,w] using h))
   have hGswapOuter:
       (planeMap Ω (swapOtherOrder order) G).natDegree ≤ 176:=by
     exact (planeMap_natDegree_le Ω (swapOtherOrder order) G).trans
       (by simpa [order,Equiv.swap_apply_def] using hG2)
   have hTswapInner:Polynomial.Bivariate.degreeX
       (planeMap Ω (swapOtherOrder order) T) ≤ 6422529:=by
     have h:=(planeMap_degreeX_le Ω (swapOtherOrder order) T).trans hT0
     exact h.trans (by norm_num)
   exact jointOrderCertificate_of_projection_data Ω order P G T prime
     25 6422480 176 46136993 2123219305 176 6422529 hG hGmem ht hTne
     hGouter hTouter hGsupport hTsupport hGswapOuter hTswapInner
     (by norm_num [prime]) (by norm_num [prime])
     (by simpa [prime] using agreement_6464_sharpY_trapezoid_cap_below_characteristic)
     (by simpa [prime] using swapped_6464_sharpY_cap_below_characteristic)
     agreement_6464_sharpY_trapezoid_budget
 have hcount:=whole_surface_seed_bound_joint_R φ F G hG hdiv hr hHproper
   selected Γ nodes x u₀ u₁ hinj prime w agreements errors
   (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,agreements])
   (by rw [hnodes];norm_num [agreements,n]) hGdegree
   (fun i _ => hmixedY i) (fun i _ => hmixedZ i)
   (fun i _ hproper => hjoint i hproper)
   hdegree hsolution hregular hGpoint hagreement hnoPencil agreementVector
   (fun i _ => hcap i)
 calc
   Γ.card*gap^2=Γ.card*(agreements-w)^2:=rfl
   _ ≤ (nodes.card-w)*fiberNumerator nodes.card w agreements errors
       (degreeVector G) agreementVector:=hcount
   _=wholeNumerator (degreeVector G):=by
     rw [hnodes]
     unfold fiberNumerator wholeNumerator gap
     ring
end
end ProximityPrize.SubmissionLower.RCN178
end PackedLegacy_L0

/-! Packed from ProximityPrize.SubmissionLower.Z9. -/
section PackedLegacy_Z9
namespace ProximityPrize.SubmissionLower.RCN222
open scoped Classical BigOperators
open RCN051 RCN068 RCN070 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN306 RCN238 RCN243 RCN231 RCN174 RCN319 RCN178 RCN177
noncomputable section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def originalDegreeVector (F:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨F.degreeOf 1,F.degreeOf 2,F.degreeOf 3⟩
theorem selectedPoint_eq_initialPoint (selected:K → Polynomial K) (γ:K):
   selectedPoint (polynomialEmbedding K) selected γ=
     fun i:Fin 3 => initialPoint K (selected γ) γ i.succ:=rfl
theorem selectedPoint_surface_evaluation
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_eq_initialPoint]
 simpa only [canonical_geometricSurfaceMap] using
   eval_at_actual_generic_initial_point K (selected γ) γ F
theorem selectedPoint_regular_of_specialization
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K)
   (hregular:specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
     (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
       (selected γ) γ ((polynomialEmbedding K) Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (initialPoint_regular_iff K F (selected γ) γ).mpr hregular
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 {g:MvPolynomial (Fin 3) (GenericField K)//g∈surfaceFactors (polynomialEmbedding K) F}
def geometricSeeds (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):Finset K:=by
 classical
 exact Γ.filter (fun γ =>
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) g.1=0)
theorem geometricSeeds_subset
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):geometricSeeds K F selected Γ g ⊆ Γ:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricSeeds
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K → Polynomial K) (Γ:Finset K)
   (hsolutions:∀ γ∈Γ,specialization K (selected γ) γ F=0):
   Γ.card ≤ ∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card:=by
 classical
 have hcover:Γ ⊆ Finset.univ.biUnion (geometricSeeds K F selected Γ):=by
   intro γ hγ
   have hz:MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [selectedPoint_surface_evaluation,hsolutions γ hγ,map_zero]
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (selectedPoint (polynomialEmbedding K) selected γ) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hγ,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometricFactor_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (g:GeometricFactor K F) (i:Fin 3):
   g.1.degreeOf i ≤ F.degreeOf i.succ:=by
 have hdiv:=(surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).2
 exact (coordinate_degree_le_of_dvd i g.1 _ hdiv
   (surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K) F hF)).trans
     (surfaceMap_degreeOf_le (polynomialEmbedding K) F i)
theorem geometricFactor_sum_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g:GeometricFactor K F,g.1.degreeOf i) ≤ F.degreeOf i.succ:=by
 classical
 have hb:=surfaceFactors_degree_budget (polynomialEmbedding K)
   (polynomialEmbedding_injective K) F hF i
 rw [←Finset.sum_attach (surfaceFactors (polynomialEmbedding K) F)
   (fun g => g.degreeOf i)] at hb
 simpa only [Finset.attach_eq_univ] using hb
theorem sum_wholeNumerator_geometricFactors_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,wholeNumerator (degreeVector g.1)) ≤
     wholeNumerator (originalDegreeVector K F):=by
 classical
 rw [←whole_sum (fun g:GeometricFactor K F => degreeVector g.1)]
 rw [whole_eq_dot,whole_eq_dot]
 exact dot_mono_left _ ⟨geometricFactor_sum_degree_le K F hF 0,
   geometricFactor_sum_degree_le K F hF 1,geometricFactor_sum_degree_le K F hF 2⟩
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem original_regular_seed_bound
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hRpos:0 < F.degreeOf 2)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutions:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap^2 ≤ wholeNumerator (originalDegreeVector K F):=by
 classical
 letI:CharP (GenericField K) prime:=genericField_charP K prime
 have hc:=degree_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap
   (by norm_num [w]) hbox
 have hY:F.degreeOf 1 ≤ yCap:=hc.1
 have hR:F.degreeOf 2 ≤ slopeCap:=hc.2.1
 have hZ:F.degreeOf 3 ≤ seedTotalCap:=hc.2.2
 have hFseed:seedDegree F ≤ seedTotalCap:=by
   exact ((mem_globalCoefficientBox_iff F weightedCap w seedTotalCap slopeCap
     (by norm_num [weightedCap,RCN051.multiplicity,
       agreements])).mp hbox).1
 have hsmall:F.degreeOf 2 < prime:=hR.trans_lt (by norm_num [slopeCap,prime])
 have hcount (g:GeometricFactor K F):
     (geometricSeeds K F selected Γ g).card*gap^2 ≤ wholeNumerator (degreeVector g.1):=by
   obtain ⟨hgirred,hgdiv⟩:=surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate:=geometric_factor_regular_gate K (GenericField K) F hF prime hRpos hsmall
     g.1 hgirred (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hHproper:¬ g.1∣surfaceMap (polynomialEmbedding K)
       (MvPolynomial.pderiv (2:Fin 4) F):=by
     simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
   have hgcaps:HasCaps g.1 RCN242.surfaceVector:=by
     intro i
     fin_cases i
     · exact (geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
     · exact (geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
     · exact (geometricFactor_degree_le K F hF.ne_zero g 2).trans hZ
   have hsurfaceNe:surfaceMap (polynomialEmbedding K) F≠0:=
     surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K)
       F hF.ne_zero
   have hsurfaceJoint:∀ d∈(surfaceMap (polynomialEmbedding K) F).support,
       d 0+d 2 ≤ seedTotalCap:=by
     apply surfaceMap_joint_seed_cap (polynomialEmbedding K) F seedTotalCap
     intro d hd
     rw [←seed_weight]
     exact (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hFseed
   have hgJoint:∀ e∈
       (RCN371.rationalMap (GenericField K)
         (Equiv.swap 0 1) g.1).support,
       e 0+e 1 ≤ seedTotalCap:=
     rationalMap_joint_support_of_dvd g.1
       (surfaceMap (polynomialEmbedding K) F) seedTotalCap hgdiv hsurfaceNe hsurfaceJoint
   have hsub:=geometricSeeds_subset K F selected Γ g
   exact whole_surface_seed_bound_fixed_joint_R (polynomialEmbedding K) F g.1 hgirred hgdiv
     hgate.1 hHproper hbox hgcaps hgJoint hFseed hY hR hZ
     selected (geometricSeeds K F selected Γ g)
     nodes x u₀ u₁ hinj hnodes
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolutions γ (hsub hγ))
     (fun γ hγ => selectedPoint_regular_of_specialization K F selected γ
       (hregular γ (hsub hγ)))
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w errors hsub hnoPencil)
 calc
   Γ.card*gap^2 ≤
       (∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card)*gap^2:=
     Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF.ne_zero selected Γ hsolutions)
   _=∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,wholeNumerator (degreeVector g.1):=
     Finset.sum_le_sum (fun g _ => hcount g)
   _ ≤ wholeNumerator (originalDegreeVector K F):=sum_wholeNumerator_geometricFactors_le K F hF.ne_zero
end
end ProximityPrize.SubmissionLower.RCN222
end PackedLegacy_Z9

/-! Packed from ProximityPrize.SubmissionLower.DW. -/
section PackedLegacy_DW
namespace ProximityPrize.SubmissionLower.RCN052
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def regularPairSeeds (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RegularIndex Q):Finset K:=
 Gamma.filter fun gamma↦
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=
 Gamma.filter fun gamma↦LiftedSolutionPair q.1 (selected gamma) gamma
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K):Finset K:=
 Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem regularPairSeeds_subset (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q):
   regularPairSeeds Q T selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (q:ImplicitIndex Q):
   implicitSeeds Q selected Gamma q ⊆ Gamma:=
 Finset.filter_subset _ _
theorem regularPairSeeds_data (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q)
   (gamma:K) (hgamma:gamma∈regularPairSeeds Q T selected Gamma F):
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0:=
 (Finset.mem_filter.mp hgamma).2
theorem implicitSeeds_data (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (q:ImplicitIndex Q)
   (gamma:K) (hgamma:gamma∈implicitSeeds Q selected Gamma q):
   LiftedSolutionPair q.1 (selected gamma) gamma:=
 (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
   (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K):
   (singularSeeds Q selected Gamma).card ≤
     (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
       (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
 exact (Finset.card_union_le _ _).trans
   (Nat.add_le_add_right Finset.card_biUnion_le _)
theorem card_le_regular_sum_add_singular
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p]
   (hs:1 ≤ s) (hsmall:s < p) (hw:1 ≤ w)
   (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ D w L s p hs hsmall hw
   hDw hj hjSmall hbox Gamma selected hQsolution
 let regularUnion:=Finset.univ.biUnion (regularPairSeeds Q T selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · exact Finset.mem_union_right _ (Finset.mem_union_right _ hexc)
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg,hTsolution gamma hgamma⟩⟩
     · apply Finset.mem_union_right
       apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,
         (regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem regularFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q):¬ F.1∣T:=by
 obtain ⟨hirr,hdiv,_⟩:=positiveRFactors_spec Q F.1 F.2
 intro hFT
 exact hirr.not_isUnit (hrel hdiv hFT)
theorem geometricFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) F.1):
   ¬ g∣surfaceMap (polynomialEmbedding K) T:=by
 obtain ⟨hFirr,_hFdiv,hFRpos⟩:=positiveRFactors_spec Q F.1 F.2
 obtain ⟨hgirred,hgdiv⟩:=
   surfaceFactors_spec (polynomialEmbedding K) F.1 g hg
 have hpos:0 < F.1.degreeOf 1+F.1.degreeOf 2+F.1.degreeOf 3:=by
   omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) F.1:=by
   simpa only [canonical_geometricSurfaceMap] using hgdiv
 intro hgT
 apply regularFactor_not_dvd_second Q T hrel F
 apply (geometric_factor_dvd_iff K (GenericField K) F.1 T hFirr hpos
   g hgirred hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using hgT
def regularVector (P:UnequalParameters)
   (F:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR,
   F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY,
   F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY⟩
def regularCapAt (v:RCN223.DegreeVector):Fin 3 → ℕ:=
 ![v.y,v.r,v.z]
theorem sum_coordinateMixedDegree_geometricFactors_le
   (P:UnequalParameters) (F T:MvPolynomial (Fin 4) K) (hF:F≠0)
   (hTY:T.degreeOf 1 ≤ P.rightY) (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ) (i:Fin 3):
   (∑ g:GeometricFactor K F,
     coordinateMixedDegree (GenericField K) g.1
       (surfaceMap (polynomialEmbedding K) T) i) ≤
     regularCapAt (regularVector P F) i:=by
 classical
 have hsum (j:Fin 3):
     (∑ g:GeometricFactor K F,g.1.degreeOf j) ≤ F.degreeOf j.succ:=
   geometricFactor_sum_degree_le K F hF j
 have hsum0:(∑ g:GeometricFactor K F,g.1.degreeOf 0) ≤ F.degreeOf 1:=by
   simpa using hsum 0
 have hsum1:(∑ g:GeometricFactor K F,g.1.degreeOf 1) ≤ F.degreeOf 2:=by
   simpa using hsum 1
 have hsum2:(∑ g:GeometricFactor K F,g.1.degreeOf 2) ≤ F.degreeOf 3:=by
   have h:=hsum 2
   rw [show (2:Fin 3).succ=(3:Fin 4) by decide] at h
   exact h
 have hT0:(surfaceMap (polynomialEmbedding K) T).degreeOf 0 ≤ P.rightY:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 0).trans hTY
 have hT1:(surfaceMap (polynomialEmbedding K) T).degreeOf 1 ≤ P.rightR:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 1).trans hTR
 have hT2:(surfaceMap (polynomialEmbedding K) T).degreeOf 2 ≤ P.rightZ:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 2).trans hTZ
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 1*geom.1.degreeOf 2+
         geom.1.degreeOf 1*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT1 hsum2)
       (Nat.mul_le_mul hsum1 hT2)
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 2+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum2)
       (Nat.mul_le_mul hsum0 hT2)
 · simp only [RCN001.coordinateMixedDegree_two,
     regularCapAt,regularVector,Matrix.cons_val_two]
   change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 1+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 1)) ≤
       F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum1)
       (Nat.mul_le_mul hsum0 hT1)
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hrel:IsRelPrime Q T) (F:RegularIndex Q)
   (p:ℕ) [CharP K p]
   (hFY:F.1.degreeOf 1 ≤ P.leftY)
   (hFR:F.1.degreeOf 2 ≤ P.leftR)
   (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=regularPairSeeds Q T selected Gamma F
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFspec:=positiveRFactors_spec Q F.1 F.2
 have hFne:F.1≠0:=hFspec.1.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=regularPairSeeds_subset Q T selected Gamma F
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F.1 (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   regularPairSeeds_data Q T selected Gamma F gamma hgamma
 have hcover:=card_le_sum_geometricSeeds K F.1 hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F.1):
     (geometricSeeds K F.1 selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F.1 g.1 g.2
   have hsub:=geometricSeeds_subset K F.1 selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F.1 hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F.1 selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.agreement j:=by
     have h:=surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j
     · apply hj.trans
       change P.leftAgreement.y ≤ max P.leftAgreement.y P.rightAgreement.y
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.r ≤ max P.leftAgreement.r P.rightAgreement.r
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.z ≤ max P.leftAgreement.z P.rightAgreement.z
       exact le_max_left _ _
   have hcount:=proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
     selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.agreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F.1,∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F.1,
         (geometricSeeds K F.1 selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F.1,
       (geometricSeeds K F.1 selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F.1,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*regularCapAt (regularVector P F.1) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F.1) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]
theorem all_regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hrel:IsRelPrime Q T)
   (D w L s p:ℕ) [CharP K p]
   (hbox:Q∈globalCoefficientBox K D w L s) (hwBox:1 ≤ w)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   ∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 intro F
 have hFbox:=(directFactor_data Q F.1 hQ D w L s hbox F.2).2.2
 have hFcaps:=degree_bounds_of_mem_box F.1 D w L s hwBox hFbox
 exact regularPairSeeds_bound P Q T hrel F p
   (hFcaps.1.trans (by simpa using hY))
   (hFcaps.2.1.trans hR) (hFcaps.2.2.trans hZ)
   hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
   hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u₀ u₁
   hinj hnodes hw hchar hwa han hdegree hagreement hnoPencil
def implicitVector (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):
   RCN223.DegreeVector:=
 ⟨pairYCost (K:=K) q,pairRCost (K:=K) q,pairZCost (K:=K) q⟩
theorem regularVector_budgets
   (P:UnequalParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ):
   (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z:=by
 classical
 have hb:=directFactor_input_budgets Q hQ D w L s hw hbox
 have hbY:(∑ F:RegularIndex Q,F.1.degreeOf (1:Fin 4)) ≤ (D-1)/w:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.1
 have hbR:(∑ F:RegularIndex Q,F.1.degreeOf (2:Fin 4)) ≤ s:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.1
 have hbZ:(∑ F:RegularIndex Q,F.1.degreeOf (3:Fin 4)) ≤ L:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.2
 simp only [regularVector,Finset.sum_add_distrib]
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbR.trans hR))
     (Nat.mul_le_mul_right P.rightR (hbZ.trans hZ))
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbZ.trans hZ))
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightR (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbR.trans hR))
theorem dot_sum_right {I:Type} [Fintype I]
   (v:I → RCN223.DegreeVector)
   (a:RCN223.DegreeVector):
   dot a (RCN294.sumVector v)=∑ i,dot a (v i):=by
 calc
   _=dot (RCN294.sumVector v) a:=by
     simp only [dot]
     ring
   _=∑ i,dot (v i) a:=
     RCN294.dot_sum_left v a
   _=_:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [dot]
     ring
theorem sum_regular_counts_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z)
   (hcount:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)*
       P.gap ≤ P.regularNumerator:=by
 calc
   _=∑ F:RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.agreement
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1).z:=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
       ←dot_sum_right]
     simp only [RCN294.sumVector]
   _ ≤ (P.n-P.w)*dot P.agreement P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.agreement.y hcost.1)
           (Nat.mul_le_mul_left P.agreement.r hcost.2.1))
         (Nat.mul_le_mul_left P.agreement.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=P.regularNumerator:=rfl
theorem asymmetric_stage_count_lt
   (P:UnequalParameters) (S:TightParameters)
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (p:ℕ) [CharP K p]
   (hs:1 ≤ S.s) (hsmall:S.s < p) (hw:1 ≤ S.w)
   (hDw:S.w < (2*S.s-1)*S.D)
   (hj:1 ≤ (2*S.s-1)*S.L)
   (hjSmall:(2*S.s-1)*S.L < p)
   (hbox:Q∈globalCoefficientBox K S.D S.w S.L S.s)
   (hgap:0 < P.gap) (hgapEq:S.gap=P.gap)
   (hY:(S.D-1)/S.w ≤ P.leftY)
   (hR:S.s ≤ P.leftR) (hZ:S.L ≤ P.leftZ)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0)
   (hregular:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z)
   (himplicit:∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*S.gap ≤
       (S.n-S.w)*dot S.agreement (implicitVector q.1)+
         (S.errors+1)*S.gap*(implicitVector q.1).z):
   Gamma.card < P.regularCountCap+S.countCap+1:=by
 classical
 have hcover:=card_le_regular_sum_add_singular Q T hQ S.D S.w S.L S.s p
   hs hsmall hw hDw hj hjSmall hbox selected Gamma hQsolution hTsolution
 have hdecomp:=selected_seed_decomposition Q hQ S.D S.w S.L S.s p
   hs hsmall hw hDw hj hjSmall hbox Gamma selected hQsolution
 have hregularScaled:=sum_regular_counts_bound P Q T selected Gamma
   (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
   hregular
 have hregularCap:
     (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card) ≤
       P.regularCountCap:=
   P.regular_count_le _ hgap hregularScaled
 have himplicitBudgets:
     (∑ q:ImplicitIndex Q,(implicitVector q.1).y) ≤ S.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector q.1).r) ≤
       2*S.implicitYCap*S.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector q.1).z) ≤ S.implicitYCap:=by
   constructor
   · change (∑ q∈(implicitPairSet (singularAuxiliary Q)).attach,
         pairYCost (K:=K) q.1) ≤ S.algebraicCap
     rw [Finset.sum_attach]
     simpa [implicitVector,TightParameters.algebraicCap,
       TightParameters.implicitYCap,TightParameters.kappa] using hdecomp.2.2.2.1
   constructor
   · change (∑ q∈(implicitPairSet (singularAuxiliary Q)).attach,
         pairRCost (K:=K) q.1) ≤ 2*S.implicitYCap*S.algebraicCap
     rw [Finset.sum_attach]
     simpa [implicitVector,TightParameters.algebraicCap,
       TightParameters.implicitYCap,TightParameters.kappa] using hdecomp.2.2.2.2.1
   · change (∑ q∈(implicitPairSet (singularAuxiliary Q)).attach,
         pairZCost (K:=K) q.1) ≤ S.implicitYCap
     rw [Finset.sum_attach]
     simpa [implicitVector,TightParameters.algebraicCap,
       TightParameters.implicitYCap,TightParameters.kappa] using hdecomp.2.2.2.2.2
 have hexceptions:
     (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
       2*S.algebraicCap^2:=by
   simpa [TightParameters.algebraicCap,TightParameters.kappa] using hdecomp.1
 have hsingularScaled:=S.with_exceptions_bound
   (fun q:ImplicitIndex Q↦(implicitSeeds Q selected Gamma q).card)
   (fun q:ImplicitIndex Q↦implicitVector q.1)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   himplicitBudgets.1 himplicitBudgets.2.1 himplicitBudgets.2.2
   himplicit hexceptions
 have hsingularUnionScaled:
     (singularSeeds Q selected Gamma).card*S.gap ≤ S.tightNumerator:=
   (Nat.mul_le_mul_right S.gap
     (singularSeeds_card_le_sum Q selected Gamma)).trans hsingularScaled
 have hSgap:0 < S.gap:=by simpa [hgapEq] using hgap
 have hsingularCap:(singularSeeds Q selected Gamma).card ≤ S.countCap:=
   S.count_le_countCap _ hSgap hsingularUnionScaled
 omega
end
end ProximityPrize.SubmissionLower.RCN052
end PackedLegacy_DW

/-! Packed from ProximityPrize.SubmissionLower.BP. -/
section PackedLegacy_BP
namespace ProximityPrize.SubmissionLower.RCN157
open RCN136 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def embedX (K:Type) [Field K]:Polynomial K →+*Poly4 K:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0:Fin 4))
@[simp] theorem embedX_C (a:K):
   embedX K (Polynomial.C a)=MvPolynomial.C a:=by
 simp [embedX]
@[simp] theorem embedX_X:
   embedX K Polynomial.X=MvPolynomial.X (0:Fin 4):=by
 simp [embedX]
@[simp] theorem pderiv_embedX_R (P:Polynomial K):
   MvPolynomial.pderiv (2:Fin 4) (embedX K P)=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ => simp [hP,hQ]
 | monomial n a =>
     simp [embedX,MvPolynomial.pderiv_X]
@[simp] theorem specialization_embedX (C:Polynomial K) (gamma:K)
   (P:Polynomial K):
   specialization K C gamma (embedX K P)=P:=by
 change ((specialization K C gamma).toRingHom.comp (embedX K)) P=
   (RingHom.id (Polynomial K)) P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [embedX,specialization,RingHom.comp_apply]
 · simp [embedX,specialization,RingHom.comp_apply]
@[simp] theorem specialization_X (C:Polynomial K) (gamma:K)
   (i:Fin 4):
   specialization K C gamma (MvPolynomial.X i)=
     ![Polynomial.X,C,C.derivative,Polynomial.C gamma] i:=by
 simp [specialization]
@[simp] theorem surfaceMap_embedX (phi:Polynomial K →+*Omega)
   (P:Polynomial K):
   surfaceMap phi (embedX K P)=MvPolynomial.C (phi P):=by
 change ((surfaceMap phi).comp (embedX K)) P=
   (MvPolynomial.C.comp phi) P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [embedX,surfaceMap,RingHom.comp_apply]
 · simp [embedX,surfaceMap,RingHom.comp_apply]
@[simp] theorem surfaceMap_X_one (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (1:Fin 4))=
     MvPolynomial.X (0:Fin 3):=by
 simpa using surfaceMap_X_succ phi (0:Fin 3)
@[simp] theorem surfaceMap_X_two (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (2:Fin 4))=
     MvPolynomial.X (1:Fin 3):=by
 simpa using surfaceMap_X_succ phi (1:Fin 3)
@[simp] theorem surfaceMap_X_three (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (3:Fin 4))=
     MvPolynomial.X (2:Fin 3):=by
 simpa using surfaceMap_X_succ phi (2:Fin 3)
def globalResidualImage (P0 P1 V:Polynomial K) (i:Fin 4):Poly4 K:=
 ![MvPolynomial.X 0,
   embedX K P0+MvPolynomial.X 3*embedX K P1+
     embedX K V*MvPolynomial.X 1,
   embedX K P0.derivative+MvPolynomial.X 3*embedX K P1.derivative+
     embedX K V.derivative*MvPolynomial.X 1+
     embedX K V*MvPolynomial.X 2,
   MvPolynomial.X 3] i
def globalResidualHom (P0 P1 V:Polynomial K):Poly4 K →ₐ[K] Poly4 K:=
 MvPolynomial.aeval (globalResidualImage P0 P1 V)
@[simp] theorem globalResidualHom_X (P0 P1 V:Polynomial K) (i:Fin 4):
   globalResidualHom P0 P1 V (MvPolynomial.X i)=
     globalResidualImage P0 P1 V i:=by
 simp [globalResidualHom]
theorem specialization_globalResidualHom
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K):
   specialization K C gamma (globalResidualHom P0 P1 V F)=
     specialization K
       (P0+Polynomial.C gamma*P1+V*C) gamma F:=by
 let S:=P0+Polynomial.C gamma*P1+V*C
 have hSderiv:S.derivative=
     P0.derivative+Polynomial.C gamma*P1.derivative+
       V.derivative*C+V*C.derivative:=by
   simp only [S,Polynomial.derivative_add,Polynomial.derivative_mul,
     Polynomial.derivative_C,zero_mul,zero_add]
   ring
 have hhom:
     (specialization K C gamma).comp (globalResidualHom P0 P1 V)=
       specialization K S gamma:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [globalResidualImage,hSderiv,S] <;> ring
 exact DFunLike.congr_fun hhom F
theorem globalResidual_solution
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K)
   (hsolution:specialization K
     (P0+Polynomial.C gamma*P1+V*C) gamma F=0):
   specialization K C gamma (globalResidualHom P0 P1 V F)=0:=by
 rw [specialization_globalResidualHom]
 exact hsolution
theorem pderiv_globalResidualHom_R
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   MvPolynomial.pderiv (2:Fin 4) (globalResidualHom P0 P1 V F)=
     embedX K V*globalResidualHom P0 P1 V
       (MvPolynomial.pderiv (2:Fin 4) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add F G hF hG => simp [hF,hG,mul_add]
 | mul_X F i hF =>
     fin_cases i <;>
       simp [globalResidualImage,hF,Derivation.leibniz] <;> ring
theorem eval_globalResidualHom_polynomialPoint
   (coefficients:K →+*Omega) (P0 P1 V C:Polynomial K)
   (gamma:K) (xi:Omega) (F:Poly4 K):
   MvPolynomial.eval₂Hom coefficients
       (RCN231.polynomialPoint coefficients C gamma xi)
       (globalResidualHom P0 P1 V F)=
     MvPolynomial.eval₂Hom coefficients
       (RCN231.polynomialPoint coefficients
         (P0+Polynomial.C gamma*P1+V*C) gamma xi) F:=by
 rw [RCN231.eval_polynomialPoint_eq_specialization,
   RCN231.eval_polynomialPoint_eq_specialization,
   specialization_globalResidualHom]
theorem globalResidual_regular_at_polynomialPoint
   (coefficients:K →+*Omega) (P0 P1 V C:Polynomial K)
   (gamma:K) (xi:Omega) (F:Poly4 K)
   (hV:V.eval₂ coefficients xi≠0)
   (hregular:MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients
       (P0+Polynomial.C gamma*P1+V*C) gamma xi)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)
     (MvPolynomial.pderiv (2:Fin 4)
       (globalResidualHom P0 P1 V F))≠0:=by
 rw [pderiv_globalResidualHom_R,map_mul,
   eval_globalResidualHom_polynomialPoint]
 have hembed:MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)
     (embedX K V)=V.eval₂ coefficients xi:=by
   change ((MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)).comp
       (embedX K)) V=(Polynomial.eval₂RingHom coefficients xi) V
   congr 1
   apply Polynomial.ringHom_ext
   · intro a
     simp [embedX,RCN231.polynomialPoint,
       RingHom.comp_apply]
   · simp [embedX,RCN231.polynomialPoint,
       RingHom.comp_apply]
 rw [hembed]
 exact mul_ne_zero hV hregular
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
def componentResidualImage
   (aY v bY aR bR cR:Omega) (i:Fin 3):Poly3 Omega:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aR+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bR*MvPolynomial.X 0+
     MvPolynomial.C cR*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def componentResidualHom
   (aY v bY aR bR cR:Omega):Poly3 Omega →ₐ[Omega] Poly3 Omega:=
 MvPolynomial.aeval (componentResidualImage aY v bY aR bR cR)
@[simp] theorem componentResidualHom_X
   (aY v bY aR bR cR:Omega) (i:Fin 3):
   componentResidualHom aY v bY aR bR cR (MvPolynomial.X i)=
     componentResidualImage aY v bY aR bR cR i:=by
 simp [componentResidualHom]
theorem surfaceMap_globalResidualHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   surfaceMap phi (globalResidualHom P0 P1 V F)=
     componentResidualHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
       (surfaceMap phi F):=by
 have hhom:
     (surfaceMap phi).comp (globalResidualHom P0 P1 V).toRingHom=
       (componentResidualHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative)).toRingHom.comp
         (surfaceMap phi):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,globalResidualHom,componentResidualHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,globalResidualImage,componentResidualImage,
         globalResidualHom,componentResidualHom] <;> ring
 exact RingHom.congr_fun hhom F
end
end ProximityPrize.SubmissionLower.RCN157
end PackedLegacy_BP

/-! Packed from ProximityPrize.SubmissionLower.AA. -/
section PackedLegacy_AA
namespace ProximityPrize.SubmissionLower.RCN234
open scoped BigOperators
open RCN081 RCN167 RCN313
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def wt (weights:Fin 4 → ℕ) (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights P
theorem wt_mul_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P*Q) ≤ wt weights P+wt weights Q:=
 weighted_mul_le weights P Q
theorem wt_add_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P+Q) ≤ max (wt weights P) (wt weights Q):=
 weighted_add_le weights P Q
theorem wt_sub_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P-Q) ≤ max (wt weights P) (wt weights Q):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (4:Fin 5)
     (weightedLift K weights P) (weightedLift K weights Q)
theorem wt_neg (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (-P)=wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
theorem wt_pow_le (weights:Fin 4 → ℕ) (P:Poly4 K) (n:ℕ):
   wt weights (P^n) ≤ n*wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K weights P) n
theorem wt_C (weights:Fin 4 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly4 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (MvPolynomial.X i:Poly4 K)=weights i:=by
 unfold wt
 exact weighted_X weights i
theorem wt_natCast (weights:Fin 4 → ℕ) (n:ℕ):
   wt weights (n:Poly4 K)=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),wt_C]
theorem wt_sum_le (weights:Fin 4 → ℕ) (I:Finset ℕ)
   (f:ℕ → Poly4 K) (a:ℕ) (hf:∀ i∈I,wt weights (f i) ≤ a):
   wt weights (∑ i∈I,f i) ≤ a:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem wt_pderiv_le (weights:Fin 4 → ℕ) (P:Poly4 K)
   (i:Fin 4) (A:ℕ) (hP:wt weights P ≤ A):
   wt weights (MvPolynomial.pderiv i P) ≤ A-weights i:=
 pderiv_weight_sub_bound weights P i A hP
theorem wt_polyH_le (weights:Fin 4 → ℕ) (F:Poly4 K)
   (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyH K F) ≤ C-weights 2:=
 wt_pderiv_le weights F 2 C hF
theorem wt_polyG_le (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C+weights 2:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem numeratorStep_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F M:Poly4 K) (b A C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
   (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
   wt weights (numeratorStep K F b M) ≤
     A+C+(C-weights 2):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 let Hcap:=C-weights 2
 have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
 have hG:wt weights G ≤ C+weights 2:=wt_polyG_le weights hX F C hF
 have hRwt:wt weights R=weights 2:=weighted_X weights 2
 have hHC:Hcap ≤ C:=Nat.sub_le C (weights 2)
 have hRH:weights 2+Hcap=C:=by
   dsimp [Hcap]
   omega
 have hRH2:weights 2 ≤ Hcap:=by
   dsimp [Hcap]
   omega
 have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
   have h:=wt_pderiv_le weights M 0 A hM
   rw [hX,Nat.sub_zero] at h
   exact h
 have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A:=
   (wt_pderiv_le weights M 1 A hM).trans (Nat.sub_le A (weights 1))
 have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
   wt_pderiv_le weights M 2 A hM
 have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
   have h:=wt_pderiv_le weights H 0 Hcap hH
   rw [hX,Nat.sub_zero] at h
   exact h
 have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap:=
   (wt_pderiv_le weights H 1 Hcap hH).trans
     (Nat.sub_le Hcap (weights 1))
 have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
   wt_pderiv_le weights H 2 Hcap hH
 have hH2:wt weights (H^2) ≤ 2*Hcap:=
   (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
 have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
     A+C+Hcap:=by
   have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
     A+C+Hcap:=by
   have h1:=wt_mul_le weights R (H^2)
   have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
     A+C+Hcap:=by
   have h1:=wt_mul_le weights G H
   have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ C+Hcap:=by
   have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
   omega
 have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤ C+Hcap:=by
   have h1:=wt_mul_le weights R H
   have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
   have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
   omega
 have hinner:wt weights
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
   exact (wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
 have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
 have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
   omega
 have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change wt weights
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap
 exact (wt_sub_le weights _ _).trans
   (max_le ((wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (b:ℕ):
   wt weights (numerator K F b) ≤
     weights 1+b*(C+(C-weights 2)):=by
 induction b with
 | zero =>
     rw [numerator_zero]
     unfold wt
     rw [weighted_X]
     simp
 | succ b ih =>
     rw [numerator_succ]
     have h:=numeratorStep_wt_le_minkowski weights hX F (numerator K F b) b
       (weights 1+b*(C+(C-weights 2))) C hR hRR
       (hbase.trans (Nat.le_add_right _ _)) hF ih
     convert h using 1 <;> ring
theorem shiftedX_wt_eq_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (x:K):
   wt weights (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)=0:=by
 apply Nat.eq_zero_of_le_zero
 apply (wt_sub_le weights _ _).trans
 rw [wt_C,wt_X,hX]
 simp
theorem affineSeedPolynomial_wt_le (weights:Fin 4 → ℕ) (u₀ u₁:K):
   wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3:=by
 unfold affineSeedPolynomial
 apply (wt_add_le weights _ _).trans
 apply max_le
 · rw [wt_C]
   exact Nat.zero_le _
 · have hm:=wt_mul_le weights (MvPolynomial.X (3:Fin 4):Poly4 K)
     (MvPolynomial.C u₁)
   rw [wt_X,wt_C,Nat.add_zero] at hm
   exact hm
theorem commonNumeratorTerm_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
   (coeffs:ℕ → K) (x:K):
   wt weights (commonNumeratorTerm F w coeffs x j) ≤
     weights 1+w*(C+(C-weights 2)):=by
 let Hcap:=C-weights 2
 let Qcap:=C+Hcap
 have hHC:Hcap ≤ C:=Nat.sub_le _ _
 have hM:wt weights (numerator K F j) ≤ weights 1+j*Qcap:=by
   simpa only [Hcap,Qcap] using
     numerator_wt_le_minkowski weights hX F C hR hRR hbase hF j
 have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
     weights 1+j*Qcap:=by
   have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
   rw [wt_C,Nat.zero_add] at hm
   exact hm.trans hM
 have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*(w-j))) ≤
     2*(w-j)*Hcap:=by
   exact (wt_pow_le weights (polyH K F) (2*(w-j))).trans
     (Nat.mul_le_mul_left _ hH)
 have hSX:=shiftedX_wt_eq_zero weights hX x
 have h1:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j*
     polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 have hSXP:wt weights
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   have hp:=wt_pow_le weights
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
   rw [hSX,Nat.mul_zero] at hp
   exact hp
 have hraw:wt weights (commonNumeratorTerm F w coeffs x j) ≤
     (weights 1+j*Qcap)+2*(w-j)*Hcap:=by
   simpa only [commonNumeratorTerm,Nat.add_zero] using
     h2.trans (Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP)
 have hunit:2*Hcap ≤ Qcap:=by
   dsimp [Qcap]
   omega
 have hmul:=Nat.mul_le_mul_left (w-j) hunit
 have hwj:j+(w-j)=w:=by omega
 apply hraw.trans
 calc
   (weights 1+j*Qcap)+2*(w-j)*Hcap=
       weights 1+j*Qcap+(w-j)*(2*Hcap):=by ring
   _ ≤ weights 1+j*Qcap+(w-j)*Qcap:=
     Nat.add_le_add_left hmul _
   _=weights 1+(j+(w-j))*Qcap:=by ring
   _=weights 1+w*Qcap:=by rw [hwj]
theorem clearedTaylorNumerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K) (x:K):
   wt weights (clearedTaylorNumerator F w coeffs x) ≤
     weights 1+w*(C+(C-weights 2)):=by
 unfold clearedTaylorNumerator
 apply wt_sum_le
 intro j hj
 apply commonNumeratorTerm_wt_le_minkowski weights hX F C hR hRR hbase hF
 have:=Finset.mem_range.mp hj
 omega
theorem agreementNumerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K)
   (x u₀ u₁:K):
   wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
     max (weights 1) (weights 3)+w*(C+(C-weights 2)):=by
 let Hcap:=C-weights 2
 let Qcap:=C+Hcap
 have hHC:Hcap ≤ C:=Nat.sub_le _ _
 have hTaylor:=clearedTaylorNumerator_wt_le_minkowski weights hX F C hR hRR
   hbase hF w coeffs x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*w)) ≤ 2*w*Hcap:=
   (wt_pow_le weights (polyH K F) (2*w)).trans
     (Nat.mul_le_mul_left _ hH)
 have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
   (polyH K F^(2*w))
 have hunit:2*Hcap ≤ Qcap:=by
   dsimp [Qcap]
   omega
 have hmul:=Nat.mul_le_mul_left w hunit
 have hright:wt weights
     (affineSeedPolynomial u₀ u₁*polyH K F^(2*w)) ≤
     max (weights 1) (weights 3)+w*Qcap:=by
   apply hprod.trans
   calc
     wt weights (affineSeedPolynomial u₀ u₁)+
         wt weights (polyH K F^(2*w)) ≤ weights 3+2*w*Hcap:=
       Nat.add_le_add hA hHP
     _=weights 3+w*(2*Hcap):=by ring
     _ ≤ max (weights 1) (weights 3)+w*Qcap:=
       Nat.add_le_add (Nat.le_max_right _ _) hmul
 unfold agreementNumerator
 apply (wt_sub_le weights _ _).trans
 apply max_le
 · simpa only [Hcap,Qcap] using
     hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
 · simpa only [Hcap,Qcap] using hright
end
end ProximityPrize.SubmissionLower.RCN234
end PackedLegacy_AA

/-! Packed from ProximityPrize.SubmissionLower.FO. -/
section PackedLegacy_FO
namespace ProximityPrize.SubmissionLower.RCN235
open scoped BigOperators Matrix
open ProximityPrize.SubmissionLower.RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def shearImage (i:Fin 4):Poly4 K:=
 ![MvPolynomial.X 0,MvPolynomial.X 1,
   MvPolynomial.X 2-MvPolynomial.X 3,MvPolynomial.X 3] i
def shearMap:Poly4 K →+*Poly4 K:=
 MvPolynomial.eval₂Hom MvPolynomial.C shearImage
def pullShearWeights (weights:Fin 4 → ℕ):Fin 4 → ℕ:=
 ![weights 0,weights 1,max (weights 2) (weights 3),weights 3]
theorem shearImage_wt_le (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (shearImage (K:=K) i) ≤ pullShearWeights weights i:=by
 fin_cases i
 · simp [shearImage,pullShearWeights,wt_X]
 · simp [shearImage,pullShearWeights,wt_X]
 · dsimp [shearImage,pullShearWeights]
   exact (wt_sub_le weights _ _).trans (by rw [wt_X,wt_X])
 · simp [shearImage,pullShearWeights,wt_X]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty =>
     simp only [Finset.prod_empty,Finset.sum_empty]
     unfold wt MvPolynomial.weightedTotalDegree
     simp
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights _ _).trans (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←RCN081.degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => RCN081.weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [RCN081.degree_weightedLift]
 exact hf i hi
theorem shear_monomial_product_wt_le
   (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   wt weights (∏ i∈d.support,shearImage (K:=K) i^d i) ≤
     Finsupp.weight (pullShearWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i => shearImage (K:=K) i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (shearImage (K:=K) i^d i)) ≤
       ∑ i∈d.support,d i*pullShearWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (shearImage (K:=K) i) (d i)).trans
       (Nat.mul_le_mul_left _ (shearImage_wt_le weights i))
   _=Finsupp.weight (pullShearWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem shearMap_wt_le_pulled (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (shearMap P) ≤ wt (pullShearWeights weights) P:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C (shearImage (K:=K)) P) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=shear_monomial_product_wt_le (K:=K) weights d
 have hcoeff:wt weights (MvPolynomial.C (P.coeff d):Poly4 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (P.coeff d):Poly4 K)
   (∏ i∈d.support,shearImage (K:=K) i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (pullShearWeights weights) hd))
end
end ProximityPrize.SubmissionLower.RCN235
end PackedLegacy_FO

/-! Packed from ProximityPrize.SubmissionLower.AH. -/
section PackedLegacy_AH
namespace ProximityPrize.SubmissionLower.RCN295
open scoped Classical BigOperators WithZero
open RCN187
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
local instance:DecidableEq K:=Classical.decEq K
def exponentPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*poleOrder v (x i)
def exponentValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*(v (x i)).log
def exponentSetValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentValuationWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def ExponentSetDownwardClosed (E:Finset (σ →₀ ℕ)):Prop:=
 ∀ d∈E,∀ e:σ →₀ ℕ,e ≤ d → e∈E
def exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentPoleWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):ℤ:=
 exponentSetPoleWeight v x F.support
theorem supportPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):
   0 ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem exponentPoleWeight_le_supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support):
   exponentPoleWeight v x d ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
theorem exponentSetPoleWeight_mono
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) {E D:Finset (σ →₀ ℕ)} (hED:E ⊆ D):
   exponentSetPoleWeight v x E ≤ exponentSetPoleWeight v x D:=by
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   apply Finset.le_max'
   exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hED hd,rfl⟩)
theorem supportPoleWeight_le_exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K) (E:Finset (σ →₀ ℕ))
   (hFE:F.support ⊆ E):
   supportPoleWeight v x F ≤ exponentSetPoleWeight v x E:=
 exponentSetPoleWeight_mono v x hFE
theorem exponentValuationWeight_le_exponentPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentValuationWeight v x d ≤ exponentPoleWeight v x d:=by
 unfold exponentValuationWeight exponentPoleWeight poleOrder
 apply Finset.sum_le_sum
 intro i _
 exact mul_le_mul_of_nonneg_left (le_max_right _ _)
   (Int.natCast_nonneg _)
def poleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=by
 classical
 exact d.filter (fun i↦0 ≤ (v (x i)).log)
theorem poleTruncation_le
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):poleTruncation v x d ≤ d:=by
 intro i
 simp only [poleTruncation,Finsupp.filter_apply]
 split_ifs
 · exact le_rfl
 · exact Nat.zero_le _
theorem exponentValuationWeight_poleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentValuationWeight v x (poleTruncation v x d)=
     exponentPoleWeight v x d:=by
 classical
 unfold exponentValuationWeight exponentPoleWeight poleOrder
 apply Finset.sum_congr rfl
 intro i _
 simp only [poleTruncation,Finsupp.filter_apply]
 by_cases h:0 ≤ (v (x i)).log
 · rw [if_pos h,max_eq_right h]
 · have hle:(v (x i)).log ≤ 0:=le_of_not_ge h
   rw [if_neg h,max_eq_left hle]
   simp
theorem exponentSetPoleWeight_eq_valuationWeight_of_downwardClosed
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E):
   exponentSetPoleWeight v x E=exponentSetValuationWeight v x E:=by
 classical
 apply le_antisymm
 · unfold exponentSetPoleWeight exponentSetValuationWeight
   apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
   · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
     let e:=poleTruncation v x d
     have he:e∈E:=hdown d hd e (poleTruncation_le v x d)
     rw [←exponentValuationWeight_poleTruncation v x d]
     apply Finset.le_max'
     exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e,he,rfl⟩)
 · unfold exponentSetPoleWeight exponentSetValuationWeight
   apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
   · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
     exact (exponentValuationWeight_le_exponentPoleWeight v x d).trans
       (Finset.le_max' _ _ (Finset.mem_insert_of_mem
         (Finset.mem_image.mpr ⟨d,hd,rfl⟩)))
def naturalPoleWeights
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:σ → L):σ → ℕ:=
 fun i↦(poleOrder v (x i)).toNat
theorem naturalPoleWeights_cast
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:σ → L) (i:σ):
   ((naturalPoleWeights v x i:ℕ):ℤ)=poleOrder v (x i):=by
 unfold naturalPoleWeights
 exact Int.toNat_of_nonneg (by
   unfold poleOrder
   exact le_max_left _ _)
theorem exponentPoleWeight_eq_naturalWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentPoleWeight v x d=
     (Finsupp.weight (naturalPoleWeights v x) d:ℕ):=by
 unfold exponentPoleWeight
 rw [Finsupp.weight_apply]
 rw [Finsupp.sum_fintype d
   (fun i n↦n • naturalPoleWeights v x i) (fun _↦zero_nsmul _)]
 simp only [nsmul_eq_mul]
 push_cast
 apply Finset.sum_congr rfl
 intro i _
 rw [naturalPoleWeights_cast]
theorem supportPoleWeight_le_weightedTotalDegree_naturalPole
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):
   supportPoleWeight v x F ≤
     (MvPolynomial.weightedTotalDegree (naturalPoleWeights v x) F:ℕ):=by
 classical
 unfold supportPoleWeight exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · exact Int.natCast_nonneg _
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   rw [exponentPoleWeight_eq_naturalWeight]
   exact_mod_cast MvPolynomial.le_weightedTotalDegree (naturalPoleWeights v x) hd
theorem valuation_monomial_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support) (c:K):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 apply WithZero.le_exp_of_log_le
 calc
   (v (MvPolynomial.eval₂Hom coeff x
       (MvPolynomial.monomial d c))).log ≤
       poleOrder v (MvPolynomial.eval₂Hom coeff x
         (MvPolynomial.monomial d c)):=
     le_max_right _ _
   _ ≤ exponentPoleWeight v x d:=by
     by_cases hc:c=0
     · subst c
       simp [exponentPoleWeight,poleOrder]
       positivity
     · have hmono:=poleOrder_eval_le_box v coeff hcoeff x
         (fun i↦d i) (MvPolynomial.monomial d c) (fun i↦by
           rw [MvPolynomial.degreeOf_monomial_eq d i hc])
       simpa only [exponentPoleWeight] using hmono
   _ ≤ supportPoleWeight v x F:=
     exponentPoleWeight_le_supportPoleWeight v x F d hd
theorem valuation_eval_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 conv_lhs => rw [MvPolynomial.as_sum F,map_sum]
 apply v.map_sum_le
 intro d hd
 exact valuation_monomial_le_exp_support v coeff hcoeff x F d hd
   (F.coeff d)
theorem valuation_eval_le_exp_exponentSet
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   v (MvPolynomial.eval₂Hom coeff x F) ≤
     WithZero.exp (exponentSetPoleWeight v x E):=by
 exact (valuation_eval_le_exp_support v coeff hcoeff x F).trans
   ((WithZero.exp_le_exp).2
     (supportPoleWeight_le_exponentSetPoleWeight v x F E hFE))
theorem poleOrder_eval_le_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K):
   poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
     supportPoleWeight v x F:=by
 classical
 have heval:=valuation_eval_le_exp_support v coeff hcoeff x F
 have hone:(1:WithZero (Multiplicative ℤ)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact supportPoleWeight_nonneg v x F
 have hmax:max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
     WithZero.exp (supportPoleWeight v x F):=max_le hone heval
 have hleft0:max 1 (v (MvPolynomial.eval₂Hom coeff x F))≠0:=
   ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
 have hlog:=(WithZero.log_le_log hleft0 WithZero.exp_ne_zero).2 hmax
 rw [log_max_one,WithZero.log_exp] at hlog
 simpa only [poleOrder] using hlog
theorem weighted_poleOrder_eval_le_exponentSet
   {τ:Type*} (S:Finset τ) (weight:τ → ℕ)
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L)
   (hcoeff:∀ t∈S,∀ c:K,v t (coeff c) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (F:MvPolynomial σ K)
   (hFE:F.support ⊆ E):
   (∑ t∈S,(weight t:ℤ)*
     poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
     ∑ t∈S,(weight t:ℤ)*exponentSetPoleWeight (v t) x E:=by
 classical
 apply Finset.sum_le_sum
 intro t ht
 apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
 exact (poleOrder_eval_le_support (v t) coeff (hcoeff t ht) x F).trans
   (supportPoleWeight_le_exponentSetPoleWeight (v t) x F E hFE)
end
end ProximityPrize.SubmissionLower.RCN295
end PackedLegacy_AH

/-! Packed from ProximityPrize.SubmissionLower.D. -/
section PackedLegacy_D
namespace ProximityPrize.SubmissionLower.RCN095
open scoped BigOperators
open ProximityPrize.SubmissionLower.RCN295
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
structure FlagDegree where
 zOnly:ℕ
 yz:ℕ
 all:ℕ
 deriving DecidableEq,Repr
instance:Add FlagDegree:=⟨fun p q↦
 ⟨p.zOnly+q.zOnly,p.yz+q.yz,p.all+q.all⟩⟩
instance:SMul ℕ FlagDegree:=⟨fun n p↦
 ⟨n*p.zOnly,n*p.yz,n*p.all⟩⟩
@[simp] theorem add_zOnly (p q:FlagDegree):
   (p+q).zOnly=p.zOnly+q.zOnly:=rfl
@[simp] theorem add_yz (p q:FlagDegree):
   (p+q).yz=p.yz+q.yz:=rfl
@[simp] theorem add_all (p q:FlagDegree):
   (p+q).all=p.all+q.all:=rfl
@[simp] theorem nsmul_zOnly (n:ℕ) (p:FlagDegree):
   (n • p).zOnly=n*p.zOnly:=rfl
@[simp] theorem nsmul_yz (n:ℕ) (p:FlagDegree):
   (n • p).yz=n*p.yz:=rfl
@[simp] theorem nsmul_all (n:ℕ) (p:FlagDegree):
   (n • p).all=n*p.all:=rfl
def InFlag (p:FlagDegree) (d:Fin 3 →₀ ℕ):Prop:=
 d 1 ≤ p.all∧
   d 0+d 1 ≤ p.yz+p.all∧
   d 0+d 1+d 2 ≤ p.zOnly+p.yz+p.all
theorem inFlag_zero (p:FlagDegree):InFlag p 0:=by
 simp [InFlag]
theorem inFlag_add {p q:FlagDegree} {d e:Fin 3 →₀ ℕ}
   (hd:InFlag p d) (he:InFlag q e):InFlag (p+q) (d+e):=by
 rcases hd with ⟨hdS,hdYS,hdTot⟩
 rcases he with ⟨heS,heYS,heTot⟩
 simp only [InFlag,Finsupp.add_apply,add_zOnly,add_yz,add_all]
 omega
noncomputable def exponentOfTriple (t:ℕ × ℕ × ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 t.1+Finsupp.single 1 t.2.1+
   Finsupp.single 2 t.2.2
noncomputable def flagSupport (p:FlagDegree):Finset (Fin 3 →₀ ℕ):=
 by
   classical
   exact (((((Finset.range (p.zOnly+p.yz+p.all+1)).product
       (Finset.range (p.all+1))).product
       (Finset.range (p.zOnly+p.yz+p.all+1))).image
         (fun t↦exponentOfTriple (t.1.1,t.1.2,t.2))).filter (InFlag p))
theorem exponentOfTriple_coordinates (y s z:ℕ):
   exponentOfTriple (y,s,z) 0=y∧
     exponentOfTriple (y,s,z) 1=s∧
     exponentOfTriple (y,s,z) 2=z:=by
 simp [exponentOfTriple]
theorem mem_flagSupport_iff (p:FlagDegree) (d:Fin 3 →₀ ℕ):
   d∈flagSupport p ↔ InFlag p d:=by
 classical
 constructor
 · intro hd
   unfold flagSupport at hd
   exact (Finset.mem_filter.mp hd).2
 · intro hd
   unfold flagSupport
   rw [Finset.mem_filter]
   refine ⟨?_,hd⟩
   apply Finset.mem_image.mpr
   rcases hd with ⟨hS,hYS,htotal⟩
   refine ⟨((d 0,d 1),d 2),?_,?_⟩
   · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
       ⟨Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega),
         Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩,
       Finset.mem_range.mpr (by simp only [Prod.fst,Prod.snd];omega)⟩
   · ext i
     fin_cases i <;> simp [exponentOfTriple]
theorem zero_mem_flagSupport (p:FlagDegree):
   (0:Fin 3 →₀ ℕ)∈flagSupport p:=by
 rw [mem_flagSupport_iff]
 exact inFlag_zero p
theorem flagSupport_downwardClosed (p:FlagDegree):
   ExponentSetDownwardClosed (flagSupport p):=by
 intro d hd e he
 rw [mem_flagSupport_iff] at hd ⊢
 rcases hd with ⟨hdS,hdYS,hdtotal⟩
 have h0:=he 0
 have h1:=he 1
 have h2:=he 2
 exact ⟨h1.trans hdS,by omega,by omega⟩
def PolynomialInFlag {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):Prop:=
 ∀ d∈A.support,InFlag p d
theorem support_subset_flagSupport_iff {K:Type*} [Field K]
   (p:FlagDegree) (A:MvPolynomial (Fin 3) K):
   A.support ⊆ flagSupport p ↔ PolynomialInFlag p A:=by
 simp only [PolynomialInFlag,Finset.subset_iff,mem_flagSupport_iff]
def flagSWeights:Fin 3 → ℕ:=![0,1,0]
def flagYSWeights:Fin 3 → ℕ:=![1,1,0]
def flagTotalWeights:Fin 3 → ℕ:=![1,1,1]
theorem flag_weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
theorem support_subset_flagSupport_of_weighted_degrees
   {K:Type*} [Field K] (p:FlagDegree)
   (A:MvPolynomial (Fin 3) K)
   (hS:MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all)
   (hYS:MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz+p.all)
   (hTotal:MvPolynomial.weightedTotalDegree flagTotalWeights A ≤
     p.zOnly+p.yz+p.all):
   A.support ⊆ flagSupport p:=by
 rw [support_subset_flagSupport_iff]
 intro d hd
 have hs:=(MvPolynomial.le_weightedTotalDegree flagSWeights hd).trans hS
 have hys:=(MvPolynomial.le_weightedTotalDegree flagYSWeights hd).trans hYS
 have htotal:=
   (MvPolynomial.le_weightedTotalDegree flagTotalWeights hd).trans hTotal
 rw [flag_weight_fin3] at hs hys htotal
 change d 0*0+d 1*1+d 2*0 ≤ p.all at hs
 change d 0*1+d 1*1+d 2*0 ≤ p.yz+p.all at hys
 change d 0*1+d 1*1+d 2*1 ≤
   p.zOnly+p.yz+p.all at htotal
 simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.zero_add] at hs hys htotal
 exact ⟨hs,hys,htotal⟩
def flagMixed (p q r:FlagDegree):ℕ:=
 p.all*q.all*r.all+
 (p.zOnly*q.all*r.all+q.zOnly*p.all*r.all+
   r.zOnly*p.all*q.all)+
 (p.yz*q.all*r.all+q.yz*p.all*r.all+
   r.yz*p.all*q.all)+
 (p.all*q.yz*r.yz+q.all*p.yz*r.yz+
   r.all*p.yz*q.yz)+
 (p.zOnly*q.yz*r.all+p.zOnly*r.yz*q.all+
   q.zOnly*p.yz*r.all+q.zOnly*r.yz*p.all+
   r.zOnly*p.yz*q.all+r.zOnly*q.yz*p.all)
def unitZFlag:FlagDegree:=⟨1,0,0⟩
def unitYZFlag:FlagDegree:=⟨0,1,0⟩
def unitAllFlag:FlagDegree:=⟨0,0,1⟩
def seedFlag:FlagDegree:=unitYZFlag
private def legacyN:ℕ:=262144
private def legacyW:ℕ:=131071
private def legacyErrors:ℕ:=78210
private def legacyAgreements:ℕ:=legacyN-legacyErrors
private def legacyGap:ℕ:=legacyAgreements-legacyW
private def legacyAlignmentBudget:ℕ:=100000000000000000
private def legacyShearedWholeMixedCap:ℕ:=16230040480658160
private def legacySingularNumerator:ℕ:=8043405963321174171
private def legacyGapSquared:ℕ:=legacyGap^2
def shearedSurfaceFlag:FlagDegree:=⟨350,21,5⟩
def shearedDerivativeFlag:FlagDegree:=⟨350,21,4⟩
def shearedAgreementFlag:FlagDegree:=
 seedFlag+legacyW • (shearedSurfaceFlag+shearedDerivativeFlag)
theorem shearedAgreementFlag_value:
   shearedAgreementFlag=⟨91749700,5504983,1179639⟩:=by
 change (⟨0+131071*(350+350),
     1+131071*(21+21),
     0+131071*(5+4)⟩:FlagDegree)=_
 norm_num
def flagWholeMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag shearedAgreementFlag
def flagZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitZFlag
def flagYZMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitYZFlag
def flagAllMixedCap:ℕ:=
 flagMixed shearedSurfaceFlag shearedAgreementFlag unitAllFlag
theorem flag_mixed_values:
   flagWholeMixedCap=16236998221509765∧
     flagZMixedCap=58195529∧
     flagYZMixedCap=929817679∧
     flagAllMixedCap=4898910072:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagMixed,
   flagYZMixedCap,flagAllMixedCap,
   shearedSurfaceFlag,shearedAgreementFlag,shearedDerivativeFlag,
   seedFlag,unitZFlag,unitYZFlag,unitAllFlag,legacyW]
theorem flag_projection_decomposition:
   flagWholeMixedCap=
     shearedAgreementFlag.zOnly*flagZMixedCap+
     shearedAgreementFlag.yz*flagYZMixedCap+
     shearedAgreementFlag.all*flagAllMixedCap:=by
 norm_num [flagWholeMixedCap,flagZMixedCap,flagYZMixedCap,
   flagAllMixedCap,flagMixed,shearedSurfaceFlag,
   shearedAgreementFlag,shearedDerivativeFlag,seedFlag,
   unitZFlag,unitYZFlag,unitAllFlag,legacyW]
theorem flag_excess_exact:
   flagWholeMixedCap-legacyShearedWholeMixedCap=6957740851605:=by
 rw [flag_mixed_values.1]
 norm_num [legacyShearedWholeMixedCap]
def flagWholeNumerator:ℕ:=
 (legacyN-legacyW)^2*flagWholeMixedCap+
   (legacyErrors+1)*(legacyN-legacyW)*legacyGap*flagZMixedCap
def flagTotalNumerator:ℕ:=
 flagWholeNumerator+legacyGap*legacySingularNumerator
def flagLedgerCeiling:ℕ:=
 (flagTotalNumerator+legacyGapSquared-1)/legacyGapSquared
theorem flag_whole_numerator_exact:
   flagWholeNumerator=278985298988701469237937066:=by
 norm_num [flagWholeNumerator,flag_mixed_values.1,flag_mixed_values.2.1,
   legacyN,legacyW,legacyErrors,legacyGap,legacyAgreements]
theorem flag_total_numerator_exact:
   flagTotalNumerator=279410497558140516468138639:=by
 rw [show flagTotalNumerator=
     flagWholeNumerator+legacyGap*legacySingularNumerator by rfl,
   flag_whole_numerator_exact]
 norm_num [legacySingularNumerator,legacyGap,legacyAgreements,
   legacyN,legacyErrors,legacyW]
theorem flag_ledger_ceiling_exact:
   flagLedgerCeiling=99985979822093871:=by
 norm_num [flagLedgerCeiling,flag_total_numerator_exact,
   legacyGapSquared,legacyGap,legacyAgreements,legacyN,legacyErrors,
   legacyW]
theorem flag_budget_slack:
   legacyAlignmentBudget-flagLedgerCeiling=14020177906129:=by
 rw [flag_ledger_ceiling_exact]
 norm_num [legacyAlignmentBudget]
theorem flag_strict_budget:
   flagTotalNumerator < legacyAlignmentBudget*legacyGapSquared:=by
 rw [flag_total_numerator_exact]
 norm_num [legacyAlignmentBudget,legacyGapSquared,legacyGap,
   legacyAgreements,legacyN,legacyErrors,legacyW]
end ProximityPrize.SubmissionLower.RCN095
end PackedLegacy_D

/-! Packed from ProximityPrize.SubmissionLower.BO. -/
section PackedLegacy_BO
namespace ProximityPrize.SubmissionLower.RCN156
open scoped Classical BigOperators
open RCN157 RCN234 RCN235 RCN095 RCN136 RCN313
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def residualPullWeights (weights:Fin 4 → ℕ):Fin 4 → ℕ:=
 ![weights 0,
   max (weights 1) (weights 3),
   max (weights 2) (max (weights 1) (weights 3)),
   weights 3]
theorem wt_embedX_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P:Polynomial K):
   wt weights (embedX K P)=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ =>
     rw [map_add]
     apply Nat.eq_zero_of_le_zero
     exact (wt_add_le weights (embedX K P) (embedX K Q)).trans
       (by simpa only [hP,hQ,max_self] using (Nat.le_refl 0))
 | monomial n a =>
     have hembed:embedX K (Polynomial.monomial n a)=
         MvPolynomial.C a*MvPolynomial.X (0:Fin 4)^n:=by
       simp [embedX]
     rw [hembed]
     apply Nat.eq_zero_of_le_zero
     have hm:=wt_mul_le weights (MvPolynomial.C a:Poly4 K)
       (MvPolynomial.X (0:Fin 4)^n)
     have hp:=wt_pow_le weights (MvPolynomial.X (0:Fin 4):Poly4 K) n
     rw [wt_C] at hm
     rw [wt_X,hX,Nat.mul_zero] at hp
     omega
theorem globalResidualImage_wt_le
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (i:Fin 4):
   wt weights (globalResidualImage P0 P1 V i) ≤
     residualPullWeights weights i:=by
 fin_cases i
 · simp [globalResidualImage,residualPullWeights,wt_X]
 · dsimp [globalResidualImage,residualPullWeights]
   have hP0:=wt_embedX_zero weights hX P0
   have hP1:=wt_embedX_zero weights hX P1
   have hV:=wt_embedX_zero weights hX V
   have hz:=wt_mul_le weights
     (MvPolynomial.X (3:Fin 4):Poly4 K) (embedX K P1)
   have hy:=wt_mul_le weights (embedX K V)
     (MvPolynomial.X (1:Fin 4):Poly4 K)
   rw [wt_X,hP1,Nat.add_zero] at hz
   rw [hV,wt_X,Nat.zero_add] at hy
   have h01:=wt_add_le weights (embedX K P0)
     (MvPolynomial.X (3:Fin 4)*embedX K P1)
   have h012:=wt_add_le weights
     (embedX K P0+MvPolynomial.X (3:Fin 4)*embedX K P1)
     (embedX K V*MvPolynomial.X (1:Fin 4))
   omega
 · dsimp [globalResidualImage,residualPullWeights]
   have hP0:=wt_embedX_zero weights hX P0.derivative
   have hP1:=wt_embedX_zero weights hX P1.derivative
   have hV':=wt_embedX_zero weights hX V.derivative
   have hV:=wt_embedX_zero weights hX V
   have hz:=wt_mul_le weights
     (MvPolynomial.X (3:Fin 4):Poly4 K) (embedX K P1.derivative)
   have hy:=wt_mul_le weights (embedX K V.derivative)
     (MvPolynomial.X (1:Fin 4):Poly4 K)
   have hr:=wt_mul_le weights (embedX K V)
     (MvPolynomial.X (2:Fin 4):Poly4 K)
   rw [wt_X,hP1,Nat.add_zero] at hz
   rw [hV',wt_X,Nat.zero_add] at hy
   rw [hV,wt_X,Nat.zero_add] at hr
   have h01:=wt_add_le weights (embedX K P0.derivative)
     (MvPolynomial.X (3:Fin 4)*embedX K P1.derivative)
   have h012:=wt_add_le weights
     (embedX K P0.derivative+
       MvPolynomial.X (3:Fin 4)*embedX K P1.derivative)
     (embedX K V.derivative*MvPolynomial.X (1:Fin 4))
   have h0123:=wt_add_le weights
     (embedX K P0.derivative+
       MvPolynomial.X (3:Fin 4)*embedX K P1.derivative+
       embedX K V.derivative*MvPolynomial.X (1:Fin 4))
     (embedX K V*MvPolynomial.X (2:Fin 4))
   omega
 · simp [globalResidualImage,residualPullWeights,wt_X]
theorem globalResidual_monomial_product_wt_le
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (d:Fin 4 →₀ ℕ):
   wt weights
       (∏ i∈d.support,globalResidualImage P0 P1 V i^d i) ≤
     Finsupp.weight (residualPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦globalResidualImage P0 P1 V i^d i)).trans
 calc
   (∑ i∈d.support,
       wt weights (globalResidualImage P0 P1 V i^d i)) ≤
       ∑ i∈d.support,d i*residualPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (globalResidualImage P0 P1 V i) (d i)).trans
       (Nat.mul_le_mul_left _
         (globalResidualImage_wt_le weights hX P0 P1 V i))
   _=Finsupp.weight (residualPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem globalResidualHom_wt_le_pulled
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   wt weights (globalResidualHom P0 P1 V F) ≤
     wt (residualPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C
       (globalResidualImage P0 P1 V) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=globalResidual_monomial_product_wt_le
   weights hX P0 P1 V d
 have hcoeff:wt weights
     (MvPolynomial.C (F.coeff d):Poly4 K)=0:=wt_C weights _
 have hmul:=wt_mul_le weights
   (MvPolynomial.C (F.coeff d):Poly4 K)
   (∏ i∈d.support,globalResidualImage P0 P1 V i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree
     (residualPullWeights weights) hd))
def residualSWeights:Fin 4 → ℕ:=![0,0,1,0]
def residualYSWeights:Fin 4 → ℕ:=![0,1,1,0]
def residualTotalWeights:Fin 4 → ℕ:=![0,1,1,1]
theorem residualPullWeights_s:
   residualPullWeights residualSWeights=residualSWeights:=by
 funext i
 fin_cases i <;> rfl
theorem residualPullWeights_ys:
   residualPullWeights residualYSWeights=residualYSWeights:=by
 funext i
 fin_cases i <;> rfl
theorem residualPullWeights_total:
   residualPullWeights residualTotalWeights=residualTotalWeights:=by
 funext i
 fin_cases i <;> rfl
theorem globalResidualHom_surface_flag_weights
   (P0 P1 V:Polynomial K) (F:Poly4 K)
   (hS:wt residualSWeights F ≤ 8)
   (hYS:wt residualYSWeights F ≤ 43)
   (hTotal:wt residualTotalWeights F ≤ 503):
   wt residualSWeights (globalResidualHom P0 P1 V F) ≤ 8∧
     wt residualYSWeights (globalResidualHom P0 P1 V F) ≤ 43∧
     wt residualTotalWeights (globalResidualHom P0 P1 V F) ≤ 503:=by
 refine ⟨?_,?_,?_⟩
 · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_s] using hS)
 · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_ys] using hYS)
 · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_total] using hTotal)
theorem globalResidual_agreement_weight_bounds
   (P0 P1 V:Polynomial K) (F:Poly4 K)
   (hS:wt residualSWeights F ≤ 8)
   (hYS:wt residualYSWeights F ≤ 43)
   (hTotal:wt residualTotalWeights F ≤ 503)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator (globalResidualHom P0 P1 V F)
       d coeffs x u0 u1).degreeOf (2:Fin 4) ≤ 15*d∧
     wt residualYSWeights
       (agreementNumerator (globalResidualHom P0 P1 V F)
         d coeffs x u0 u1) ≤ 1+85*d∧
     wt residualTotalWeights
       (agreementNumerator (globalResidualHom P0 P1 V F)
         d coeffs x u0 u1) ≤ 1+1005*d:=by
 let Fres:=globalResidualHom P0 P1 V F
 obtain ⟨hFs,hFys,hFtot⟩:=
   globalResidualHom_surface_flag_weights P0 P1 V F hS hYS hTotal
 have hR:Fres.degreeOf (2:Fin 4) ≤ 8:=by
   have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
     funext i
     fin_cases i <;> rfl
   rw [hw,wt,MvPolynomial.weightedTotalDegree_piSingle] at hFs
   exact hFs
 have hY:Fres.degreeOf (1:Fin 4) ≤ 43:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans hFys
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*0 ≤ 43 at hw
   norm_num at hw
   omega
 have hZ:Fres.degreeOf (3:Fin 4) ≤ 503:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hFtot
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*1 ≤ 503 at hw
   norm_num at hw
   omega
 refine ⟨?_,?_,?_⟩
 · have hr:=(agreementNumerator_degree_bounds Fres 43 8 503
     (by norm_num) hY hR hZ d coeffs x u0 u1).2.1
   convert hr using 1 <;> ring
 · have h:=agreementNumerator_wt_le_minkowski residualYSWeights rfl
     Fres 43 (by change 1 ≤ 43;norm_num)
     (by change 2*1 ≤ 43;norm_num)
     (by change 1 ≤ 1;norm_num) hFys d coeffs x u0 u1
   calc
     wt residualYSWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
         max (residualYSWeights 1) (residualYSWeights 3)+
           d*(43+(43-residualYSWeights 2)):=h
     _=1+85*d:=by
       change max 1 0+d*(43+(43-1))=1+85*d
       norm_num
       ring
 · have h:=agreementNumerator_wt_le_minkowski residualTotalWeights rfl
     Fres 503 (by change 1 ≤ 503;norm_num)
     (by change 2*1 ≤ 503;norm_num)
     (by change 1 ≤ 1;norm_num) hFtot d coeffs x u0 u1
   calc
     wt residualTotalWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
         max (residualTotalWeights 1) (residualTotalWeights 3)+
           d*(503+(503-residualTotalWeights 2)):=h
     _=1+1005*d:=by
       change max 1 1+d*(503+(503-1))=1+1005*d
       norm_num
       ring
def residualAgreementFlag (d:ℕ):FlagDegree:=
 ⟨920*d,1+70*d,15*d⟩
theorem surfaceMap_globalResidual_agreement_in_flag
   (phi:Polynomial K →+*Omega)
   (P0 P1 V:Polynomial K) (F:Poly4 K)
   (hS:wt residualSWeights F ≤ 8)
   (hYS:wt residualYSWeights F ≤ 43)
   (hTotal:wt residualTotalWeights F ≤ 503)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (residualAgreementFlag d)
     (surfaceMap phi
       (agreementNumerator (globalResidualHom P0 P1 V F)
         d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi
     (agreementNumerator (globalResidualHom P0 P1 V F)
       d coeffs x u0 u1) he)
 obtain ⟨hR,hYS',hTot⟩:=globalResidual_agreement_weight_bounds
   P0 P1 V F hS hYS hTotal d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS'
 have hqTot:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTot
 rw [RCN081.weight_fin4] at hqYS hqTot
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤ 1+85*d at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤ 1+1005*d at hqTot
 norm_num at hqYS hqTot
 change q 2 ≤ 15*d∧
   q 1+q 2 ≤ (1+70*d)+15*d∧
   q 1+q 2+q 3 ≤ 920*d+(1+70*d)+15*d
 omega
end
end ProximityPrize.SubmissionLower.RCN156
end PackedLegacy_BO

/-! Packed from ProximityPrize.SubmissionLower.D5. -/
section PackedLegacy_D5
namespace ProximityPrize.SubmissionLower.RCN215
open RCN095 RCN156 RCN213
def surfaceFlag6600:FlagDegree:=⟨460,35,8⟩
def derivativeFlag6600:FlagDegree:=⟨460,35,7⟩
def agreementDirection6600:FlagDegree:=⟨920,70,15⟩
theorem agreementDirection6600_eq:
   agreementDirection6600=surfaceFlag6600+derivativeFlag6600:=by
 rfl
theorem residualAgreementFlag_eq_affine (d:ℕ):
   residualAgreementFlag d=
     unitYZFlag+d • agreementDirection6600:=by
 change (⟨920*d,1+70*d,15*d⟩:FlagDegree)=
   (⟨0+d*920,1+d*70,0+d*15⟩:FlagDegree)
 congr 1 <;> omega
theorem flagMixed_residualAgreementFlag
   (d e:ℕ):
   flagMixed surfaceFlag6600 (residualAgreementFlag d)
       (residualAgreementFlag e)=
     mixedQuadratic*d*e+mixedLinear*(d+e)+mixedUnit:=by
 norm_num [flagMixed,surfaceFlag6600,residualAgreementFlag,
   mixedQuadratic,mixedLinear,mixedUnit]
 ring
theorem flagMixed_residualAgreementFlag_unitZ (d:ℕ):
   flagMixed surfaceFlag6600 (residualAgreementFlag d) unitZFlag=
     zLinear*d+zUnit:=by
 norm_num [flagMixed,surfaceFlag6600,residualAgreementFlag,unitZFlag,
   zLinear,zUnit]
 ring
theorem flagMixed_direction_values:
   flagMixed surfaceFlag6600 agreementDirection6600 agreementDirection6600=
       mixedQuadratic∧
     flagMixed surfaceFlag6600 agreementDirection6600 unitYZFlag=
       mixedLinear∧
     flagMixed surfaceFlag6600 unitYZFlag unitYZFlag=mixedUnit∧
     flagMixed surfaceFlag6600 agreementDirection6600 unitZFlag=zLinear∧
     flagMixed surfaceFlag6600 unitYZFlag unitZFlag=zUnit:=by
 norm_num [flagMixed,surfaceFlag6600,agreementDirection6600,
   unitYZFlag,unitZFlag,mixedQuadratic,mixedLinear,mixedUnit,
   zLinear,zUnit]
end ProximityPrize.SubmissionLower.RCN215
end PackedLegacy_D5

/-! Packed from ProximityPrize.SubmissionLower.D4. -/
section PackedLegacy_D4
namespace ProximityPrize.SubmissionLower.RCN214
open scoped BigOperators
open RCN095 RCN213 RCN215
set_option maxHeartbeats 1000000
def factorPrimary (p:FlagDegree):ℕ:=
 flagMixed p agreementDirection6600 agreementDirection6600*degreeIncidence^2+
   2*flagMixed p agreementDirection6600 unitYZFlag*
     degreeIncidence*unitIncidence+
   flagMixed p unitYZFlag unitYZFlag*unitIncidence^2
def factorZTail (p:FlagDegree):ℕ:=
 (errors+1)*gap*
   (flagMixed p agreementDirection6600 unitZFlag*degreeIncidence+
     flagMixed p unitYZFlag unitZFlag*unitIncidence)
def factorAllTail (p:FlagDegree):ℕ:=
 (errors+1)*gap*
   (flagMixed p agreementDirection6600 unitAllFlag*degreeIncidence+
     flagMixed p unitYZFlag unitAllFlag*unitIncidence)
def factorRegularLedger (p:FlagDegree):ℕ:=
 factorPrimary p+factorZTail p+factorAllTail p
theorem factorRegularLedger_projection_decomposition (p:FlagDegree):
   factorRegularLedger p=
     p.zOnly*factorRegularLedger unitZFlag+
     p.yz*factorRegularLedger unitYZFlag+
     p.all*factorRegularLedger unitAllFlag:=by
 cases p
 simp [factorRegularLedger,factorPrimary,factorZTail,factorAllTail,flagMixed,
   unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem factorRegularLedger_surface_exact:
   factorRegularLedger surfaceFlag6600=
     stratifiedPrimary+stratifiedZTail+factorAllTail surfaceFlag6600:=by
 simp only [factorRegularLedger,factorPrimary,factorZTail]
 rw [flagMixed_direction_values.1,
   flagMixed_direction_values.2.1,
   flagMixed_direction_values.2.2.1,
   flagMixed_direction_values.2.2.2.1,
   flagMixed_direction_values.2.2.2.2]
 rfl
theorem sum_factorRegularLedger_le_flag
   {I:Type} [Fintype I] (p:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(p i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(p i).yz) ≤ cap.yz)
   (hall:(∑ i,(p i).all) ≤ cap.all):
   (∑ i,factorRegularLedger (p i)) ≤ factorRegularLedger cap:=by
 classical
 calc
   (∑ i,factorRegularLedger (p i))=
       ∑ i,((p i).zOnly*factorRegularLedger unitZFlag+
         (p i).yz*factorRegularLedger unitYZFlag+
         (p i).all*factorRegularLedger unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedger_projection_decomposition (p i)
   _=
       (∑ i,(p i).zOnly)*factorRegularLedger unitZFlag+
       (∑ i,(p i).yz)*factorRegularLedger unitYZFlag+
       (∑ i,(p i).all)*factorRegularLedger unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*factorRegularLedger unitZFlag+
       cap.yz*factorRegularLedger unitYZFlag+
       cap.all*factorRegularLedger unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=factorRegularLedger cap:=
     (factorRegularLedger_projection_decomposition cap).symm
theorem sum_factorRegularLedger_le
   {I:Type} [Fintype I] (p:I → FlagDegree)
   (hz:(∑ i,(p i).zOnly) ≤ surfaceFlag6600.zOnly)
   (hyz:(∑ i,(p i).yz) ≤ surfaceFlag6600.yz)
   (hall:(∑ i,(p i).all) ≤ surfaceFlag6600.all):
   (∑ i,factorRegularLedger (p i)) ≤
     stratifiedPrimary+stratifiedZTail+factorAllTail surfaceFlag6600:=by
 calc
   _ ≤ factorRegularLedger surfaceFlag6600:=
     sum_factorRegularLedger_le_flag p surfaceFlag6600 hz hyz hall
   _=stratifiedPrimary+stratifiedZTail+factorAllTail surfaceFlag6600:=
     factorRegularLedger_surface_exact
def rectangularSurfaceFlag6600:FlagDegree:=⟨495,43,8⟩
def rectangularRegularNumerator:ℕ:=
 factorRegularLedger rectangularSurfaceFlag6600
def rectangularTotalNumerator:ℕ:=
 rectangularRegularNumerator+retainedSingularContribution
def rectangularLedgerCeiling:ℕ:=
 (rectangularTotalNumerator+gap^2-1)/gap^2
theorem rectangular_regular_exact:
   rectangularRegularNumerator=361802540717144456802514527:=by
 norm_num [rectangularRegularNumerator,factorRegularLedger,
   factorPrimary,factorZTail,factorAllTail,rectangularSurfaceFlag6600,
   flagMixed,agreementDirection6600,unitYZFlag,unitZFlag,unitAllFlag,
   degreeIncidence,unitIncidence,errors,gap,agreements,n,w]
theorem rectangular_total_exact:
   rectangularTotalNumerator=368517457418416467513333482:=by
 rw [show rectangularTotalNumerator=
     rectangularRegularNumerator+retainedSingularContribution by rfl,
   rectangular_regular_exact]
 norm_num [retainedSingularContribution]
theorem rectangular_ledger_ceiling_exact:
   rectangularLedgerCeiling=135685232102542715:=by
 norm_num [rectangularLedgerCeiling,rectangular_total_exact,
   gap,agreements,n,errors,w]
theorem rectangular_strict_budget:
   rectangularTotalNumerator < alignmentBudget*gap^2:=by
 rw [rectangular_total_exact]
 norm_num [alignmentBudget,gap,agreements,n,errors,w]
theorem rectangular_budget_slack:
   alignmentBudget-rectangularLedgerCeiling=1805131953154828:=by
 rw [rectangular_ledger_ceiling_exact]
 norm_num [alignmentBudget]
theorem sum_factorRegularLedger_rectangular_le
   {I:Type} [Fintype I] (p:I → FlagDegree)
   (hz:(∑ i,(p i).zOnly) ≤ 495)
   (hyz:(∑ i,(p i).yz) ≤ 43)
   (hall:(∑ i,(p i).all) ≤ 8):
   (∑ i,factorRegularLedger (p i)) ≤ rectangularRegularNumerator:=by
 exact sum_factorRegularLedger_le_flag p rectangularSurfaceFlag6600 hz hyz hall
theorem sum_factor_counts_le
   {I:Type} [Fintype I] (count:I → ℕ) (p:I → FlagDegree)
   (hcount:∀ i,count i*gap^2 ≤ factorRegularLedger (p i))
   (hz:(∑ i,(p i).zOnly) ≤ surfaceFlag6600.zOnly)
   (hyz:(∑ i,(p i).yz) ≤ surfaceFlag6600.yz)
   (hall:(∑ i,(p i).all) ≤ surfaceFlag6600.all):
   (∑ i,count i)*gap^2 ≤
     stratifiedPrimary+stratifiedZTail+factorAllTail surfaceFlag6600:=by
 calc
   (∑ i,count i)*gap^2=∑ i,count i*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ i,factorRegularLedger (p i):=
     Finset.sum_le_sum (fun i _↦hcount i)
   _ ≤ stratifiedPrimary+stratifiedZTail+factorAllTail surfaceFlag6600:=
     sum_factorRegularLedger_le p hz hyz hall
theorem sum_factor_counts_rectangular_le
   {I:Type} [Fintype I] (count:I → ℕ) (p:I → FlagDegree)
   (hcount:∀ i,count i*gap^2 ≤ factorRegularLedger (p i))
   (hz:(∑ i,(p i).zOnly) ≤ 495)
   (hyz:(∑ i,(p i).yz) ≤ 43)
   (hall:(∑ i,(p i).all) ≤ 8):
   (∑ i,count i)*gap^2 ≤ rectangularRegularNumerator:=by
 calc
   (∑ i,count i)*gap^2=∑ i,count i*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ i,factorRegularLedger (p i):=
     Finset.sum_le_sum (fun i _↦hcount i)
   _ ≤ rectangularRegularNumerator:=
     sum_factorRegularLedger_rectangular_le p hz hyz hall
theorem combined_rectangular_scaled_bound
   (regularCount singularCount:ℕ)
   (hregular:regularCount*gap^2 ≤ rectangularRegularNumerator)
   (hsingular:singularCount*gap^2 ≤ retainedSingularContribution):
   (regularCount+singularCount)*gap^2 ≤ rectangularTotalNumerator:=by
 calc
   (regularCount+singularCount)*gap^2=
       regularCount*gap^2+singularCount*gap^2:=by ring
   _ ≤ rectangularRegularNumerator+retainedSingularContribution:=
     Nat.add_le_add hregular hsingular
   _=rectangularTotalNumerator:=rfl
end ProximityPrize.SubmissionLower.RCN214
end PackedLegacy_D4

/-! Packed from ProximityPrize.SubmissionLower.AC. -/
section PackedLegacy_AC
namespace ProximityPrize.SubmissionLower.RCN266
open scoped BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN136 RCN095
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
def regularFlag (Q:MvPolynomial (Fin 4) K) (F:RegularIndex Q):
   FlagDegree:=
 ⟨F.1.degreeOf (3:Fin 4),F.1.degreeOf (1:Fin 4),
   F.1.degreeOf (2:Fin 4)⟩
theorem surfaceMap_in_regularFlag
   (phi:Polynomial K →+*Omega)
   (Q:MvPolynomial (Fin 4) K) (F:RegularIndex Q):
   PolynomialInFlag (regularFlag Q F) (surfaceMap phi F.1):=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 have h0':d 0 ≤ F.1.degreeOf (1:Fin 4):=by
   simpa using h0.trans (surfaceMap_degreeOf_le phi F.1 0)
 have h1':d 1 ≤ F.1.degreeOf (2:Fin 4):=by
   simpa using h1.trans (surfaceMap_degreeOf_le phi F.1 1)
 have h2':d 2 ≤ F.1.degreeOf (3:Fin 4):=by
   simpa using h2.trans (surfaceMap_degreeOf_le phi F.1 2)
 change d 1 ≤ F.1.degreeOf (2:Fin 4)∧
   d 0+d 1 ≤ F.1.degreeOf (1:Fin 4)+F.1.degreeOf (2:Fin 4)∧
   d 0+d 1+d 2 ≤
     F.1.degreeOf (3:Fin 4)+F.1.degreeOf (1:Fin 4)+
       F.1.degreeOf (2:Fin 4)
 omega
theorem regularFlag_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   (∑ F:RegularIndex Q,(regularFlag Q F).zOnly) ≤ 495∧
     (∑ F:RegularIndex Q,(regularFlag Q F).yz) ≤ 43∧
     (∑ F:RegularIndex Q,(regularFlag Q F).all) ≤ 8:=by
 classical
 have hb:=directFactor_input_budgets Q hQ
   weightedCap w seedTotalCap slopeCap (by norm_num [w]) hbox
 simp only [regularFlag,Finset.sum_coe_sort]
 refine ⟨?_,?_,?_⟩
 · simpa [seedTotalCap] using hb.2.2
 · have hy:(weightedCap-1)/w=43:=by
     norm_num [RCN223.weightedCap,
       RCN223.multiplicity,
       RCN223.agreements,
       RCN223.n,
       RCN223.errors,
       RCN223.w]
   simpa only [hy] using hb.1
 · simpa [slopeCap] using hb.2.1
end
end ProximityPrize.SubmissionLower.RCN266
end PackedLegacy_AC

/-! Packed from ProximityPrize.SubmissionLower.I3. -/
section PackedLegacy_I3
namespace ProximityPrize.SubmissionLower.RCN069
open RCN223 RCN174 RCN136 RCN068 RCN238
noncomputable section
def legacyVector (v:RCN223.DegreeVector):
   RCN051.DegreeVector:=⟨v.y,v.r,v.z⟩
variable {K Omega:Type} [Field K] [Field Omega]
theorem fixed_implicit_agreement_caps
   (phi:Polynomial K →+*Omega) (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ implicitYCap)
   (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
   (x u0 u1:K):
   HasCaps (agreementPolynomial phi F w x u0 u1)
     (legacyVector liftedAgreement):=by
 have h:=surface_agreement_caps phi F implicitYCap 1 algebraicCap
   (by decide) hY hR hZ w (fun j => (j.factorial:K)⁻¹) x u0 u1
 simpa [agreementPolynomial,agreementCaps,legacyVector,
   liftedAgreement] using h
theorem fixed_implicit_surface_caps_below_characteristic:
   forall j,capAt (legacyVector liftedSurface) j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,legacyVector,liftedSurface,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates
   (G T:MvPolynomial (Fin 3) Omega)
   (hG:HasCaps G (legacyVector liftedSurface))
   (hT:HasCaps T (legacyVector implicitCut)):
   (forall j,G.degreeOf j < prime)∧
     forall j k:Fin 3,j≠k->
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
 apply actual_characteristic_gates G T _ _ prime hG hT
   fixed_implicit_surface_caps_below_characteristic
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitY,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitR,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitZ,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
end
end ProximityPrize.SubmissionLower.RCN069
end PackedLegacy_I3

/-! Packed from ProximityPrize.SubmissionLower.K6. -/
section PackedLegacy_K6
namespace ProximityPrize.SubmissionLower.RCN171
open scoped Classical BigOperators
open RCN223 RCN294 RCN069 RCN068 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K:Type} [Field K]
def pairCost (A G:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨RCN169.pairYCost ⟨A,G⟩,
   RCN169.pairRCost ⟨A,G⟩,
   RCN169.pairZCost ⟨A,G⟩⟩
variable {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound_fixed
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (hAbox:A∈globalCoefficientBox K implicitWeightedCap w algebraicCap 0)
   (hGbox:G∈globalCoefficientBox K implicitWeightedCap w algebraicCap 1)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
     (errors+1)*gap*RCN169.pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitWeightedCap w algebraicCap 0
   (by norm_num [w]) hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitWeightedCap w algebraicCap 1
   (by norm_num [w]) hGbox
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) (legacyVector implicitCut):=by
   intro i
   fin_cases i
   · simpa [legacyVector,RCN068.capAt,implicitCut,implicitYCap] using
       (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
   · simpa [legacyVector,RCN068.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · simpa [legacyVector,RCN068.capAt,implicitCut] using
       (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ (polynomialEmbedding_injective K)
     G hG.ne_zero (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*gap ≤
       (n-w)*(∑ i:Fin 3,
         capAt (legacyVector liftedAgreement) i*
           capAt (RCN170.geometricPairCost A g) i)+
         (errors+1)*gap*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g (legacyVector liftedSurface):=by
     intro i
     fin_cases i
     · simpa [legacyVector,RCN068.capAt,liftedSurface,implicitYCap] using
         (hfacdegree 0).trans hGGcaps.1
     · simpa [legacyVector,RCN068.capAt,liftedSurface] using
         (hfacdegree 1).trans hGGcaps.2.1
     · simpa [legacyVector,RCN068.capAt,liftedSurface] using
         (hfacdegree 2).trans hGGcaps.2.2
   have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
   have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (RCN231.polynomialPoint (φ.comp Polynomial.C)
         (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
       (legacyVector liftedAgreement):=
     RCN069.fixed_implicit_agreement_caps φ G
       hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj prime w agreements errors
     (by norm_num [w]) (by norm_num [w,prime])
     (by norm_num [w,agreements,n,errors])
     (by rw [hnodes];norm_num [agreements,n,errors]) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
     (capAt (legacyVector liftedAgreement)) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i) (hδ i))))
     (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=
     Nat.mul_le_mul_right gap hcard
   _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt (legacyVector liftedAgreement) i*
         capAt (RCN170.geometricPairCost A g) i)+
       (errors+1)*gap*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (errors+1)*gap*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt (legacyVector liftedAgreement) i*
       capAt (RCN170.pairCost A G) i)+
       (errors+1)*gap*capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt (legacyVector liftedAgreement) i)
         (hbudget i))))
       (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
   _=(n-w)*dot liftedAgreement (pairCost A G)+
       (errors+1)*gap*RCN169.pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,RCN068.capAt,legacyVector,
       RCN170.pairCost,pairCost,
       RCN169.pairYCost,RCN169.pairRCost,
       RCN169.pairZCost,dot]
end
end ProximityPrize.SubmissionLower.RCN171
end PackedLegacy_K6

/-! Packed from ProximityPrize.SubmissionLower.F1. -/
section PackedLegacy_F1
namespace ProximityPrize.SubmissionLower.RCN291
open scoped BigOperators
open RCN223 RCN294 RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN171 RCN081 RCN238 RCN243
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=by
 classical
 exact Gamma.filter (fun gamma => LiftedSolutionPair q.1 (selected gamma) gamma)
def implicitVector (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):Finset K:=by
 classical
 exact Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):implicitSeeds Q selected Gamma q ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitSeeds_solution (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q) (gamma:K)
   (hgamma:gamma∈implicitSeeds Q selected Gamma q):
   LiftedSolutionPair q.1 (selected gamma) gamma:=by
 classical
 exact (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
   (Q:MvPolynomial (Fin 4) K)
   (selected:K-> Polynomial K) (Gamma:Finset K):
   (singularSeeds Q selected Gamma).card ≤
     (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
       (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
 classical
 unfold singularSeeds
 exact (Finset.card_union_le _ _).trans
   (Nat.add_le_add_right Finset.card_biUnion_le _)
theorem implicitVector_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   (∑ q:ImplicitIndex Q,(implicitVector Q q).y) ≤ algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).r) ≤
       2*implicitYCap*algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).z) ≤ implicitYCap:=by
 classical
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
   weightedCap w seedTotalCap slopeCap prime hQ
   (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
 have hb:=implicitPair_input_budgets (singularAuxiliary Q) hJ
   implicitWeightedCap w algebraicCap (by norm_num [w]) hJbox
 simpa only [implicitVector,Finset.sum_coe_sort,implicitYCap] using hb
theorem exceptionalSeeds_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K-> Polynomial K) (Gamma:Finset K):
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
     2*algebraicCap^2:=by
 classical
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
   weightedCap w seedTotalCap slopeCap prime hQ
   (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
 have hcaps:=degree_bounds_of_mem_box (singularAuxiliary Q)
   implicitWeightedCap w algebraicCap 0 (by norm_num [w]) hJbox
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=
   Nat.eq_zero_of_le_zero hcaps.2.1
 apply exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
   algebraicCap prime
 · norm_num [algebraicCap,slopeCap,seedTotalCap]
 · exact characteristic_gates.2.2.1
 · exact hcaps.1.trans (by
     norm_num [implicitYCap,implicitWeightedCap,weightedCap,
       RCN223.multiplicity,agreements,n,errors,
       w,algebraicCap,slopeCap,seedTotalCap])
 · exact hcaps.2.2
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem implicitSeeds_pair_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota-> K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (q:ImplicitIndex Q):
   (implicitSeeds Q selected Gamma q).card*gap ≤
     (n-w)*dot liftedAgreement (implicitVector Q q)+
       (errors+1)*gap*(implicitVector Q q).z:=by
 classical
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q
   weightedCap w seedTotalCap slopeCap prime hQ
   (by norm_num [slopeCap]) characteristic_gates.2.2.2 hbox
 obtain ⟨_hA,hG,hGR,hAbox,hGbox,hproper⟩:=
   implicitPair_data (singularAuxiliary Q) hJ implicitWeightedCap w
     algebraicCap (by norm_num [w])
     (by norm_num [w,implicitWeightedCap,weightedCap,
       RCN223.multiplicity,agreements,n,errors,
       slopeCap]) hJbox q.1 q.2
 have hsub:=implicitSeeds_subset Q selected Gamma q
 have hpair:=RCN171.implicit_pair_seed_bound_fixed
   q.1.1 q.1.2 hG hGR hproper hAbox hGbox selected
   (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
   (fun gamma hgamma => hdegree gamma (hsub hgamma))
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
   (fun gamma hgamma => hagreement gamma (hsub hgamma))
   (noLargeSelectedPencil_mono selected Gamma _ w errors hsub hnoPencil)
 simpa [implicitVector,
   RCN171.pairCost] using hpair
theorem singularSeeds_gap_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota-> K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (singularSeeds Q selected Gamma).card*gap ≤
     retainedSingularNumerator:=by
 have hcaps:=implicitVector_budgets Q hQ hbox
 have hexc:=exceptionalSeeds_bound Q hQ hbox selected Gamma
 have hsum:=implicit_with_exceptions_bound
   (fun q:ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
   (implicitVector Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hcaps.1 hcaps.2.1 hcaps.2.2
   (implicitSeeds_pair_bound Q hQ hbox selected Gamma nodes x u0 u1
     hinj hnodes hdegree hagreement hnoPencil)
   hexc
 exact (Nat.mul_le_mul_right gap
   (singularSeeds_card_le_sum Q selected Gamma)).trans hsum
theorem singularSeeds_scaled_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K-> Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota-> K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (singularSeeds Q selected Gamma).card*gap^2 ≤
     retainedSingularContribution:=by
 have h:=singularSeeds_gap_bound Q hQ hbox selected Gamma nodes x u0 u1
   hinj hnodes hdegree hagreement hnoPencil
 calc
   (singularSeeds Q selected Gamma).card*gap^2=
       ((singularSeeds Q selected Gamma).card*gap)*gap:=by ring
   _ ≤ retainedSingularNumerator*gap:=Nat.mul_le_mul_right gap h
   _=retainedSingularContribution:=by
     simp only [retainedSingularContribution]
     ring
end
end ProximityPrize.SubmissionLower.RCN291
end PackedLegacy_F1

/-! Packed from ProximityPrize.SubmissionLower.Z4. -/
section PackedLegacy_Z4
namespace ProximityPrize.SubmissionLower.RCN140
open scoped Classical BigOperators
open RCN223 RCN286 RCN167 RCN174 RCN319 RCN081 RCN266 RCN291 RCN214 RCN238
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def regularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):Finset K:=
 Gamma.filter (fun gamma↦RegularSolution F.1 (selected gamma) gamma)
theorem regularSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RCN266.RegularIndex Q):
   regularSeeds Q selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem card_le_regular_sum_add_singular
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RCN266.RegularIndex Q,
       (regularSeeds Q selected Gamma F).card)+
     (singularSeeds Q selected Gamma).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩ | hexc:=
     solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
       (by norm_num [slopeCap]) characteristic_gates.2.2.2
       (by norm_num [w])
       (by norm_num [RCN223.w,
         RCN223.weightedCap,
         RCN223.multiplicity,
         RCN223.agreements,
         RCN223.n,
         RCN223.errors,
         RCN223.slopeCap])
       hbox (selected gamma) gamma (hsolution gamma hgamma)
   · apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨q,hq⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact Finset.mem_filter.mpr ⟨hgamma,hexc⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RCN266.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem regularSeeds_scaled_rectangular_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hregular:∀ F:RCN266.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   (∑ F:RCN266.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card)*gap^2 ≤
       rectangularRegularNumerator:=by
 have hcaps:=regularFlag_budgets Q hQ hbox
 exact sum_factor_counts_rectangular_le
   (fun F:RCN266.RegularIndex Q↦
     (regularSeeds Q selected Gamma F).card)
   (regularFlag Q) hregular hcaps.1 hcaps.2.1 hcaps.2.2
theorem global_scaled_bound_of_regular_factors
   {Iota:Type} [DecidableEq Iota]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (hregular:∀ F:RCN266.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   Gamma.card*gap^2 ≤ rectangularTotalNumerator:=by
 have hcover:=card_le_regular_sum_add_singular Q hQ hbox selected Gamma
   hsolution
 have hreg:=regularSeeds_scaled_rectangular_bound Q hQ hbox selected Gamma
   hregular
 have hsing:=singularSeeds_scaled_bound Q hQ hbox selected Gamma nodes
   x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 calc
   Gamma.card*gap^2 ≤
       ((∑ F:RCN266.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
         (singularSeeds Q selected Gamma).card)*gap^2:=
     Nat.mul_le_mul_right (gap^2) hcover
   _=(∑ F:RCN266.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)*gap^2+
       (singularSeeds Q selected Gamma).card*gap^2:=by ring
   _ ≤ rectangularRegularNumerator+retainedSingularContribution:=
     Nat.add_le_add hreg hsing
   _=rectangularTotalNumerator:=rfl
theorem global_count_lt_alignment_of_regular_factors
   {Iota:Type} [DecidableEq Iota]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (hregular:∀ F:RCN266.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   Gamma.card < alignmentBudget:=by
 have hscaled:=global_scaled_bound_of_regular_factors Q hQ hbox selected
   Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
   hregular
 have hlt:Gamma.card*gap^2 < alignmentBudget*gap^2:=
   hscaled.trans_lt rectangular_strict_budget
 exact Nat.lt_of_mul_lt_mul_right hlt
end
end ProximityPrize.SubmissionLower.RCN140
end PackedLegacy_Z4

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier11 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BC. -/
section PackedLegacy_BC
namespace ProximityPrize.SubmissionLower.RCN119
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def slopeDifference:Poly K:=MvPolynomial.X 0-MvPolynomial.X 1
private def plusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0+MvPolynomial.X 1 else MvPolynomial.X i
private def minusVariables (i:Fin 3):Poly K:=
 if i=0 then MvPolynomial.X 0-MvPolynomial.X 1 else MvPolynomial.X i
def shiftPlus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (plusVariables K)
def shiftMinus:Poly K →ₐ[K] Poly K:=MvPolynomial.aeval (minusVariables K)
theorem shiftMinus_comp_shiftPlus:
   (shiftMinus K).comp (shiftPlus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
theorem shiftPlus_comp_shiftMinus:
   (shiftPlus K).comp (shiftMinus K)=AlgHom.id K (Poly K):=by
 ext i
 fin_cases i <;> simp [shiftPlus,shiftMinus,plusVariables,minusVariables]
@[simp] theorem shiftMinus_shiftPlus (f:Poly K):
   shiftMinus K (shiftPlus K f)=f:=
 DFunLike.congr_fun (shiftMinus_comp_shiftPlus K) f
@[simp] theorem shiftPlus_shiftMinus (f:Poly K):
   shiftPlus K (shiftMinus K f)=f:=
 DFunLike.congr_fun (shiftPlus_comp_shiftMinus K) f
@[simp] theorem shiftPlus_slopeDifference:
   shiftPlus K (slopeDifference K)=MvPolynomial.X 0:=by
 simp [slopeDifference,shiftPlus,plusVariables]
@[simp] theorem shiftMinus_X_zero:
   shiftMinus K (MvPolynomial.X 0)=slopeDifference K:=by
 simp [shiftMinus,minusVariables,slopeDifference]
theorem slopeDifference_ne_zero:slopeDifference K≠0:=by
 intro h
 have hh:=congrArg (shiftPlus K) h
 simpa using hh
def monomialRemainder (d:Fin 3 →₀ ℕ):Poly K →ₗ[K] Poly K where
 toFun f:=f.modMonomial d
 map_add' f g:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
 map_smul' c f:=by
   ext e
   by_cases he:d ≤ e
   · simp [MvPolynomial.coeff_modMonomial_of_le _ he]
   · simp [MvPolynomial.coeff_modMonomial_of_not_le _ he]
def contactJet (h:ℕ):Poly K →ₗ[K] Poly K:=
 (monomialRemainder K (Finsupp.single 0 h)).comp (shiftPlus K).toLinearMap
theorem contactJet_apply (h:ℕ) (f:Poly K):
   contactJet K h f=(shiftPlus K f).modMonomial (Finsupp.single 0 h):=rfl
theorem contactJet_eq_zero_iff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔ slopeDifference K^h∣f:=by
 rw [contactJet_apply,
   ←MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero,
   ←MvPolynomial.X_pow_eq_monomial]
 constructor
 · rintro ⟨q,hq⟩
   refine ⟨shiftMinus K q,?_⟩
   have hh:=congrArg (shiftMinus K) hq
   simpa only [shiftMinus_shiftPlus,map_mul,map_pow,shiftMinus_X_zero] using hh
 · rintro ⟨q,rfl⟩
   exact ⟨shiftPlus K q,by simp⟩
theorem contactJet_mul_slopeDifference (h:ℕ) (q:Poly K):
   contactJet K h (slopeDifference K^h*q)=0:=
 (contactJet_eq_zero_iff K h _).2 ⟨q,rfl⟩
theorem contactJet_eq_zero_iff_coeff (h:ℕ) (f:Poly K):
   contactJet K h f=0 ↔
     ∀ d:Fin 3 →₀ ℕ,d 0 < h → MvPolynomial.coeff d (shiftPlus K f)=0:=by
 constructor
 · intro hf d hd
   have hnot:¬ Finsupp.single (0:Fin 3) h ≤ d:=by
     intro hle
     have hh:=hle 0
     simp only [Finsupp.single_eq_same] at hh
     omega
   have hh:=congrArg (MvPolynomial.coeff d) hf
   simpa [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hnot] using hh
 · intro hf
   ext d
   by_cases hle:Finsupp.single (0:Fin 3) h ≤ d
   · simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_le _ hle]
   · have hd:d 0 < h:=by
       by_contra hnot
       apply hle
       intro i
       by_cases hi:i=0
       · subst i
         simp only [Finsupp.single_eq_same]
         omega
       · simp [Finsupp.single_eq_of_ne hi]
     simp [contactJet_apply,MvPolynomial.coeff_modMonomial_of_not_le _ hle,hf d hd]
def boxExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1+d 2 ≤ L∧d 1 ≤ s}
def coefficientBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (boxExponents M L s)
theorem mem_coefficientBox_iff (M L s:ℕ) (f:Poly K):
   f∈coefficientBox K M L s ↔
     ∀ d∈f.support,d 0 ≤ M∧d 0+d 1+d 2 ≤ L∧d 1 ≤ s:=by
 rfl
theorem coefficientBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈coefficientBox K M L s)
   (hg:g∈coefficientBox K M' L' s'):
   f*g∈coefficientBox K (M+M') (L+L') (s+s'):=by
 have hset:boxExponents M L s+boxExponents M' L' s' ⊆
     boxExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hdTotal,hd1⟩
   rcases he with ⟨he0,heTotal,he1⟩
   simp only [boxExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   omega
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_coefficientBox:
   slopeDifference K∈coefficientBox K 1 1 1:=by
 apply (coefficientBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem slopeDifference_pow_mem_coefficientBox (h:ℕ):
   slopeDifference K^h∈coefficientBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ h ih =>
     simpa only [pow_succ] using coefficientBox_mul K ih (slopeDifference_mem_coefficientBox K)
theorem slopeDifference_mul_mem_coefficientBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈coefficientBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈coefficientBox K M L s:=by
 have hh:=coefficientBox_mul K (slopeDifference_pow_mem_coefficientBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,Nat.add_sub_of_le hs] using hh
private def exponentTriple (i j z:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j+Finsupp.single 2 z
@[simp] private theorem exponentTriple_zero (i j z:ℕ):
   exponentTriple i j z 0=i:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_one (i j z:ℕ):
   exponentTriple i j z 1=j:=by simp [exponentTriple]
@[simp] private theorem exponentTriple_two (i j z:ℕ):
   exponentTriple i j z 2=z:=by simp [exponentTriple]
private theorem exponentTriple_eta (d:Fin 3 →₀ ℕ):
   exponentTriple (d 0) (d 1) (d 2)=d:=by
 ext i
 fin_cases i <;> simp
private theorem finPair_heq_of_val_eq
   {n a b:ℕ} {i j:Fin n} {u:Fin a} {v:Fin b}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (i,u) (j,v):=by
 subst b
 have hi:i=j:=Fin.ext hij
 have hu:u=v:=Fin.ext huv
 cases hi
 cases hu
 rfl
private theorem finSigma_heq_of_val_eq
   {n:ℕ} {a b:Fin n → ℕ}
   {i j:Fin n} {u:Fin (a i)} {v:Fin (b j)}
   (hab:a=b) (hij:i.val=j.val) (huv:u.val=v.val):
   HEq (⟨i,u⟩:(k:Fin n) × Fin (a k))
     (⟨j,v⟩:(k:Fin n) × Fin (b k)):=by
 subst b
 have hi:i=j:=Fin.ext hij
 subst j
 have hu:u=v:=Fin.ext huv
 subst v
 rfl
abbrev BoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) ×
   (j:Fin (s+1)) × Fin (L+1-i.val-j.val)
def boxExponentsEquivIndex (M L s:ℕ):
   boxExponents M L s ≃ BoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨⟨d.val 1,by
       rcases d.property with ⟨hM,hL,hs⟩
       omega⟩,
     ⟨d.val 2,by
       rcases d.property with ⟨hM,hL,hs⟩
       change d.val 2 < L+1-d.val 0-d.val 1
       omega⟩⟩⟩
 invFun q:=
   ⟨exponentTriple q.1.val q.2.1.val q.2.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.1.isLt
     have hz:=q.2.2.isLt
     simp only [boxExponents,Set.mem_setOf_eq,exponentTriple_zero,
       exponentTriple_one,exponentTriple_two]
     omega⟩
 left_inv d:=Subtype.ext (exponentTriple_eta d.val)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨⟨j,hj⟩,⟨z,hz⟩⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentTriple_zero i j z
   · dsimp only
     apply @finSigma_heq_of_val_eq (s+1)
       (fun k↦L+1-(exponentTriple i j z) 0-k.val)
       (fun k↦L+1-i-k.val) _ _ _ _
     · funext k
       simp only [exponentTriple_zero]
     · exact exponentTriple_one i j z
     · exact exponentTriple_two i j z
instance boxExponentsFintype (M L s:ℕ):Fintype (boxExponents M L s):=
 Fintype.ofEquiv (BoxIndex M L s) (boxExponentsEquivIndex M L s).symm
instance coefficientBoxFinite (M L s:ℕ):
   Module.Finite K (coefficientBox K M L s):=
 Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K (boxExponents M L s))
theorem coefficientBox_finrank (M L s:ℕ):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 change Module.finrank K (MvPolynomial.restrictSupport K (boxExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (boxExponents M L s))]
 rw [Fintype.card_congr (boxExponentsEquivIndex M L s)]
 simp [BoxIndex,Fintype.card_sigma]
theorem coefficientBox_finrank_of_le (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 exact coefficientBox_finrank K M L s
def multiplyIntoBox {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     coefficientBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_coefficientBox K hM hL hs q.property⟩
 map_add' q r:=by
   apply Subtype.ext
   simp [mul_add]
 map_smul' c q:=by
   apply Subtype.ext
   simp [mul_smul_comm]
theorem multiplyIntoBox_injective
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=slopeDifference K^h*r.val:=
   congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def blockJet (M L s h:ℕ):coefficientBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (coefficientBox K M L s).subtype
def kernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   coefficientBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (blockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (blockJet K M L s h))
   (multiplyIntoBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem kernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (kernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoBox_injective K hM hL hs
 exact congrArg Subtype.val heq
theorem blockJet_rank_add_quotient_finrank_le {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h))+
       Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) ≤
     Module.finrank K (coefficientBox K M L s):=by
 have hker:=LinearMap.finrank_le_finrank_of_injective
   (kernelEmbedding_injective K hM hL hs)
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 omega
theorem blockJet_rank_le_triangle_difference {M L s h:ℕ}
   (hML:M ≤ L) (hM:h ≤ M) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (∑ i:Fin (M+1),
         ∑ j:Fin (s+1),(L+1-i.val-j.val))-
       (∑ i:Fin (M-h+1),
         ∑ j:Fin (s-h+1),(L-h+1-i.val-j.val)):=by
 have hineq:=blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
 rw [coefficientBox_finrank_of_le K M L s hML,
   coefficientBox_finrank_of_le K (M-h) (L-h) (s-h)
     (Nat.sub_le_sub_right hML h)] at hineq
 omega
theorem blockJet_rank_le_input (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     ∑ i:Fin (M+1),
       ∑ j:Fin (s+1),(L+1-i.val-j.val):=by
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 rw [coefficientBox_finrank_of_le K M L s hML] at hsum
 omega
theorem coefficientBox_finrank_range (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     ∑ i∈Finset.range (M+1),
       ∑ j∈Finset.range (s+1),(L+1-i-j):=by
 rw [coefficientBox_finrank_of_le K M L s hML]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro i hi
 rw [Finset.sum_range]
def blockInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),
   ∑ j∈Finset.range (s+1),(L+1-i-j)
def blockKernelLowerBound (M L s h:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1-h),
   ∑ j∈Finset.range (s+1-h),(L+1-h-i-j)
def contactRankBound (M L s h:ℕ):ℕ:=
 blockInputCount M L s-blockKernelLowerBound M L s h
theorem blockJet_rank_le_contactRankBound (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     contactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hineq:=blockJet_rank_add_quotient_finrank_le K hM hL hs
     rw [coefficientBox_finrank_range K M L s hML,
       coefficientBox_finrank_range K (M-h) (L-h) (s-h)
         (Nat.sub_le_sub_right hML h)] at hineq
     have hMeq:M-h+1=M+1-h:=by omega
     have hLeq:L-h+1=L+1-h:=by omega
     have hseq:s-h+1=s+1-h:=by omega
     rw [hMeq,hLeq,hseq] at hineq
     unfold contactRankBound blockInputCount blockKernelLowerBound
     omega
   · have hzero:s+1-h=0:=by omega
     have hinput:=blockJet_rank_le_input K M L s h hML
     simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
       hzero,Finset.sum_range] using hinput
 · have hzero:M+1-h=0:=by omega
   have hinput:=blockJet_rank_le_input K M L s h hML
   simpa [contactRankBound,blockKernelLowerBound,blockInputCount,
     hzero,Finset.sum_range] using hinput
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   contactRankBound (min r L) L s (min (r+1) (m-r))
theorem sum_blockJet_ranks_le_localRankBound (m L s:ℕ):
   (∑ r∈Finset.range m,
     Module.finrank K (LinearMap.range
       (blockJet K (min r L) L s (min (r+1) (m-r))))) ≤
     localRankBound m L s:=by
 apply Finset.sum_le_sum
 intro r hr
 exact blockJet_rank_le_contactRankBound K (min r L) L s
   (min (r+1) (m-r)) (min_le_right r L)
end
end ProximityPrize.SubmissionLower.RCN119
end PackedLegacy_BC

/-! Packed from ProximityPrize.SubmissionLower.C1. -/
section PackedLegacy_C1
namespace ProximityPrize.SubmissionLower.RCN100
open RCN119 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
theorem coefficientBox_mono {M L s M' L' s':ℕ}
   (hM:M ≤ M') (hL:L ≤ L') (hs:s ≤ s'):
   coefficientBox K M L s ≤ coefficientBox K M' L' s':=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 exact ⟨hd.1.trans hM,hd.2.1.trans hL,hd.2.2.trans hs⟩
def localMonomial (f j z:ℕ):Poly K:=
 MvPolynomial.monomial
   (Finsupp.single 0 f+Finsupp.single 1 j+Finsupp.single 2 z) 1
theorem localMonomial_mem (f j z:ℕ):
   localMonomial K f j z∈coefficientBox K f (f+j+z) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [boxExponents]
def seedAffine (u₀ u₁:K):Poly K:=
 MvPolynomial.C u₀+MvPolynomial.monomial (Finsupp.single 2 1) u₁
theorem seedAffine_mem (u₀ u₁:K):
   seedAffine K u₀ u₁∈coefficientBox K 0 1 0:=by
 apply (coefficientBox K 0 1 0).add_mem
 · change MvPolynomial.monomial 0 u₀∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem seedAffine_pow_mem (u₀ u₁:K) (t:ℕ):
   seedAffine K u₀ u₁^t∈coefficientBox K 0 t 0:=by
 induction t with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ t ih =>
     simpa only [pow_succ,Nat.zero_add] using
       coefficientBox_mul K ih (seedAffine_mem K u₀ u₁)
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (L+1-i.val-j.val) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ} (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val+Finsupp.single 3 c.2.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 0=c.2.2.2.val:=by simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 1=c.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 2=c.2.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 3=c.2.2.1.val:=by simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 have hz:=congrArg (fun e:Fin 4 →₀ ℕ => e 3) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 simp only [columnExponent_z] at hz
 subst di
 subst dj
 subst dz
 subst de
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have hz:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 simp only [globalExponents,Set.mem_setOf_eq,columnExponent_x,
   columnExponent_y,columnExponent_r,columnExponent_z]
 omega
def reconstruct (D w L s:ℕ) (θ:CoefficientIndex D w L s → K):
   MvPolynomial (Fin 4) K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (θ c)
theorem reconstruct_coeff (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s θ)=θ c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro θ η h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (hθ:θ≠0):
   reconstruct K D w L s θ≠0:=by
 intro hzero
 apply hθ
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hzero
theorem reconstruct_mem_globalCoefficientBox (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   reconstruct K D w L s θ∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (θ c)
theorem reconstruct_support_caps (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   ∀ d∈(reconstruct K D w L s θ).support,
     d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
       d 0+w*d 1+(w-1)*d 2 < D:=
 reconstruct_mem_globalCoefficientBox K D w L s θ
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,Finset.sum_range]
def blockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):Poly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     (((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)) •
         (seedAffine K u₀ u₁^(c.1.val-f.val)*
           localMonomial K f.val c.2.1.val c.2.2.1.val)
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u₀ u₁ c r∈
     coefficientBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (coefficientBox K (min r L) L s).smul_mem
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have hz:=c.2.2.1.isLt
   have hfi:=f.isLt
   have hmul:=coefficientBox_mul K
     (seedAffine_pow_mem K u₀ u₁ (c.1.val-f.val))
     (localMonomial_mem K f.val c.2.1.val c.2.2.1.val)
   apply coefficientBox_mono K (show 0+f.val ≤ min r L by omega)
     (show c.1.val-f.val+
         (f.val+c.2.1.val+c.2.2.1.val) ≤ L by omega)
     (show 0+c.2.1.val ≤ s by omega)
   exact hmul
 · exact (coefficientBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   coefficientBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u₀ u₁ c r,
   blockEntry_mem K D w L s x u₀ u₁ c r⟩
def extractBlock (D w L s:ℕ) (x u₀ u₁:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     coefficientBox K (min r L) L s where
 toFun θ:=∑ c:CoefficientIndex D w L s,
   θ c • boundedBlockEntry K D w L s x u₀ u₁ c r
 map_add' θ η:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a θ:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]
theorem full_contactRankBound_eq (r m L s:ℕ):
   contactRankBound (min r L) L s (m-r)=
     contactRankBound (min r L) L s (min (r+1) (m-r)):=by
 by_cases h:r+1 ≤ m-r
 · have hM:min r L ≤ r:=min_le_left r L
   have hzero:min r L+1-(m-r)=0:=by omega
   have hzero':min r L+1-(r+1)=0:=by omega
   simp only [Nat.min_eq_left h,contactRankBound,blockKernelLowerBound,
     hzero,hzero',Finset.range_zero,Finset.sum_empty,mul_zero,Nat.sub_zero]
 · have h':m-r ≤ r+1:=by omega
   rw [Nat.min_eq_right h']
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 have hh:=blockJet_rank_le_contactRankBound K (min r.val L) L s (m-r.val)
   (min_le_right r.val L)
 rw [full_contactRankBound_eq] at hh
 exact hh
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
theorem globalTarget_finrank_le {I:Type*} [Fintype I] (m L s:ℕ):
   Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
 change Module.finrank K (I → LocalTarget K m L s) ≤ _
 rw [Module.finrank_pi_fintype]
 calc
   (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
       ∑ _i:I,localRankBound m L s:=by
     apply Finset.sum_le_sum
     intro i hi
     exact localTarget_finrank_le K m L s
   _=Fintype.card I*localRankBound m L s:=by simp
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
theorem constraintMap_apply {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (θ:CoefficientIndex D w L s → K) (i:I) (r:Fin m):
   ((constraintMap K D w L s m nodes u₀ u₁ θ i r):Poly K)=
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K):=rfl
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,
     θ≠0∧constraintMap K D w L s m nodes u₀ u₁ θ=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective (constraintMap K D w L s m nodes u₀ u₁):=by
   intro θ η heq
   by_contra hne
   apply hnone
   refine ⟨θ-η,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have hupper:=globalTarget_finrank_le K (I:=I) m L s
 exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)
theorem exists_nonzero_block_equations {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,θ≠0∧
     ∀ (i:I) (r:Fin m),
       contactJet K (m-r.val)
         ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0:=by
 obtain ⟨θ,hθ,hzero⟩:=exists_nonzero_kernel_array K D w L s m nodes u₀ u₁ hgate
 refine ⟨θ,hθ,?_⟩
 intro i r
 have hh:=congrArg (fun t:GlobalTarget K I m L s => ((t i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0 at hh
 exact hh
theorem all_blocks_divisible_of_equations
   (D w L s m:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K)
   (h:∀ r:Fin m,contactJet K (m-r.val)
     ((extractBlock K D w L s x u₀ u₁ r.val θ):Poly K)=0):
   ∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 intro r
 by_cases hr:r < m
 · exact (contactJet_eq_zero_iff K (m-r) _).mp (h ⟨r,hr⟩)
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
end
end ProximityPrize.SubmissionLower.RCN100
end PackedLegacy_C1

/-! Packed from ProximityPrize.SubmissionLower.BD. -/
section PackedLegacy_BD
namespace ProximityPrize.SubmissionLower.RCN122
open RCN119 RCN100 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
abbrev LocalPolynomial:=Polynomial (Poly K)
def translationVariables (x u₀ u₁:K):Fin 4 → LocalPolynomial K:=
 ![Polynomial.X+Polynomial.C (MvPolynomial.C x),
   Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
     Polynomial.C (seedAffine K u₀ u₁),
   Polynomial.C (MvPolynomial.X 1),
   Polynomial.C (MvPolynomial.X 2)]
def homogenizedTranslation (x u₀ u₁:K):
   MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K:=
 MvPolynomial.aeval (translationVariables K x u₀ u₁)
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val*
       MvPolynomial.X 3^c.2.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j z:ℕ):
   localMonomial K f j z=
     MvPolynomial.X 0^f*MvPolynomial.X 1^j*MvPolynomial.X 2^z:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.X_pow_eq_monomial]
theorem coeff_shifted_affine_product
   {A:Type*} [CommRing A] (x a y b:A) (e i r:ℕ):
   (((Polynomial.X+Polynomial.C x)^e*
       (Polynomial.X*Polynomial.C y+Polynomial.C a)^i*
       Polynomial.C b):Polynomial A).coeff r=
     ∑ f:Fin (i+1),if f.val ≤ r then
       (x^(e-(r-f.val))*(e.choose (r-f.val):A))*
         (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b)
     else 0:=by
 rw [add_pow (Polynomial.X*Polynomial.C y) (Polynomial.C a) i,
   Finset.mul_sum,Finset.sum_mul,Polynomial.finsetSum_coeff]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro f hf
 have hfactor:
     (((Polynomial.X+Polynomial.C x)^e*
       ((Polynomial.X*Polynomial.C y)^f.val*
         Polynomial.C a^(i-f.val)*(i.choose f.val:Polynomial A)))*
         Polynomial.C b)=
       (((Polynomial.X+Polynomial.C x)^e*
         Polynomial.C (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b))*
         Polynomial.X^f.val):=by
   simp only [mul_pow,map_mul,map_pow,map_natCast]
   ring
 rw [hfactor,Polynomial.coeff_mul_X_pow']
 split_ifs with hfr
 · rw [Polynomial.coeff_mul_C,Polynomial.coeff_X_add_C_pow]
 · rfl
theorem translation_column (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K):
   homogenizedTranslation K x u₀ u₁ (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       (Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
       (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
         Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
       Polynomial.C (MvPolynomial.X 1)^c.2.1.val*
       Polynomial.C (MvPolynomial.X 2)^c.2.2.1.val:=by
 rw [columnMonomial_eq K D w L s c a]
 simp [homogenizedTranslation,translationVariables,
   Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
theorem translation_column_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u₀ u₁ c r:=by
 have hfactor:
     homogenizedTranslation K x u₀ u₁
       (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       ((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
         (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
           Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
         Polynomial.C (MvPolynomial.X 1^c.2.1.val*
           MvPolynomial.X 2^c.2.2.1.val)):=by
   rw [translation_column K D w L s x u₀ u₁ c a]
   simp only [map_mul,map_pow]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,
     map_mul,map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁ (reconstruct K D w L s θ)).coeff r=
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
   θ c • blockEntry K D w L s x u₀ u₁ c r)=
     (((∑ c:CoefficientIndex D w L s,
       θ c • boundedBlockEntry K D w L s x u₀ u₁ c r):
         coefficientBox K (min r L) L s):Poly K)
 simp [boundedBlockEntry]
def contactEvaluation (R B:Polynomial K) (γ:K):Poly K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![R+Polynomial.X*B,R,Polynomial.C γ]
def outerEvaluation (R B:Polynomial K) (γ:K):
   LocalPolynomial K →+*Polynomial K:=
 Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X
@[simp] theorem contactEvaluation_slopeDifference (R B:Polynomial K) (γ:K):
   contactEvaluation K R B γ (slopeDifference K)=Polynomial.X*B:=by
 simp [contactEvaluation,slopeDifference]
theorem contactEvaluation_seedAffine (R B:Polynomial K) (γ u₀ u₁:K):
   contactEvaluation K R B γ (seedAffine K u₀ u₁)=
     Polynomial.C (u₀+γ*u₁):=by
 rw [seedAffine, ←MvPolynomial.C_mul_X_eq_monomial]
 simp [contactEvaluation,Polynomial.algebraMap_eq,mul_comm]
theorem outerEvaluation_contact_dvd
   (H:LocalPolynomial K) (m:ℕ) (R B:Polynomial K) (γ:K)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣H.coeff r):
   (Polynomial.X:Polynomial K)^m∣outerEvaluation K R B γ H:=by
 classical
 change (Polynomial.X:Polynomial K)^m∣
   H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
 rw [Polynomial.eval₂_eq_sum]
 change (Polynomial.X:Polynomial K)^m∣
   ∑ r∈H.support,contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r
 apply Finset.dvd_sum
 intro r hr
 have hlocal:(Polynomial.X:Polynomial K)^(m-r)∣
     contactEvaluation K R B γ (H.coeff r):=by
   obtain ⟨q,hq⟩:=hcoeff r
   refine ⟨B^(m-r)*contactEvaluation K R B γ q,?_⟩
   simp only [hq,map_mul,map_pow,contactEvaluation_slopeDifference,
     mul_pow,mul_assoc]
 have hprod:=mul_dvd_mul hlocal
   (dvd_refl ((Polynomial.X:Polynomial K)^r))
 have htotal:(Polynomial.X:Polynomial K)^((m-r)+r)∣
     contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r:=by
   simpa only [pow_add] using hprod
 exact (pow_dvd_pow Polynomial.X (show m ≤ (m-r)+r by omega)).trans htotal
def specialization (P:Polynomial K) (γ:K):
   MvPolynomial (Fin 4) K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![Polynomial.X,P,P.derivative,Polynomial.C γ]
theorem outerEvaluation_translation
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (B:Polynomial K)
   (hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B)):
   outerEvaluation K (Polynomial.taylor x P.derivative) B γ
       (homogenizedTranslation K x u₀ u₁ Q)=
     Polynomial.taylor x (specialization K P γ Q):=by
 have hhom:
     (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
       (homogenizedTranslation K x u₀ u₁).toRingHom=
     (Polynomial.taylorAlgHom x).toRingHom.comp
       (specialization K P γ).toRingHom:=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
       homogenizedTranslation,specialization,Polynomial.algebraMap_apply,
       MvPolynomial.algebraMap_eq]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
         homogenizedTranslation,translationVariables,specialization,
         seedAffine,MvPolynomial.aeval_monomial,Polynomial.algebraMap_apply,
         MvPolynomial.algebraMap_eq,hP] <;> ring
 exact DFunLike.congr_fun hhom Q
theorem X_pow_dvd_taylor_specialization
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (m:ℕ)
   (hvalue:P.eval x=u₀+γ*u₁)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K x u₀ u₁ Q).coeff r):
   (Polynomial.X:Polynomial K)^m∣
     Polynomial.taylor x (specialization K P γ Q):=by
 obtain ⟨B,hB⟩:=RCN185.X_sq_dvd_contactResidual P x
 have hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B):=by
   change Polynomial.taylor x P-Polynomial.C (P.eval x)-
     Polynomial.X*Polynomial.taylor x P.derivative=Polynomial.X^2*B at hB
   rw [hvalue] at hB
   linear_combination hB
 have hh:=outerEvaluation_contact_dvd K
   (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
 rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
 exact hh
theorem specialization_eq_zero_of_contact_and_degree
   [DecidableEq K] {I:Type*} [DecidableEq I]
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (nodes:I ↪ K) (u₀ u₁:I → K) (support:Finset I) (m:ℕ)
   (hcontact:∀ i∈support,∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
   (hvalues:∀ i∈support,P.eval (nodes i)=u₀ i+γ*u₁ i)
   (hdegree:(specialization K P γ Q).natDegree < m*support.card):
   specialization K P γ Q=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,
     m ≤ (specialization K P γ Q).rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:=X_pow_dvd_taylor_specialization K Q P
     (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣
       specialization K P γ Q:=
     (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
       (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   (specialization K P γ Q) nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hh
theorem monomial_eq (d:Fin 4 →₀ ℕ) (a:K):
   MvPolynomial.monomial d a=
     MvPolynomial.C a*MvPolynomial.X 0^d 0*MvPolynomial.X 1^d 1*
       MvPolynomial.X 2^d 2*MvPolynomial.X 3^d 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem specialization_monomial
   (P:Polynomial K) (γ:K) (d:Fin 4 →₀ ℕ) (a:K):
   specialization K P γ (MvPolynomial.monomial d a)=
     Polynomial.C a*Polynomial.X^d 0*P^d 1*P.derivative^d 2*
       Polynomial.C γ^d 3:=by
 rw [monomial_eq K d a]
 simp [specialization,Polynomial.algebraMap_eq]
theorem specialization_monomial_natDegree_le
   (P:Polynomial K) (γ:K) (w:ℕ) (hP:P.natDegree ≤ w)
   (d:Fin 4 →₀ ℕ) (a:K):
   (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
     d 0+w*d 1+(w-1)*d 2:=by
 rw [specialization_monomial]
 have hc:(Polynomial.C a:Polynomial K).natDegree ≤ 0:=by simp
 have hx:((Polynomial.X:Polynomial K)^d 0).natDegree ≤ d 0:=by simp
 have hy:(P^d 1).natDegree ≤ d 1*w:=
   Polynomial.natDegree_pow_le_of_le (d 1) hP
 have hderiv:P.derivative.natDegree ≤ w-1:=
   (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
 have hr:(P.derivative^d 2).natDegree ≤ d 2*(w-1):=
   Polynomial.natDegree_pow_le_of_le (d 2) hderiv
 have hz:((Polynomial.C γ:Polynomial K)^d 3).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
     (show (Polynomial.C γ:Polynomial K).natDegree ≤ 0 by simp)
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le
     (Polynomial.natDegree_mul_le_of_le
       (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
 simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_comm] using hh
theorem specialization_natDegree_lt
   (D w L s:ℕ) (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (hD:0 < D) (hcaps:Q∈globalCoefficientBox K D w L s)
   (hP:P.natDegree ≤ w):
   (specialization K P γ Q).natDegree < D:=by
 classical
 have hsupport:∀ d∈Q.support,
     d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
       d 0+w*d 1+(w-1)*d 2 < D:=hcaps
 have hterms:∀ d∈Q.support,
     (specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤
       D-1:=by
   intro d hd
   have hweight:=(hsupport d hd).2.2
   have hh:=specialization_monomial_natDegree_le K P γ w hP d (MvPolynomial.coeff d Q)
   omega
 rw [MvPolynomial.as_sum Q,map_sum]
 have hh:=Polynomial.natDegree_sum_le_of_forall_le Q.support
   (fun d => specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
 exact lt_of_le_of_lt hh (by omega)
end
end ProximityPrize.SubmissionLower.RCN122
end PackedLegacy_BD

/-! Packed from ProximityPrize.SubmissionLower.C2. -/
section PackedLegacy_C2
namespace ProximityPrize.SubmissionLower.RCN101
open ProximityPrize.Benchmark RCN100 RCN119 RCN122
noncomputable section
variable (K:Type*) [Field K]
theorem block_equations_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:Fin m),
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
         Poly K)=0:=by
 intro i r
 have hzero:constraintMap K D w L s m nodes u0 u1 theta=0:=
   LinearMap.mem_ker.mp htheta
 have happ:=congrArg
   (fun target:GlobalTarget K I m L s => ((target i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
     Poly K)=0 at happ
 exact happ
theorem translated_contact_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:ℕ),
     slopeDifference K^(m-r)∣
       (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
         (reconstruct K D w L s theta)).coeff r:=by
 intro i r
 rw [translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations K D w L s m
   (nodes i) (u0 i) (u1 i) theta
   (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r
theorem specialization_eq_zero_of_mem_ker
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hD:0 < D) (hP:P.natDegree ≤ w)
   (hcapacity:D ≤ m*support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_contact_and_degree K
   (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
 · intro i hi r
   exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
     htheta i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt K D w L s
     (reconstruct K D w L s theta) P gamma hD
     (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
   exact hdegree.trans_le hcapacity
theorem specialization_eq_zero_of_agreements
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a)
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hP:P.natDegree ≤ w) (hcard:a ≤ support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
   htheta P gamma support hD hP
 · rw [hDa]
   exact Nat.mul_le_mul_left m hcard
 · exact hvalues
theorem nonzero_kernel_member_universal
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta0:theta≠0)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a):
   reconstruct K D w L s theta≠0∧
     reconstruct K D w L s theta∈globalCoefficientBox K D w L s∧
     ∀ (gamma:K) (P:Polynomial K) (support:Finset I),
       P.natDegree ≤ w → a ≤ support.card →
       (∀ i∈support,
         P.eval (nodes i)=u0 i+gamma*u1 i) →
       specialization K P gamma (reconstruct K D w L s theta)=0:=by
 refine ⟨reconstruct_ne_zero K D w L s theta htheta0,
   reconstruct_mem_globalCoefficientBox K D w L s theta,?_⟩
 intro gamma P support hP hcard hvalues
 exact specialization_eq_zero_of_agreements K D w L s m a nodes u0 u1
   theta htheta hD hDa P gamma support hP hcard hvalues
theorem flag_box_to_ordinary (D w L s:ℕ)
   (Q:MvPolynomial (Fin 4) K)
   (hQ:Q∈globalCoefficientBox K D w L s):
   Q∈RCN174.globalCoefficientBox K D w L s:=by
 intro d hd
 obtain ⟨hT,hR,hD⟩:=hQ hd
 exact ⟨by omega,hR,hD⟩
theorem specialization_eq_ordinary (P:Polynomial K) (gamma:K):
   specialization K P gamma=RCN319.specialization K P gamma:=rfl
end
end ProximityPrize.SubmissionLower.RCN101
end PackedLegacy_C2

/-! Packed from ProximityPrize.SubmissionLower.I4. -/
section PackedLegacy_I4
namespace ProximityPrize.SubmissionLower.RCN071
open scoped BigOperators
open RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem weightedTotalDegree_prod_eq
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=
       Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul weights (f a) (∏ i∈s,f i) hfa hprod,
       ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq weights s f hf]
 exact weightedTotalDegree_le_of_dvd weights _ Q hdiv hQ
def weightEmbed3 (weights:Fin 3 → ℕ):
   (Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+
   Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed3_original (weights:Fin 3 → ℕ)
   (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed3 weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed3]
theorem weightEmbed3_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed3 weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed3]
theorem weightEmbed3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed3 weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 4 →₀ ℕ↦a i.castSucc) h
 simpa only [weightEmbed3_original] using hi
def weightedLift3 (weights:Fin 3 → ℕ):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed3 weights)
theorem weightedLift3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift3 (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed3_injective weights)
theorem weightedLift3_ne_zero (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K) (hP:P≠0):
   weightedLift3 weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift3_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).support=
     P.support.image (weightEmbed3 weights):=by
 change (Finsupp.mapDomain (weightEmbed3 weights)
     (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed3 weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective
   (weightEmbed3_injective weights) _
theorem degree_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift3 weights P).degreeOf (3:Fin 4)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift3,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦P.support.sup f)
 funext d
 exact weightEmbed3_last weights d
theorem weightedTotalDegree_mul_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift3 weights (P*Q)).degreeOf (3:Fin 4):=
     (degree_weightedLift3 weights (P*Q)).symm
   _=(weightedLift3 weights P*weightedLift3 weights Q).degreeOf
       (3:Fin 4):=by rw [map_mul]
   _=(weightedLift3 weights P).degreeOf (3:Fin 4)+
       (weightedLift3 weights Q).degreeOf (3:Fin 4):=
     MvPolynomial.degreeOf_mul_eq
       (weightedLift3_ne_zero weights P hP)
       (weightedLift3_ne_zero weights Q hQ)
   _=_:=by rw [degree_weightedLift3,degree_weightedLift3]
theorem weightedTotalDegree_le_of_dvd_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul_fin3 weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_prod_eq_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul_fin3 weights (f a) (∏ i∈s,f i)
         hfa hprod,ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K) (Q:MvPolynomial (Fin 3) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq_fin3 weights s f hf]
 exact weightedTotalDegree_le_of_dvd_fin3 weights _ Q hdiv hQ
end
end ProximityPrize.SubmissionLower.RCN071
end PackedLegacy_I4

/-! Packed from ProximityPrize.SubmissionLower.X3. -/
section PackedLegacy_X3
namespace ProximityPrize.SubmissionLower.RCN372
open scoped Classical BigOperators
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def shearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1-MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def unshearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1+MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def shearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (shearImage a)
def unshearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unshearImage a)
@[simp] theorem shearAlgHom_X (a:K) (i:Fin 3):
   shearAlgHom a (MvPolynomial.X i)=shearImage a i:=by
 simp [shearAlgHom]
@[simp] theorem unshearAlgHom_X (a:K) (i:Fin 3):
   unshearAlgHom a (MvPolynomial.X i)=unshearImage a i:=by
 simp [unshearAlgHom]
theorem unshear_comp_shear (a:K):
   (unshearAlgHom a).comp (shearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
theorem shear_comp_unshear (a:K):
   (shearAlgHom a).comp (unshearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
def shearEquiv (a:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (shearAlgHom a) (unshearAlgHom a)
   (shear_comp_unshear a) (unshear_comp_shear a)
@[simp] theorem shearEquiv_apply (a:K) (F:Poly3 K):
   shearEquiv a F=shearAlgHom a F:=rfl
theorem shear_irreducible_iff (a:K) (F:Poly3 K):
   Irreducible (shearAlgHom a F) ↔ Irreducible F:=by
 simpa only [shearEquiv_apply] using
   (MulEquiv.irreducible_iff (shearEquiv a))
theorem shear_dvd_iff (a:K) (F G:Poly3 K):
   shearAlgHom a F∣shearAlgHom a G ↔ F∣G:=by
 simpa only [shearEquiv_apply] using (map_dvd_iff (shearEquiv a))
theorem aeval_shear (F:Poly3 K) (y s z:K) (a:K):
   MvPolynomial.aeval ![y,s,z] (shearAlgHom a F)=
     MvPolynomial.aeval ![y,s-a*z,z] F:=by
 have hhom:
     (MvPolynomial.aeval ![y,s,z]).comp (shearAlgHom a)=
       MvPolynomial.aeval ![y,s-a*z,z]:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;> simp [shearImage,shearAlgHom] <;> ring
 exact DFunLike.congr_fun hhom F
theorem aeval_shear_at_add (F:Poly3 K) (y r z:K) (a:K):
   MvPolynomial.aeval ![y,r+a*z,z] (shearAlgHom a F)=
     MvPolynomial.aeval ![y,r,z] F:=by
 rw [aeval_shear]
 congr 2
 funext i
 fin_cases i <;> simp <;> ring
section WeightedDegree
def weightEmbed (weights:Fin 3 → ℕ):(Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun b:Fin 4 →₀ ℕ↦b i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
def weightedLift (weights:Fin 3 → ℕ):Poly3 K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem support_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).support=F.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff F)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff F).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift weights F).degreeOf (3:Fin 4)=
   F.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦F.support.sup f)
 funext d
 exact weightEmbed_last weights d
def wt (weights:Fin 3 → ℕ) (F:Poly3 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights F
theorem wt_mul_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F*G) ≤ wt weights F+wt weights G:=by
 unfold wt
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_mul_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_sub_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F-G) ≤ max (wt weights F) (wt weights G):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_pow_le (weights:Fin 3 → ℕ) (F:Poly3 K) (n:ℕ):
   wt weights (F^n) ≤ n*wt weights F:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (3:Fin 4) (weightedLift weights F) n
theorem wt_C (weights:Fin 3 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly3 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 3 → ℕ) (i:Fin 3):
   wt weights (MvPolynomial.X i:Poly3 K)=weights i:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp [MvPolynomial.support_X,Finsupp.weight_single]
def pullWeights (weights:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![weights 0,max (weights 1) (weights 2),weights 2]
theorem shearImage_wt_le (weights:Fin 3 → ℕ) (a:K) (i:Fin 3):
   wt weights (shearImage a i) ≤ pullWeights weights i:=by
 fin_cases i
 · simp [shearImage,pullWeights,wt_X]
 · dsimp [shearImage,pullWeights]
   have hm:=wt_mul_le weights (MvPolynomial.C a:Poly3 K) (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hm
   have hx:wt weights (MvPolynomial.X (1:Fin 3):Poly3 K)=weights 1:=
     wt_X weights 1
   exact (wt_sub_le weights (MvPolynomial.X 1)
     (MvPolynomial.C a*MvPolynomial.X 2)).trans
       (by rw [hx];exact max_le_max le_rfl hm)
 · simp [shearImage,pullWeights,wt_X]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty => simp [wt,MvPolynomial.weightedTotalDegree]
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights (f i) (∏ j∈I,f j)).trans
       (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (3:Fin 4) I
   (fun i↦weightedLift weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem shear_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (a:K) (d:Fin 3 →₀ ℕ):
   wt weights (∏ i∈d.support,shearImage a i^d i) ≤
     Finsupp.weight (pullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦shearImage a i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (shearImage a i^d i)) ≤
       ∑ i∈d.support,d i*pullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (shearImage a i) (d i)).trans
       (Nat.mul_le_mul_left _ (shearImage_wt_le weights a i))
   _=Finsupp.weight (pullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem shear_wt_le_pulled (weights:Fin 3 → ℕ) (a:K) (F:Poly3 K):
   wt weights (shearAlgHom a F) ≤ wt (pullWeights weights) F:=by
 change wt weights (MvPolynomial.eval₂ MvPolynomial.C (shearImage a) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=shear_monomial_product_wt_le weights a d
 have hcoeff:wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,shearImage a i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (pullWeights weights) hd))
theorem shear_degreeOf_zero_le (a:K) (F:Poly3 K):
   (shearAlgHom a F).degreeOf 0 ≤ F.degreeOf 0:=by
 have h:=shear_wt_le_pulled (Pi.single (0:Fin 3) 1) a F
 have hp:pullWeights (Pi.single (0:Fin 3) 1)=Pi.single 0 1:=by
   funext i
   fin_cases i <;> simp [pullWeights]
 rw [hp] at h
 simpa [wt] using h
theorem shear_degreeOf_one_le (a:K) (F:Poly3 K):
   (shearAlgHom a F).degreeOf 1 ≤ F.degreeOf 1:=by
 have h:=shear_wt_le_pulled (Pi.single (1:Fin 3) 1) a F
 have hp:pullWeights (Pi.single (1:Fin 3) 1)=Pi.single 1 1:=by
   funext i
   fin_cases i <;> simp [pullWeights]
 rw [hp] at h
 simpa [wt] using h
theorem weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
theorem two_weight_degree_le (F:Poly3 K):
   wt (![0,1,1]:Fin 3 → ℕ) F ≤ F.degreeOf 1+F.degreeOf 2:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 rw [weight_fin3]
 change d 0*0+d 1*1+d 2*1 ≤ _
 have h1:=MvPolynomial.le_degreeOf_of_mem_support 1 hd
 have h2:=MvPolynomial.le_degreeOf_of_mem_support 2 hd
 simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add]
 omega
theorem shear_degreeOf_two_le (a:K) (F:Poly3 K):
   (shearAlgHom a F).degreeOf 2 ≤ F.degreeOf 2+F.degreeOf 1:=by
 have h:=shear_wt_le_pulled (Pi.single (2:Fin 3) 1) a F
 have hp:pullWeights (Pi.single (2:Fin 3) 1)=(![0,1,1]:Fin 3 → ℕ):=by
   funext i
   fin_cases i <;> simp [pullWeights]
 rw [hp] at h
 have h':(shearAlgHom a F).degreeOf 2 ≤ wt (![0,1,1]:Fin 3 → ℕ) F:=by
   simpa [wt] using h
 exact h'.trans (by simpa [Nat.add_comm] using two_weight_degree_le F)
end WeightedDegree
end
end ProximityPrize.SubmissionLower.RCN372
end PackedLegacy_X3

/-! Packed from ProximityPrize.SubmissionLower.Z3. -/
section PackedLegacy_Z3
namespace ProximityPrize.SubmissionLower.RCN125
open scoped Classical BigOperators
open RCN095 RCN372 RCN003 RCN002 RCN011 RCN371 RCN012 RCN013
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def flagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0-MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1-
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def unflagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0+MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1+MvPolynomial.C μ*MvPolynomial.X 0+
     MvPolynomial.C ν*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def flagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (flagImage lam μ ν)
def unflagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unflagImage lam μ ν)
@[simp] theorem flagAlgHom_X (lam μ ν:K) (i:Fin 3):
   flagAlgHom lam μ ν (MvPolynomial.X i)=flagImage lam μ ν i:=by
 simp [flagAlgHom]
@[simp] theorem unflagAlgHom_X (lam μ ν:K) (i:Fin 3):
   unflagAlgHom lam μ ν (MvPolynomial.X i)=unflagImage lam μ ν i:=by
 simp [unflagAlgHom]
theorem unflag_comp_flag (lam μ ν:K):
   (unflagAlgHom lam μ ν).comp (flagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
theorem flag_comp_unflag (lam μ ν:K):
   (flagAlgHom lam μ ν).comp (unflagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
def flagEquiv (lam μ ν:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (flagAlgHom lam μ ν) (unflagAlgHom lam μ ν)
   (flag_comp_unflag lam μ ν) (unflag_comp_flag lam μ ν)
@[simp] theorem flagEquiv_apply (lam μ ν:K) (F:Poly3 K):
   flagEquiv lam μ ν F=flagAlgHom lam μ ν F:=rfl
theorem flag_irreducible_iff (lam μ ν:K) (F:Poly3 K):
   Irreducible (flagAlgHom lam μ ν F) ↔ Irreducible F:=by
 simpa only [flagEquiv_apply] using
   (MulEquiv.irreducible_iff (flagEquiv lam μ ν))
theorem flag_dvd_iff (lam μ ν:K) (F G:Poly3 K):
   flagAlgHom lam μ ν F∣flagAlgHom lam μ ν G ↔ F∣G:=by
 simpa only [flagEquiv_apply] using
   (map_dvd_iff (flagEquiv lam μ ν))
theorem flag_ne_zero (lam μ ν:K) {F:Poly3 K} (hF:F≠0):
   flagAlgHom lam μ ν F≠0:=
 (flagEquiv lam μ ν).injective.ne hF
theorem eval₂Hom_flag
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (u v z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]
       (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![u-algebraMap K A lam*z,
         v-algebraMap K A μ*u+
           algebraMap K A (μ*lam-ν)*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]).comp
         (flagAlgHom lam μ ν).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![u-algebraMap K A lam*z,
           v-algebraMap K A μ*u+
             algebraMap K A (μ*lam-ν)*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,flagAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,flagAlgHom,flagImage] <;> ring
 exact RingHom.congr_fun hhom F
theorem eval₂Hom_flag_at_affine
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A)
       ![y+algebraMap K A lam*z,
         s+algebraMap K A μ*y+algebraMap K A ν*z,
         z] (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z] F:=by
 rw [eval₂Hom_flag]
 congr 2
 funext i
 fin_cases i <;> simp <;> ring
def flagPullWeights (weights:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![max (weights 0) (weights 2),
   max (weights 1) (max (weights 0) (weights 2)),
   weights 2]
theorem flagImage_wt_le (weights:Fin 3 → ℕ) (lam μ ν:K) (i:Fin 3):
   wt weights (flagImage lam μ ν i) ≤ flagPullWeights weights i:=by
 fin_cases i
 · dsimp [flagImage,flagPullWeights]
   have hm:=wt_mul_le weights (MvPolynomial.C lam:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hm
   exact (wt_sub_le weights (MvPolynomial.X 0)
     (MvPolynomial.C lam*MvPolynomial.X 2)).trans
       (max_le_max (by rw [wt_X]) hm)
 · dsimp [flagImage,flagPullWeights]
   have hμ:=wt_mul_le weights (MvPolynomial.C μ:Poly3 K)
     (MvPolynomial.X 0)
   have hν:=wt_mul_le weights (MvPolynomial.C (μ*lam-ν):Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hμ hν
   have hinner:=wt_sub_le weights
     (MvPolynomial.C μ*MvPolynomial.X 0)
     (MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   have houter:=wt_sub_le weights (MvPolynomial.X 1)
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   exact houter.trans (max_le_max (by rw [wt_X])
     (hinner.trans (max_le_max hμ hν)))
 · simp [flagImage,flagPullWeights,wt_X]
theorem flag_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (lam μ ν:K) (d:Fin 3 →₀ ℕ):
   wt weights (∏ i∈d.support,flagImage lam μ ν i^d i) ≤
     Finsupp.weight (flagPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦flagImage lam μ ν i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (flagImage lam μ ν i^d i)) ≤
       ∑ i∈d.support,d i*flagPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (flagImage lam μ ν i) (d i)).trans
       (Nat.mul_le_mul_left _ (flagImage_wt_le weights lam μ ν i))
   _=Finsupp.weight (flagPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem flagAlgHom_wt_le_pulled
   (weights:Fin 3 → ℕ) (lam μ ν:K) (F:Poly3 K):
   wt weights (flagAlgHom lam μ ν F) ≤ wt (flagPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C (flagImage lam μ ν) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=flag_monomial_product_wt_le weights lam μ ν d
 have hcoeff:wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,flagImage lam μ ν i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (flagPullWeights weights) hd))
def sWeight:Fin 3 → ℕ:=![0,1,0]
def ysWeight:Fin 3 → ℕ:=![1,1,0]
def totalWeight:Fin 3 → ℕ:=![1,1,1]
@[simp] theorem flagPullWeights_sWeight:flagPullWeights sWeight=sWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,sWeight]
@[simp] theorem flagPullWeights_ysWeight:flagPullWeights ysWeight=ysWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,ysWeight]
@[simp] theorem flagPullWeights_totalWeight:
   flagPullWeights totalWeight=totalWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,totalWeight]
def PolynomialInFlag (p:FlagDegree) (F:Poly3 K):Prop:=
 ∀ d∈F.support,InFlag p d
theorem wt_s_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt sWeight F ≤ p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).1
 simpa [sWeight,weight_fin3] using h
theorem wt_ys_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt ysWeight F ≤ p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.1
 simpa [ysWeight,weight_fin3,Nat.add_comm] using h
theorem wt_total_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):
   wt totalWeight F ≤ p.zOnly+p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.2
 simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
   Nat.add_assoc] using h
theorem polynomialInFlag_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam μ ν:K)
   (hF:PolynomialInFlag p F):
   PolynomialInFlag p (flagAlgHom lam μ ν F):=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 have hsw:=(flagAlgHom_wt_le_pulled sWeight lam μ ν F).trans
   (by simpa using wt_s_le_of_inFlag hF)
 have hysw:=(flagAlgHom_wt_le_pulled ysWeight lam μ ν F).trans
   (by simpa using wt_ys_le_of_inFlag hF)
 have htotw:=(flagAlgHom_wt_le_pulled totalWeight lam μ ν F).trans
   (by simpa using wt_total_le_of_inFlag hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight,weight_fin3] using this
 · have:=hys.trans hysw
   simpa [ysWeight,weight_fin3,Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
     Nat.add_assoc] using this
def uOrder:Fin 3 ≃ Fin 3:=Equiv.refl _
def vOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
def zOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 2
structure FlagJointCertificateProvider
   (lam μ ν:K) (G H:Poly3 K) (p:ℕ):Prop where
 u:JointOrderCertificate K uOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
 v:JointOrderCertificate K vOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
 z:JointOrderCertificate K zOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
theorem flag_jointOrderCertificate_of_projection_data
   (lam μ ν:K) (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Poly3 K)) [P.IsPrime]
   (G H:Poly3 K) (p n mCap totalG totalH cap gOuter hInner:ℕ)
   (hG:Irreducible G)
   (hGmem:flagAlgHom lam μ ν G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (hHne:H≠0)
   (hGouter:(RCN011.planeMap K order
     (flagAlgHom lam μ ν G)).natDegree ≤ n)
   (hHouter:(RCN011.planeMap K order
     (flagAlgHom lam μ ν H)).natDegree ≤ mCap)
   (hGsupport:∀ d∈(RCN371.rationalMap K order
     (flagAlgHom lam μ ν G)).support,d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(RCN371.rationalMap K order
     (flagAlgHom lam μ ν H)).support,d 0+d 1 ≤ totalH)
   (hGswapOuter:(RCN011.planeMap K
     (RCN013.swapOtherOrder order)
     (flagAlgHom lam μ ν G)).natDegree ≤ gOuter)
   (hHswapInner:Polynomial.Bivariate.degreeX
     (RCN011.planeMap K
       (RCN013.swapOtherOrder order)
       (flagAlgHom lam μ ν H)) ≤ hInner)
   (hnp:n < p) (hgOuterP:gOuter < p) (hcapP:cap < p)
   (hswapP:gOuter*hInner < p)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   JointOrderCertificate K order
     (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p:=by
 exact jointOrderCertificate_of_projection_data K order P
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H)
   p n mCap totalG totalH cap gOuter hInner
   ((flag_irreducible_iff lam μ ν G).mpr hG) hGmem ht
   (flag_ne_zero lam μ ν hHne) hGouter hHouter hGsupport hHsupport
   hGswapOuter hHswapInner hnp hgOuterP hcapP hswapP hbudget
end
end ProximityPrize.SubmissionLower.RCN125
end PackedLegacy_Z3

/-! Packed from ProximityPrize.SubmissionLower.B9. -/
section PackedLegacy_B9
namespace ProximityPrize.SubmissionLower.RCN094
open scoped Classical BigOperators
open RCN095 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def residualImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bS*MvPolynomial.X 0+
     MvPolynomial.C cS*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def originalImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 let y:=MvPolynomial.C v⁻¹*
   (MvPolynomial.X 0-MvPolynomial.C aY-
     MvPolynomial.C bY*MvPolynomial.X 2)
 ![y,
   MvPolynomial.C v⁻¹*
     (MvPolynomial.X 1-MvPolynomial.C aS-
       MvPolynomial.C bS*y-MvPolynomial.C cS*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def residualAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (residualImage aY v bY aS bS cS)
def originalAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (originalImage aY v bY aS bS cS)
@[simp] theorem residualAlgHom_X
   (aY v bY aS bS cS:K) (i:Fin 3):
   residualAlgHom aY v bY aS bS cS (MvPolynomial.X i)=
     residualImage aY v bY aS bS cS i:=by
 simp [residualAlgHom]
@[simp] theorem originalAlgHom_X
   (aY v bY aS bS cS:K) (i:Fin 3):
   originalAlgHom aY v bY aS bS cS (MvPolynomial.X i)=
     originalImage aY v bY aS bS cS i:=by
 simp [originalAlgHom]
theorem original_comp_residual
   (aY v bY aS bS cS:K) (hv:v≠0):
   (originalAlgHom aY v bY aS bS cS).comp
       (residualAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v:Poly3 K)*MvPolynomial.C v⁻¹=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 0-MvPolynomial.C bY*MvPolynomial.X 2-
       MvPolynomial.C aY)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-MvPolynomial.C cS*MvPolynomial.X 2-
       (MvPolynomial.C aS+MvPolynomial.C v⁻¹*MvPolynomial.C bS*
         (MvPolynomial.X 0-MvPolynomial.C aY-
           MvPolynomial.C bY*MvPolynomial.X 2)))*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
theorem residual_comp_original
   (aY v bY aS bS cS:K) (hv:v≠0):
   (residualAlgHom aY v bY aS bS cS).comp
       (originalAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v⁻¹:Poly3 K)*MvPolynomial.C v=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination MvPolynomial.X 0*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-
       MvPolynomial.C v⁻¹*MvPolynomial.C bS*MvPolynomial.X 0)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
def residualEquiv (aY v bY aS bS cS:K) (hv:v≠0):
   Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom
   (residualAlgHom aY v bY aS bS cS)
   (originalAlgHom aY v bY aS bS cS)
   (residual_comp_original aY v bY aS bS cS hv)
   (original_comp_residual aY v bY aS bS cS hv)
@[simp] theorem residualEquiv_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   residualEquiv aY v bY aS bS cS hv F=
     residualAlgHom aY v bY aS bS cS F:=rfl
theorem residual_irreducible_iff
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   Irreducible (residualAlgHom aY v bY aS bS cS F) ↔ Irreducible F:=by
 simpa only [residualEquiv_apply] using
   (MulEquiv.irreducible_iff (residualEquiv aY v bY aS bS cS hv))
theorem residual_dvd_iff
   (aY v bY aS bS cS:K) (hv:v≠0) (F G:Poly3 K):
   residualAlgHom aY v bY aS bS cS F∣
       residualAlgHom aY v bY aS bS cS G ↔ F∣G:=by
 simpa only [residualEquiv_apply] using
   (map_dvd_iff (residualEquiv aY v bY aS bS cS hv))
theorem residual_ne_zero
   (aY v bY aS bS cS:K) (hv:v≠0) {F:Poly3 K}
   (hF:F≠0):residualAlgHom aY v bY aS bS cS F≠0:=
 (residualEquiv aY v bY aS bS cS hv).injective.ne hF
theorem eval₂Hom_residual
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (aY v bY aS bS cS:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]
       (residualAlgHom aY v bY aS bS cS F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![algebraMap K A aY+algebraMap K A v*y+
           algebraMap K A bY*z,
         algebraMap K A aS+algebraMap K A v*s+
           algebraMap K A bS*y+algebraMap K A cS*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]).comp
         (residualAlgHom aY v bY aS bS cS).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![algebraMap K A aY+algebraMap K A v*y+
             algebraMap K A bY*z,
           algebraMap K A aS+algebraMap K A v*s+
             algebraMap K A bS*y+algebraMap K A cS*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,residualAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,residualAlgHom,residualImage] <;> ring
 exact RingHom.congr_fun hhom F
theorem pderiv_residual
   (aY v bY aS bS cS:K) (F:Poly3 K):
   MvPolynomial.pderiv (1:Fin 3)
       (residualAlgHom aY v bY aS bS cS F)=
     MvPolynomial.C v*
       residualAlgHom aY v bY aS bS cS
         (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ => simp [hP,hQ,mul_add]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [residualImage,hP,Derivation.leibniz] <;> ring
theorem wt_add_le_residual
   (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F+G) ≤ max (wt weights F) (wt weights G):=by
 unfold wt
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_add_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem residualImage_wt_le
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K) (i:Fin 3):
   wt weights (residualImage aY v bY aS bS cS i) ≤
     RCN125.flagPullWeights weights i:=by
 fin_cases i
 · dsimp [residualImage,
     RCN125.flagPullWeights]
   have hvx:=wt_mul_le weights (MvPolynomial.C v:Poly3 K)
     (MvPolynomial.X 0)
   have hbx:=wt_mul_le weights (MvPolynomial.C bY:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hvx hbx
   have hleft:=wt_add_le_residual weights (MvPolynomial.C aY:Poly3 K)
     (MvPolynomial.C v*MvPolynomial.X 0)
   have hall:=wt_add_le_residual weights
     (MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0:Poly3 K)
     (MvPolynomial.C bY*MvPolynomial.X 2)
   rw [wt_C] at hleft
   exact hall.trans (by omega)
 · dsimp [residualImage,
     RCN125.flagPullWeights]
   have hvx:=wt_mul_le weights (MvPolynomial.C v:Poly3 K)
     (MvPolynomial.X 1)
   have hbx:=wt_mul_le weights (MvPolynomial.C bS:Poly3 K)
     (MvPolynomial.X 0)
   have hcx:=wt_mul_le weights (MvPolynomial.C cS:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hvx hbx hcx
   have h0:=wt_add_le_residual weights (MvPolynomial.C aS:Poly3 K)
     (MvPolynomial.C v*MvPolynomial.X 1)
   have h1:=wt_add_le_residual weights
     (MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1:Poly3 K)
     (MvPolynomial.C bS*MvPolynomial.X 0)
   have h2:=wt_add_le_residual weights
     (MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
       MvPolynomial.C bS*MvPolynomial.X 0:Poly3 K)
     (MvPolynomial.C cS*MvPolynomial.X 2)
   rw [wt_C] at h0
   exact h2.trans (by omega)
 · simp [residualImage,
     RCN125.flagPullWeights,wt_X]
theorem residual_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K)
   (d:Fin 3 →₀ ℕ):
   wt weights
       (∏ i∈d.support,residualImage aY v bY aS bS cS i^d i) ≤
     Finsupp.weight
       (RCN125.flagPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦residualImage aY v bY aS bS cS i^d i)).trans
 calc
   (∑ i∈d.support,
       wt weights (residualImage aY v bY aS bS cS i^d i)) ≤
       ∑ i∈d.support,d i*
         RCN125.flagPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (residualImage aY v bY aS bS cS i) (d i)).trans
       (Nat.mul_le_mul_left _
         (residualImage_wt_le weights aY v bY aS bS cS i))
   _=Finsupp.weight
       (RCN125.flagPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem residualAlgHom_wt_le_pulled
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K) (F:Poly3 K):
   wt weights (residualAlgHom aY v bY aS bS cS F) ≤
     wt (RCN125.flagPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C
       (residualImage aY v bY aS bS cS) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=residual_monomial_product_wt_le weights
   aY v bY aS bS cS d
 have hcoeff:
     wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,residualImage aY v bY aS bS cS i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree
     (RCN125.flagPullWeights weights) hd))
theorem polynomialInFlag_residualAlgHom
   (p:FlagDegree) (F:Poly3 K) (aY v bY aS bS cS:K)
   (hF:RCN125.PolynomialInFlag p F):
   RCN125.PolynomialInFlag p
     (residualAlgHom aY v bY aS bS cS F):=by
 intro d hd
 let sWeight:=RCN125.sWeight
 let ysWeight:=RCN125.ysWeight
 let totalWeight:=RCN125.totalWeight
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 have hsw:=(residualAlgHom_wt_le_pulled sWeight
   aY v bY aS bS cS F).trans (by
     simpa [sWeight] using
       RCN125.wt_s_le_of_inFlag hF)
 have hysw:=(residualAlgHom_wt_le_pulled ysWeight
   aY v bY aS bS cS F).trans (by
     simpa [ysWeight] using
       RCN125.wt_ys_le_of_inFlag hF)
 have htotw:=(residualAlgHom_wt_le_pulled totalWeight
   aY v bY aS bS cS F).trans (by
     simpa [totalWeight] using
       RCN125.wt_total_le_of_inFlag hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight,RCN125.sWeight,
     weight_fin3] using this
 · have:=hys.trans hysw
   simpa [ysWeight,RCN125.ysWeight,
     weight_fin3,
     Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight,RCN125.totalWeight,
     weight_fin3,
     Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using this
end
end ProximityPrize.SubmissionLower.RCN094
end PackedLegacy_B9

/-! Packed from ProximityPrize.SubmissionLower.K4. -/
section PackedLegacy_K4
namespace ProximityPrize.SubmissionLower.RCN161
noncomputable section
open scoped Function
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
variable {K:Type*} [Field K]
theorem nodal_dvd_of_eval_eq_zero
   {ι:Type*} (I:Finset ι) (x:ι → K)
   (hinj:Set.InjOn x I) (P:Polynomial K)
   (hzero:∀ i∈I,P.eval (x i)=0):
   Lagrange.nodal I x∣P:=by
 classical
 rw [Lagrange.nodal_eq]
 apply Finset.prod_dvd_of_coprime
 · intro i hi j hj hij
   exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
     (sub_ne_zero.mpr (fun hxy => hij (hinj hi hj hxy))).isUnit
 · intro i hi
   rw [Polynomial.dvd_iff_isRoot,Polynomial.IsRoot]
   exact hzero i hi
theorem exists_affine_nodal_residual
   {ι:Type*} (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (gamma:K) (S:Polynomial K) (hS:S.natDegree ≤ w)
   (hvalues:∀ i∈I,S.eval (x i)=u0 i+gamma*u1 i):
   ∃ P0 P1 C:Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     C.natDegree ≤ w-I.card∧
     S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 let D:=S-(P0+Polynomial.C gamma*P1)
 have hDdegree:D.natDegree ≤ w:=by
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le hS ((Polynomial.natDegree_add_le _ _).trans
     (max_le hP0 ((Polynomial.natDegree_C_mul_le gamma P1).trans hP1)))
 have hDeval:∀ i∈I,D.eval (x i)=0:=by
   intro i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,hvalues i hi]
   ring
 obtain ⟨C,hC⟩:=nodal_dvd_of_eval_eq_zero I x hinj D hDeval
 have hCdegree:C.natDegree ≤ w-I.card:=by
   by_cases hC0:C=0
   · simp [hC0]
   · have hdegmul:(Lagrange.nodal I x*C).natDegree=
         I.card+C.natDegree:=by
       rw [(Lagrange.nodal_monic (s:=I) (v:=x)).natDegree_mul' hC0,
         Lagrange.natDegree_nodal]
     have hmul:(Lagrange.nodal I x*C).natDegree ≤ w:=by
       rw [←hC]
       exact hDdegree
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,C,hP0,hP1,hCdegree,?_⟩
 change S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C
 change S-(P0+Polynomial.C gamma*P1)=
   Lagrange.nodal I x*C at hC
 linear_combination hC
variable {L:Type*} [Field L]
theorem map_nodal (coefficients:K →+*L)
   {ι:Type*} (I:Finset ι) (x:ι → K):
   (Lagrange.nodal I x).map coefficients=
     Lagrange.nodal I (fun i↦coefficients (x i)):=by
 classical
 simp only [Lagrange.nodal_eq,Polynomial.map_prod,Polynomial.map_sub,
   Polynomial.map_X,Polynomial.map_C]
theorem exists_basefield_affine_nodal_residual
   (coefficients:K →+*L)
   {ι:Type*} (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (gamma:L) (S:Polynomial L) (hS:S.natDegree ≤ w)
   (hvalues:∀ i∈I,
     S.eval (coefficients (x i))=
       coefficients (u0 i)+gamma*coefficients (u1 i)):
   ∃ P0 P1:Polynomial K,∃ C:Polynomial L,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     C.natDegree ≤ w-I.card∧
     S=P0.map coefficients+Polynomial.C gamma*P1.map coefficients+
       (Lagrange.nodal I x).map coefficients*C:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 let D:=S-(P0.map coefficients+
   Polynomial.C gamma*P1.map coefficients)
 have hDdegree:D.natDegree ≤ w:=by
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le hS ((Polynomial.natDegree_add_le _ _).trans
     (max_le (Polynomial.natDegree_map_le.trans hP0)
       ((Polynomial.natDegree_C_mul_le gamma _).trans
         (Polynomial.natDegree_map_le.trans hP1))))
 have hmapinj:Set.InjOn (fun i↦coefficients (x i)) I:=by
   intro i hi j hj hij
   exact hinj hi hj (coefficients.injective hij)
 have hDeval:∀ i∈I,D.eval (coefficients (x i))=0:=by
   intro i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map_apply]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,hvalues i hi]
   ring
 obtain ⟨C,hC⟩:=nodal_dvd_of_eval_eq_zero I
   (fun i↦coefficients (x i)) hmapinj D hDeval
 have hCdegree:C.natDegree ≤ w-I.card:=by
   by_cases hC0:C=0
   · simp [hC0]
   · have hdegmul:
         (Lagrange.nodal I (fun i↦coefficients (x i))*C).natDegree=
           I.card+C.natDegree:=by
       rw [(Lagrange.nodal_monic
         (s:=I) (v:=fun i↦coefficients (x i))).natDegree_mul' hC0,
         Lagrange.natDegree_nodal]
     have hmul:
         (Lagrange.nodal I (fun i↦coefficients (x i))*C).natDegree ≤ w:=by
       rw [←hC]
       exact hDdegree
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,C,hP0,hP1,hCdegree,?_⟩
 rw [map_nodal]
 change S=P0.map coefficients+Polynomial.C gamma*P1.map coefficients+
   Lagrange.nodal I (fun i↦coefficients (x i))*C
 change S-(P0.map coefficients+Polynomial.C gamma*P1.map coefficients)=
   Lagrange.nodal I (fun i↦coefficients (x i))*C at hC
 linear_combination hC
end
end ProximityPrize.SubmissionLower.RCN161
end PackedLegacy_K4

/-! Packed from ProximityPrize.SubmissionLower.EZ. -/
section PackedLegacy_EZ
namespace ProximityPrize.SubmissionLower.RCN160
open RCN238
noncomputable section
variable {K ι:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem nodal_eval_ne_zero_of_mem_sdiff
   (I nodes:Finset ι) (x:ι → K)
   (hsub:I ⊆ nodes) (hinj:Set.InjOn x nodes)
   {j:ι} (hj:j∈nodes \ I):
   (Lagrange.nodal I x).eval (x j)≠0:=by
 apply Lagrange.eval_nodal_not_at_node
 intro i hi hji
 have hji':j=i:=hinj (Finset.mem_sdiff.mp hj).1 (hsub hi) hji
 exact (Finset.mem_sdiff.mp hj).2 (hji' ▸ hi)
def residualReceived
   (I:Finset ι) (x u:ι → K) (P:Polynomial K) (j:ι):K:=
 (u j-P.eval (x j))/(Lagrange.nodal I x).eval (x j)
theorem residual_agreement_of_original
   (I nodes:Finset ι) (x u0 u1:ι → K)
   (hsub:I ⊆ nodes) (hinj:Set.InjOn x nodes)
   (P0 P1 C S:Polynomial K) (gamma:K)
   (hnormal:S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C)
   {j:ι} (hj:j∈nodes \ I)
   (hagree:S.eval (x j)=u0 j+gamma*u1 j):
   C.eval (x j)=residualReceived I x u0 P0 j+
     gamma*residualReceived I x u1 P1 j:=by
 have hV:=nodal_eval_ne_zero_of_mem_sdiff I nodes x hsub hinj hj
 have heval:=congrArg (fun P:Polynomial K↦P.eval (x j)) hnormal
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at heval
 unfold residualReceived
 field_simp [hV]
 linear_combination hagree-heval
theorem noLargeSelectedPencil_residual
   (I:Finset ι) (x:ι → K) (w e:ℕ) (hIw:I.card ≤ w)
   (selected residual:K → Polynomial K) (Gamma:Finset K)
   (P0 P1:Polynomial K) (hP0:P0.natDegree ≤ w)
   (hP1:P1.natDegree ≤ w)
   (hnormal:∀ gamma∈Gamma,
     selected gamma=P0+Polynomial.C gamma*P1+
       Lagrange.nodal I x*residual gamma)
   (hno:NoLargeSelectedPencil selected Gamma w e):
   NoLargeSelectedPencil residual Gamma (w-I.card) e:=by
 intro A B hA hB
 let V:=Lagrange.nodal I x
 let A0:=P0+V*A
 let B0:=P1+V*B
 have hV:V.natDegree=I.card:=by
   exact Lagrange.natDegree_nodal
 have hVA:(V*A).natDegree ≤ w:=by
   calc
     (V*A).natDegree ≤ V.natDegree+A.natDegree:=
       Polynomial.natDegree_mul_le
     _ ≤ I.card+(w-I.card):=by omega
     _=w:=Nat.add_sub_of_le hIw
 have hVB:(V*B).natDegree ≤ w:=by
   calc
     (V*B).natDegree ≤ V.natDegree+B.natDegree:=
       Polynomial.natDegree_mul_le
     _ ≤ I.card+(w-I.card):=by omega
     _=w:=Nat.add_sub_of_le hIw
 have hA0:A0.natDegree ≤ w:=by
   exact (Polynomial.natDegree_add_le _ _).trans (max_le hP0 hVA)
 have hB0:B0.natDegree ≤ w:=by
   exact (Polynomial.natDegree_add_le _ _).trans (max_le hP1 hVB)
 calc
   (Gamma.filter (fun gamma↦
     residual gamma=A+Polynomial.C gamma*B)).card ≤
       (Gamma.filter (fun gamma↦
         selected gamma=A0+Polynomial.C gamma*B0)).card:=by
     apply Finset.card_le_card
     intro gamma hgamma
     obtain ⟨hGamma,hpencil⟩:=Finset.mem_filter.mp hgamma
     apply Finset.mem_filter.mpr
     refine ⟨hGamma,?_⟩
     rw [hnormal gamma hGamma,hpencil]
     simp only [A0,B0,V]
     ring
   _ ≤ e+1:=hno A0 B0 hA0 hB0
end
end ProximityPrize.SubmissionLower.RCN160
end PackedLegacy_EZ

/-! Packed from ProximityPrize.SubmissionLower.EX. -/
section PackedLegacy_EX
namespace ProximityPrize.SubmissionLower.RCN155
open RCN238 RCN161 RCN160
noncomputable section
variable {K ι:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem exists_common_affine_nodal_residual_family
   (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,(residual gamma).natDegree ≤ w-I.card)∧
     ∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma:=by
 classical
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 let V:Polynomial K:=Lagrange.nodal I x
 let D:K → Polynomial K:=fun gamma↦
   selected gamma-(P0+Polynomial.C gamma*P1)
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hDdegree:∀ gamma∈Gamma,(D gamma).natDegree ≤ w:=by
   intro gamma hgamma
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le (hdegree gamma hgamma)
     ((Polynomial.natDegree_add_le _ _).trans
       (max_le hP0 ((Polynomial.natDegree_C_mul_le gamma P1).trans hP1)))
 have hDeval:∀ gamma∈Gamma,∀ i∈I,
     (D gamma).eval (x i)=0:=by
   intro gamma hgamma i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,
     hvalues gamma hgamma i hi]
   ring
 have hdvd:∀ gamma,gamma∈Gamma → V∣D gamma:=by
   intro gamma hgamma
   exact nodal_dvd_of_eval_eq_zero I x hinj (D gamma)
     (hDeval gamma hgamma)
 let residual:K → Polynomial K:=fun gamma↦
   if hgamma:gamma∈Gamma then (hdvd gamma hgamma).choose else 0
 have hfactor:∀ gamma∈Gamma,
     D gamma=V*residual gamma:=by
   intro gamma hgamma
   dsimp only [residual]
   rw [dif_pos hgamma]
   exact (hdvd gamma hgamma).choose_spec
 have hresidualDegree:∀ gamma∈Gamma,
     (residual gamma).natDegree ≤ w-I.card:=by
   intro gamma hgamma
   by_cases hzero:residual gamma=0
   · simp [hzero]
   · have hdegmul:(V*residual gamma).natDegree=
         I.card+(residual gamma).natDegree:=by
       rw [(Lagrange.nodal_monic (s:=I) (v:=x)).natDegree_mul' hzero,
         Lagrange.natDegree_nodal]
     have hmul:(V*residual gamma).natDegree ≤ w:=by
       rw [←hfactor gamma hgamma]
       exact hDdegree gamma hgamma
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,residual,hP0,hP1,hresidualDegree,?_⟩
 intro gamma hgamma
 have hf:=hfactor gamma hgamma
 change selected gamma=P0+Polynomial.C gamma*P1+V*residual gamma
 change selected gamma-(P0+Polynomial.C gamma*P1)=
   V*residual gamma at hf
 linear_combination hf
theorem exists_residual_family_with_incidence_data
   (I nodes:Finset ι) (x u0 u1:ι → K)
   (w e:ℕ) (hsub:I ⊆ nodes) (hIw:I.card ≤ w)
   (hinj:Set.InjOn x nodes)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i)
   (hno:NoLargeSelectedPencil selected Gamma w e):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,(residual gamma).natDegree ≤ w-I.card)∧
     NoLargeSelectedPencil residual Gamma (w-I.card) e∧
     (∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma)∧
     ∀ gamma∈Gamma,∀ j∈nodes \ I,
       (selected gamma).eval (x j)=u0 j+gamma*u1 j →
         (residual gamma).eval (x j)=
           residualReceived (K:=K) I x u0 P0 j+
             gamma*residualReceived (K:=K) I x u1 P1 j:=by
 have hIinj:Set.InjOn x I:=hinj.mono hsub
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnormal⟩:=
   exists_common_affine_nodal_residual_family I x u0 u1 w hIw hIinj
     selected Gamma hdegree hvalues
 have hnores:NoLargeSelectedPencil residual Gamma (w-I.card) e:=
   noLargeSelectedPencil_residual I x w e hIw selected residual Gamma
     P0 P1 hP0 hP1 hnormal hno
 refine ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,?_⟩
 intro gamma hgamma j hj hagree
 exact residual_agreement_of_original I nodes x u0 u1 hsub hinj
   P0 P1 (residual gamma) (selected gamma) gamma
   (hnormal gamma hgamma) hj hagree
end
end ProximityPrize.SubmissionLower.RCN155
end PackedLegacy_EX

/-! Packed from ProximityPrize.SubmissionLower.BQ. -/
section PackedLegacy_BQ
namespace ProximityPrize.SubmissionLower.RCN163
open scoped Classical
open RCN094 RCN157 RCN155 RCN160 RCN238 RCN125 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
local instance:DecidableEq Omega:=Classical.decEq Omega
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
theorem originalAlgHom_eq_residualAlgHom_inverse
   (aY v bY aS bS cS:Omega):
   originalAlgHom aY v bY aS bS cS=
     residualAlgHom (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
       (-v⁻¹*aS+v⁻¹*v⁻¹*bS*aY)
       (-v⁻¹*v⁻¹*bS)
       (v⁻¹*v⁻¹*bS*bY-v⁻¹*cS):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [originalAlgHom,originalImage,residualAlgHom,residualImage] <;>
   ring
theorem residual_degreeOf_one_le
   (aY v bY aS bS cS:Omega) (F:Poly3 Omega):
   (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1:=by
 have h:=residualAlgHom_wt_le_pulled
   (Pi.single (1:Fin 3) 1) aY v bY aS bS cS F
 have hp:flagPullWeights (Pi.single (1:Fin 3) 1)=
     Pi.single (1:Fin 3) 1:=by
   funext i
   fin_cases i <;> simp [flagPullWeights]
 rw [hp] at h
 simpa [wt] using h
theorem original_degreeOf_one_le
   (aY v bY aS bS cS:Omega) (F:Poly3 Omega):
   (originalAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1:=by
 rw [originalAlgHom_eq_residualAlgHom_inverse]
 exact residual_degreeOf_one_le _ _ _ _ _ _ F
theorem residual_degreeOf_one_eq
   (aY v bY aS bS cS:Omega) (hv:v≠0) (F:Poly3 Omega):
   (residualAlgHom aY v bY aS bS cS F).degreeOf 1=F.degreeOf 1:=by
 apply Nat.le_antisymm
 · exact residual_degreeOf_one_le _ _ _ _ _ _ F
 · have h:=original_degreeOf_one_le aY v bY aS bS cS
     (residualAlgHom aY v bY aS bS cS F)
   have hback:
       originalAlgHom aY v bY aS bS cS
           (residualAlgHom aY v bY aS bS cS F)=F:=by
     have hc:=DFunLike.congr_fun
       (original_comp_residual aY v bY aS bS cS hv) F
     simpa [AlgHom.comp_apply] using hc
   simpa only [hback] using h
theorem residual_degreeOf_one_pos_iff
   (aY v bY aS bS cS:Omega) (hv:v≠0) (F:Poly3 Omega):
   0 < (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ↔
     0 < F.degreeOf 1:=by
 rw [residual_degreeOf_one_eq aY v bY aS bS cS hv F]
theorem componentResidualHom_eq_residualAlgHom
   (aY v bY aS bS cS:Omega):
   componentResidualHom aY v bY aS bS cS=
     residualAlgHom aY v bY aS bS cS:=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [componentResidualHom,componentResidualImage,
     residualAlgHom,residualImage]
theorem surfaceMap_globalResidualHom_eq_residualAlgHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F)=
     residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
       (RCN136.surfaceMap phi F):=by
 rw [surfaceMap_globalResidualHom]
 rw [componentResidualHom_eq_residualAlgHom]
theorem surfaceMap_globalResidualHom_degreeOf_one
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0) (F:Poly4 K):
   (RCN136.surfaceMap phi
     (globalResidualHom P0 P1 V F)).degreeOf 1=
       (RCN136.surfaceMap phi F).degreeOf 1:=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact residual_degreeOf_one_eq _ _ _ _ _ _
   ((map_ne_zero_iff phi hphi).mpr hV) _
theorem surfaceMap_globalResidualHom_irreducible_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0) (F:Poly4 K):
   Irreducible (RCN136.surfaceMap phi
     (globalResidualHom P0 P1 V F)) ↔
     Irreducible (RCN136.surfaceMap phi F):=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact residual_irreducible_iff _ _ _ _ _ _
   ((map_ne_zero_iff phi hphi).mpr hV) _
theorem surfaceMap_globalResidualHom_dvd_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0) (F G:Poly4 K):
   RCN136.surfaceMap phi (globalResidualHom P0 P1 V F)∣
       RCN136.surfaceMap phi (globalResidualHom P0 P1 V G) ↔
     RCN136.surfaceMap phi F∣
       RCN136.surfaceMap phi G:=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom,
   surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact residual_dvd_iff _ _ _ _ _ _
   ((map_ne_zero_iff phi hphi).mpr hV) _ _
theorem surfaceMap_globalResidualHom_polynomialInFlag
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K)
   (F:Poly4 K) (p:RCN095.FlagDegree)
   (hflag:PolynomialInFlag p (RCN136.surfaceMap phi F)):
   PolynomialInFlag p (RCN136.surfaceMap phi
     (globalResidualHom P0 P1 V F)):=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact polynomialInFlag_residualAlgHom p _ _ _ _ _ _ _ hflag
theorem pderiv_globalResidualHom
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   MvPolynomial.pderiv (2:Fin 4) (globalResidualHom P0 P1 V F)=
     embedX K V*globalResidualHom P0 P1 V
       (MvPolynomial.pderiv (2:Fin 4) F):=
 pderiv_globalResidualHom_R P0 P1 V F
theorem specialization_pderiv_globalResidualHom
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K):
   RCN319.specialization K C gamma
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F))=
     V*RCN319.specialization K
       (P0+Polynomial.C gamma*P1+V*C) gamma
         (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [pderiv_globalResidualHom,map_mul,specialization_embedX,
   specialization_globalResidualHom]
theorem residual_specialization_regular
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K)
   (hV:V≠0)
   (hregular:RCN319.specialization K
     (P0+Polynomial.C gamma*P1+V*C) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   RCN319.specialization K C gamma
     (MvPolynomial.pderiv (2:Fin 4)
       (globalResidualHom P0 P1 V F))≠0:=by
 rw [specialization_pderiv_globalResidualHom]
 exact mul_ne_zero hV hregular
theorem surfaceMap_pderiv_globalResidualHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F))=
     MvPolynomial.C (phi V)*
       residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
         (RCN136.surfaceMap phi
           (MvPolynomial.pderiv (2:Fin 4) F)):=by
 rw [pderiv_globalResidualHom,map_mul,surfaceMap_embedX,
   surfaceMap_globalResidualHom_eq_residualAlgHom]
theorem residual_dvd_surfaceMap_globalResidualHom_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (G:Poly3 Omega) (F:Poly4 K):
   residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G∣
     RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F) ↔
     G∣RCN136.surfaceMap phi F:=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact residual_dvd_iff _ _ _ _ _ _
   ((map_ne_zero_iff phi hphi).mpr hV) _ _
theorem residual_dvd_pderiv_globalResidualHom_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (G:Poly3 Omega) (F:Poly4 K):
   residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G∣
     RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F)) ↔
     G∣RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [surfaceMap_pderiv_globalResidualHom]
 have hv:phi V≠0:=(map_ne_zero_iff phi hphi).mpr hV
 have hu:IsUnit (MvPolynomial.C (phi V):Poly3 Omega):=
   (isUnit_iff_ne_zero.mpr hv).map MvPolynomial.C
 rw [hu.dvd_mul_left]
 exact residual_dvd_iff _ _ _ _ _ _ hv _ _
theorem residual_component_transport
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (F:Poly4 K) (G:Poly3 Omega)
   (hG:Irreducible G)
   (hdiv:G∣RCN136.surfaceMap phi F)
   (hr:0 < G.degreeOf 1)
   (hproper:¬ G∣RCN136.surfaceMap phi
     (MvPolynomial.pderiv (2:Fin 4) F))
   (p:RCN095.FlagDegree)
   (hflag:PolynomialInFlag p G):
   let Gres:=residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G
   Irreducible Gres∧
     Gres∣RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F)∧
     0 < Gres.degreeOf 1∧
     ¬ Gres∣RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F))∧
     PolynomialInFlag p Gres:=by
 dsimp only
 have hv:phi V≠0:=(map_ne_zero_iff phi hphi).mpr hV
 refine ⟨(residual_irreducible_iff _ _ _ _ _ _ hv G).mpr hG,
   (residual_dvd_surfaceMap_globalResidualHom_iff
     phi hphi P0 P1 V hV G F).mpr hdiv,?_,?_,?_⟩
 · exact (residual_degreeOf_one_pos_iff _ _ _ _ _ _ hv G).mpr hr
 · exact (residual_dvd_pderiv_globalResidualHom_iff
     phi hphi P0 P1 V hV G F).not.mpr hproper
 · exact polynomialInFlag_residualAlgHom p G _ _ _ _ _ _ hflag
@[simp] theorem polynomial_eval₂_comp_C_X
   (phi:Polynomial K →+*Omega) (P:Polynomial K):
   P.eval₂ (phi.comp Polynomial.C) (phi Polynomial.X)=phi P:=by
 change (Polynomial.eval₂RingHom (phi.comp Polynomial.C)
   (phi Polynomial.X)) P=phi P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RingHom.comp_apply]
 · simp
theorem eval_residualComponent_selectedPoint
   (phi:Polynomial K →+*Omega)
   (P0 P1 V C S:Polynomial K) (gamma:K) (G:Poly3 Omega)
   (hnormal:S=P0+Polynomial.C gamma*P1+V*C):
   MvPolynomial.eval (selectedPoint phi (fun _↦C) gamma)
       (residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G)=
     MvPolynomial.eval (selectedPoint phi (fun _↦S) gamma) G:=by
 have hCpoint:selectedPoint phi (fun _↦C) gamma=
     ![phi C,phi C.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [selectedPoint,RCN231.polynomialPoint,
       RingHom.comp_apply]
 have hSpoint:selectedPoint phi (fun _↦S) gamma=
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [selectedPoint,RCN231.polynomialPoint,
       RingHom.comp_apply]
 rw [hCpoint,hSpoint]
 change MvPolynomial.eval₂Hom (algebraMap Omega Omega)
     ![phi C,phi C.derivative,(phi.comp Polynomial.C) gamma]
       (residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G)=
   MvPolynomial.eval₂Hom (algebraMap Omega Omega)
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma] G
 rw [eval₂Hom_residual]
 have hcoords:
     ![phi P0+phi V*phi C+phi P1*(phi.comp Polynomial.C) gamma,
       phi P0.derivative+phi V*phi C.derivative+
         phi V.derivative*phi C+
           phi P1.derivative*(phi.comp Polynomial.C) gamma,
       (phi.comp Polynomial.C) gamma]=
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [hnormal,RingHom.comp_apply] <;> ring
 simpa using congrArg
   (fun q:Fin 3 → Omega↦
     MvPolynomial.eval₂Hom (algebraMap Omega Omega) q G) hcoords
theorem exists_residual_family_with_surface_data
   {iota:Type} [DecidableEq iota]
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (I nodes:Finset iota) (x u0 u1:iota → K)
   (w e:ℕ) (hsub:I ⊆ nodes) (hIw:I.card ≤ w)
   (hinj:Set.InjOn x nodes)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i)
   (hno:NoLargeSelectedPencil selected Gamma w e)
   (F:Poly4 K)
   (hsolution:∀ gamma∈Gamma,
     RCN319.specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (RCN231.polynomialPoint
         (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,
       (residual gamma).natDegree ≤ w-I.card)∧
     NoLargeSelectedPencil residual Gamma (w-I.card) e∧
     (∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma)∧
     (∀ gamma∈Gamma,∀ j∈nodes \ I,
       (selected gamma).eval (x j)=u0 j+gamma*u1 j →
         (residual gamma).eval (x j)=
           residualReceived I x u0 P0 j+
             gamma*residualReceived I x u1 P1 j)∧
     (∀ gamma∈Gamma,
       RCN319.specialization K (residual gamma) gamma
         (globalResidualHom P0 P1 (Lagrange.nodal I x) F)=0)∧
     ∀ gamma∈Gamma,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint
           (phi.comp Polynomial.C) (residual gamma) gamma
             (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4)
           (globalResidualHom P0 P1 (Lagrange.nodal I x) F))≠0:=by
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
     hagree⟩:=exists_residual_family_with_incidence_data
   I nodes x u0 u1 w e hsub hIw hinj selected Gamma
     hdegree hvalues hno
 have hV:Lagrange.nodal I x≠0:=
   (Lagrange.nodal_monic (s:=I) (v:=x)).ne_zero
 have hVeval:(Lagrange.nodal I x).eval₂
     (phi.comp Polynomial.C) (phi Polynomial.X)≠0:=by
   rw [polynomial_eval₂_comp_C_X]
   exact (map_ne_zero_iff phi hphi).mpr hV
 refine ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
   ?_,?_,?_⟩
 · intro gamma hgamma j hj hagreement
   apply hagree gamma hgamma j
   · simpa only [Finset.mem_sdiff] using hj
   · exact hagreement
 · intro gamma hgamma
   apply globalResidual_solution
   rw [←hnormal gamma hgamma]
   exact hsolution gamma hgamma
 · intro gamma hgamma
   apply globalResidual_regular_at_polynomialPoint
     (phi.comp Polynomial.C) P0 P1 (Lagrange.nodal I x)
       (residual gamma) gamma (phi Polynomial.X) F hVeval
   rw [←hnormal gamma hgamma]
   exact hregular gamma hgamma
end
end ProximityPrize.SubmissionLower.RCN163
end PackedLegacy_BQ

/-! Packed from ProximityPrize.SubmissionLower.K5. -/
section PackedLegacy_K5
namespace ProximityPrize.SubmissionLower.RCN166
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319 RCN065
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
 (phi:Polynomial K →+*Omega)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap phi F∈P)
 (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem coordinate_y_affine_of_basefield_pencil
   (w:ℕ) (P0 P1:Polynomial K)
   (hp:truncatedPolynomial phi P F hF hH w=
     P0.map (componentCoefficients phi P)+
       Polynomial.C (coordinate Omega P 2)*
         P1.map (componentCoefficients phi P)):
   coordinate Omega P 0=algebraMap Omega (CoordinateField Omega P)
       ((P0.map (phi.comp Polynomial.C)).eval (phi Polynomial.X))+
     coordinate Omega P 2*algebraMap Omega (CoordinateField Omega P)
       ((P1.map (phi.comp Polynomial.C)).eval (phi Polynomial.X)):=by
 have hp':truncatedPolynomial phi P F hF hH w=
     (P0.map (phi.comp Polynomial.C)).map
         (algebraMap Omega (CoordinateField Omega P))+
       Polynomial.C (coordinate Omega P 2)*
         (P1.map (phi.comp Polynomial.C)).map
           (algebraMap Omega (CoordinateField Omega P)):=by
   simpa only [Polynomial.map_map,componentCoefficients] using hp
 rw [←truncatedPolynomial_initial_value phi P F hF hH w,hp']
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply]
include hF hH in
theorem identityNodes_card_le_of_r_dependent_principal_zero_safe
   {iota:Type} [DecidableEq iota]
   (nodes:Finset iota) (x u0 u1:iota → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (g:MvPolynomial (Fin 3) Omega) (hP:P=Ideal.span {g})
   (hr:0 < g.degreeOf 1):
   (identityNodes phi P F nodes x u0 u1 w).card ≤ w:=by
 by_contra h
 have hc:w < (identityNodes phi P F nodes x u0 u1 w).card:=
   Nat.lt_of_not_ge h
 obtain ⟨P0,P1,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities phi P F hF hH
     nodes x u0 u1 w hinj hc
     (fun t:Empty↦t.elim) (fun t:Empty↦t.elim)
     (fun t↦t.elim) (fun t↦t.elim)
 have hy:=coordinate_y_affine_of_basefield_pencil
   phi P F hF hH w P0 P1 hp
 exact not_y_affine_of_r_dependent_principal Omega P g hP hr _ _ hy
end
end ProximityPrize.SubmissionLower.RCN166
end PackedLegacy_K5

/-! Packed from ProximityPrize.SubmissionLower.E8. -/
section PackedLegacy_E8
namespace ProximityPrize.SubmissionLower.RCN275
open RCN136 RCN313 RCN174 RCN081 RCN234 RCN157 RCN156 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
structure ResidualSupportParameters where
 s:ℕ
 ys:ℕ
 total:ℕ
 one_le_s:1 ≤ s
 s_le_ys:s ≤ ys
 ys_le_total:ys ≤ total
 two_le_ys:2 ≤ ys
 deriving DecidableEq
namespace ResidualSupportParameters
def agreementDirection (P:ResidualSupportParameters):FlagDegree:=
 ⟨2*(P.total-P.ys),2*(P.ys-P.s),2*P.s-1⟩
def residualAgreementFlag (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
 ⟨P.agreementDirection.zOnly*d,
   1+P.agreementDirection.yz*d,
   P.agreementDirection.all*d⟩
theorem agreementDirection_values (P:ResidualSupportParameters):
   P.agreementDirection=
     ⟨2*(P.total-P.ys),2*(P.ys-P.s),2*P.s-1⟩:=rfl
theorem residualAgreementFlag_ys (P:ResidualSupportParameters) (d:ℕ):
   (P.residualAgreementFlag d).yz+(P.residualAgreementFlag d).all=
     1+d*(2*P.ys-1):=by
 have hcoeff:2*(P.ys-P.s)+(2*P.s-1)=2*P.ys-1:=by
   rw [Nat.mul_sub_left_distrib]
   have hle:=Nat.mul_le_mul_left 2 P.s_le_ys
   have hpos:=P.one_le_s
   omega
 simp only [residualAgreementFlag,agreementDirection]
 rw [←hcoeff]
 ring
theorem residualAgreementFlag_total (P:ResidualSupportParameters) (d:ℕ):
   (P.residualAgreementFlag d).zOnly+
       (P.residualAgreementFlag d).yz+
       (P.residualAgreementFlag d).all=
     1+d*(2*P.total-1):=by
 have hcoeff:2*(P.total-P.ys)+2*(P.ys-P.s)+
     (2*P.s-1)=2*P.total-1:=by
   rw [Nat.mul_sub_left_distrib,Nat.mul_sub_left_distrib]
   have hle₁:=Nat.mul_le_mul_left 2 P.s_le_ys
   have hle₂:=Nat.mul_le_mul_left 2 P.ys_le_total
   have hpos:=P.one_le_s
   omega
 simp only [residualAgreementFlag,agreementDirection]
 rw [←hcoeff]
 ring
def acceptedSupport:ResidualSupportParameters where
 s:=8
 ys:=43
 total:=503
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
def fixedMeetSupport:ResidualSupportParameters where
 s:=6
 ys:=34
 total:=604
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
theorem accepted_agreement_flag (d:ℕ):
   acceptedSupport.residualAgreementFlag d=
     RCN156.residualAgreementFlag d:=by
 rfl
theorem fixedMeet_agreement_direction:
   fixedMeetSupport.agreementDirection=⟨1140,56,11⟩:=by
 norm_num [fixedMeetSupport,agreementDirection]
theorem fixedMeet_agreement_flag (d:ℕ):
   fixedMeetSupport.residualAgreementFlag d=
     ⟨1140*d,1+56*d,11*d⟩:=by
 rfl
end ResidualSupportParameters
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualSupportData (P:ResidualSupportParameters) (F:Poly4 K):Prop where
 s_weight:wt residualSWeights F ≤ P.s
 ys_weight:wt residualYSWeights F ≤ P.ys
 total_weight:wt residualTotalWeights F ≤ P.total
namespace ResidualSupportData
theorem fixedMeet_of_mem_box
   (F:Poly4 K)
   (hbox:F∈globalCoefficientBox K 4570175 131071 598 6):
   ResidualSupportData ResidualSupportParameters.fixedMeetSupport F:=by
 refine ⟨?_,?_,?_⟩
 · apply (weightedTotalDegree_le_iff residualSWeights F 6).mpr
   intro d hd
   have hb:d 1+d 3 ≤ 598∧d 2 ≤ 6∧
       d 0+131071*d 1+(131071-1)*d 2 < 4570175:=hbox hd
   rw [RCN081.weight_fin4]
   change d 0*0+d 1*0+d 2*1+d 3*0 ≤ 6
   norm_num
   exact hb.2.1
 · apply (weightedTotalDegree_le_iff residualYSWeights F 34).mpr
   intro d hd
   have hb:d 1+d 3 ≤ 598∧d 2 ≤ 6∧
       d 0+131071*d 1+(131071-1)*d 2 < 4570175:=hbox hd
   rw [RCN081.weight_fin4]
   change d 0*0+d 1*1+d 2*1+d 3*0 ≤ 34
   norm_num
   norm_num at hb
   omega
 · apply (weightedTotalDegree_le_iff residualTotalWeights F 604).mpr
   intro d hd
   have hb:d 1+d 3 ≤ 598∧d 2 ≤ 6∧
       d 0+131071*d 1+(131071-1)*d 2 < 4570175:=hbox hd
   rw [RCN081.weight_fin4]
   change d 0*0+d 1*1+d 2*1+d 3*1 ≤ 604
   norm_num
   norm_num at hb
   omega
theorem globalResidual
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F)
   (P0 P1 V:Polynomial K):
   ResidualSupportData P (globalResidualHom P0 P1 V F):=by
 refine ⟨?_,?_,?_⟩
 · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_s] using H.s_weight)
 · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_ys] using H.ys_weight)
 · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
     P0 P1 V F).trans (by
       simpa [residualPullWeights_total] using H.total_weight)
theorem coordinate_bounds
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F):
   F.degreeOf (1:Fin 4) ≤ P.ys∧
     F.degreeOf (2:Fin 4) ≤ P.s∧
     F.degreeOf (3:Fin 4) ≤ P.total:=by
 have hR:F.degreeOf (2:Fin 4) ≤ P.s:=by
   have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
     funext i
     fin_cases i <;> rfl
   have hs:=H.s_weight
   rw [hw,wt,MvPolynomial.weightedTotalDegree_piSingle] at hs
   exact hs
 have hY:F.degreeOf (1:Fin 4) ≤ P.ys:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans
     H.ys_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*0 ≤ P.ys at hw
   norm_num at hw
   omega
 have hZ:F.degreeOf (3:Fin 4) ≤ P.total:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans
     H.total_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*1 ≤ P.total at hw
   norm_num at hw
   omega
 exact ⟨hY,hR,hZ⟩
theorem agreement_weight_bounds
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
       d*(2*P.s-1)∧
     wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.ys-1)∧
     wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.total-1):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=agreementNumerator_wt_le_minkowski residualYSWeights rfl
     F P.ys (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2 ≤ P.ys;exact P.two_le_ys)
     (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:P.ys+(P.ys-1)=2*P.ys-1:=by omega
   apply h.trans_eq
   change max 1 0+d*(P.ys+(P.ys-1))=
     1+d*(2*P.ys-1)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1 ≤ P.total:=
     le_trans P.one_le_s (le_trans P.s_le_ys P.ys_le_total)
   have h:=agreementNumerator_wt_le_minkowski residualTotalWeights rfl
     F P.total (by change 1 ≤ P.total;exact honeTotal)
     (by change 2 ≤ P.total;exact htotalTwo)
     (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:P.total+(P.total-1)=2*P.total-1:=by omega
   apply h.trans_eq
   change max 1 1+d*(P.total+(P.total-1))=
     1+d*(2*P.total-1)
   rw [hcoeff]
   norm_num
theorem surfaceMap_agreement_in_flag
   {P:ResidualSupportParameters}
   (phi:Polynomial K →+*Omega) {F:Poly4 K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (P.residualAgreementFlag d)
     (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=H.agreement_weight_bounds d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤
   1+d*(2*P.ys-1) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤
   1+d*(2*P.total-1) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2 ≤ (P.residualAgreementFlag d).all:=by
   change q 2 ≤ (2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2 ≤ (P.residualAgreementFlag d).all∧
   q 1+q 2 ≤ (P.residualAgreementFlag d).yz+
     (P.residualAgreementFlag d).all∧
   q 1+q 2+q 3 ≤ (P.residualAgreementFlag d).zOnly+
     (P.residualAgreementFlag d).yz+
     (P.residualAgreementFlag d).all
 refine ⟨hqR',?_,?_⟩
 · rw [P.residualAgreementFlag_ys]
   exact hqYS
 · rw [P.residualAgreementFlag_total]
   exact hqTotal
theorem globalResidual_and_agreement_in_flag
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F)
   (phi:Polynomial K →+*Omega)
   (P0 P1 V:Polynomial K)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   let Fres:=globalResidualHom P0 P1 V F
   ResidualSupportData P Fres∧
     PolynomialInFlag (P.residualAgreementFlag d)
       (surfaceMap phi (agreementNumerator Fres d coeffs x u0 u1)):=by
 let Hres:=H.globalResidual P0 P1 V
 exact ⟨Hres,Hres.surfaceMap_agreement_in_flag phi d coeffs x u0 u1⟩
end ResidualSupportData
end
end ProximityPrize.SubmissionLower.RCN275
end PackedLegacy_E8

/-! Packed from ProximityPrize.SubmissionLower.B. -/
section PackedLegacy_B
namespace ProximityPrize.SubmissionLower.RCN159
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN160 RCN157 RCN163 RCN166 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualStage
   (phi:Polynomial K →+*Omega) (Gamma:Finset K) (x:Iota → K)
   (p e:ℕ) [CharP Omega p] (flag:FlagDegree) (d:ℕ)
   (support:ResidualSupportParameters:=
     ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota → K
 u1:Iota → K
 selected:K → Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 irreducible_G:Irreducible G
 G_dvd_surface:G∣surfaceMap phi F
 y_dependent:0 < G.degreeOf 1
 regular_proper:¬ G∣surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)
 flag_support:RCN095.PolynomialInFlag flag G
 surface_s_weight:wt residualSWeights F ≤ support.s
 surface_ys_weight:wt residualYSWeights F ≤ support.ys
 surface_total_weight:wt residualTotalWeights F ≤ support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d
 solution:∀ gamma∈Gamma,
   specialization K (selected gamma) gamma F=0
 regular:∀ gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_component:∀ gamma∈Gamma,
   MvPolynomial.eval (selectedPoint phi selected gamma) G=0
 no_large_pencil:NoLargeSelectedPencil selected Gamma d e
 characteristic_bound:d < p
namespace ResidualStage
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree} {d:ℕ}
 {support:ResidualSupportParameters}
def componentIdeal (S:ResidualStage phi Gamma x p e flag d support):
   Ideal (Poly3 Omega):=Ideal.span {S.G}
def identities (S:ResidualStage phi Gamma x p e flag d support):Finset Iota:=
 identityNodes phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
def Agrees (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance (S:ResidualStage phi Gamma x p e flag d support):
   ∀ gamma i,Decidable (S.Agrees gamma i):=fun _ _↦Classical.propDecidable _
def agreementFiber (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K):Finset Iota:=
 S.nodes.filter (S.Agrees gamma)
theorem componentIdeal_isPrime
   (S:ResidualStage phi Gamma x p e flag d support):S.componentIdeal.IsPrime:=by
 exact Ideal.isPrime_span_singleton_of_prime S.irreducible_G.prime
theorem surface_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi S.F∈S.componentIdeal:=by
 exact Ideal.mem_span_singleton.mpr S.G_dvd_surface
theorem regularity_not_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)∉
     S.componentIdeal:=by
 intro h
 exact S.regular_proper (Ideal.mem_span_singleton.mp h)
theorem selected_point_ideal
   (S:ResidualStage phi Gamma x p e flag d support)
   {gamma:K} (hgamma:gamma∈Gamma):
   S.componentIdeal ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom:=by
 change Ideal.span {S.G} ≤
   RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom
 rw [Ideal.span_le]
 intro Q hQ
 simp only [Set.mem_singleton_iff] at hQ
 subst Q
 exact S.on_component gamma hgamma
theorem agrees_on_identities
   (S:ResidualStage phi Gamma x p e flag d support):
   ∀ gamma∈Gamma,∀ i∈S.identities,S.Agrees gamma i:=by
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 intro gamma hgamma i hi
 exact selected_agrees_on_identity_nodes
   phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
   (S.selected gamma) gamma (S.degree_le gamma hgamma)
   (S.solution gamma hgamma) (S.regular gamma hgamma)
   (S.selected_point_ideal hgamma) i hi
theorem identities_card_le
   (S:ResidualStage phi Gamma x p e flag d support):S.identities.card ≤ d:=by
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 exact identityNodes_card_le_of_r_dependent_principal_zero_safe
   phi P S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
   S.nodes x S.u0 S.u1 d S.x_injective S.G rfl S.y_dependent
theorem advance
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support)
   (hne:S.identities≠∅):
   0 < S.identities.card∧
     ∃ Snext:ResidualStage phi Gamma x p e flag
         (d-S.identities.card) support,
       Snext.nodes=S.nodes \ S.identities∧
       (∀ gamma∈Gamma,∀ i∈S.identities,
         S.Agrees gamma i)∧
       ∀ gamma∈Gamma,∀ i∈Snext.nodes,
         S.Agrees gamma i → Snext.Agrees gamma i:=by
 classical
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 let J:=S.identities
 have hJsub:J ⊆ S.nodes:=identityNodes_subset
   phi P S.F S.nodes x S.u0 S.u1 d
 have hJcard:J.card ≤ d:=S.identities_card_le
 have hJpos:0 < J.card:=Finset.card_pos.mpr
   (Finset.nonempty_iff_ne_empty.mpr (by simpa only [J] using hne))
 have hvalues:∀ gamma∈Gamma,∀ i∈J,
     (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i:=by
   intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
     hagree,hsolution,hregular⟩:=
   exists_residual_family_with_surface_data
     phi hphi J S.nodes x S.u0 S.u1 d e hJsub hJcard S.x_injective
     S.selected Gamma S.degree_le hvalues S.no_large_pencil S.F
     S.solution S.regular
 let V:Polynomial K:=Lagrange.nodal J x
 have hV:V≠0:=(Lagrange.nodal_monic (s:=J) (v:=x)).ne_zero
 let Fres:Poly4 K:=globalResidualHom P0 P1 V S.F
 let Gres:Poly3 Omega:=
   residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G
 obtain ⟨hGirred,hGdiv,hGy,hGproper,hGflag⟩:=
   residual_component_transport phi hphi P0 P1 V hV S.F S.G
     S.irreducible_G S.G_dvd_surface S.y_dependent S.regular_proper
     flag S.flag_support
 let hsupport:ResidualSupportData support S.F:=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 have hsupportRes:=hsupport.globalResidual P0 P1 V
 let u0res:Iota → K:=fun i↦residualReceived J x S.u0 P0 i
 let u1res:Iota → K:=fun i↦residualReceived J x S.u1 P1 i
 let Snext:ResidualStage phi Gamma x p e flag (d-J.card) support:={
   nodes:=S.nodes \ J
   u0:=u0res
   u1:=u1res
   selected:=residual
   F:=Fres
   G:=Gres
   irreducible_G:=hGirred
   G_dvd_surface:=hGdiv
   y_dependent:=hGy
   regular_proper:=hGproper
   flag_support:=hGflag
   surface_s_weight:=hsupportRes.s_weight
   surface_ys_weight:=hsupportRes.ys_weight
   surface_total_weight:=hsupportRes.total_weight
   x_injective:=S.x_injective.mono (Finset.sdiff_subset)
   degree_le:=hresdeg
   solution:=hsolution
   regular:=hregular
   on_component:=by
     intro gamma hgamma
     have heval:=eval_residualComponent_selectedPoint
       phi P0 P1 V (residual gamma) (S.selected gamma) gamma S.G
         (hnormal gamma hgamma)
     change MvPolynomial.eval
       (selectedPoint phi (fun _↦residual gamma) gamma) Gres=0
     exact heval.trans (S.on_component gamma hgamma)
   no_large_pencil:=hnores
   characteristic_bound:=lt_of_le_of_lt (Nat.sub_le d J.card)
     S.characteristic_bound
 }
 refine ⟨?hpos,Snext,rfl,?_,?_⟩
 · simpa only [J] using hJpos
 · intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 · intro gamma hgamma i hi hold
   exact hagree gamma hgamma i (by simpa [Snext,J] using hi) hold
theorem advance_card
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support)
   (hne:S.identities≠∅):
   ∃ Snext:ResidualStage phi Gamma x p e flag
       (d-S.identities.card) support,
     Snext.nodes.card=S.nodes.card-S.identities.card∧
     ∀ gamma∈Gamma,
       (S.agreementFiber gamma).card-S.identities.card ≤
         (Snext.agreementFiber gamma).card:=by
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 obtain ⟨_,Snext,hnodes,hidAgree,hdescend⟩:=S.advance hphi hne
 have hIdentityNodesSubset:S.identities ⊆ S.nodes:=by
   exact identityNodes_subset
     phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
 refine ⟨Snext,?_,?_⟩
 · rw [hnodes,Finset.card_sdiff_of_subset hIdentityNodesSubset]
 · intro gamma hgamma
   have hIdentitySubset:S.identities ⊆ S.agreementFiber gamma:=by
     intro i hi
     exact Finset.mem_filter.mpr ⟨
       (identityNodes_subset phi S.componentIdeal S.F
         S.nodes x S.u0 S.u1 d) hi,
       hidAgree gamma hgamma i hi⟩
   have hRemainingSubset:
       S.agreementFiber gamma \ S.identities ⊆
         Snext.agreementFiber gamma:=by
     intro i hi
     obtain ⟨holdFiber,hnotIdentity⟩:=Finset.mem_sdiff.mp hi
     obtain ⟨hinode,hold⟩:=Finset.mem_filter.mp holdFiber
     apply Finset.mem_filter.mpr
     refine ⟨?_,hdescend gamma hgamma i ?_ hold⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
   calc
     (S.agreementFiber gamma).card-S.identities.card=
         (S.agreementFiber gamma \ S.identities).card:=by
       rw [Finset.card_sdiff_of_subset hIdentitySubset]
     _ ≤ (Snext.agreementFiber gamma).card:=
       Finset.card_le_card hRemainingSubset
structure TerminalDescendant
   (S:ResidualStage phi Gamma x p e flag d support) where
 degree:ℕ
 degree_le:degree ≤ d
 stage:ResidualStage phi Gamma x p e flag degree support
 terminal:stage.identities=∅
 nodes_card:stage.nodes.card=S.nodes.card-(d-degree)
 agreement_card:∀ gamma∈Gamma,
   (S.agreementFiber gamma).card-(d-degree) ≤
     (stage.agreementFiber gamma).card
theorem proper_agreement_of_terminal
   (S:ResidualStage phi Gamma x p e flag d support)
   (hterminal:S.identities=∅) {i:Iota} (hi:i∈S.nodes):
   ¬ S.G∣agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i):=by
 intro hdvd
 have hmem:i∈S.identities:=by
   apply Finset.mem_filter.mpr
   exact ⟨hi,Ideal.mem_span_singleton.mpr hdvd⟩
 rw [hterminal] at hmem
 simpa using hmem
theorem exists_terminal_descendant
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support):
   Nonempty S.TerminalDescendant:=by
 induction d using Nat.strong_induction_on with
 | h d ih =>
     by_cases hterminal:S.identities=∅
     · exact ⟨{
         degree:=d
         degree_le:=le_rfl
         stage:=S
         terminal:=hterminal
         nodes_card:=by simp
         agreement_card:=by simp
       }⟩
     · have hk:S.identities.card ≤ d:=S.identities_card_le
       have hkpos:0 < S.identities.card:=Finset.card_pos.mpr
         (Finset.nonempty_iff_ne_empty.mpr hterminal)
       obtain ⟨Snext,hnodes,hagreements⟩:=
         S.advance_card hphi hterminal
       have hdegree_lt:d-S.identities.card < d:=by omega
       obtain ⟨Dnext⟩:=ih (d-S.identities.card) hdegree_lt Snext
       have hDle:Dnext.degree ≤ d-S.identities.card:=
         Dnext.degree_le
       have hdegree_split:d-Dnext.degree=
           S.identities.card+
             ((d-S.identities.card)-Dnext.degree):=by
         omega
       refine ⟨{
         degree:=Dnext.degree
         degree_le:=Dnext.degree_le.trans (Nat.sub_le d S.identities.card)
         stage:=Dnext.stage
         terminal:=Dnext.terminal
         nodes_card:=?_
         agreement_card:=?_
       }⟩
       · rw [Dnext.nodes_card,hnodes]
         rw [hdegree_split]
         exact Nat.sub_sub _ _ _
       · intro gamma hgamma
         have hstep:=hagreements gamma hgamma
         have htail:=Dnext.agreement_card gamma hgamma
         have hmono:
             ((S.agreementFiber gamma).card-S.identities.card)-
                 ((d-S.identities.card)-Dnext.degree) ≤
               (Snext.agreementFiber gamma).card-
                 ((d-S.identities.card)-Dnext.degree):=
           Nat.sub_le_sub_right hstep _
         calc
           (S.agreementFiber gamma).card-(d-Dnext.degree)=
               ((S.agreementFiber gamma).card-S.identities.card)-
                 ((d-S.identities.card)-Dnext.degree):=by
             rw [hdegree_split]
             exact (Nat.sub_sub _ _ _).symm
           _ ≤ (Snext.agreementFiber gamma).card-
                 ((d-S.identities.card)-Dnext.degree):=hmono
           _ ≤ (Dnext.stage.agreementFiber gamma).card:=htail
end ResidualStage
end
end ProximityPrize.SubmissionLower.RCN159
end PackedLegacy_B

/-! Packed from ProximityPrize.SubmissionLower.D8. -/
section PackedLegacy_D8
namespace ProximityPrize.SubmissionLower.RCN221
open scoped Classical BigOperators
open RCN223 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN238 RCN231 RCN174 RCN319 RCN243 RCN222 RCN266 RCN159 RCN156 RCN275 RCN234 RCN095 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):FlagDegree:=
 ⟨g.1.degreeOf (2:Fin 3),g.1.degreeOf (0:Fin 3),
   g.1.degreeOf (1:Fin 3)⟩
theorem polynomialIn_geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):PolynomialInFlag (geometricFlag K g) g.1:=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 change d 1 ≤ g.1.degreeOf 1∧
   d 0+d 1 ≤ g.1.degreeOf 0+g.1.degreeOf 1∧
   d 0+d 1+d 2 ≤
     g.1.degreeOf 2+g.1.degreeOf 0+g.1.degreeOf 1
 omega
theorem residual_surface_weights_of_box
   (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   wt residualSWeights F ≤ 8∧
     wt residualYSWeights F ≤ 43∧
     wt residualTotalWeights F ≤ 503:=by
 constructor
 · apply (weightedTotalDegree_le_iff residualSWeights F 8).mpr
   intro d hd
   have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
       d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
   rw [weight_fin4]
   rw [show residualSWeights 0=0 by rfl,
     show residualSWeights 1=0 by rfl,
     show residualSWeights 2=1 by rfl,
     show residualSWeights 3=0 by rfl]
   simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
   simpa only [slopeCap] using hb.2.1
 · constructor
   · apply (weightedTotalDegree_le_iff residualYSWeights F 43).mpr
     intro d hd
     have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
         d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
     rw [weight_fin4]
     rw [show residualYSWeights 0=0 by rfl,
       show residualYSWeights 1=1 by rfl,
       show residualYSWeights 2=1 by rfl,
       show residualYSWeights 3=0 by rfl]
     simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
     norm_num [weightedCap,RCN223.multiplicity,
       agreements,n,errors,w] at hb
     omega
   · apply (weightedTotalDegree_le_iff residualTotalWeights F 503).mpr
     intro d hd
     have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
         d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
     rw [weight_fin4]
     rw [show residualTotalWeights 0=0 by rfl,
       show residualTotalWeights 1=1 by rfl,
       show residualTotalWeights 2=1 by rfl,
       show residualTotalWeights 3=1 by rfl]
     simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
     norm_num [seedTotalCap,slopeCap] at hb
     omega
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
def geometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf (2:Fin 4))
   (hRsmall:F.degreeOf (2:Fin 4) < pchar)
   (hsupport:ResidualSupportData support F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K F):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K F selected Gamma g) x pchar errorCap
     (geometricFlag K g) degree support:=by
 classical
 letI:CharP (GenericField K) pchar:=genericField_charP K pchar
 have hgspec:=surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
 have hgirred:=hgspec.1
 have hgdiv:=hgspec.2
 have hgate:=geometric_factor_regular_gate K (GenericField K) F hF pchar
   hRpos hRsmall g.1 hgirred
   (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
 have hsub:=geometricSeeds_subset K F selected Gamma g
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=g.1
   irreducible_G:=hgirred
   G_dvd_surface:=hgdiv
   y_dependent:=hgate.1
   regular_proper:=by
     simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
   flag_support:=polynomialIn_geometricFlag K g
   surface_s_weight:=hsupport.s_weight
   surface_ys_weight:=hsupport.ys_weight
   surface_total_weight:=hsupport.total_weight
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolutions gamma (hsub hgamma)
   regular:=fun gamma hgamma↦
     selectedPoint_regular_of_specialization K F selected gamma
       (hregular gamma (hsub hgamma))
   on_component:=fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma _ degree errorCap
     hsub hnoPencil
   characteristic_bound:=hdegreeChar
 }
def geometricResidualStage
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf (2:Fin 4))
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (g:GeometricFactor K F):
   letI:CharP (GenericField K) prime:=genericField_charP K prime
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K F selected Gamma g) x prime errors
     (geometricFlag K g) w:=by
 have hRsmall:F.degreeOf (2:Fin 4) < prime:=
   (degreeOf_R_le_of_mem_box F weightedCap w seedTotalCap slopeCap hbox).trans_lt
     (by norm_num [slopeCap,prime])
 have hsupport:=residual_surface_weights_of_box K F hbox
 exact geometricResidualStageOfSupport K
   ResidualSupportParameters.acceptedSupport F hF hRpos hRsmall
   ⟨hsupport.1,hsupport.2.1,hsupport.2.2⟩ selected Gamma nodes x u0 u1
   hinj hdegree hsolutions hregular hnoPencil
   (by norm_num [w,prime]) g
theorem geometricFlag_budgets
   (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,(geometricFlag K g).zOnly) ≤
       F.degreeOf (3:Fin 4)∧
     (∑ g:GeometricFactor K F,(geometricFlag K g).yz) ≤
       F.degreeOf (1:Fin 4)∧
     (∑ g:GeometricFactor K F,(geometricFlag K g).all) ≤
       F.degreeOf (2:Fin 4):=by
 exact ⟨geometricFactor_sum_degree_le K F hF 2,
   geometricFactor_sum_degree_le K F hF 0,
   geometricFactor_sum_degree_le K F hF 1⟩
theorem original_regular_seed_bound_of_geometric_factor_counts
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hcount:∀ g:GeometricFactor K F,
     (geometricSeeds K F selected Gamma g).card*gap^2 ≤
       factorRegularLedger (geometricFlag K g)):
   Gamma.card*gap^2 ≤
     factorRegularLedger
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩:=by
 have hcover:=card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma
   hsolutions
 have hcaps:=geometricFlag_budgets K F hF.ne_zero
 calc
   Gamma.card*gap^2 ≤
       (∑ g:GeometricFactor K F,
         (geometricSeeds K F selected Gamma g).card)*gap^2:=
     Nat.mul_le_mul_right _ hcover
   _=∑ g:GeometricFactor K F,
       (geometricSeeds K F selected Gamma g).card*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       factorRegularLedger (geometricFlag K g):=
     Finset.sum_le_sum (fun g _↦hcount g)
   _ ≤ factorRegularLedger
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩:=
     sum_factorRegularLedger_le_flag (geometricFlag K)
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩ hcaps.1 hcaps.2.1 hcaps.2.2
end
end ProximityPrize.SubmissionLower.RCN221
end PackedLegacy_D8

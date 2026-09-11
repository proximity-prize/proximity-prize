import ProximityPrize.SubmissionLower.PartF002

section Compact_PackedLegacyCore1
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
end
end ProximityPrize.SubmissionLower.RCN256
end PackedLegacy_N4
end Compact_PackedLegacyCore1

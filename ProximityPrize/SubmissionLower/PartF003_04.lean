import ProximityPrize.SubmissionLower.PartF003_03
section Compact_PackedLegacyCore1
section PackedLegacy_J1
namespace ProximityPrize.SubmissionLower.RCN082
open UniqueFactorizationMonoid RCN136 RCN174
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid

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
theorem initialPoint_regular_iff (F:Poly4 K) (P:Polynomial K) (γ:K):
   MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
       (MvPolynomial.pderiv (2:Fin 4) F)≠0 ↔
     specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0:=by
 simp only [evaluation_at_initialPoint,ne_eq,polynomialEmbedding_eq_zero_iff]
def valueSeedProjection (pair:Polynomial K × K):GenericField K × GenericField K:=
 (initialPoint K pair.1 pair.2 1,initialPoint K pair.1 pair.2 3)
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
end SurfaceFamilies
section CanonicalPoints
variable (K:Type*) [Field K]
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
end
end ProximityPrize.SubmissionLower.RCN079
end PackedLegacy_I9
end Compact_PackedLegacyCore1

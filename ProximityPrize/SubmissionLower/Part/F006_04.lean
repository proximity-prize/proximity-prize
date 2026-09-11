import ProximityPrize.SubmissionLower.Part.F006_03
section Compact_PackedLegacy
section PackedLegacy_FM
namespace ProximityPrize.SubmissionLower.RCN230
open IsLocalRing Polynomial Ideal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable (R:Type*) [CommRing R]

instance polynomial_isRegularRing_compat [IsRegularRing R]:
   IsRegularRing R[X]:=by
 apply isRegularRing_iff.mpr
 intro p hp
 let q:=p.comap Polynomial.C
 let S:=(Localization.AtPrime q)[X]
 let pc:=Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
 letI:Algebra R[X] S:=Polynomial.algebra R (Localization.AtPrime q)
 haveI:IsLocalization pc S:=Polynomial.isLocalization _ _
 let pS:=p.map (algebraMap R[X] S)
 have hdisj:Disjoint (pc:Set R[X]) (p:Set R[X]):=by
   apply Set.disjoint_left.mpr
   rintro _ ⟨b,hb,rfl⟩ hp
   exact hb hp
 haveI:pS.IsPrime:=
   IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance hdisj
 haveI:IsLocalization.AtPrime (Localization.AtPrime pS) p:=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     pc (Localization.AtPrime pS) pS
   exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj).symm
 haveI:IsRegularLocalRing (Localization.AtPrime q):=
   IsRegularRing.isRegularLocalRing_localization q
 have hbase:pS.comap Polynomial.C=maximalIdeal (Localization.AtPrime q):=by
   rw [←IsLocalization.map_under q.primeCompl _ (pS.comap Polynomial.C),
     ←IsLocalization.map_under q.primeCompl _
       (maximalIdeal (Localization.AtPrime q))]
   simp only [Ideal.comap_comap,S,pS]
   rw [←Polynomial.algebraMap_eq (R:=Localization.AtPrime q),
     ←IsScalarTower.algebraMap_eq R (Localization.AtPrime q)
       (Localization.AtPrime q)[X],
     IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X],
     ←Ideal.comap_comap, ←Ideal.under_def R[X],
     IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj]
   simp [q,IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
 haveI:=polynomial_localization_isRegularLocalRing_compat
   (Localization.AtPrime q) pS hbase
 exact IsRegularLocalRing.of_ringEquiv (R:=Localization.AtPrime pS)
   (IsLocalization.algEquiv p.primeCompl
     (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
instance mvPolynomial_isRegularRing_compat [IsRegularRing R]
   {ι:Type*} [Finite ι]:IsRegularRing (MvPolynomial ι R):=by
 induction ι using Finite.induction_empty_option with
 | of_equiv e H =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.renameEquiv _ e).toRingEquiv
 | h_empty =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R _).symm
 | h_option IH =>
     exact IsRegularRing.of_ringEquiv
       (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
theorem mvPolynomial_atPrime_isRegularLocalRing
   {K:Type*} [Field K] {ι:Type*} [Finite ι]
   (p:Ideal (MvPolynomial ι K)) [p.IsPrime]:
   IsRegularLocalRing (Localization.AtPrime p):=by
 letI:IsRegularRing K:=inferInstance
 letI:IsRegularRing (MvPolynomial ι K):=
   mvPolynomial_isRegularRing_compat K
 infer_instance
end
end ProximityPrize.SubmissionLower.RCN230
end PackedLegacy_FM

/-! Packed from ProximityPrize.SubmissionLower.FF. -/
section PackedLegacy_FF
namespace ProximityPrize.SubmissionLower.RCN218
open RCN313 RCN077 RCN136 RCN055 RCN188 RCN270 RCN186 RCN230 IsLocalRing
variable {K:Type*} [Field K]
abbrev Poly:=MvPolynomial (Fin 4) K
noncomputable def factorIdeal (F:Poly (K:=K)):Ideal (Poly (K:=K)):=Ideal.span {F}
theorem factorIdeal_isPrime (F:Poly (K:=K)) (hF:Irreducible F):
   (factorIdeal F).IsPrime:=by
 exact (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
noncomputable def contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)):
   Ideal (Poly (K:=K)):=
 C.comap (surfaceMap phi)
instance contractedPrime_isPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)) [C.IsPrime]:
   (contractedPrime phi C).IsPrime:=by
 exact Ideal.comap_isPrime (surfaceMap phi) C
theorem mem_contractedPrime_iff {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (A:Poly (K:=K)):
   A∈contractedPrime phi C ↔ surfaceMap phi A∈C:=
 Iff.rfl
theorem factorIdeal_le_contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (F:Poly (K:=K)) (hF:surfaceMap phi F∈C):
   factorIdeal F ≤ contractedPrime phi C:=by
 apply Ideal.span_le.2
 intro A hA
 simpa only [Set.mem_singleton_iff] using hA ▸ hF
noncomputable abbrev FactorLocal
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   (hFp:factorIdeal F ≤ p):Type _:=
 LocalizedQuotient (factorIdeal F) p hFp
theorem derivation_mem_maximal_of_mem_sq
   {A:Type*} [CommRing A] [Algebra K A] [IsLocalRing A]
   (D:Derivation K A A) (x:A) (hx:x∈maximalIdeal A^2):
   D x∈maximalIdeal A:=by
 rw [pow_two] at hx
 refine Submodule.mul_induction_on hx ?_ ?_
 · intro a ha b hb
   rw [D.leibniz]
   simpa [Algebra.smul_def] using (maximalIdeal A).add_mem
     ((maximalIdeal A).mul_mem_right (D b) ha)
     ((maximalIdeal A).mul_mem_right (D a) hb)
 · intro a b ha hb
   simpa only [map_add] using (maximalIdeal A).add_mem ha hb
noncomputable def factorAmbientQuotientEquiv
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   (Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}) ≃+*
     FactorLocal F p hFp:=
 (Ideal.quotEquivOfEq (by
   simp only [factorIdeal,Ideal.map_span,Set.image_singleton])).trans
   (quotientAmbientEquivLocalizedQuotient (factorIdeal F) p hFp)
theorem factorLocal_isRegularLocalRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p)
   (hdimFactor:ringKrullDim (FactorLocal F p hFp)=1):
   IsRegularLocalRing (FactorLocal F p hFp):=by
 letI:IsRegularLocalRing (Localization.AtPrime p):=
   mvPolynomial_atPrime_isRegularLocalRing p
 let A:=Localization.AtPrime p
 let f:A:=algebraMap (Poly (K:=K)) A F
 have hdim:ringKrullDim A=2:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A,hheight]
   norm_num
 have hf:f∈maximalIdeal A:=by
   exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p F).mpr
     (hFp (Ideal.mem_span_singleton_self F))
 have hf2:f∉maximalIdeal A^2:=by
   intro hf2
   let D:Derivation K A A:=localizationDerivation p.primeCompl
     (MvPolynomial.pderiv (2:Fin 4):Derivation K (Poly (K:=K)) _)
   have hDmem:D f∈maximalIdeal A:=derivation_mem_maximal_of_mem_sq D f hf2
   have hD:D f=algebraMap (Poly (K:=K)) A (polyH K F):=by
     exact localizationDerivation_algebraMap p.primeCompl _ F
   rw [hD] at hDmem
   exact hH ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p (polyH K F)).mp hDmem)
 haveI hsource:IsRegularLocalRing
     (Localization.AtPrime p ⧸ Ideal.span {
       algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}):=by
   change IsRegularLocalRing (A ⧸ Ideal.span {f})
   apply quotient_span_singleton_isRegularLocalRing f hf hf2 hdim
   calc
     ringKrullDim (A ⧸ Ideal.span {f})=
         ringKrullDim (FactorLocal F p hFp):=
       ringKrullDim_eq_of_ringEquiv (factorAmbientQuotientEquiv F p hFp)
     _=1:=hdimFactor
 exact IsRegularLocalRing.of_ringEquiv (R:=
   Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F})
   (factorAmbientQuotientEquiv F p hFp)
theorem quotientPrime_height_eq_one
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   (quotientPrime (factorIdeal F) p).height=1:=by
 let I:=factorIdeal F
 have hF0:F≠0:=by
   intro hzero
   subst F
   apply hH
   simp [polyH]
 have hFunit:¬ IsUnit F:=by
   intro hunit
   exact hfactorPrime.ne_top (by
     rw [factorIdeal,Ideal.span_singleton_eq_top]
     exact hunit)
 have hIheight:I.height=1:=by
   change (Ideal.span ({F}:Set (Poly (K:=K)))).height=1
   exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
     (by simpa [mem_nonZeroDivisors_iff_ne_zero] using hF0) hFunit
 have hIpne:I≠p:=by
   intro heq
   have:I.height=p.height:=congrArg Ideal.height heq
   rw [hIheight,hheight] at this
   norm_num at this
 have hIlt:I < p:=lt_of_le_of_ne hFp hIpne
 obtain ⟨x,hxp,hxI⟩:=SetLike.exists_of_lt hIlt
 have hmin:p∈(I ⊔ Ideal.span {x}).minimalPrimes:=by
   refine ⟨⟨inferInstance,sup_le hFp (Ideal.span_le.2 (by simpa))⟩,?_⟩
   intro r hr hrp
   rcases hr with ⟨hrprime,hJr⟩
   letI:r.IsPrime:=hrprime
   have hIr:I ≤ r:=le_sup_left.trans hJr
   have hIrne:I≠r:=by
     intro heq
     apply hxI
     rw [heq]
     exact hJr ((show Ideal.span {x} ≤ I ⊔ Ideal.span {x} from le_sup_right)
       (Ideal.mem_span_singleton_self x))
   have hIrlt:I < r:=lt_of_le_of_ne hIr hIrne
   have hrpEq:r=p:=by
     apply le_antisymm hrp
     by_contra hnot
     have hrlt:r < p:=lt_of_le_of_ne hrp (Ne.symm (ne_of_not_le hnot))
     have h1:=Ideal.height_add_one_le_of_lt_of_isPrime hIrlt
     have h2:=Ideal.height_add_one_le_of_lt_of_isPrime hrlt
     have hbad:(3:ℕ∞) ≤ p.height:=by
       calc
         3=I.height+1+1:=by rw [hIheight];norm_num
         _ ≤ r.height+1:=by
           simpa [add_comm,add_left_comm,add_assoc] using add_le_add_left h1 1
         _ ≤ p.height:=h2
     rw [hheight] at hbad
     norm_num at hbad
   exact hrpEq.ge
 apply le_antisymm
 · exact Ideal.map_height_le_one_of_mem_minimalPrimes hmin
 · rw [Order.one_le_iff_ne_zero]
   intro hz
   have hqbot:quotientPrime I p=⊥:=Ideal.height_eq_zero_iff_eq_bot.mp hz
   have hcomap:=quotientPrime_comap_quotientMk I p hFp
   rw [hqbot] at hcomap
   have hpI:p=I:=by
     change RingHom.ker (Ideal.Quotient.mk I)=p at hcomap
     rw [Ideal.mk_ker] at hcomap
     exact hcomap.symm
   exact hIpne hpI.symm
theorem factorLocal_isDiscreteValuationRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   IsDiscreteValuationRing (FactorLocal F p hFp):=by
 have hdim:ringKrullDim (FactorLocal F p hFp)=1:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height
     (quotientPrime (factorIdeal F) p) (FactorLocal F p hFp)]
   exact_mod_cast quotientPrime_height_eq_one F p hFp hheight hH
 letI:IsRegularLocalRing (FactorLocal F p hFp):=
   factorLocal_isRegularLocalRing F p hFp hheight hH hdim
 exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim
private theorem baseDerivation_self (F:Poly (K:=K)):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
private theorem baseDerivation_stable_factor (F:Poly (K:=K)):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [factorIdeal,Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [(baseDerivation F).leibniz,baseDerivation_self]
 simp
noncomputable def factorDerivation (F:Poly (K:=K)):
   Derivation K (Poly (K:=K) ⧸ factorIdeal F) (Poly (K:=K) ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F) (baseDerivation_stable_factor F)
noncomputable def factorLocalDerivation
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   Derivation K (FactorLocal F p hFp) (FactorLocal F p hFp):=
 localizationDerivation (K:=K)
   (R:=Poly (K:=K) ⧸ factorIdeal F) (S:=FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p).primeCompl (factorDerivation F)
theorem factorLocalDerivation_mk
   (F P:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   factorLocalDerivation F p hFp
       (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
         (Ideal.Quotient.mk (factorIdeal F) P))=
     algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
       (Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P)):=by
 rw [factorLocalDerivation,localizationDerivation_algebraMap]
 have hq:=RCN077.quotientDerivation_mk
   (K:=K) (A:=Poly (K:=K)) (baseDerivation F) (factorIdeal F)
     (baseDerivation_stable_factor F) P
 exact congrArg
   (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp))
   (by simpa only [factorDerivation] using hq)
noncomputable def factorLocalImage
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (P:Poly (K:=K)):FactorLocal F p hFp:=
 algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
   (Ideal.Quotient.mk (factorIdeal F) P)
theorem factorLocal_numerator_succ
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (b:ℕ):
   factorLocalImage F p hFp (numerator K F (b+1))=
     factorLocalImage F p hFp (polyH K F)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (numerator K F b))-
       (2*b:FactorLocal F p hFp)*
         factorLocalImage F p hFp (numerator K F b)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (polyH K F)):=by
 rw [numerator_succ,numeratorStep_eq]
 simp only [factorLocalImage,map_sub,map_mul,map_natCast]
 rw [←factorLocalDerivation_mk F (numerator K F b) p hFp,
   ←factorLocalDerivation_mk F (polyH K F) p hFp]
 push_cast
 ring
theorem factorLocal_image_isUnit_of_not_mem
   (F A:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hA:A∉p):
   IsUnit (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
     (Ideal.Quotient.mk (factorIdeal F) A)):=by
 apply (IsLocalization.AtPrime.isUnit_to_map_iff (FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p) _).mpr
 intro hmem
 apply hA
 have hmem':A∈(quotientPrime (factorIdeal F) p).comap
     (Ideal.Quotient.mk (factorIdeal F)):=hmem
 rw [quotientPrime_comap_quotientMk (factorIdeal F) p hFp] at hmem'
 exact hmem'
end ProximityPrize.SubmissionLower.RCN218
end PackedLegacy_FF

/-! Packed from ProximityPrize.SubmissionLower.CJ. -/
section PackedLegacy_CJ
namespace ProximityPrize.SubmissionLower.RCN326
open ProximityPrize.Benchmark RCN095 RCN100 RCN119
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6733
def errors:ℕ:=80092
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def radiusNumerator:ℕ:=128*errors+127
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity:ℕ
 totalCap:ℕ
 slopeCap:ℕ
 middleCap:ℕ
 coefficients:ℕ
 rank:ℕ
 deriving DecidableEq
namespace Profile
def nullity (P:Profile):ℕ:=P.coefficients-n*P.rank
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def totalRank (P:Profile):ℕ:=n*P.rank
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
end Profile
def profileA:Profile:=⟨41,19688,12,56,44579488339867,170057251⟩
def profileB:Profile:=⟨81,1242,25,112,20738895387938,79112293⟩
def profileC:Profile:=⟨43,624668,11,59,1477011414465277,5634351404⟩
def finalMeet:Profile:=⟨41,1242,11,56,0,0⟩
def fixedFlag:FlagDegree:=
 ⟨finalMeet.totalCap-finalMeet.middleCap,
   finalMeet.middleCap-finalMeet.slopeCap,
   finalMeet.slopeCap⟩
def direction:FlagDegree:=
 ⟨2*fixedFlag.zOnly,2*fixedFlag.yz-1,2*fixedFlag.all-1⟩
def tailFlag (d:ℕ):FlagDegree:=unitYZFlag+(d+1) • direction
def fixedRegularCost:ℕ:=flagMixed fixedFlag (tailFlag (w+1)) (tailFlag (w+2))
def fixedSingularCost:ℕ:=63020462332448
def firstResidualRegularCost:ℕ:=112248424128199
def firstResidualSingularCost:ℕ:=678257591819300
def secondResidualRegularCost:ℕ:=1127729807323574
def secondResidualSingularCost:ℕ:=75606965639647
def fixedCost:ℕ:=fixedRegularCost+fixedSingularCost
def firstResidualCeiling:ℕ:=
 firstResidualRegularCost+firstResidualSingularCost
def secondResidualCeiling:ℕ:=
 secondResidualRegularCost+secondResidualSingularCost
def totalCost:ℕ:=
 fixedRegularCost+fixedSingularCost+
   firstResidualRegularCost+firstResidualSingularCost+
   secondResidualRegularCost+secondResidualSingularCost
def seedlessListNumerator:ℕ:=43585392724533
def seedlessListCeiling:ℕ:=seedlessListNumerator/gap+1
def capacity:ℕ:=prime^6/2^128
def mcaBudget:ℕ:=capacity-seedlessListCeiling
def slack:ℕ:=mcaBudget-totalCost
abbrev scoreGate (e:ℕ):Prop:=
 (radiusDenominator-(128*e+127))^12800*2^score ≤
   radiusDenominator^12800
theorem profileA_coefficients_exact:
   coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap=
     profileA.coefficients:=by
 change coefficientCount (41*182052) 131071 19688 12=44579488339867
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (41*182052) 131071 19688 12 57 (by decide) (by decide)]
 decide
theorem profileB_coefficients_exact:
   coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap=
     profileB.coefficients:=by
 change coefficientCount (81*182052) 131071 1242 25=20738895387938
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (81*182052) 131071 1242 25 113 (by decide) (by decide)]
 decide
theorem profileC_coefficients_exact:
   coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap=
     profileC.coefficients:=by
 change coefficientCount (43*182052) 131071 624668 11=1477011414465277
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (43*182052) 131071 624668 11 60 (by decide) (by decide)]
 decide
theorem interpolation_gates:
   profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 decide
theorem fixed_flag_values:
   fixedFlag=⟨1186,45,11⟩∧direction=⟨2372,89,21⟩∧
     tailFlag (w+1)=⟨310905156,11665498,2752533⟩∧
     tailFlag (w+2)=⟨310907528,11665587,2752554⟩:=by
 decide
end
end ProximityPrize.SubmissionLower.RCN326
end PackedLegacy_CJ

/-! Packed from ProximityPrize.SubmissionLower.Q7. -/
section PackedLegacy_Q7
namespace ProximityPrize.SubmissionLower.RCN339
open RCN095 RCN237 RCN264 RCN326
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1:FlagDegree}
theorem yzCost_mul_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ B.weightedCost r C:=by
 unfold PrimeFlagBudgetFamily.weightedCost
 calc
   coefficient*B.yzCost C ≤ r.yz*B.yzCost C:=
     Nat.mul_le_mul_right (B.yzCost C) hcoefficient
   _ ≤ r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C:=by
     omega
end
end ProximityPrize.SubmissionLower.RCN339
end PackedLegacy_Q7

/-! Packed from ProximityPrize.SubmissionLower.FE. -/
section PackedLegacy_FE
namespace ProximityPrize.SubmissionLower.RCN217
open RCN077 RCN313
 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
private abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
private theorem baseDerivation_self (F:Poly4 K):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
private theorem baseDerivation_stable_factor (F:Poly4 K):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [leibniz_product,baseDerivation_self]
 ring
private def factorDerivation (F:Poly4 K):
   Derivation K (Poly4 K ⧸ factorIdeal F) (Poly4 K ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F)
   (baseDerivation_stable_factor F)
private theorem factorDerivation_mk (F P:Poly4 K):
   factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P)=
     Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P):=
 quotientDerivation_mk _ _ _ P
private theorem factor_zero (F:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) F=0:=
 Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
private theorem polyH_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul,factor_zero]
 ring
private theorem polyG_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyG K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyG K F):=by
 unfold polyG
 simp only [MvPolynomial.pderiv_mul,map_neg,map_add,map_mul,factor_zero]
 ring
private theorem baseDerivation_mul_factor_mod (F Q P:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (baseDerivation (F*Q) P)=
     Ideal.Quotient.mk (factorIdeal F) Q*
       factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P):=by
 rw [factorDerivation_mk,baseDerivation_apply,baseDerivation_apply]
 simp only [map_add,map_mul]
 rw [polyH_mul_factor_mod,polyG_mul_factor_mod]
 ring
private theorem scaled_step_identity {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (q h n nS:A) (b:ℕ)
   (hN:nS=q^(2*b)*n):
   q*h*(q*D nS)-(2*b:A)*nS*(q*D (q*h))=
     q^(2*(b+1))*(h*D n-(2*b:A)*n*D h):=by
 cases b with
 | zero =>
     simp only [hN,mul_zero,pow_zero,one_mul,Nat.cast_zero,
       zero_mul,sub_zero]
     ring
 | succ c =>
     rw [hN]
     simp only [leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
       Nat.cast_mul,Nat.cast_ofNat]
     have he:2*(c+1)=2*c+2:=by omega
     have hesub:2*c+2-1=2*c+1:=by omega
     have henext:2*(c+1+1)=2*c+4:=by omega
     rw [he,hesub,henext]
     have hp1:q^(2*c+1)=q^(2*c)*q:=by
       rw [pow_add,pow_one]
     have hp2:q^(2*c+2)=q^(2*c)*q^2:=by rw [pow_add]
     have hp4:q^(2*c+4)=q^(2*c)*q^4:=by rw [pow_add]
     rw [hp1,hp2,hp4]
     ring
private theorem numerator_scaling_mod (F Q:Poly4 K) (b:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*b)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F b):=by
 induction b with
 | zero => simp
 | succ b ih =>
   change Ideal.Quotient.mk (factorIdeal F)
       (numeratorStep K (F*Q) b (numerator K (F*Q) b))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*(b+1))*
       Ideal.Quotient.mk (factorIdeal F)
         (numeratorStep K F b (numerator K F b))
   rw [numeratorStep_eq,numeratorStep_eq]
   simp only [map_sub,map_mul,map_natCast]
   rw [polyH_mul_factor_mod,
     baseDerivation_mul_factor_mod F Q (numerator K (F*Q) b),
     baseDerivation_mul_factor_mod F Q (polyH K (F*Q))]
   rw [←factorDerivation_mk F (numerator K F b),
     ←factorDerivation_mk F (polyH K F)]
   have hDH:=congrArg (factorDerivation F) (polyH_mul_factor_mod F Q)
   rw [hDH]
   simp only [Nat.cast_mul,Nat.cast_ofNat]
   apply scaled_step_identity (factorDerivation F)
     (Ideal.Quotient.mk (factorIdeal F) Q)
     (Ideal.Quotient.mk (factorIdeal F) (polyH K F))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K F b))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b))
     b
   exact ih
theorem numerator_sub_factor_power_mem (F Q:Poly4 K) (b:ℕ):
   numerator K (F*Q) b-Q^(2*b)*numerator K F b∈
     Ideal.span ({F}:Set (Poly4 K)):=by
 rw [←Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 simpa only [map_mul,map_pow] using numerator_scaling_mod F Q b
theorem factor_dvd_numerator_sub_power (F Q:Poly4 K) (b:ℕ):
   F∣numerator K (F*Q) b-Q^(2*b)*numerator K F b:=by
 exact Ideal.mem_span_singleton.mp (numerator_sub_factor_power_mem F Q b)
theorem factor_dvd_numerator_sub_power_of_eq (F Q S:Poly4 K)
   (hS:S=F*Q) (b:ℕ):
   F∣numerator K S b-Q^(2*b)*numerator K F b:=by
 subst S
 exact factor_dvd_numerator_sub_power F Q b
end
end ProximityPrize.SubmissionLower.RCN217
end PackedLegacy_FE

/-! Packed from ProximityPrize.SubmissionLower.A5. -/
section PackedLegacy_A5
namespace ProximityPrize.SubmissionLower.RCN048
open scoped BigOperators
open RCN077 RCN313 RCN217
noncomputable section
variable {K:Type*} [Field K]
private abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
private theorem H_scaling_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul]
 have hz:Ideal.Quotient.mk (factorIdeal F) F=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
 rw [hz,zero_mul,add_zero]
 ring
private theorem numerator_scaling_mod (F Q:Poly4 K) (j:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*j)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F j):=by
 have h:=numerator_sub_factor_power_mem F Q j
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,sub_eq_zero] at h
 exact h
private theorem commonTerm_scaling_mod (F Q:Poly4 K) (w j:ℕ) (hj:j≤w)
   (c:ℕ → K) (x:K):
   Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm (F*Q) w c x j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm F w c x j):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have he:2*j+2*(w-j)=2*w:=by omega
 unfold commonNumeratorTerm
 simp only [map_mul,map_pow,MvPolynomial.map_C]
 rw [numerator_scaling_mod,H_scaling_mod,mul_pow]
 calc
   _=ev Q^(2*j+2*(w-j))*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by
     rw [pow_add]
     ring
   _=ev Q^(2*w)*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by rw [he]
   _=_:=by ring
private theorem seed_scaling_mod (F Q:Poly4 K) (w:ℕ) (u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F)
       (affineSeedPolynomial u0 u1*polyH K (F*Q)^(2*w))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F)
         (affineSeedPolynomial u0 u1*polyH K F^(2*w)):=by
 simp only [map_mul,map_pow]
 rw [H_scaling_mod,mul_pow]
 ring
theorem agreementNumerator_scaling_mod (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F) (agreementNumerator (F*Q) w c x u0 u1)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (agreementNumerator F w c x u0 u1):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have hsum:ev (clearedTaylorNumerator (F*Q) w c x)=
     ev Q^(2*w)*ev (clearedTaylorNumerator F w c x):=by
   unfold clearedTaylorNumerator
   simp only [map_sum]
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j hj
   exact commonTerm_scaling_mod F Q w j (by have:=Finset.mem_range.mp hj;omega) c x
 unfold agreementNumerator
 rw [map_sub,map_sub,hsum,seed_scaling_mod]
 ring
theorem factor_dvd_agreement_sub_power (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   F∣agreementNumerator (F*Q) w c x u0 u1-
     Q^(2*w)*agreementNumerator F w c x u0 u1:=by
 rw [←Ideal.mem_span_singleton]
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,
   agreementNumerator_scaling_mod,sub_self]
end
end ProximityPrize.SubmissionLower.RCN048
end PackedLegacy_A5

/-! Packed from ProximityPrize.SubmissionLower.FH. -/
section PackedLegacy_FH
namespace ProximityPrize.SubmissionLower.RCN220
open RCN136 RCN135 RCN138 RCN137 RCN082 RCN350 RCN313 RCN159 RCN217 RCN002 RCN048 RCN095 RCN275 RCN065
noncomputable section
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
theorem exists_original_factor_with_first_tail
   {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1))):
   ∃ F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧S.G∣surfaceMap (polynomialEmbedding K) F0∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) Q∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0)∧
     F0∣numerator K F0 (w+1):=by
 classical
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 have hFne:S.F≠0:=by
   intro hzero
   apply S.regular_proper
   rw [hzero]
   simp [polyH]
 let φC:Polynomial K →+*CoordinateField (Ω K) P:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).comp (polynomialEmbedding K)
 let vC:Fin 3 → CoordinateField (Ω K) P:=
   fun i => componentPoint (polynomialEmbedding K) P i.succ
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap φC S.F)=0:=by
   rw [eval_surfaceMap]
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) S.F=0
   rw [component_evaluation]
   rw [coordinateEvaluation_eq_aeval,aeval_coordinate_eq_quotient,
     Ideal.Quotient.eq_zero_iff_mem.mpr S.surface_mem_componentIdeal,map_zero]
 have hφC:Function.Injective φC:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).injective.comp
     (polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=exists_active_factor_of_surface_zero
   φC hφC S.F hFne vC hsurfaceZero
 have hF0spec:=activeFactors_spec S.F F0 hF0mem
 have hmapF0mem:surfaceMap (polynomialEmbedding K) F0∈P:=by
   rw [←coordinateEvaluation_ker (Ω K) P]
   rw [eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) F0=0 at hF0zero
   rw [component_evaluation] at hF0zero
   exact hF0zero
 have hGdivF0:S.G∣surfaceMap (polynomialEmbedding K) F0:=
   Ideal.mem_span_singleton.mp hmapF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hQnot:¬ S.G∣surfaceMap (polynomialEmbedding K) Q:=by
   intro hGQ
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_right hGQ _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hH0not:¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0):=by
   intro hGH
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [polyH,map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_left hGH _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hscale:=factor_dvd_numerator_sub_power F0 Q (w+1)
 have hdiff:S.G∣surfaceMap (polynomialEmbedding K)
     (numerator K (F0*Q) (w+1)-Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGdivF0.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hscale)
 have htail':S.G∣surfaceMap (polynomialEmbedding K) (numerator K (F0*Q) (w+1)):=by
   simpa only [hprod] using hTail
 have hmul:S.G∣surfaceMap (polynomialEmbedding K)
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using dvd_sub htail' hdiff
 have hfactor:S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))∨
     S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   have hmul':S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))*
       surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
     rw [map_mul,map_pow] at hmul
     exact hmul
   exact S.irreducible_G.prime.dvd_or_dvd hmul'
 have hnum:S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   rcases hfactor with hpow | hnum
   · exact False.elim (hQnot (Prime.dvd_of_dvd_pow S.irreducible_G.prime
       (by simpa only [map_pow] using hpow)))
   · exact hnum
 have hbase:F0∣numerator K F0 (w+1):=
   (geometric_factor_dvd_iff K (Ω K) F0 (numerator K F0 (w+1))
     hF0spec.1 hF0spec.2.2 S.G S.irreducible_G
     (by simpa only [canonical_geometricSurfaceMap] using hGdivF0)).mp
     (by simpa only [canonical_geometricSurfaceMap] using hnum)
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGdivF0,hQnot,hH0not,hbase⟩
theorem original_factor_agreement_proper
   (φ:Polynomial K →+*Ω K) (F0 Q:MvPolynomial (Fin 4) K)
   (G:MvPolynomial (Fin 3) (Ω K))
   (hGdivF0:G∣surfaceMap φ F0)
   (w:ℕ) (c:ℕ → K) (x0 u0 u1:K)
   (hproper:¬G∣surfaceMap φ (agreementNumerator (F0*Q) w c x0 u0 u1)):
   ¬F0∣agreementNumerator F0 w c x0 u0 u1:=by
 intro hF0cut
 have hcut:G∣surfaceMap φ (agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ) hF0cut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (agreementNumerator (F0*Q) w c x0 u0 u1-
       Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ)
     (factor_dvd_agreement_sub_power F0 Q w c x0 u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.RCN220
end PackedLegacy_FH

/-! Packed from ProximityPrize.SubmissionLower.FL. -/
section PackedLegacy_FL
namespace ProximityPrize.SubmissionLower.RCN228
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347 RCN311 RCN174
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000
variable {K L M:Type} [Field K] [Field L] [Field M]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem canonical_polynomiality_of_first_tail
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   specialization L (globalPolynomial coefficients F v hF hreg w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 apply global_polynomiality_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end
end ProximityPrize.SubmissionLower.RCN228
end PackedLegacy_FL

/-! Packed from ProximityPrize.SubmissionLower.E4. -/
section PackedLegacy_E4
namespace ProximityPrize.SubmissionLower.RCN258
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L M:Type*} [Field k] [Field L] [Field M]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem mv_eval_mem (E:Subfield M) (c:k →+*M)
   (hc:∀ a,c a∈E) (v:Fin 4 → M) (hv:∀ i,v i∈E) (Q:Poly4 k):
   MvPolynomial.eval₂Hom c v Q∈E:=by
 induction Q using MvPolynomial.induction_on with
 | C a => simpa using hc a
 | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
 | mul_X P i hP =>
     simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using E.mul_mem hP (hv i)
theorem polynomial_eval_mem (E:Subfield M) (c:L →+*M)
   (P:Polynomial L) (hP:∀ j,c (P.coeff j)∈E) (x:M) (hx:x∈E):
   P.eval₂ c x∈E:=by
 rw [Polynomial.eval₂_eq_sum_range]
 exact E.sum_mem fun j _ => E.mul_mem (hP j) (E.pow_mem hx j)
theorem taylor_coeff_mem (E:Subfield M) (P:Polynomial M)
   (hP:∀ j,P.coeff j∈E) (x:M) (hx:x∈E) (j:ℕ):
   (Polynomial.taylor x P).coeff j∈E:=by
 rw [Polynomial.taylor_coeff]
 apply polynomial_eval_mem E (RingHom.id M) (Polynomial.hasseDeriv j P) _ x hx
 intro n
 simp only [RingHom.id_apply,Polynomial.hasseDeriv_coeff]
 exact E.mul_mem (natCast_mem E _) (hP _)
theorem globalPolynomial_coeff_mem_of_evaluations
   (E:Subfield M) (c:k →+*M) (F:Poly4 k) (v:Fin 4 → M)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hv0:v 0∈E)
   (hnum:∀ j,MvPolynomial.eval₂Hom c v (numerator k F j)∈E)
   (hH:MvPolynomial.eval₂Hom c v (polyH k F)∈E) (j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=by
 unfold globalPolynomial
 apply taylor_coeff_mem E _ _ _ (E.neg_mem hv0) j
 intro n
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 split_ifs with hn
 · rw [jetCoefficient_eq_evaluated_numerator]
   exact E.div_mem (E.mul_mem (hnum n) (E.pow_mem (E.inv_mem hH) _))
     (natCast_mem E _)
 · exact E.zero_mem
theorem map_numeratorStep (c:k →+*L) (F Q:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numeratorStep k F n Q)=
     numeratorStep L (MvPolynomial.map c F) n (MvPolynomial.map c Q):=by
 simp only [numeratorStep,clearedStep,polyH,polyG,MvPolynomial.pderiv_map,
   map_sub,map_add,map_mul,map_pow,map_natCast,map_neg,MvPolynomial.map_X]
theorem map_numerator (c:k →+*L) (F:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numerator k F n)=numerator L (MvPolynomial.map c F) n:=by
 induction n with
 | zero => simp
 | succ n ih => rw [numerator_succ,map_numeratorStep,ih,numerator_succ]
theorem mapped_globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (v:Fin 4 → M)
   (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom φ v (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ v
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (w j:ℕ):
   (globalPolynomial φ (MvPolynomial.map c F) v hF hreg w).coeff j∈E:=by
 apply globalPolynomial_coeff_mem_of_evaluations E φ (MvPolynomial.map c F)
   v hF hreg w (hv 0) _ _ j
 · intro n
   rw [←map_numerator c F n,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (numerator k F n)
 · unfold polyH
   rw [MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (MvPolynomial.pderiv (2:Fin 4) F)
theorem solution_coeff_mem_of_regular_point
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (P:Polynomial L) (γ:L) (ξ:M)
   (hsolution:specialization L P γ (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ (polynomialPoint φ P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (hv:∀ i,polynomialPoint φ P γ ξ i∈E)
   (p w:ℕ) [CharP M p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   φ (P.coeff j)∈E:=by
 have hmem:=mapped_globalPolynomial_coeff_mem E c φ hc F
   (polynomialPoint φ P γ ξ) hv
   (polynomialPoint_relation φ (MvPolynomial.map c F) P γ ξ hsolution)
   hreg w j
 rw [globalPolynomial_eq_map_of_solution φ (MvPolynomial.map c F) P γ ξ
   hsolution hreg p w hw hP,Polynomial.coeff_map] at hmem
 exact hmem
end
end ProximityPrize.SubmissionLower.RCN258
end PackedLegacy_E4

/-! Packed from ProximityPrize.SubmissionLower.J2. -/
section PackedLegacy_J2
namespace ProximityPrize.SubmissionLower.RCN083
open RCN077 RCN313 RCN269 RCN233 RCN139 RCN347 RCN047 RCN217 RCN048 RCN136 RCN258
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 15000
variable {K L Ω:Type} [Field K] [Field L] [Field Ω]
theorem map_agreementNumerator_base
   (c:K →+*L) (F:Poly4 K) (w:ℕ) (a:ℕ → K) (x u0 u1:K):
   MvPolynomial.map c (agreementNumerator F w a x u0 u1)=
     agreementNumerator (MvPolynomial.map c F) w (fun j => c (a j))
       (c x) (c u0) (c u1):=by
 simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
   affineSeedPolynomial,map_sub,map_sum,map_add,map_mul,map_pow,MvPolynomial.map_C,
   MvPolynomial.map_X,map_numerator,polyH,MvPolynomial.pderiv_map]
theorem globalPolynomial_mul_factor
   (c:K →+*L) (F Q:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hQ:MvPolynomial.eval₂Hom c v Q≠0)
   (hregF:MvPolynomial.eval₂Hom c v (polyH K F)≠0)
   (hprod:MvPolynomial.eval₂Hom c v (F*Q)=0)
   (hregprod:MvPolynomial.eval₂Hom c v (polyH K (F*Q))≠0)
   (w:ℕ):
   globalPolynomial c (F*Q) v hprod hregprod w=
     globalPolynomial c F v hF hregF w:=by
 let ev:=MvPolynomial.eval₂Hom c v
 change ev F=0 at hF
 change ev Q≠0 at hQ
 change ev (polyH K F)≠0 at hregF
 have hHscale:ev (polyH K (F*Q))=ev (polyH K F)*ev Q:=by
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul,hF,zero_mul,add_zero]
 have hNscale (j:ℕ):ev (numerator K (F*Q) j)=
     ev Q^(2*j)*ev (numerator K F j):=by
   obtain ⟨A,hA⟩:=factor_dvd_numerator_sub_power F Q j
   have h:=congrArg ev hA
   simp only [map_sub,map_mul,map_pow,hF,zero_mul] at h
   exact sub_eq_zero.mp h
 have hrecon:reconstructedPolynomial c (F*Q) v hprod hregprod w=
     reconstructedPolynomial c F v hF hregF w:=by
   ext j
   simp only [reconstructedPolynomial,jetPolynomial_coeff]
   by_cases hj:j<w+1
   · rw [if_pos hj,if_pos hj]
     rw [jetCoefficient_eq_evaluated_numerator,
       jetCoefficient_eq_evaluated_numerator]
     change ev (numerator K (F*Q) j)*(ev (polyH K (F*Q)))⁻¹^(2*j)/
         (j.factorial:L)=
       ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j)/
         (j.factorial:L)
     rw [hNscale,hHscale,mul_inv,mul_pow]
     have hcancel:ev Q^(2*j)*(ev Q)⁻¹^(2*j)=1:=by
       rw [←mul_pow,mul_inv_cancel₀ hQ,one_pow]
     calc
       _=(ev Q^(2*j)*(ev Q)⁻¹^(2*j))*
           (ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j))/
             (j.factorial:L):=by ring
       _=_:=by rw [hcancel,one_mul]
   · rw [if_neg hj,if_neg hj]
 unfold globalPolynomial
 rw [hrecon]
theorem original_factor_agreement_proper
   (φ:Polynomial K →+*Ω) (F Q:Poly4 K)
   (G:MvPolynomial (Fin 3) Ω)
   (hGF:G∣surfaceMap φ F)
   (w:ℕ) (c:ℕ → K) (x u0 u1:K)
   (hproper:¬G∣surfaceMap φ
     (agreementNumerator (F*Q) w c x u0 u1)):
   ¬F∣agreementNumerator F w c x u0 u1:=by
 intro hFcut
 have hcut:G∣surfaceMap φ
     (agreementNumerator F w c x u0 u1):=
   hGF.trans (map_dvd (surfaceMap φ) hFcut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*agreementNumerator F w c x u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut
     (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (agreementNumerator (F*Q) w c x u0 u1-
       Q^(2*w)*agreementNumerator F w c x u0 u1):=
   hGF.trans (map_dvd (surfaceMap φ)
     (factor_dvd_agreement_sub_power F Q w c x u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.RCN083
end PackedLegacy_J2

/-! Packed from ProximityPrize.SubmissionLower.EF. -/
section PackedLegacy_EF
namespace ProximityPrize.SubmissionLower.RCN126
open RCN077 RCN231 RCN229 RCN139 RCN319 RCN258
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L:Type*} [Field k] [Field L] [Algebra k L]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
def freshPoint (P:Polynomial L) (γ:L):Fin 4 → RatFunc L:=
 polynomialPoint (algebraMap L (RatFunc L)) P γ RatFunc.X
def jetField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k (Set.range (freshPoint P γ))
def coefficientField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k
   (insert RatFunc.X (insert (algebraMap L (RatFunc L) γ)
     (Set.range (fun j:ℕ => algebraMap L (RatFunc L) (P.coeff j)))))
@[simp] theorem freshPoint_X (P:Polynomial L) (γ:L):
   freshPoint P γ 0=RatFunc.X:=rfl
@[simp] theorem freshPoint_Z (P:Polynomial L) (γ:L):
   freshPoint P γ 3=algebraMap L (RatFunc L) γ:=rfl
theorem fresh_eval_eq (P:Polynomial L) (γ:L) (Q:Poly4 L):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ) Q=
     algebraMap (Polynomial L) (RatFunc L) (specialization L P γ Q):=by
 rw [freshPoint,eval_polynomialPoint_eq_specialization]
 exact RatFunc.aeval_X_left_eq_algebraMap _
theorem freshPoint_regular (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0:=by
 rw [fresh_eval_eq]
 exact RatFunc.algebraMap_ne_zero hreg
theorem coefficient_mem_of_freshPoint_mem
   (E:IntermediateField k (RatFunc L))
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (hv:∀ i,freshPoint P γ i∈E)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈E:=by
 apply solution_coeff_mem_of_regular_point E.toSubfield (algebraMap k L)
   (algebraMap L (RatFunc L)) _ F P γ RatFunc.X hsolution
   (freshPoint_regular F P γ hreg) hv p w hw hP j
 intro a
 change algebraMap k (RatFunc L) a∈E
 exact E.algebraMap_mem a
theorem coefficient_mem_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈jetField (k:=k) P γ:=by
 apply coefficient_mem_of_freshPoint_mem (jetField (k:=k) P γ)
   F P γ hsolution hreg _ p w hw hP j
 intro i
 exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
theorem jetField_le_coefficientField (P:Polynomial L) (γ:L):
   jetField (k:=k) P γ ≤ coefficientField (k:=k) P γ:=by
 let E:=coefficientField (k:=k) P γ
 have hX:(RatFunc.X:RatFunc L)∈E:=
   IntermediateField.subset_adjoin k _ (Or.inl rfl)
 have hγ:algebraMap L (RatFunc L) γ∈E:=
   IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 have hc:∀ j,algebraMap L (RatFunc L) (P.coeff j)∈E:=
   fun j => IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
 apply IntermediateField.adjoin_le_iff.mpr
 rintro x ⟨i,rfl⟩
 fin_cases i
 · exact hX
 · exact polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L)) P hc
     RatFunc.X hX
 · apply polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L))
     P.derivative _ RatFunc.X hX
   intro j
   rw [Polynomial.coeff_derivative,map_mul]
   exact E.mul_mem (hc _) (by simpa using E.natCast_mem (j+1))
 · exact hγ
theorem coefficientField_le_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   coefficientField (k:=k) P γ ≤ jetField (k:=k) P γ:=by
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨3,rfl⟩
 obtain ⟨j,rfl⟩:=hx
 exact coefficient_mem_jetField F P γ hsolution hreg p w hw hP j
theorem fresh_jetField_eq_coefficientField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   jetField (k:=k) P γ=coefficientField (k:=k) P γ:=
 le_antisymm (jetField_le_coefficientField P γ)
   (coefficientField_le_jetField F P γ hsolution hreg p w hw hP)
end
end ProximityPrize.SubmissionLower.RCN126
end PackedLegacy_EF

/-! Packed from ProximityPrize.SubmissionLower.GS. -/
section PackedLegacy_GS
namespace ProximityPrize.SubmissionLower.RCN321
noncomputable section
variable {k B E:Type} [Field k] [Field B] [Field E]
 [Algebra k B] [Algebra B E] [Algebra k E] [IsScalarTower k B E]
theorem trdeg_le_one_of_tower
   (hE:Algebra.trdeg k E ≤ 2) (htrans:Algebra.Transcendental B E):
   Algebra.trdeg k B ≤ 1:=by
 letI:Algebra.Transcendental B E:=htrans
 have hb:0 < Algebra.trdeg B E:=trdeg_pos B E
 have hsum:Algebra.trdeg k B+Algebra.trdeg B E=Algebra.trdeg k E:=
   trdeg_add_eq k B
 have hab:Algebra.trdeg k B+Algebra.trdeg B E ≤ 2:=by
   rw [hsum]
   exact hE
 by_contra hnot
 have ha:(1:Cardinal) < Algebra.trdeg k B:=lt_of_not_ge hnot
 have htwo:(2:Cardinal) ≤ Algebra.trdeg k B:=by
   have h:=Cardinal.add_one_le_of_lt ha
   norm_num at h
   exact h
 have hbone:(1:Cardinal) ≤ Algebra.trdeg B E:=Cardinal.one_le_iff_pos.mpr hb
 have hthree:(3:Cardinal) ≤ Algebra.trdeg k B+Algebra.trdeg B E:=by
   calc
     (3:Cardinal)=2+1:=by norm_num
     _ ≤ _:=add_le_add htwo hbone
 have:(3:Cardinal) ≤ 2:=hthree.trans hab
 norm_num at this
section RationalExtension
variable {k L:Type} [Field k] [Field L] [Algebra k L]
theorem coefficient_trdeg_le_one_of_rational_extension
   (B:IntermediateField k L) (E:IntermediateField k (RatFunc L))
   (hmap:B.map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤ E)
   (hX:(RatFunc.X:RatFunc L)∈E)
   (hE:Algebra.trdeg k E ≤ 2):Algebra.trdeg k B ≤ 1:=by
 let f:L →ₐ[k] RatFunc L:=IsScalarTower.toAlgHom k L (RatFunc L)
 let bToE:B →ₐ[k] E:=
   (IntermediateField.inclusion hmap).comp (B.equivMap f).toAlgHom
 letI:Algebra B E:=bToE.toRingHom.toAlgebra
 letI:IsScalarTower k B E:=IsScalarTower.of_algebraMap_eq fun c => by
   change bToE (algebraMap k B c)=algebraMap k E c
   exact bToE.commutes c
 let xE:E:=⟨RatFunc.X,hX⟩
 have hcomp:RingHom.comp (algebraMap L (RatFunc L)) B.val=
     RingHom.comp E.val (algebraMap B E):=by
   ext b
   rfl
 have hxE:Transcendental B xE:=
   (show Transcendental L (RatFunc.X:RatFunc L) from RatFunc.transcendental_X).of_ringHom_of_comp_eq
     B.val E.val B.val.injective hcomp
 exact trdeg_le_one_of_tower hE ⟨xE,hxE⟩
end RationalExtension
end
end ProximityPrize.SubmissionLower.RCN321
end PackedLegacy_GS

/-! Packed from ProximityPrize.SubmissionLower.A7. -/
section PackedLegacy_A7
namespace ProximityPrize.SubmissionLower.RCN062
open RCN126
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
def baseCoefficientField (P:Polynomial L) (γ:L):IntermediateField k L:=
 IntermediateField.adjoin k
   (insert γ (Set.range (fun j:ℕ => P.coeff j)))
theorem baseCoefficientField_map_le (P:Polynomial L) (γ:L):
   (baseCoefficientField (k:=k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤
     coefficientField (k:=k) P γ:=by
 rw [IntermediateField.map_le_iff_le_comap]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with h | hx
 · rw [h]
   change algebraMap L (RatFunc L) γ∈coefficientField (k:=k) P γ
   exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 obtain ⟨j,hj⟩:=hx
 rw [←hj]
 change algebraMap L (RatFunc L) (P.coeff j)∈coefficientField (k:=k) P γ
 exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
theorem baseCoefficientField_trdeg_le_one
   (P:Polynomial L) (γ:L)
   (hE:Algebra.trdeg k (coefficientField (k:=k) P γ) ≤ 2):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 apply RCN321.coefficient_trdeg_le_one_of_rational_extension
   (B:=baseCoefficientField (k:=k) P γ)
   (E:=coefficientField (k:=k) P γ)
   (baseCoefficientField_map_le P γ) _ hE
 exact IntermediateField.subset_adjoin k _ (Or.inl rfl)
end
end ProximityPrize.SubmissionLower.RCN062
end PackedLegacy_A7

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EH. -/
section PackedLegacy_EH
namespace ProximityPrize.SubmissionLower.RCN129
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
 [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
theorem trdeg_le_one_of_functionField:Algebra.trdeg K L ≤ 1:=by
 classical
 unfold Algebra.trdeg
 refine ciSup_le' fun s↦Cardinal.mk_le_one_iff_set_subsingleton.mpr ?_
 intro x hx y hy
 by_contra hxy
 let i:s.1:=⟨x,hx⟩
 let j:s.1:=⟨y,hy⟩
 have ht:Transcendental K x:=s.2.transcendental i
 letI:FiniteDimensional (IntermediateField.adjoin K ({x}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental ht
 have hyalg:IsAlgebraic (Algebra.adjoin K ({x}:Set L)) y:=
   IntermediateField.isAlgebraic_adjoin_iff.mp
     (Algebra.IsAlgebraic.isAlgebraic y)
 have hji:j∉({i}:Set s.1):=by
   simpa only [Set.mem_singleton_iff] using
     (show j≠i from fun h↦hxy (congrArg Subtype.val h).symm)
 have hytr:=s.2.transcendental_adjoin hji
 have himage:(fun z:s.1↦(z:L)) '' ({i}:Set s.1)={x}:=by
   simp [i]
 change Transcendental (Algebra.adjoin K
   ((fun z:s.1↦(z:L)) '' ({i}:Set s.1))) y at hytr
 rw [himage] at hytr
 exact hytr hyalg
end
end ProximityPrize.SubmissionLower.RCN129
end PackedLegacy_EH

/-! Packed from ProximityPrize.SubmissionLower.GT. -/
section PackedLegacy_GT
namespace ProximityPrize.SubmissionLower.RCN322
open RCN371 RCN011 RCN009
 RCN013
 RCN022 RCN021
 RCN024
 RCN129
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L]
set_option maxHeartbeats 1000000
theorem trdeg_le_one_of_generated_relations
   (v:Fin 3 → L)
   (hgen:IntermediateField.adjoin K (Set.range v)=⊤)
   (F T:MvPolynomial (Fin 3) K)
   (hF:Irreducible F) (hproper:¬ F∣T)
   (hFzero:MvPolynomial.aeval v F=0)
   (hTzero:MvPolynomial.aeval v T=0):Algebra.trdeg K L ≤ 1:=by
 classical
 by_cases halg:∀ i,IsAlgebraic K (v i)
 · have hA:=IntermediateField.isAlgebraic_adjoin
     (K:=K) (L:=L) (S:=Set.range v) (by
       rintro x ⟨i,rfl⟩
       exact isAlgebraic_iff_isIntegral.mp (halg i))
   rw [hgen] at hA
   letI:=hA
   letI:Algebra.IsAlgebraic K L:=(IntermediateField.topEquiv).isAlgebraic
   exact (trdeg_eq_zero (R:=K) (A:=L)).trans_le zero_le
 push Not at halg
 obtain ⟨i,hi⟩:=halg
 let e:Original K →ₐ[K] L:=MvPolynomial.aeval v
 let initial:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hi0:initial 0=i:=Equiv.swap_apply_left _ _
 have ht0:Transcendental K (e (MvPolynomial.X (initial 0))):=by
   simpa [e,hi0] using (show Transcendental K (v i) from hi)
 have hex:∃ order:Fin 3 ≃ Fin 3,
     Transcendental K (e (MvPolynomial.X (order 0)))∧
     0 < (planeMap K order F).natDegree:=by
   have hirr:=rationalMap_irreducible_of_evaluation K L initial e F hF hFzero ht0
   rcases positive_degree_of_irreducible (rationalMap K initial F) hirr with h0 | h1
   · refine ⟨initial,ht0,?_⟩
     change 0 < (bivariateEquiv (RatFunc K) (rationalMap K initial F)).natDegree
     rwa [bivariateEquiv_natDegree]
   · exact ⟨swapOtherOrder initial,by simpa only [swapOtherOrder_zero] using ht0,
       by rwa [swapped_outer_degree]⟩
 obtain ⟨order,ht,hpositive⟩:=hex
 let base:=elementEmbedding K L (e (MvPolynomial.X (order 0))) ht
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hpair:IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤:=by
   let S:=IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)
   have hcoords:Set.range v ⊆ S.restrictScalars K:=by
     rintro x ⟨l,rfl⟩
     obtain ⟨j,rfl⟩:=order.surjective l
     have hj:j=0∨j=1∨j=2:=by omega
     rcases hj with rfl | rfl | rfl
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
       change elementEmbedding K L _ ht _∈S at hm
       rw [elementEmbedding_variable] at hm
       simpa [e] using hm
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_right (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_left (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   have htop:S.restrictScalars K=⊤:=by
     apply top_unique
     rw [←hgen]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
 have hroot (G:Original K) (hG:e G=0):
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (RatFunc K) L)
       (e (MvPolynomial.X (order 2))))
       (e (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
   rw [←RCN365.planeEval_eq_eval₂]
   change planeEvaluation K L order e ht (planeMap K order G)=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   exact hG
 have hirr:=planeMap_irreducible_of_evaluation K L order e F hF hFzero ht
 have hproperPlane:¬ planeMap K order F∣planeMap K order T:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_evaluation K L order e F T hF hFzero ht).mp h)
 letI:FiniteDimensional (RatFunc K) L:=finite_of_proper_plane_roots
   (planeMap K order F) (planeMap K order T) hirr hpositive hproperPlane
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   (hroot F hFzero) (hroot T hTzero) hpair
 exact trdeg_le_one_of_functionField K L
end
end ProximityPrize.SubmissionLower.RCN322
end PackedLegacy_GT

/-! Packed from ProximityPrize.SubmissionLower.EG. -/
section PackedLegacy_EG
namespace ProximityPrize.SubmissionLower.RCN127
open RCN077 RCN319 RCN136
 RCN132 RCN126
 RCN062
 RCN322 RCN129
 RCN022
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
private def freshJet (P:Polynomial L) (γ:L) (i:Fin 4):
   jetField (k:=k) P γ:=
 ⟨freshPoint P γ i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
@[simp] private theorem freshJet_val (P:Polynomial L) (γ:L) (i:Fin 4):
   ((freshJet (k:=k) P γ i:jetField (k:=k) P γ):RatFunc L)=
     freshPoint P γ i:=rfl
private def freshOtherJet (P:Polynomial L) (γ:L) (i:Fin 3):
   jetField (k:=k) P γ:=freshJet (k:=k) P γ i.succ
private theorem freshTau_transcendental (P:Polynomial L) (γ:L):
   Transcendental k (freshJet (k:=k) P γ 0):=by
 intro h
 have h':IsAlgebraic k (RatFunc.X:RatFunc L):=by
   exact IntermediateField.isAlgebraic_iff.mp h
 exact (RatFunc.transcendental_X.restrictScalars
   (algebraMap k L).injective) h'
set_option maxHeartbeats 1000000 in
theorem baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
   (F T:Poly4 k) (P:Polynomial L) (γ:L)
   (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (hproper:¬ F∣T)
   (hFsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) F)=0)
   (hTsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) T)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4)
       (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 classical
 let E:=jetField (k:=k) P γ
 let full:Fin 4 → E:=freshJet (k:=k) P γ
 let v:Fin 3 → E:=freshOtherJet (k:=k) P γ
 let τ:E:=freshJet (k:=k) P γ 0
 have hτ:Transcendental k τ:=freshTau_transcendental P γ
 let rawEquiv:=FractionRing.algEquiv (Polynomial k) (RatFunc k)
 let coeffEquiv:RationalCoefficients k ≃ₐ[k] RatFunc k:=rawEquiv.restrictScalars k
 let baseRat:RatFunc k →ₐ[k] E:=elementEmbedding k E τ hτ
 let base:RationalCoefficients k →ₐ[k] E:=baseRat.comp coeffEquiv.toAlgHom
 letI:Algebra (RationalCoefficients k) E:=base.toRingHom.toAlgebra
 letI:IsScalarTower k (RationalCoefficients k) E:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hbaseX:base
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=τ:=by
   change baseRat (rawEquiv
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X))=τ
   rw [rawEquiv.commutes,elementEmbedding_variable]
 have hfull:IntermediateField.adjoin k (Set.range full)=⊤:=by
   apply IntermediateField.map_injective E.val
   rw [IntermediateField.adjoin_map, ←AlgHom.fieldRange_eq_map,
     IntermediateField.fieldRange_val]
   have himage:E.val '' Set.range full=Set.range (freshPoint P γ):=by
     ext x
     simp [full,freshJet]
   rw [himage]
   rfl
 have hgen:IntermediateField.adjoin (RationalCoefficients k) (Set.range v)=⊤:=by
   let S:=IntermediateField.adjoin (RationalCoefficients k) (Set.range v)
   have hcoords:Set.range full ⊆ S.restrictScalars k:=by
     rintro x ⟨i,rfl⟩
     refine Fin.cases ?_ (fun j↦?_) i
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)∈S at hm
       rw [hbaseX] at hm
       exact hm
     · exact IntermediateField.subset_adjoin (RationalCoefficients k) _ ⟨j,rfl⟩
   have htop:S.restrictScalars k=⊤:=by
     apply top_unique
     rw [←hfull]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp htop
 have hsurface:∀ G:Poly4 k,
     MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
         (rationalSurfaceMap k G)=
       MvPolynomial.eval₂Hom (algebraMap k E) full G:=by
   intro G
   have heq:(MvPolynomial.eval₂Hom
         (algebraMap (RationalCoefficients k) E) v).comp (rationalSurfaceMap k)=
       MvPolynomial.eval₂Hom (algebraMap k E) full:=by
     apply MvPolynomial.ringHom_ext
     · intro a
       simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_C,
         MvPolynomial.eval₂Hom_C]
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) (Polynomial.C a))=
           algebraMap k E a
       calc
         _=base (algebraMap k (RationalCoefficients k) a):=by
           congr 1
         _=algebraMap k E a:=base.commutes a
     · intro i
       refine Fin.cases ?_ (fun j↦?_) i
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_zero,
           MvPolynomial.eval₂Hom_C,
           MvPolynomial.eval₂Hom_X']
         change base
           (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=full 0
         exact hbaseX
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_succ,
           MvPolynomial.eval₂Hom_X']
         rfl
   exact RingHom.congr_fun heq G
 have hcoeffcomp:E.val.toRingHom.comp
       (MvPolynomial.eval₂Hom (algebraMap k E) full)=
     (MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)).comp
       (MvPolynomial.map (algebraMap k L)):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_C,
       MvPolynomial.map_C]
     change algebraMap k (RatFunc L) a=
       algebraMap L (RatFunc L) (algebraMap k L a)
     exact IsScalarTower.algebraMap_apply k L (RatFunc L) a
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_X',
       MvPolynomial.map_X]
     change E.val (full i)=freshPoint P γ i
     rfl
 have hfullroot (G:Poly4 k)
     (hG:specialization L P γ (MvPolynomial.map (algebraMap k L) G)=0):
     MvPolynomial.eval₂Hom (algebraMap k E) full G=0:=by
   apply E.val.injective
   change (E.val.toRingHom.comp
     (MvPolynomial.eval₂Hom (algebraMap k E) full)) G=E.val 0
   rw [hcoeffcomp,RingHom.comp_apply,fresh_eval_eq,hG,map_zero,map_zero]
 have hFroot:MvPolynomial.aeval v (rationalSurfaceMap k F)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k F)=0
   rw [hsurface]
   exact hfullroot F hFsolution
 have hTroot:MvPolynomial.aeval v (rationalSurfaceMap k T)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k T)=0
   rw [hsurface]
   exact hfullroot T hTsolution
 have hirr:Irreducible (rationalSurfaceMap k F):=
   rationalSurfaceMap_irreducible k F hF hpos
 have hproperRat:¬ rationalSurfaceMap k F∣rationalSurfaceMap k T:=by
   intro h
   exact hproper ((rationalSurfaceMap_dvd_iff k F T hF hpos).mp h)
 have hrelative:Algebra.trdeg (RationalCoefficients k) E ≤ 1:=
   trdeg_le_one_of_generated_relations (RationalCoefficients k) E v hgen
     (rationalSurfaceMap k F) (rationalSurfaceMap k T)
     hirr hproperRat hFroot hTroot
 have hbaseRat:Algebra.trdeg k (RatFunc k) ≤ 1:=
   trdeg_le_one_of_functionField k (RatFunc k)
 have hbase:Algebra.trdeg k (RationalCoefficients k) ≤ 1:=by
   rw [coeffEquiv.trdeg_eq]
   exact hbaseRat
 have hsum:Algebra.trdeg k (RationalCoefficients k)+
     Algebra.trdeg (RationalCoefficients k) E=Algebra.trdeg k E:=
   trdeg_add_eq k (RationalCoefficients k)
 have hjet:Algebra.trdeg k E ≤ 2:=by
   rw [←hsum]
   exact (add_le_add hbase hrelative).trans_eq (by norm_num)
 have hfield:=fresh_jetField_eq_coefficientField F P γ hFsolution hreg p w hw hP
 change Algebra.trdeg k (jetField (k:=k) P γ) ≤ 2 at hjet
 rw [hfield] at hjet
 exact baseCoefficientField_trdeg_le_one P γ hjet
end
end ProximityPrize.SubmissionLower.RCN127
end PackedLegacy_EG

/-! Packed from ProximityPrize.SubmissionLower.H9. -/
section PackedLegacy_H9
namespace ProximityPrize.SubmissionLower.RCN059
open scoped BigOperators
noncomputable section
variable {k F L Γ:Type*} [Field k] [Field F] [Field L]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq F:=Classical.decEq F
end
end ProximityPrize.SubmissionLower.RCN059
end PackedLegacy_H9
end Compact_PackedLegacy

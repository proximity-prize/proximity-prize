import ProximityPrize.SubmissionLower.ContactLocalHypersurfaceBridge6731Research
import ProximityPrize.SubmissionLower.ContactLocalizationDerivation6731Research
import ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra6676Research
import ProximityPrize.SubmissionLower.ContactTwoTailDVRExact6731Research
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactPolynomialRegularLocalCompat6732Research
namespace ProximityPrize.SubmissionLower.ContactOriginalFactorLocalDVR6731Research
open ContactTaylorNumerators ContactDifferentialRing
open ContactGenericSurface
open ContactBaseIdealAlgebra6676Research
open ContactLocalizationDerivation6731Research
open ContactRegularQuotient6731Research
open ContactLocalHypersurfaceBridge6731Research
open ContactPolynomialRegularLocalCompat6732Research
open IsLocalRing
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
  exact ContactTwoTailDVRExact6731Research.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim
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
  have hq:=ContactDifferentialRing.quotientDerivation_mk
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
end ProximityPrize.SubmissionLower.ContactOriginalFactorLocalDVR6731Research

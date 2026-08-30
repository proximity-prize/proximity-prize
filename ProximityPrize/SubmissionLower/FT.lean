import ProximityPrize.SubmissionLower.I6
import ProximityPrize.SubmissionLower.FF
import ProximityPrize.SubmissionLower.FG
import ProximityPrize.SubmissionLower.AL
namespace ProximityPrize.SubmissionLower.ContactProperDelayedTailCertificate6732Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactTwoTailProviderAssembly6732Research
open ContactTangentCoefficientProvider6732Research
open ContactOriginalFactorLocalDVR6732Research
open ContactOriginalFactorLocalDVR6731Research
open ContactDVRRecurrenceDichotomy6732Research
open ContactFirstTailCertificate6731Research ContactTwoTailRecurrence6731Research
open ContactTwoTailProperBranch6731Research
open ContactPrimeFlagBudgetFamilyResearch ContactFlagBezout6543Research
open ContactMovingAgreementCertificate6719Research
open ContactSharpTaylorFixedMeet6656Research
open ContactTaylorNumerators
open ContactNumeratorFactorScaling6731Research
open ContactProperCutSeedCount ContactCurveComponents
open ContactPrimeSeedIncidence
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
abbrev fixedSupport:=support 1225 43 10
abbrev Stage (K I:Type) [Field K]
   (Gamma:Finset K) (x:I → K) (p:ℕ) [CharP (GenericField K) p]
   (flag:FlagDegree):=
 ResidualStage (polynomialEmbedding K) Gamma x p
   ContactTwoTailParameters6734Research.errors flag
   ContactTwoTailParameters6733Research.w fixedSupport
structure OriginalData
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S) where
 factor:MvPolynomial (Fin 4) K
 cofactor:MvPolynomial (Fin 4) K
 irreducible:Irreducible factor
 positive:0 < factor.degreeOf 1+factor.degreeOf 2+factor.degreeOf 3
 product:S.F=factor*cofactor
 factor_dvd:S.G∣surfaceMap (polynomialEmbedding K) factor
 factor_mem:surfaceMap (polynomialEmbedding K) factor∈C.1
 cofactor_not_mem:surfaceMap (polynomialEmbedding K) cofactor∉C.1
 regularity_not_mem:
   surfaceMap (polynomialEmbedding K) (polyH K factor)∉C.1
noncomputable def originalData
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   OriginalData S C:=by
 let h:=exists_original_factor_of_firstTailComponent S C
 let factor:=h.choose
 let cofactor:=h.choose_spec.choose
 have hs:=h.choose_spec.choose_spec
 exact ⟨factor,cofactor,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
   hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩
abbrev componentPrime
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):=
 contractedPrime (polynomialEmbedding K) C.1
theorem factorLe
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   factorIdeal (originalData S C).factor ≤ componentPrime S C:=
 factorIdeal_le_contractedPrime (polynomialEmbedding K) C.1
   (originalData S C).factor (originalData S C).factor_mem
abbrev LocalRing
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):=
 FactorLocal (originalData S C).factor (componentPrime S C) (factorLe S C)
local instance factorIdealPrime
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   (factorIdeal (originalData S C).factor).IsPrime:=
 factorIdeal_isPrime _ (originalData S C).irreducible
local instance quotientPrimeInstance
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   (ContactLocalHypersurfaceBridge6731Research.quotientPrime
     (factorIdeal (originalData S C).factor) (componentPrime S C)).IsPrime:=
 ContactLocalHypersurfaceBridge6731Research.quotientPrime_isPrime _ _ (factorLe S C)
noncomputable def localImage
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):LocalRing S C:=
 factorLocalImage (originalData S C).factor (componentPrime S C)
   (factorLe S C) A
noncomputable def localDerivation
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   Derivation K (LocalRing S C) (LocalRing S C):=
 factorLocalDerivation (originalData S C).factor (componentPrime S C)
   (factorLe S C)
theorem original_firstNumerator_mem_component
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K)
     (numerator K (originalData S C).factor
       (ContactTwoTailParameters6733Research.w+1))∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 let b:=ContactTwoTailParameters6733Research.w+1
 have hwhole:surfaceMap phi (numerator K S.F b)∈C.1:=by
   apply (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
     S.F b C.1).mp
   exact regularComponent_T_mem (GenericField K) S.G
     (globalTailCut phi S.F b) (regularitySurface phi S.F) C
 have hdiff:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hdiffMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   exact C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hdiff))
     d.factor_mem
 have hproduct:surfaceMap phi
     (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   have:=C.1.sub_mem hwhole hdiffMap
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
 have hproduct':surfaceMap phi (d.cofactor^(2*b))*
     surfaceMap phi (numerator K d.factor b)∈C.1:=by
   simpa only [map_mul] using hproduct
 have hsplit:surfaceMap phi (d.cofactor^(2*b))∈C.1∨
     surfaceMap phi (numerator K d.factor b)∈C.1:=
   (inferInstance:C.1.IsPrime).mem_or_mem hproduct'
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rcases hsplit with hleft | hright
 · exact False.elim (hcofactorPow (by simpa only [map_pow] using hleft))
 · exact hright
theorem componentPrime_height_eq_two
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1)):
   (componentPrime S C).height=2:=by
 let d:=originalData S C
 let N:=numerator K d.factor (ContactTwoTailParameters6733Research.w+1)
 have hproperN:¬ d.factor∣N:=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hheightC:C.1.height ≤ 2:=
   component_height_le_two (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F
       (ContactTwoTailParameters6733Research.w+1)) C.1
     (regularComponent_mem (GenericField K) S.G _ _ C)
 have horiginal:=originalPrime_height_eq_two C.1 hheightC d.factor N
   d.irreducible d.factor_mem (original_firstNumerator_mem_component S C) hproperN
 have heq:componentPrime S C=originalPrime C.1:=by
   apply Ideal.ext
   intro A
   exact (mem_contractedPrime_iff (polynomialEmbedding K) C.1 A).trans
     (mem_originalPrime_iff C.1 A).symm
 rw [heq]
 exact horiginal
structure LocalDVRFamily (S:Stage K I Gamma x p flag) where
 domain:∀ C:FirstTailComponent S,IsDomain (LocalRing S C)
 dvr:∀ C:FirstTailComponent S,
   @IsDiscreteValuationRing (LocalRing S C) _ (domain C)
theorem canonicalLocalDVRFamily
   (S:Stage K I Gamma x p flag)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1)):
   LocalDVRFamily S where
 domain:=fun C↦inferInstance
 dvr:=fun C↦by
   exact factorLocal_isDiscreteValuationRing
     (originalData S C).factor (componentPrime S C) (factorLe S C)
     (componentPrime_height_eq_two S C hfirstProper)
     (originalData S C).regularity_not_mem
noncomputable def localMultiplicity
   (S:Stage K I Gamma x p flag) (L:LocalDVRFamily S)
   (C:FirstTailComponent S):ℕ:=by
 letI:IsDomain (LocalRing S C):=L.domain C
 letI:IsDiscreteValuationRing (LocalRing S C):=L.dvr C
 exact (IsDiscreteValuationRing.addVal (LocalRing S C)
   (localImage S C (numerator K (originalData S C).factor
     (ContactTwoTailParameters6733Research.w+1)))).toNat
theorem localImage_isUnit_iff_not_mem
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):
   IsUnit (localImage S C A) ↔
     surfaceMap (polynomialEmbedding K) A∉C.1:=by
 constructor
 · intro hunit hmem
   have hnon:¬ IsUnit (localImage S C A):=by
     change ¬ IsUnit
       (factorLocalImage
         (originalData S C).factor (componentPrime S C) (factorLe S C) A)
     have hmax:=
       (IsLocalization.AtPrime.to_map_mem_maximal_iff
         (LocalRing S C)
         (ContactLocalHypersurfaceBridge6731Research.quotientPrime
           (factorIdeal (originalData S C).factor) (componentPrime S C))
         (Ideal.Quotient.mk (factorIdeal (originalData S C).factor) A)).2 (by
           have:A∈
               (ContactLocalHypersurfaceBridge6731Research.quotientPrime
                 (factorIdeal (originalData S C).factor) (componentPrime S C)).comap
                 (Ideal.Quotient.mk (factorIdeal (originalData S C).factor)):=by
             rw [ContactLocalHypersurfaceBridge6731Research.quotientPrime_comap_quotientMk
               (factorIdeal (originalData S C).factor) (componentPrime S C)
               (factorLe S C)]
             exact hmem
           exact this)
     simpa only [factorLocalImage,IsLocalRing.mem_maximalIdeal,
       mem_nonunits_iff] using hmax
   exact hnon hunit
 · intro hnot
   exact factorLocal_image_isUnit_of_not_mem
     (originalData S C).factor A (componentPrime S C) (factorLe S C) hnot
theorem tail_mem_iff_original_numerator_mem
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S) (b:ℕ):
   globalTailCut (polynomialEmbedding K) S.F b∈C.1 ↔
     surfaceMap (polynomialEmbedding K)
       (numerator K (originalData S C).factor b)∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 have hscaled:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hscaledMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=
   C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hscaled))
     d.factor_mem
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rw [globalTailCut_mem_iff phi (polynomialEmbedding_injective K) S.F b C.1]
 constructor
 · intro hwhole
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     have:=C.1.sub_mem hwhole hscaledMap
     simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
   have hproduct':surfaceMap phi (d.cofactor^(2*b))*
       surfaceMap phi (numerator K d.factor b)∈C.1:=by
     simpa only [map_mul] using hproduct
   exact ((inferInstance:C.1.IsPrime).mem_or_mem hproduct').resolve_left
     hcofactorPow
 · intro horiginal
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     rw [map_mul]
     exact C.1.mul_mem_left _ horiginal
   have:=C.1.add_mem hscaledMap hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using this
private theorem chosenLocalImage_ne_zero_of_not_dvd
   (S:Stage K I Gamma x p flag) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K)
   (hA:¬ (originalData S C).factor∣A):
   localImage S C A≠0:=by
 intro hzero
 have hquot:Ideal.Quotient.mk (factorIdeal (originalData S C).factor) A=0:=by
   apply (IsLocalization.injective (LocalRing S C)
     (ContactLocalHypersurfaceBridge6731Research.quotientPrime
       (factorIdeal (originalData S C).factor)
       (componentPrime S C)).primeCompl_le_nonZeroDivisors)
   simpa only [localImage,factorLocalImage,map_zero] using hzero
 exact hA (Ideal.mem_span_singleton.mp
   (Ideal.Quotient.eq_zero_iff_mem.mp hquot))
theorem local_order_tail_dichotomy
   (S:Stage K I Gamma x p flag) (L:LocalDVRFamily S)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1)):
   1 ≤ localMultiplicity S L C∧
     ((∃ delay,1 ≤ delay∧delay ≤ localMultiplicity S L C∧
       globalTailCut (polynomialEmbedding K) S.F
         (ContactTwoTailParameters6733Research.w+1+delay)∉C.1)∨
     (∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (ContactTwoTailParameters6733Research.w+1+delay)∈C.1)):=by
 let d:=originalData S C
 let p0:=componentPrime S C
 let hFp:=factorLe S C
 let R:=LocalRing S C
 let D:=localDerivation S C
 let H:R:=localImage S C (polyH K d.factor)
 let N:ℕ → R:=fun j↦localImage S C
   (numerator K d.factor (ContactTwoTailParameters6733Research.w+1+j))
 let coeff:ℕ → R:=fun j↦
   (2*(ContactTwoTailParameters6733Research.w+1+j):R)
 letI:IsDomain R:=L.domain C
 letI:IsDiscreteValuationRing R:=L.dvr C
 letI:CharP K p:=
   (coefficientEmbedding K).charP (coefficientEmbedding_injective K) p
 letI:CharP R p:=charP_of_injective_algebraMap
   (algebraMap K R).injective p
 have hpne:p≠0:=by
   have:=S.characteristic_bound
   dsimp only [ContactTwoTailParameters6733Research.w] at this
   omega
 have hp:p.Prime:=CharP.char_prime_of_ne_zero (GenericField K) hpne
 have hproperN:¬ d.factor∣
     numerator K d.factor (ContactTwoTailParameters6733Research.w+1):=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hN0ne:N 0≠0:=by
   exact chosenLocalImage_ne_zero_of_not_dvd S C _ hproperN
 have hN0nonunit:¬ IsUnit (N 0):=by
   have hmem:=original_firstNumerator_mem_component S C
   exact (localImage_isUnit_iff_not_mem S C _).not.mpr (not_not.mpr hmem)
 have hHunit:IsUnit H:=
   (localImage_isUnit_iff_not_mem S C _).2 d.regularity_not_mem
 have hrec:∀ j,N (j+1)=
     H*D (N j)-coeff j*N j*D H:=by
   intro j
   dsimp only [N,H,D,coeff,d,localImage,localDerivation]
   convert
     (factorLocal_numerator_succ
       (originalData S C).factor (componentPrime S C) (factorLe S C)
       (ContactTwoTailParameters6733Research.w+1+j)) using 1 <;>
     push_cast <;> ring
 have hd:=recurrence_unit_or_persistent D H (D H) coeff N p hp
   hrec hHunit hN0ne hN0nonunit
 change 1 ≤ localMultiplicity S L C∧_
 change 1 ≤ (IsDiscreteValuationRing.addVal R (N 0)).toNat∧_ at hd
 refine ⟨hd.1,?_⟩
 rcases hd.2 with hproper | hpersistent
 · left
   obtain ⟨delay,hdelay1,hdelayMu,hunit⟩:=hproper
   refine ⟨delay,hdelay1,hdelayMu,?_⟩
   apply (tail_mem_iff_original_numerator_mem S C _).not.mpr
   exact (localImage_isUnit_iff_not_mem S C _).1 hunit
 · right
   intro delay
   by_contra hnot
   apply hpersistent delay
   apply (localImage_isUnit_iff_not_mem S C _).2
   exact (tail_mem_iff_original_numerator_mem S C _).not.mp hnot
theorem one_le_localMultiplicity
   (S:Stage K I Gamma x p flag)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1)):
   ∀ C,1 ≤ localMultiplicity S
     (canonicalLocalDVRFamily S hfirstProper) C:=by
 intro C
 exact (local_order_tail_dichotomy S
   (canonicalLocalDVRFamily S hfirstProper) C hfirstProper).1
end
end ProximityPrize.SubmissionLower.ContactProperDelayedTailCertificate6732Research

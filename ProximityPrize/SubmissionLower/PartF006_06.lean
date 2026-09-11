import ProximityPrize.SubmissionLower.PartF006_05
section Compact_PackedLegacy
section PackedLegacy_AL
namespace ProximityPrize.SubmissionLower.RCN327
open ProximityPrize.Benchmark RCN095 RCN275 RCN198 RCN206 RCN263
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6734
def errors:ℕ:=80102
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def radiusNumerator:ℕ:=10253183
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity:ℕ
 totalCap:ℕ
 slopeCap:ℕ
 middleCap:ℕ
 deriving DecidableEq
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity * agreements
end Profile
def profileA:Profile:=⟨42,84439,12,58⟩
def profileB:Profile:=⟨81,1262,25,112⟩
def profileC:Profile:=⟨41,41787,12,56⟩
def profileH:Profile:=⟨42,1261,12,55⟩
def supportYS:ResidualSupportParameters :=
 RCN198.support 1207 41 10
def supportS:ResidualSupportParameters :=
 RCN198.support 1206 43 9
def fixedFlagYS:FlagDegree:=surfaceFlag 1207 41 10
def fixedFlagS:FlagDegree:=surfaceFlag 1206 43 9
def firstTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 1)
def secondTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 2)
def firstTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 1)
def secondTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 2)
def fixedRegularCostYS:ℕ:=flagMixed fixedFlagYS firstTailYS secondTailYS
def fixedSingularCostYS:ℕ:=76778677599070
def firstResidualRegularCostYS:ℕ:=9644144290222
def firstResidualSingularCostYS:ℕ:=235470664
def secondResidualRegularCostYS:ℕ:=0
def secondResidualSingularCostYS:ℕ:=4646124
def fixedRegularCostS:ℕ:=flagMixed fixedFlagS firstTailS secondTailS
def fixedSingularCostS:ℕ:=63997115995699
def firstResidualRegularCostS:ℕ:=15868064433192
def firstResidualSingularCostS:ℕ:=235470664
def secondResidualRegularCostS:ℕ:=2376733763872
def secondResidualSingularCostS:ℕ:=4646124
def fixedCostYS:ℕ:=fixedRegularCostYS + fixedSingularCostYS
def firstResidualCeilingYS:ℕ :=
 firstResidualRegularCostYS + firstResidualSingularCostYS
def secondResidualCeilingYS:ℕ :=
 secondResidualRegularCostYS + secondResidualSingularCostYS
def totalCostYS:ℕ :=
 fixedCostYS + firstResidualCeilingYS + secondResidualCeilingYS
def fixedCostS:ℕ:=fixedRegularCostS + fixedSingularCostS
def firstResidualCeilingS:ℕ :=
 firstResidualRegularCostS + firstResidualSingularCostS
def secondResidualCeilingS:ℕ :=
 secondResidualRegularCostS + secondResidualSingularCostS
def totalCostS:ℕ :=
 fixedCostS + firstResidualCeilingS + secondResidualCeilingS
def capacity:ℕ:=prime ^ 6 / 2 ^ 128
def listBudget:ℕ:=1000000000
def mcaBudget:ℕ:=capacity - listBudget
theorem fixed_flag_values :
   fixedFlagYS = ⟨1207,42,12⟩ ∧
     fixedFlagS = ⟨1206,44,11⟩:=by
 decide
theorem radius_floor :
   ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ = errors:=by
 norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   errors, IRSProfile.Index]
theorem radius_admissible :
   radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
 constructor <;>
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
     IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ) ^ 17 * 598 ^ 50 ≤ 757 ^ 50:=by
 decide
theorem score_radius_integer :
   (23301249:ℕ) ^ 128 * (2 ^ 67 * 757) ≤ 598 * 33554432 ^ 128:=by
 decide
theorem two_rpow_score_fraction_le :
   (2:ℝ≥0) ^ ((17:ℝ) / 50) ≤ (757:ℝ≥0) / 598:=by
 have hroot:((2:ℝ≥0) ^ (17:ℕ)) ^ ((50:ℝ)⁻¹) ≤
     (757:ℝ≥0) / 598:=by
   rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 50)]
   rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
   exact_mod_cast score_root_integer
 calc
   (2:ℝ≥0) ^ ((17:ℝ) / 50) =
       ((2:ℝ≥0) ^ (17:ℕ)) ^ ((50:ℝ)⁻¹):=by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (757:ℝ≥0) / 598:=hroot
theorem radius_power_rational_bound :
   (1 - radius) ^ IRSProfile.repetitions ≤
     ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757):=by
 have hsub:(1 - radius:ℝ≥0) = 23301249 / 33554432:=by
   have hr:radius ≤ 1:=by
     rw [← NNReal.coe_le_coe]
     norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
 change (1 - radius) ^ 128 ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757)
 rw [hsub, div_pow, div_mul_div_comm, one_mul,
   div_le_div_iff₀ (by positivity) (by positivity)]
 exact_mod_cast score_radius_integer
theorem score_target_le :
   (1 - radius) ^ IRSProfile.repetitions ≤ claimedError score:=by
 have hscale:(598:ℝ≥0) / 757 ≤
     (2:ℝ≥0) ^ (-((17:ℝ) / 50)):=by
   calc
     (598:ℝ≥0) / 757 = 1 / ((757:ℝ≥0) / 598):=by norm_num
     _ ≤ 1 / ((2:ℝ≥0) ^ ((17:ℝ) / 50)) :=
       one_div_le_one_div_of_le (by positivity) two_rpow_score_fraction_le
     _ = (2:ℝ≥0) ^ (-((17:ℝ) / 50)):=by
       rw [one_div, NNReal.rpow_neg]
 calc
   (1 - radius) ^ IRSProfile.repetitions ≤
       ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757) :=
     radius_power_rational_bound
   _ ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) *
       (2:ℝ≥0) ^ (-((17:ℝ) / 50)) :=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _ = claimedError score:=by
     unfold claimedError score
     rw [show -((((6734:ℕ):ℝ) / 100)) =
         -((67:ℕ):ℝ) + -((17:ℝ) / 50) by norm_num,
       NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
     simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.RCN327
end PackedLegacy_AL

/-! Packed from ProximityPrize.SubmissionLower.FT. -/
section PackedLegacy_FT
namespace ProximityPrize.SubmissionLower.RCN244
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN329 RCN312 RCN219 RCN218 RCN073 RCN086 RCN330 RCN328 RCN237 RCN095 RCN198 RCN287 RCN313 RCN217 RCN243 RCN072 RCN238
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
abbrev fixedSupport:=support 1206 42 10
abbrev Stage (K I:Type) [Field K]
   (Gamma:Finset K) (x:I → K) (p:ℕ) [CharP (GenericField K) p]
   (flag:FlagDegree)
   (errorCap:ℕ:=RCN327.errors)
   (stageSupport:RCN275.ResidualSupportParameters:=fixedSupport):=
 ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag
   RCN326.w stageSupport
variable {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
structure OriginalData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) where
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
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   OriginalData S C:=by
 let h:=exists_original_factor_of_firstTailComponent S C
 let factor:=h.choose
 let cofactor:=h.choose_spec.choose
 have hs:=h.choose_spec.choose_spec
 exact ⟨factor,cofactor,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
   hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩
abbrev componentPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 contractedPrime (polynomialEmbedding K) C.1
theorem factorLe
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   RCN218.factorIdeal (originalData S C).factor ≤ componentPrime S C:=
 RCN218.factorIdeal_le_contractedPrime (polynomialEmbedding K) C.1
   (originalData S C).factor (originalData S C).factor_mem
abbrev LocalRing
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 FactorLocal (originalData S C).factor (componentPrime S C) (factorLe S C)
local instance factorIdealPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN218.factorIdeal (originalData S C).factor).IsPrime:=
 RCN218.factorIdeal_isPrime _ (originalData S C).irreducible
local instance quotientPrimeInstance
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN186.quotientPrime
     (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).IsPrime:=
 RCN186.quotientPrime_isPrime _ _ (factorLe S C)
noncomputable def localImage
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):LocalRing S C:=
 factorLocalImage (originalData S C).factor (componentPrime S C)
   (factorLe S C) A
noncomputable def localDerivation
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   Derivation K (LocalRing S C) (LocalRing S C):=
 factorLocalDerivation (originalData S C).factor (componentPrime S C)
   (factorLe S C)
theorem original_firstNumerator_mem_component
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K)
     (numerator K (originalData S C).factor
       (RCN326.w+1))∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 let b:=RCN326.w+1
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
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   (componentPrime S C).height=2:=by
 let d:=originalData S C
 let N:=numerator K d.factor (RCN326.w+1)
 have hproperN:¬ d.factor∣N:=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hheightC:C.1.height ≤ 2:=
   component_height_le_two (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1)) C.1
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
structure LocalDVRFamily (S:Stage K I Gamma x p flag errorCap stageSupport) where
 domain:∀ C:FirstTailComponent S,IsDomain (LocalRing S C)
 dvr:∀ C:FirstTailComponent S,
   @IsDiscreteValuationRing (LocalRing S C) _ (domain C)
theorem canonicalLocalDVRFamily
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   LocalDVRFamily S where
 domain:=fun C↦inferInstance
 dvr:=fun C↦by
   exact factorLocal_isDiscreteValuationRing
     (originalData S C).factor (componentPrime S C) (factorLe S C)
     (componentPrime_height_eq_two S C hfirstProper)
     (originalData S C).regularity_not_mem
noncomputable def localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S):ℕ:=by
 letI:IsDomain (LocalRing S C):=L.domain C
 letI:IsDiscreteValuationRing (LocalRing S C):=L.dvr C
 exact (IsDiscreteValuationRing.addVal (LocalRing S C)
   (localImage S C (numerator K (originalData S C).factor
     (RCN326.w+1)))).toNat
theorem localImage_isUnit_iff_not_mem
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
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
         (RCN186.quotientPrime
           (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C))
         (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A)).2 (by
           have:A∈
               (RCN186.quotientPrime
                 (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).comap
                 (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor)):=by
             rw [RCN186.quotientPrime_comap_quotientMk
               (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)
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
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) (b:ℕ):
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
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K)
   (hA:¬ (originalData S C).factor∣A):
   localImage S C A≠0:=by
 intro hzero
 have hquot:Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A=0:=by
   apply (IsLocalization.injective (LocalRing S C)
     (RCN186.quotientPrime
       (RCN218.factorIdeal (originalData S C).factor)
       (componentPrime S C)).primeCompl_le_nonZeroDivisors)
   simpa only [localImage,factorLocalImage,map_zero] using hzero
 exact hA (Ideal.mem_span_singleton.mp
   (Ideal.Quotient.eq_zero_iff_mem.mp hquot))
theorem local_order_tail_dichotomy
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   1 ≤ localMultiplicity S L C∧
     ((∃ delay,1 ≤ delay∧delay ≤ localMultiplicity S L C∧
       globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1+delay)∉C.1)∨
     (∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1)):=by
 let d:=originalData S C
 let p0:=componentPrime S C
 let hFp:=factorLe S C
 let R:=LocalRing S C
 let D:=localDerivation S C
 let H:R:=localImage S C (polyH K d.factor)
 let N:ℕ → R:=fun j↦localImage S C
   (numerator K d.factor (RCN326.w+1+j))
 let coeff:ℕ → R:=fun j↦
   (2*(RCN326.w+1+j):R)
 letI:IsDomain R:=L.domain C
 letI:IsDiscreteValuationRing R:=L.dvr C
 letI:CharP K p:=
   (coefficientEmbedding K).charP (coefficientEmbedding_injective K) p
 letI:CharP R p:=charP_of_injective_algebraMap
   (algebraMap K R).injective p
 have hpne:p≠0:=by
   have:=S.characteristic_bound
   dsimp only [RCN326.w] at this
   omega
 have hp:p.Prime:=CharP.char_prime_of_ne_zero (GenericField K) hpne
 have hproperN:¬ d.factor∣
     numerator K d.factor (RCN326.w+1):=
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
       (RCN326.w+1+j)) using 1 <;>
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
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   ∀ C,1 ≤ localMultiplicity S
     (canonicalLocalDVRFamily S hfirstProper) C:=by
 intro C
 exact (local_order_tail_dichotomy S
   (canonicalLocalDVRFamily S hfirstProper) C hfirstProper).1
end
end ProximityPrize.SubmissionLower.RCN244
end PackedLegacy_FT

/-! Packed from ProximityPrize.SubmissionLower.GL. -/
section PackedLegacy_GL
namespace ProximityPrize.SubmissionLower.RCN310
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A:Type*} [CommRing A]
theorem exists_multiplier_mem_sup_pow_of_localized_mem
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n):
   ∃ s:A,s∉p∧s*x∈I ⊔ p^n:=by
 let S:=A ⧸ I
 let L:=Localization.AtPrime pbar
 let q:A →+*S:=Ideal.Quotient.mk I
 have hxMap:algebraMap S L (q x)∈
     Ideal.map (algebraMap S L) (pbar^n):=by
   rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal pbar L]
   exact hx
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
   pbar.primeCompl L] at hxMap
 obtain ⟨m,hmM,hmprod⟩:=hxMap
 obtain ⟨s,hs⟩:=Ideal.Quotient.mk_surjective m
 have hcomap:Ideal.comap q pbar=p:=by
   rw [hpbar,Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
     ←RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp]
 have hsnot:s∉p:=by
   intro hsp
   have hqsp:q s∈pbar:=by
     change s∈Ideal.comap q pbar
     rwa [hcomap]
   exact hmM (hs ▸ hqsp)
 have hmprod':q (s*x)∈pbar^n:=by
   simpa only [q,map_mul,hs] using hmprod
 have hmapped:q (s*x)∈Ideal.map q (p^n):=by
   rw [Ideal.map_pow, ←hpbar]
   exact hmprod'
 have hcomapPow:s*x∈Ideal.comap q (Ideal.map q (p^n)):=hmapped
 rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
   ←RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcomapPow
 exact ⟨s,hsnot,by simpa only [sup_comm] using hcomapPow⟩
theorem isPrimary_of_maximal_power_le_le
   (J Q:Ideal A) [J.IsMaximal] (n:ℕ) (hn:1 ≤ n)
   (hpow:J^n ≤ Q) (hle:Q ≤ J):Q.IsPrimary:=by
 apply Ideal.isPrimary_of_isMaximal_radical
 have hrad:Ideal.radical Q=J:=by
   apply le_antisymm
   · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
   · intro x hx
     exact ⟨n,hpow (Ideal.pow_mem_pow hx n)⟩
 rw [hrad]
 exact inferInstance
theorem mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   (surface x s:A) (J:Ideal A) [J.IsMaximal]
   (hsurface:surface∈J) (n:ℕ) (hn:1 ≤ n)
   (hs:s∉J)
   (hmul:s*x∈Ideal.span {surface} ⊔ J^n):
   x∈Ideal.span {surface} ⊔ J^n:=by
 let Q:=Ideal.span {surface} ⊔ J^n
 have hpow:J^n ≤ Q:=le_sup_right
 have hle:Q ≤ J:=by
   exact sup_le (Ideal.span_le.mpr (by simpa))
     (Ideal.pow_le_self (Nat.ne_of_gt hn))
 have hprimary:Q.IsPrimary:=
   isPrimary_of_maximal_power_le_le J Q n hn hpow hle
 have hcases:=(Ideal.isPrimary_iff.mp hprimary).2
   (by simpa only [mul_comm] using hmul)
 rcases hcases with hxQ | hsrad
 · exact hxQ
 · have hrad:Ideal.radical Q=J:=by
     apply le_antisymm
     · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
     · intro y hy
       exact ⟨n,hpow (Ideal.pow_mem_pow hy n)⟩
   exact False.elim (hs (hrad ▸ hsrad))
end
end ProximityPrize.SubmissionLower.RCN310
end PackedLegacy_GL

/-! Packed from ProximityPrize.SubmissionLower.FX. -/
section PackedLegacy_FX
namespace ProximityPrize.SubmissionLower.RCN248
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem exists_original_multiplier_for_localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S):
   let d:=originalData S C
   let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
   ∃ s:MvPolynomial (Fin 4) K,
     s∉componentPrime S C∧
     s*numerator K d.factor
       (RCN326.w+1)∈
         RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu:=by
 let d:=originalData S C
 let family:=canonicalLocalDVRFamily S hfirstProper
 let mu:=localMultiplicity S family C
 let N:=numerator K d.factor
   (RCN326.w+1)
 let p0:=componentPrime S C
 let I0:=RCN218.factorIdeal d.factor
 let q0:=quotientPrime I0 p0
 let R:=LocalRing S C
 letI:IsDomain R:=family.domain C
 letI:IsDiscreteValuationRing R:=family.dvr C
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have horder:IsDiscreteValuationRing.addVal R (localImage S C N)=mu:=by
   change IsDiscreteValuationRing.addVal R (localImage S C N)=
     (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat
   apply (ENat.coe_toNat ?_).symm
   intro htop
   change 1 ≤ (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat at hmuPos
   rw [htop] at hmuPos
   simp at hmuPos
 obtain ⟨uniformizer,hUniformizer⟩:=
   IsDiscreteValuationRing.exists_irreducible R
 have hdvd:uniformizer^mu∣localImage S C N:=by
   apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
   rw [hUniformizer.addVal_pow,horder]
 have hxMax:localImage S C N∈IsLocalRing.maximalIdeal R^mu:=by
   rw [hUniformizer.maximalIdeal_eq,Ideal.span_singleton_pow,
     Ideal.mem_span_singleton]
   exact hdvd
 haveI:I0.IsPrime:=RCN218.factorIdeal_isPrime d.factor d.irreducible
 haveI:q0.IsPrime:=quotientPrime_isPrime I0 p0 (factorLe S C)
 exact exists_multiplier_mem_sup_pow_of_localized_mem
   I0 p0 (factorLe S C) q0 rfl N mu hxMax
theorem proper_global_tail_mem_projected_primary
   {B:Type*} [CommRing B]
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S)
   (f:MvPolynomial (Fin 4) K →+*B)
   (surface tail scalar:B) (J:Ideal B) [J.IsMaximal]
   (hfactor:f (originalData S C).factor∈Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=componentPrime S C)
   (htail:tail=f (numerator K S.F
     (RCN326.w+1))*scalar):
   tail∈Ideal.span {surface} ⊔
     J^localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C:=by
 let d:=originalData S C
 let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
 let b:=RCN326.w+1
 let Nfactor:=numerator K d.factor b
 let Q:=Ideal.span {surface} ⊔ J^mu
 obtain ⟨s,hsnot,hsN⟩:=
   exists_original_multiplier_for_localMultiplicity S hfirstProper C
 have hmapI:Ideal.map f (RCN218.factorIdeal d.factor) ≤ Ideal.span {surface}:=by
   rw [RCN218.factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
   exact Set.singleton_subset_iff.mpr hfactor
 have hmapP:Ideal.map f (componentPrime S C) ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (componentPrime S C^mu) ≤ J^mu:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP mu
 have htarget:Ideal.map f
     (RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu) ≤ Q:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f Nfactor∈Q:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsN)
 have hfs:f s∉J:=by
   intro hsJ
   apply hsnot
   rw [←hcontract]
   exact hsJ
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have hNfactor:f Nfactor∈Q:=
   mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
     surface (f Nfactor) (f s) J hsurface mu hmuPos hfs hmul
 have hdiff:d.factor∣numerator K S.F b-
     d.cofactor^(2*b)*Nfactor:=
   factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
     d.product b
 have hdiffMap:f (numerator K S.F b-
     d.cofactor^(2*b)*Nfactor)∈Ideal.span {surface}:=
   (Ideal.span {surface}).mem_of_dvd (map_dvd f hdiff) hfactor
 have hproduct:f (d.cofactor^(2*b)*Nfactor)∈Q:=by
   rw [map_mul]
   exact Q.mul_mem_left _ hNfactor
 have hwhole:f (numerator K S.F b)∈Q:=by
   have hdiffQ:f (numerator K S.F b-
       d.cofactor^(2*b)*Nfactor)∈Q:=
     (show Ideal.span {surface} ≤ Q from le_sup_left) hdiffMap
   have hadd:=Q.add_mem hdiffQ hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using hadd
 rw [htail]
 exact Q.mul_mem_right scalar hwhole
end
end ProximityPrize.SubmissionLower.RCN248
end PackedLegacy_FX

/-! Packed from ProximityPrize.SubmissionLower.FU. -/
section PackedLegacy_FU
namespace ProximityPrize.SubmissionLower.RCN245
open RCN244 RCN135 RCN136 RCN074 RCN095 RCN102 RCN113 RCN120 RCN086 RCN313 RCN002 RCN011 RCN125
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
 {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
abbrev StageComponent (S:Stage K I Gamma x p flag errorCap stageSupport):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
 ((fiberLocalizePlane q hq).comp
   (flagPlaneMap (GenericField K) lam mu nu order)).comp
     (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq
   (flagPlaneMap (GenericField K) lam mu nu order
     (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
       (RCN326.w+1))))
end
end ProximityPrize.SubmissionLower.RCN245
end PackedLegacy_FU

/-! Packed from ProximityPrize.SubmissionLower.FV. -/
section PackedLegacy_FV
namespace ProximityPrize.SubmissionLower.RCN246
open RCN244 RCN248 RCN135 RCN136 RCN095 RCN074 RCN106 RCN107 RCN102 RCN245 RCN113 RCN120 RCN086 RCN264 RCN218 RCN313 RCN002 RCN011 RCN021 RCN125 RCN093
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedStageSurface_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageSurfacePlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu S.G))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu S.G)=0
 rw [flagEvaluation_flag]
 change S.G∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_G_mem (GenericField K) S.G _ _ (component a)
theorem indexedStageTail_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageTailPlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 let tail:=globalTailCut (polynomialEmbedding K) S.F
   (RCN326.w+1)
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu tail))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu tail)=0
 rw [flagEvaluation_flag]
 change tail∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_T_mem (GenericField K) S.G tail _ (component a)
structure IndexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):Prop where
 relationMax:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
 factor_mem:stageFiberTargetMap S lam mu nu order q hq
   (originalData S (component a.1)).factor∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)}
 surface_mem:indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)∈
   indexedFiberRelation component lam mu nu order ht q hq a
 contract:(indexedFiberRelation component lam mu nu order ht q hq a).comap
   (stageFiberTargetMap S lam mu nu order q hq)=componentPrime S (component a.1)
 tail_eq:indexedFiberTail q hq (stageTailPlane S lam mu nu order)=
   stageFiberTargetMap S lam mu nu order q hq
     (numerator K S.F (RCN326.w+1))*
       stageFiberScalar S lam mu nu order q hq
theorem indexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   IndexedFiberProjectionData S component lam mu nu order ht q hq a:=by
 let phi:=polynomialEmbedding K
 let plane:=flagPlaneMap (GenericField K) lam mu nu order
 let localize:=fiberLocalizePlane q hq
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 refine ⟨indexedFiberRelation_isMaximal component lam mu nu order ht
   hfinite hgen q hq a,?_,?_,?_,?_⟩
 · rw [Ideal.mem_span_singleton]
   exact map_dvd (localize.comp plane) (originalData S (component a.1)).factor_dvd
 · exact Ideal.mem_map_of_mem localize
     (indexedStageSurface_mem_relation S component lam mu nu order ht a.1)
 · have hplane:(relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap plane=(component a.1).1:=by
     change (relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap
       ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom)=_
     rw [←Ideal.comap_comap,relationKernel_contract,
       flagEvaluation_kernel_contract]
   change J.comap ((localize.comp plane).comp (surfaceMap phi))=
     componentPrime S (component a.1)
   rw [←Ideal.comap_comap, ←Ideal.comap_comap,
     indexedFiberRelation_under,hplane]
   rfl
 · change localize (plane (globalTailCut phi S.F
     (RCN326.w+1)))=
     localize (plane (surfaceMap phi (numerator K S.F
       (RCN326.w+1))))*
       localize (plane (MvPolynomial.C
         ((-phi Polynomial.X)^(RCN326.w+1))))
   rw [globalTailCut_eq,map_mul,map_mul]
end
end ProximityPrize.SubmissionLower.RCN246
end PackedLegacy_FV

/-! Packed from ProximityPrize.SubmissionLower.FW. -/
section PackedLegacy_FW
namespace ProximityPrize.SubmissionLower.RCN247
open RCN244 RCN248 RCN074 RCN106 RCN107 RCN102 RCN245 RCN246 RCN120 RCN086 RCN218 RCN135 RCN313 RCN095 RCN093 RCN002 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedFiberTail_mem_primary
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberTail q hq (stageTailPlane S lam mu nu order)∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^
         localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (component a.1):=by
 let D:=indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
 letI:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=
   D.relationMax
 have hfactor:=D.factor_mem
 have hsurface:=D.surface_mem
 have hcontract:=D.contract
 have htail:=D.tail_eq
 apply proper_global_tail_mem_projected_primary
   (K:=K) (I:=I) (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
   (B:=Polynomial (FiberCoefficient q hq))
   (S:=S) (hfirstProper:=hfirstProper) (C:=component a.1)
   (f:=stageFiberTargetMap S lam mu nu order q hq)
   (surface:=indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order))
   (tail:=indexedFiberTail q hq (stageTailPlane S lam mu nu order))
   (scalar:=stageFiberScalar S lam mu nu order q hq)
   (J:=indexedFiberRelation component lam mu nu order ht q hq a)
 · exact hfactor
 · exact hsurface
 · exact hcontract
 · exact htail
end
end ProximityPrize.SubmissionLower.RCN247
end PackedLegacy_FW

/-! Packed from ProximityPrize.SubmissionLower.O. -/
section PackedLegacy_O
namespace ProximityPrize.SubmissionLower.RCN111
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
noncomputable def indexedPlaneResidueWeight (a:A):ℕ:=by
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Fact (Irreducible q):=
   ⟨projectedFactor_irreducible Omega L order e (ht a) (hfinite a)⟩
 let a0:=residueAlgebra q J (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 exact Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J)
end
end ProximityPrize.SubmissionLower.RCN111
end PackedLegacy_O

/-! Packed from ProximityPrize.SubmissionLower.FY. -/
section PackedLegacy_FY
namespace ProximityPrize.SubmissionLower.RCN249
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN074 RCN245 RCN106 RCN111 RCN095 RCN120 RCN093 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) (A:Type) [Fintype A]
structure StageIndexedFlagFamily where
 component:A → StageComponent S
 injective:Function.Injective component
 lam:GenericField K
 mu:GenericField K
 nu:GenericField K
 order:Fin 3 ≃ Fin 3
 ht:∀ a,Transcendental (GenericField K)
   (flagEvaluation (GenericField K) (component a).1 lam mu nu
     (MvPolynomial.X (order 0)))
 finite:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   FiniteDimensional (RatFunc (GenericField K))
     (CoordinateField (GenericField K) (component a).1)
 generates:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   IntermediateField.adjoin (RatFunc (GenericField K))
     ({flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 2)),
       flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 1))}:
       Set (CoordinateField (GenericField K) (component a).1))=⊤
 positive:0 < (stageSurfacePlane S lam mu nu order).natDegree
structure StageIndexedFactor (F:StageIndexedFlagFamily S A) where
 q:Polynomial (RatFunc (GenericField K))
 irreducible:Irreducible q
 monic:q.Monic
 witness:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def stageFamilyGroupedExponent
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):ℕ:=
 ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
   localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
     indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
       F.ht F.finite a.1
noncomputable def stageFamilyResultant (F:StageIndexedFlagFamily S A):
   Polynomial (RatFunc (GenericField K)):=
 Polynomial.resultant (stageSurfacePlane S F.lam F.mu F.nu F.order)
   (stageTailPlane S F.lam F.mu F.nu F.order)
   (stageSurfacePlane S F.lam F.mu F.nu F.order).natDegree
   (stageTailPlane S F.lam F.mu F.nu F.order).natDegree
@[simp] theorem stageFamilyGroupedExponent_eq
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (q):
   stageFamilyGroupedExponent S A hfirstProper F q=
     ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
         indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
           F.ht F.finite a.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN249
end PackedLegacy_FY

/-! Packed from ProximityPrize.SubmissionLower.J9. -/
section PackedLegacy_J9
namespace ProximityPrize.SubmissionLower.RCN102
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN226 RCN191 RCN120 RCN113 RCN225 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
def componentFactor (C:RegularComponent Omega G T H):
   Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega C.1) order
   (flagEvaluation Omega C.1 lam mu nu) (ht C)
abbrev FactorFiber (q:Polynomial (RatFunc Omega)):=
 {C:RegularComponent Omega G T H//q=componentFactor lam mu nu order ht C}
def fiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1))
def fiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (fiberRelation lam mu nu order ht q hq C)
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_J9

/-! Packed from ProximityPrize.SubmissionLower.C5. -/
section PackedLegacy_C5
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem transformedSurface_irreducible
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   Irreducible (planeMap Omega order (flagAlgHom lam mu nu G)):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 exact planeMap_irreducible_of_evaluation Omega (CoordinateField Omega C.1)
   order e (flagAlgHom lam mu nu G)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC
theorem transformedSurface_not_dvd_tail
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   ¬ planeMap Omega order (flagAlgHom lam mu nu G)∣
     planeMap Omega order (flagAlgHom lam mu nu T):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 intro hdiv
 have hflagDvd:=(planeMap_dvd_iff_of_evaluation Omega
   (CoordinateField Omega C.1) order e
     (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC).mp hdiv
 exact hproper ((flag_dvd_iff lam mu nu G T).mp hflagDvd)
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_C5

/-! Packed from ProximityPrize.SubmissionLower.K0. -/
section PackedLegacy_K0
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_K0

/-! Packed from ProximityPrize.SubmissionLower.K3. -/
section PackedLegacy_K3
namespace ProximityPrize.SubmissionLower.RCN108
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN103 RCN106 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
theorem indexed_denominators_disjoint_surface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint (((Ideal.span {q}).primeCompl.map
     (Polynomial.C:Polynomial (RatFunc Omega) →+*PlaneRing Omega).toMonoidHom):
     Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hsurface:planeMap Omega order (flagAlgHom lam mu nu G)∈J:=by
   change planeEvaluation Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (planeMap Omega order (flagAlgHom lam mu nu G))=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   change flagEvaluation Omega (component a.1).1 lam mu nu
     (flagAlgHom lam mu nu G)=0
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega (component a.1).1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H (component a.1)
 rw [Set.disjoint_left]
 intro x hx hxSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp hxSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem indexedFiberSurface_span_isPrime
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (Ideal.span {fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (transformedSurface_irreducible lam mu nu order hG
       (component a.1) (ht a.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)})
     hglobal (indexed_denominators_disjoint_surface
       component lam mu nu order ht q hq a)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem indexedFiberTail_not_mem_surface
   (hG:Irreducible G) (hproper:¬ G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom lam mu nu T))∉
     Ideal.span {fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega →+*Polynomial R:=fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (transformedSurface_irreducible lam mu nu order hG
         (component a.1) (ht a.1)).prime)
     (indexed_denominators_disjoint_surface component lam mu nu order ht q hq a)
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   simpa only [Ideal.map_span,Set.image_singleton] using hmem
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact transformedSurface_not_dvd_tail lam mu nu order hG hproper
   (component a.1) (ht a.1) (Ideal.mem_span_singleton.mp hglobal)
end
end ProximityPrize.SubmissionLower.RCN108
end PackedLegacy_K3

/-! Packed from ProximityPrize.SubmissionLower.FK. -/
section PackedLegacy_FK
namespace ProximityPrize.SubmissionLower.RCN227
open UniqueFactorizationMonoid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [DecidableEq K]
theorem ord_algebraMap_eq_normalizedFactors_count
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic)
   (hr:r≠0):
   Ring.ord (Localization.AtPrime p)
     (algebraMap (Polynomial K) (Localization.AtPrime p) r)=
       ((normalizedFactors r).count q:ℕ∞):=by
 let R:=Localization.AtPrime p
 have hp0:p≠⊥:=by
   rw [hp,ne_eq,Ideal.span_singleton_eq_bot]
   exact hq.ne_zero
 letI:IsDiscreteValuationRing R:=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial K) hp0 R
 have hem:emultiplicity q r=((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 have hfinite:FiniteMultiplicity q r:=
   finiteMultiplicity_of_emultiplicity_eq_natCast hem
 let e:ℕ:=(normalizedFactors r).count q
 have hmult:multiplicity q r=e:=by
   rw [multiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 obtain ⟨s,hrs,hqNotDvd⟩:=hfinite.exists_eq_pow_mul_and_not_dvd
 rw [hmult] at hrs
 have hsNotMem:s∉p:=by
   simpa only [hp,Ideal.mem_span_singleton] using hqNotDvd
 have hsUnit:IsUnit (algebraMap (Polynomial K) R s):=
   (IsLocalization.AtPrime.isUnit_to_map_iff R p s).mpr hsNotMem
 have hqMapNe:algebraMap (Polynomial K) R q≠0:=
   by
     simpa only [map_zero] using
       (FaithfulSMul.algebraMap_injective (Polynomial K) R).ne hq.ne_zero
 have hmax:IsLocalRing.maximalIdeal R=
     Ideal.span {algebraMap (Polynomial K) R q}:=by
   calc
     IsLocalRing.maximalIdeal R=
         Ideal.map (algebraMap (Polynomial K) R) p:=by
       simpa only [R] using
         (Localization.AtPrime.map_eq_maximalIdeal (I:=p)).symm
     _=Ideal.map (algebraMap (Polynomial K) R) (Ideal.span {q}):=
       congrArg (Ideal.map (algebraMap (Polynomial K) R)) hp
     _=Ideal.span {algebraMap (Polynomial K) R q}:=by
       rw [Ideal.map_span]
       simp only [Set.image_singleton]
 have hqMapIrr:Irreducible (algebraMap (Polynomial K) R q):=
   IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
     _ hqMapNe hmax
 have hsNe:algebraMap (Polynomial K) R s≠0:=hsUnit.ne_zero
 have hrsMap:algebraMap (Polynomial K) R r=
     (algebraMap (Polynomial K) R q)^e*
       algebraMap (Polynomial K) R s:=by
   rw [hrs,map_mul,map_pow]
 change Ring.ord R (algebraMap (Polynomial K) R r)=_
 rw [hrsMap,
   Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hsNe),
   Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hqMapNe),
   Ring.ord_of_irreducible hqMapIrr,Ring.ord_of_isUnit hsUnit]
 simp [e]
theorem pow_sum_dvd_of_sum_le_localized_ord
   {I:Type*} [Fintype I]
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic) (hr:r≠0)
   (multiplicity:I → ℕ)
   (hle:((∑ i,multiplicity i:ℕ):ℕ∞) ≤
     Ring.ord (Localization.AtPrime p)
       (algebraMap (Polynomial K) (Localization.AtPrime p) r)):
   q^(∑ i,multiplicity i)∣r:=by
 rw [ord_algebraMap_eq_normalizedFactors_count p q r hp hq hqMonic hr] at hle
 have hcount:(∑ i,multiplicity i) ≤ (normalizedFactors r).count q:=by
   exact_mod_cast hle
 have hem:emultiplicity q r=
     ((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 apply pow_dvd_of_le_emultiplicity
 rw [hem]
 exact_mod_cast hcount
end
end ProximityPrize.SubmissionLower.RCN227
end PackedLegacy_FK

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.GK. -/
section PackedLegacy_GK
namespace ProximityPrize.SubmissionLower.RCN308
open scoped Classical
open RCN307 RCN309
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
def fullPiecesRingHom
   {J:Type*} [Fintype J]
   (pieces:J → Ideal (Polynomial R)):
   Polynomial R →+*(∀ j,Polynomial R ⧸ pieces j):=
 RingHom.pi fun j↦Ideal.Quotient.mk (pieces j)
def coefficientMaxIdeal:Ideal (Polynomial R):=
 Ideal.map (Polynomial.C:R →+*Polynomial R)
   (IsLocalRing.maximalIdeal R)
theorem rawPieces_modMax_surjective_of_monic_mod
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R))
   (hcoprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   (M:Polynomial R) (hMMonic:M.Monic)
   (hMmem:M∈intersectionIdeal P Q ⊔ coefficientMaxIdeal (R:=R))
   (hMdegree:M.natDegree ≤ m+n):
   Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let full:=fullPiecesRingHom pieces
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hfullC:full.comp (Polynomial.C:R →+*Polynomial R)=
     algebraMap R target:=by
   ext r j
   rfl
 have hcoeffMap:Ideal.map full (coefficientMaxIdeal (R:=R))=
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   rw [coefficientMaxIdeal,Ideal.map_map,hfullC]
 have hinterZero:∀ x∈intersectionIdeal P Q,full x=0:=by
   intro x hx
   funext j
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcontains j hx)
 have hMmax:full M∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp hMmem
   have hfa:full a=0:=hinterZero a ha
   have hfb:full b∈
       Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
     rw [←hcoeffMap]
     exact Ideal.mem_map_of_mem full hb
   rw [←hab,map_add,hfa,zero_add]
   exact hfb
 intro ybar
 obtain ⟨y,rfl⟩:=Submodule.mkQ_surjective maxTarget ybar
 obtain ⟨A,hA⟩:=Ideal.pi_mkQ_surjective hcoprime y
 let rem:Polynomial R:=A %ₘ M
 have hremDegree:rem.degree < (m+n:ℕ):=by
   have hlt:=Polynomial.degree_modByMonic_lt A hMMonic
   rw [Polynomial.degree_eq_natDegree hMMonic.ne_zero] at hlt
   exact hlt.trans_le (by exact_mod_cast hMdegree)
 let v:Polynomial.degreeLT R (m+n):=
   ⟨rem,Polynomial.mem_degreeLT.mpr hremDegree⟩
 refine ⟨v,?_⟩
 change maxTarget.mkQ (rawPiecesMap P Q m n pieces v)=maxTarget.mkQ y
 rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
 have hraw:rawPiecesMap P Q m n pieces v=full rem:=by
   rfl
 have hfullA:full A=y:=hA
 rw [hraw, ←hfullA, ←map_sub]
 have hdiff:rem-A= -(M*(A/ₘ M)):=by
   dsimp only [rem]
   rw [Polynomial.modByMonic_eq_sub_mul_div]
   ring
 rw [hdiff,map_neg,map_mul]
 have hmul:full M*full (A/ₘ M)∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=
   Ideal.mul_mem_right _ _ hMmax
 have hmul':full M*full (A/ₘ M)∈maxTarget:=by
   change full M*full (A/ₘ M)∈
     IsLocalRing.maximalIdeal R • (⊤:Submodule R target)
   rw [Ideal.smul_top_eq_map]
   exact hmul
 exact maxTarget.neg_mem hmul'
theorem sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)))
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤
     Module.length R (Polynomial R ⧸ pieces j)):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (Polynomial.resultant P Q m n):=by
 classical
 letI:DecidableEq (Fin (m+n)):=Classical.decEq _
 let f:=Polynomial.sylvesterMap P Q hPcap hQcap
 have hinj:Function.Injective f:=by
   intro x y hxy
   apply sub_eq_zero.mp
   let z:=x-y
   have hfz:f z=0:=by simp [z,f,hxy]
   have hcomp:=LinearMap.congr_fun
     (Polynomial.adjSylvester_comp_sylveserMap P Q hPcap hQcap) z
   have hscalar:Polynomial.resultant P Q m n • z=0:=by
     rw [LinearMap.comp_apply,hfz,map_zero] at hcomp
     simpa using hcomp.symm
   exact (smul_eq_zero.mp hscalar).resolve_left hresultant
 have hbound:=
   RCN196.sum_multiplicities_le_ord_toMatrix_det_of_surjective
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f hinj
     (fun j↦Polynomial R ⧸ pieces j) multiplicity hlength
     (RCN309.cokerToPieces
       P Q m n hPcap hQcap pieces hcontains)
     (cokerToPieces_surjective_of_modMax P Q m n hPcap hQcap
       pieces hcontains hmod)
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f=
       Polynomial.sylvester P Q m n:=by
   ext i j
   obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
   simpa [f,Polynomial.degreeLT.basisProd,LinearMap.toMatrix_apply] using
     congr($(Polynomial.toMatrix_sylvesterMap P Q hPcap hQcap) i j)
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
       Ring.ord R (LinearMap.toMatrix
         (Polynomial.degreeLT.basisProd R m n)
         (Polynomial.degreeLT.basis R (m+n)) f).det:=hbound
   _=Ring.ord R (Polynomial.resultant P Q m n):=by
     rw [hmatrix]
     congr 1
     unfold Polynomial.resultant
     convert! rfl
end
end ProximityPrize.SubmissionLower.RCN308
end PackedLegacy_GK

/-! Packed from ProximityPrize.SubmissionLower.GB. -/
section PackedLegacy_GB
namespace ProximityPrize.SubmissionLower.RCN297
open RCN307 RCN308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type*} [CommRing R] [IsLocalRing R]
end
end ProximityPrize.SubmissionLower.RCN297
end PackedLegacy_GB
end Compact_PackedLegacy

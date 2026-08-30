import ProximityPrize.SubmissionLower.FT
import ProximityPrize.SubmissionLower.GL
namespace ProximityPrize.SubmissionLower.RCN248
open RCN244
open RCN135
open RCN095
open RCN074
open RCN218
open RCN186
open RCN310
open RCN313
open RCN086
open RCN217
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
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
         factorIdeal d.factor ⊔ componentPrime S C^mu:=by
 let d:=originalData S C
 let family:=canonicalLocalDVRFamily S hfirstProper
 let mu:=localMultiplicity S family C
 let N:=numerator K d.factor
   (RCN326.w+1)
 let p0:=componentPrime S C
 let I0:=factorIdeal d.factor
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
 haveI:I0.IsPrime:=factorIdeal_isPrime d.factor d.irreducible
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
 have hmapI:Ideal.map f (factorIdeal d.factor) ≤ Ideal.span {surface}:=by
   rw [factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
   exact Set.singleton_subset_iff.mpr hfactor
 have hmapP:Ideal.map f (componentPrime S C) ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (componentPrime S C^mu) ≤ J^mu:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP mu
 have htarget:Ideal.map f
     (factorIdeal d.factor ⊔ componentPrime S C^mu) ≤ Q:=by
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

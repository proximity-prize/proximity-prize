import ProximityPrize.SubmissionLower.Y5
namespace ProximityPrize.SubmissionLower.RCN328
open scoped Classical BigOperators
open RCN264 RCN095
open RCN272
open RCN237
open RCN039
open RCN046
open RCN037
open RCN341
open RCN121
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega Seed:Type} [Field Omega]
variable {G T1 T2 H:MvPolynomial (Fin 3) Omega}
variable {flag tailFlag1 tailFlag2:FlagDegree}
def properSecondTailComponents:
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter fun C => T2∉C.1
theorem component_secondTail_card_le
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlag tailFlag2 T2) (hproper:T2∉C.1)
   (hzero:∀ gamma∈componentSeeds Omega G T1 H S point C,
     MvPolynomial.aeval (point gamma) T2=0):
   (componentSeeds Omega G T1 H S point C).card ≤
     B.weightedCost tailFlag2 C:=by
 classical
 let component:=componentSeeds Omega G T1 H S point C
 let points:=component.image point
 have hpointsPrime:∀ v∈points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T1 H S point C gamma hgamma
 have hpointsZero:∀ v∈points,MvPolynomial.aeval v T2=0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound:=(B.primeBudget C).zero_le tailFlag2 T2 hT2flag hproper
   points hpointsPrime hpointsZero
 have hcard:points.card=component.card:=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
theorem properSecondTail_component_sum_le
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlag tailFlag2 T2)
   (hzero:∀ gamma∈S,MvPolynomial.aeval (point gamma) T2=0):
   (∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       (componentSeeds Omega G T1 H S point C).card) ≤
     flagMixed flag tailFlag1 tailFlag2:=by
 classical
 calc
   _ ≤ ∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       B.weightedCost tailFlag2 C:=by
     apply Finset.sum_le_sum
     intro C hC
     apply component_secondTail_card_le B C S point hpoint_injective hT2flag
     · exact (Finset.mem_filter.mp hC).2
     · intro gamma hgamma
       exact hzero gamma (componentSeeds_subset Omega G T1 H S point C hgamma)
   _ ≤ ∑ C:RegularComponent Omega G T1 H,B.weightedCost tailFlag2 C:=by
     exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=B.sum_weightedCost_le tailFlag2
variable [IsAlgClosed Omega]
theorem properSecondTail_component_sum_le_flagMixed
   (base:∀ C:RegularComponent Omega G T1 H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T1 H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T1 H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hGirreducible:Irreducible G) (hT1proper:¬ G∣T1)
   (hGflag:PolynomialInFlag flag G)
   (hT1flag:PolynomialInFlag tailFlag1 T1)
   (hT2flag:PolynomialInFlag tailFlag2 T2)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hzero:∀ gamma∈S,MvPolynomial.aeval (point gamma) T2=0):
   (∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       (componentSeeds Omega G T1 H S point C).card) ≤
     flagMixed flag tailFlag1 tailFlag2:=by
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamily_of_nested
   flag tailFlag1 base hY hZ hSderiv hGirreducible hT1proper
   ((support_subset_flagSupport_iff flag G).mpr hGflag)
   ((support_subset_flagSupport_iff tailFlag1 T1).mpr hT1flag)
 exact properSecondTail_component_sum_le P.toPrimeFlagBudgetFamily
   S point hpoint_injective hT2flag hzero
end
end ProximityPrize.SubmissionLower.RCN328

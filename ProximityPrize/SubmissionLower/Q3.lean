import ProximityPrize.SubmissionLower.B1
import ProximityPrize.SubmissionLower.AM
namespace ProximityPrize.SubmissionLower.RCN336
open scoped Classical BigOperators
open RCN264 RCN095
open RCN237 RCN066
open RCN338
noncomputable section
set_option autoImplicit false
variable {Omega Seed : Type} [Field Omega]
variable {G T T' T2 H : MvPolynomial (Fin 3) Omega}
variable {surfaceFlag firstTailFlag secondTailFlag : FlagDegree}
theorem component_secondTail_card_le_mod
   (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
     surfaceFlag firstTailFlag)
   (C : RegularComponent Omega G T H)
   (S : Finset Seed) (point : Seed → Fin 3 → Omega)
   (hpoint_injective : Function.Injective point)
   (hT2flag : PolynomialInFlagMod C.1 secondTailFlag T2)
   (hproper : T2 ∉ C.1)
   (hzero : ∀ gamma ∈ componentSeeds Omega G T H S point C,
     MvPolynomial.aeval (point gamma) T2 = 0) :
   (componentSeeds Omega G T H S point C).card ≤
     B.weightedCost secondTailFlag C := by
 classical
 let component := componentSeeds Omega G T H S point C
 let points := component.image point
 have hpointsPrime : ∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T H S point C gamma hgamma
 have hpointsZero : ∀ v ∈ points,MvPolynomial.aeval v T2 = 0 := by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound :=
   RCN066.PrimeFlagZeroBudget.zero_le_congr
     (B.primeBudget C) secondTailFlag T2 hT2flag hproper
     points hpointsPrime hpointsZero
 have hcard : points.card = component.card :=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
def transportedMultiplicity
   (h : G ∣ T - T')
   (multiplicity : RegularComponent Omega G T H → ℕ) :
   RegularComponent Omega G T' H → ℕ :=
 fun C => multiplicity ((regularComponentEquiv h).symm C)
theorem weightedCertificate_of_congruentCut
   (h : G ∣ T - T')
   (B : PrimeFlagBudgetFamily (G := G) (T := T') (H := H)
     surfaceFlag firstTailFlag)
   (multiplicity : RegularComponent Omega G T H → ℕ)
   (C : RegularComponentWeightedInertiaResultantCertificate B
     (transportedMultiplicity h multiplicity)) :
   RegularComponentWeightedInertiaResultantCertificate
     (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
 z := by
   have hz := C.z
   dsimp only [transportedMultiplicity] at hz
   rw [← (regularComponentEquiv h).sum_comp] at hz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hz
 yz := by
   have hyz := C.yz
   dsimp only [transportedMultiplicity] at hyz
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hyz
 all := by
   have hall := C.all
   dsimp only [transportedMultiplicity] at hall
   rw [← (regularComponentEquiv h).sum_comp] at hall
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.RCN336

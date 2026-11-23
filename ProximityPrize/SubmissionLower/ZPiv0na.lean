import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import ProximityPrize.SubmissionLower.ZEdS9yd
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace q85rTDe
noncomputable section
open Polynomial IntermediateField
open P5 (p)
open q2TwyLa (PhysicalField)
variable (B:SeedData) {E :Type} [Field E] [Algebra PhysicalField E] [CharP E p]
local instance :Algebra B.constants E :=constantsAlgebra B E
end
end q85rTDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace q85rTDe
noncomputable section
open Polynomial

open P5 (p)
open q2TwyLa (PhysicalField)


local instance (B:SeedData) {E :Type} [Field E] [Algebra PhysicalField E] :
 Algebra B.constants E :=constantsAlgebra B E
private theorem btE {S:Type} [Field S] (j:PhysicalField →+* S) :
   ∃ A:ValuationSubring S,∀ x :PhysicalField,j x∈A↔physicalVal x≤1 := by
 let R:=physicalVal.valuationSubring
 obtain ⟨A,hA,hloc⟩:=IsLocalRing.exists_factor_valuationRing (j.comp R.subtype)
 let g:R →+* A:=(j.comp R.subtype).codRestrict A.toSubring hA
 let:IsLocalHom g:=hloc
 refine ⟨A,fun x=>⟨fun hx => ?_,fun hx=>hA ⟨x,hx⟩⟩⟩
 by_contra h
 have hxR:x∉R:=h
 have hx0:x≠0:= fun hz=>hxR (hz ▸ R.zero_mem)
 let a :R:=⟨x⁻¹,(R.mem_or_inv_mem x).resolve_left hxR⟩
 have ha :g a*(⟨j x,hx⟩:A)=1 := by
   apply Subtype.ext
   change j x⁻¹*j x=1
   rw [← map_mul,inv_mul_cancel₀ hx0,map_one]
 obtain ⟨b,hb⟩:=isUnit_iff_dvd_one.mp ((isUnit_iff_dvd_one.mpr
   ⟨⟨j x,hx⟩,ha.symm⟩:IsUnit (g a)).of_map g)
 have hb' : (b:PhysicalField)=x := by
   have hm:1=x⁻¹*(b:PhysicalField) :=congrArg Subtype.val hb
   calc
     (b:PhysicalField)=x*(x⁻¹*(b:PhysicalField)) := by rw [← mul_assoc,mul_inv_cancel₀ hx0,one_mul]
     _=x := by rw [← hm,mul_one]
 exact hxR (hb' ▸ b.property)
end
end q85rTDe
end

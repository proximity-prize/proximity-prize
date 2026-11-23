import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZK7Ye0a
set_option Elab.async false
set_option autoImplicit true
namespace qVXVW4b
noncomputable section
open Polynomial Finset qQ9yWTb
open P5 (K)
open P5_7_1 (Input)
open cu (aZ FX qD)
open Qt (gY Qc acG)
open scoped Classical
theorem constant_height (a :FX) :gY (Y3.constant a)=0:= by
 apply Nat.eq_zero_of_le_zero
 apply (Qc _ _).mpr
 intro i
 change ((C (MvPolynomial.C a :aZ)).coeff i).totalDegree≤0
 by_cases hi:i=0 <;> simp [coeff_C,hi]
theorem embed_degree (f :Raw) : (embed f).natDegree=f.natDegree :=
 natDegree_map_eq_of_injective
  (MvPolynomial.map_injective _ (IsFractionRing.injective _ _)) f
private theorem height_mul {f g:Raw} (hf :f≠0) (hg:g≠0) :
  height (f*g)=height f+height g:= by
 rw [show height (f*g)=gY (embed (f*g)) from rfl,map_mul]
 exact acG
  (map_ne_zero_iff _ Y3.embed_injective |>.mpr hf)
  (map_ne_zero_iff _ Y3.embed_injective |>.mpr hg)
private theorem degree_pos {f q:Raw} (hp: (embed f).IsPrimitive)
  (hd:q∣f) (hh:0<height q) :0<q.natDegree := by
 by_contra! hz
 have hc:embed q=C ((embed q).coeff 0) :=
  eq_C_of_natDegree_eq_zero ((embed_degree q).trans (Nat.eq_zero_of_le_zero hz))
 have hu:=hp ((embed q).coeff 0) (hc ▸ map_dvd embed hd)
 obtain ⟨a,_,ha⟩:=MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
 have h:height q=0:= by
  change gY (embed q)=0
  rw [hc,ha]
  exact constant_height a
 omega
private def Classified {x :Input} {U:Finset K} (J:WordChart x U)
   (P:ℕ→Prop) (f :Raw) :Prop :=
 f≠0 ∧ ∀ q:Raw,Irreducible q→q∣f →
   (0<q.natDegree∧0<height q)∧P (weight J q)
private theorem Classified.moving {x :Input} {U:Finset K} {J:WordChart x U}
   {P:ℕ→Prop} {f :Raw} (h:Classified J P f) :Moving f :=
 ⟨h.1,fun q hq hd=>(h.2 q hq hd).1⟩
private def value {x :Input} {U:Finset K} (J:WordChart x U) (γ:K) :Raw →+* FX :=
 (eval₂RingHom (qD (x.M.label γ)) (P5_7_7.dualValue J γ)).comp embed
end
end qVXVW4b

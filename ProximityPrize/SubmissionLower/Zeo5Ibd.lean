import ProximityPrize.SubmissionLower.Z5cOcra
import ProximityPrize.SubmissionLower.Z3R7Dac
set_option Elab.async false
set_option autoImplicit true
open IntermediateField renaming adjoin→qz0,subset_adjoin→qz1,topEquiv→qz2
set_option backward.isDefEq.respectTransparency false
namespace qlcyGcd
noncomputable section
open Polynomial qNu3xvc qypA4Sc
open cu (L)
open P5 (K p)
open scoped WithZero
open private normalize from ProximityPrize.SubmissionLower.Ze903db
open private separable_of_small_root separable_tower from ProximityPrize.SubmissionLower.Z3R7Dac
variable {E :Type} [Field E]
private theorem coeff_injective (A:Equation E) :Function.Injective (ajm A) :=
 (IsFractionRing.injective (AdjoinRoot A.f) (EC A)).comp
   (AdjoinRoot.of.injective_of_degree_ne_zero (f :=A.f) (fun h=> by
     rw [degree_eq_natDegree A.irreducible.ne_zero,Nat.cast_eq_zero] at h
     exact A.positive.ne' h))
local instance (A:Equation E) :Algebra (RatFunc E) (EC A) :=
 (IsFractionRing.lift (K:=RatFunc E) (coeff_injective A)).toAlgebra
private theorem fXW (A:Equation E) (q:E[X]) :
  algebraMap (RatFunc E) (EC A) (algebraMap E[X] (RatFunc E) q)=ajm A q :=
 IsFractionRing.lift_algebraMap (coeff_injective A) q
private theorem ordinate_degree (A:Equation E) :
    ∃ _:Module.Finite (RatFunc E) (EC A),
      Module.finrank (RatFunc E) (EC A)≤A.d:= by
  let F:=RatFunc E
  let y :=a7W A (Polynomial.X:E[X][X])
  let g:=A.f.map (algebraMap E[X] F)
  have q1 :=IsFractionRing.injective E[X] F
  have hg:g≠0:=(Polynomial.map_ne_zero_iff q1).mpr A.irreducible.ne_zero
  have ev (Q:E[X][X]) :aeval y (Q.map (algebraMap E[X] F))=a7W A Q:= by
    rw [aeval_def,eval₂_map]
    change Q.eval₂ ((algebraMap F (EC A)).comp (algebraMap E[X] F)) y= _
    rw [show (algebraMap F (EC A)).comp (algebraMap E[X] F)=ajm A from
      RingHom.ext (fXW A)]
    exact (hom_eval₂ Q Polynomial.C (a7W A) (Polynomial.X:E[X][X])).symm.trans
      (congrArg (a7W A) (eval₂_C_X (p:= Q)))
  have q0:aeval y g=0:= by
    rw [ev]
    change algebraMap (AdjoinRoot A.f) (EC A) (AdjoinRoot.mk A.f A.f)=0
    rw [AdjoinRoot.mk_self,map_zero]
  have hy :IsIntegral F y :=IsAlgebraic.isIntegral ⟨g,hg,q0⟩
  let T:=qz0 F ({y} : Set (EC A))
  have hT:T = ⊤ := by
    apply eq_top_iff.mpr
    intro a _
    have hp (b:AdjoinRoot A.f) :algebraMap (AdjoinRoot A.f) (EC A) b∈T:= by
      obtain ⟨Q,rfl⟩:=AdjoinRoot.mk_surjective b
      change a7W A Q∈T
      rw [← ev]
      exact Algebra.adjoin_le (qz1 F _) <|
        Polynomial.aeval_mem_adjoin_singleton F y
    obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot A.f) a
    exact T.div_mem (hp b) (hp c)
  have hF:Module.Finite F T:=qz0.finiteDimensional hy
  have hf :Module.Finite F (EC A) := by
    rw [hT] at hF
    exact Module.Finite.of_surjective (qz2 (F:=F) (E :=EC A)).toLinearMap
      (qz2 (F:=F) (E :=EC A)).surjective
  have he :=qz0.finrank hy
  change Module.finrank F T= _ at he
  rw [hT,IntermediateField.finrank_top'] at he
  refine ⟨hf,?_⟩
  change Module.finrank F (EC A)≤_
  rw [he]
  exact (natDegree_le_of_dvd (minpoly.dvd F y q0) hg).trans_eq
    (natDegree_map_eq_of_injective q1 A.f)
variable [Algebra L E] {A:Equation E} {r :Bool} (v :GraphVal A r) (h:Horizontal v)
private abbrev Residue :=IsLocalRing.ResidueField v.val.valuationSubring
private abbrev resAlgebra :Algebra E (Residue v) :=
 ((IsLocalRing.residue _).comp (a8p v h)).toAlgebra
private def physInt:v.val.valuationSubring :=⟨amm A,v.base_regular⟩
private abbrev physRes :Residue v :=IsLocalRing.residue _ (physInt v)
private abbrev ResPhys :=
 letI:=resAlgebra v h
 qz0 E ({physRes v} : Set (Residue v))
private def polyInt:E[X] →+* v.val.valuationSubring :=eval₂RingHom (a8p v h) (physInt v)
private theorem polyInt_root (q:E[X]) : (polyInt v h q:EC A)=ajm A q:= by
 have he :v.val.valuationSubring.subtype.comp (polyInt v h)=ajm A:= by
  apply Polynomial.ringHom_ext
  · intro c
    change v.val.valuationSubring.subtype ((C c).eval₂ (a8p v h) (physInt v))= _
    rw [eval₂_C]
    rfl
  · change v.val.valuationSubring.subtype (Polynomial.X.eval₂ (a8p v h) (physInt v))= _
    rw [eval₂_X]
    rfl
 exact RingHom.congr_fun he q
private theorem polyInt_res (q:E[X]) :
  letI:=resAlgebra v h
  IsLocalRing.residue _ (polyInt v h q)=aeval (physRes v) q:= by
 dsimp only [polyInt,coe_eval₂RingHom]
 rw [hom_eval₂]
 rfl
private abbrev baseVal:=v.val.comap (algebraMap (RatFunc E) (EC A))
private def baseToRing: (baseVal v).valuationSubring →+* v.val.valuationSubring :=
 ((algebraMap (RatFunc E) (EC A)).comp (baseVal v).valuationSubring.subtype).codRestrict _
   (fun a=>a.property)
private theorem base_residue (a : (baseVal v).valuationSubring) :
   IsLocalRing.residue _ (baseToRing v a)∈ResPhys v h:= by
 let:=resAlgebra v h
 let ρ:=IsLocalRing.residue v.val.valuationSubring
 let e :=polyInt v h
 let t:RatFunc E :=a.val
 have hd:ajm A t.denom≠0:= fun hz =>
   t.denom_ne_zero ((coeff_injective A) (hz.trans (map_zero (ajm A)).symm))
 have hfrac:algebraMap (RatFunc E) (EC A) t=ajm A t.num/ ajm A t.denom:= by
   conv_lhs=>rw [← t.num_div_denom]
   rw [map_div₀,fXW,fXW]
 have he :baseToRing v a*e t.denom=e t.num :=Subtype.ext (by
   change algebraMap (RatFunc E) (EC A) t*(polyInt v h t.denom:EC A)= _
   rw [polyInt_root,polyInt_root,hfrac,div_mul_cancel₀ _ hd])
 have hr :ρ (baseToRing v a)*ρ (e t.denom)=ρ (e t.num) := by rw [← map_mul,he]
 have hden:ρ (e t.denom)≠0:= by
   intro hz
   have hn:ρ (e t.num)=0:= by rw [← hr,hz,mul_zero]
   obtain ⟨b,c,hc⟩:=t.isCoprime_num_denom
   have hh:=congrArg (ρ.comp e) hc
   simp only [map_add,map_mul,RingHom.comp_apply,map_one,hn,hz,mul_zero,add_zero] at hh
   exact zero_ne_one hh
 have hm (q:E[X]) :ρ (e q)∈ResPhys v h:= by
   change IsLocalRing.residue _ (polyInt v h q)∈ResPhys v h
   rw [polyInt_res v h]
   exact Algebra.adjoin_le (qz1 E _) <|
     Polynomial.aeval_mem_adjoin_singleton E (physRes v)
 exact ((eq_div_iff_mul_eq hden).mpr hr).symm ▸ (ResPhys v h).div_mem (hm _) (hm _)
private theorem residue_annihilator (a :Residue v) :
   letI:=resAlgebra v h
   ∃ g: (ResPhys v h)[X],g≠0∧g.natDegree≤A.d ∧
     g.eval₂ (ResPhys v h).val.toRingHom a=0:= by
 let:=resAlgebra v h
 change ∃ g: (ResPhys v h)[X],g≠0∧g.natDegree≤A.d ∧
   g.eval₂ (ResPhys v h).val.toRingHom a=0
 obtain ⟨hfin,hdeg⟩:=ordinate_degree A
 let:=hfin
 obtain ⟨b,rfl⟩:=IsLocalRing.residue_surjective (R:=v.val.valuationSubring) a
 let F:=RatFunc E
 let f :=minpoly F (b:EC A)
 have hf :f≠0:=minpoly.ne_zero (IsIntegral.of_finite F _)
 let:Module.Free F (EC A) := @Module.Free.of_divisionRing F (EC A) _ _ _
 have hd:f.natDegree≤A.d:=(minpoly.natDegree_le (A:=F) (b:EC A)).trans hdeg
 let w:=baseVal v
 let ι:=w.valuationSubring.subtype
 obtain ⟨c,g,i,hg,hi⟩:=normalize w hf
 let e :w.valuationSubring →+* ResPhys v h :=
   ((IsLocalRing.residue _).comp (baseToRing v)).codRestrict _ (base_residue v h)
 refine ⟨g.map e,?_,?_,?_⟩
 · intro hz
   have he :=congrArg (fun q: (ResPhys v h)[X]=>q.coeff i) hz
   rw [coeff_map,hi,map_one,coeff_zero] at he
   exact one_ne_zero he
 · refine natDegree_map_le.trans ?_
   rw [← natDegree_map_eq_of_injective (f :=ι) Subtype.val_injective g,hg]
   exact (natDegree_C_mul_le _ _).trans hd
 · have hv :g.eval₂ (baseToRing v) b=0:= by
     apply Subtype.val_injective
     change v.val.valuationSubring.subtype _=v.val.valuationSubring.subtype 0
     rw [map_zero,hom_eval₂]
     change g.eval₂ ((algebraMap F (EC A)).comp ι) (b:EC A)=0
     rw [← eval₂_map,hg,eval₂_mul,eval₂_C,← aeval_def,minpoly.aeval,mul_zero]
   rw [eval₂_map]
   change g.eval₂ ((IsLocalRing.residue _).comp (baseToRing v)) (IsLocalRing.residue _ b)=0
   rw [← hom_eval₂,hv,map_zero]
theorem proof :qypA4Sc.c2 := by
 intro E _ _ A hd r v h q hq hqd hroot
 let:=resAlgebra v h
 change Algebra.IsSeparable E (Residue v)
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 have hx :aeval (physRes v) q=0:= by
   rw [← polyInt_res v h,IsLocalRing.residue_eq_zero_iff,v.val.mem_maximalIdeal_iff,polyInt_root]
   exact hroot
 have hF:Algebra.IsSeparable E (ResPhys v h) :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable E (Residue v)).mpr
     (separable_of_small_root hq hqd hx)
 let:CharP (ResPhys v h) p:=charP_of_injective_ringHom (algebraMap E (ResPhys v h)).injective p
 have hE :Algebra.IsSeparable (ResPhys v h) (Residue v) :=⟨fun a=> by
   obtain ⟨g,hg,hdegree,hzero⟩:=residue_annihilator v h a
   change aeval a g=0 at hzero
   exact separable_of_small_root hg (hdegree.trans_lt hd) hzero⟩
 exact separable_tower (F:=E) (E :=Residue v) (ResPhys v h) hF hE
end
end qlcyGcd

import ProximityPrize.SubmissionLower.ZYV8Uma
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace qH0Nw9c
noncomputable section
open Polynomial Finset

open P5_7_1
open cu (FX Jet A5)
open DP (U4)



open scoped Classical


private theorem anchor_mem {x :Input} {P:Poles x} (pick :Picks x.h P.rows) :
  anchorRow pick∈P.rows anchor.free (cutoff anchor.free) := by
 have hm:=(pick.main ⟨0,by decide⟩).free_mem
 change anchorRow pick∈P.rows anchor.free (buffer x.h 0 anchor.free) at hm
 simpa only [buffer,Nat.mul_zero,Nat.sub_zero] using hm
private theorem avoid {F E α:Type*} [Field F] [Infinite F] [AddCommGroup E] [Module F E]
    (V:Submodule F E) (D:Finset α) (I:α→Submodule F E)
    (missing : ∀ f∈D,∃ g∈V,g∉I f) :
    ∃ g∈V,∀ f∈D,g∉I f := by
  induction D using Finset.induction_on with
  | empty=>exact ⟨0,V.zero_mem,by simp⟩
  | @insert f D hf ih =>
    obtain ⟨a,ha,hgood⟩:=ih (fun d hd=>missing d (mem_insert_of_mem hd))
    obtain ⟨b,hb,hbad⟩:=missing f (mem_insert_self _ _)
    let bad (d:α) := {c:F | a+c•b∈I d}
    have finite (d:α) (hd:d∈insert f D) : (bad d).Finite := by
      apply Set.Subsingleton.finite
      intro v hv w hw
      by_contra hn
      have he : (v-w)•b∈I d:= by
        rw [sub_smul,← show (a+v•b)-(a+w•b)=v•b - w•b by abel]
        exact (I d).sub_mem hv hw
      have hdb:b∈I d:= by
        simpa only [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr hn),one_smul] using
          (I d).smul_mem (v-w)⁻¹ he
      rcases mem_insert.mp hd with rfl | hd
      · exact hbad hdb
      · exact hgood d hd (by simpa only [add_sub_cancel_right] using (I d).sub_mem hv ((I d).smul_mem v hdb))
    obtain ⟨c,hc⟩:=(Set.finite_iUnion (fun d : {d // d∈insert f D} => finite d d.2)).exists_notMem
    exact ⟨a+c•b,V.add_mem ha (V.smul_mem c hb),fun d hd hz =>
      hc (Set.mem_iUnion.mpr ⟨⟨d,hd⟩,hz⟩)⟩
private theorem avoid_divisors (V:Submodule FX Jet) (D:Finset Jet)
  (missing : ∀ f∈D,∃ g∈V,¬ f∣g) :
  ∃ g∈V,∀ f∈D,¬ f∣g:= by
 let:Infinite FX:=Infinite.of_injective _ (IsFractionRing.injective cu.L[X] FX)
 let I (f :Jet) :Submodule FX Jet:=(Ideal.span ({f} : Set Jet)).restrictScalars FX
 have h (f g:Jet) :g∈I f↔f∣g:= by
  change g∈Ideal.span ({f} : Set Jet)↔f∣g
  exact Ideal.mem_span_singleton (x :=g) (y :=f)
 have hh : ∀ f∈D,∃ g∈V,g∉I f := by simpa only [h] using missing
 obtain ⟨g,hg,hc⟩:=avoid (F:=FX) (E :=Jet) V D I hh
 exact ⟨g,hg,fun f hf hd=>hc f hf ((h f g).mpr hd)⟩
private def passes {x :Input} {P:Poles x} (pick :Picks x.h P.rows)
   (R:Reference x P) (f :Jet) (i:Intro) :Prop :=
 (∀ v a,a≤dI i→f∣A5 v a (pick.intro i)) ∧
   (i.val=0→f∣U4 R.raw)
private def first {x :Input} {P:Poles x} (pick :Picks x.h P.rows)
   (R:Reference x P) (f :Jet) :IntroIndex :=
 let h : ∃ n,n=introductions.length ∨ ∃ i:Intro,i.val=n ∧ ¬ passes pick R f i :=
   ⟨introductions.length,Or.inl rfl⟩
 ⟨Nat.find h,Nat.lt_succ_of_le (Nat.find_min' h (Or.inl rfl))⟩
end
end qH0Nw9c

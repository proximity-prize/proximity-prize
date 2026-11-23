import ProximityPrize.SubmissionLower.ZcC9kBb
set_option Elab.async false
set_option autoImplicit true
namespace qVm3Zhc
noncomputable section
open Finset Polynomial
open P5 (K jG)
open P5_7_2 (A fO Window row rankBlend)
open q7F2qKe (I0 wX rankPrice freeCap globalCap)

open pI (pN)
open TD (FP bCb)
open private OF.mk from ProximityPrize.SubmissionLower.ZogIzOe
open private bLI from ProximityPrize.SubmissionLower.ZdSQxye
open private c3F from ProximityPrize.SubmissionLower.U
open scoped BigOperators
private theorem word_from_window {b u del} {M:jG u del} {Γ}
   (F:P1.bje A M Γ) (h:Window b M.iF) {T:Finset K} (hT:T⊆Γ) :
   Word M.word T F.scalar (wX b) := by
 have hw:M.iF≤((row b).declaredHi:ℤ) :=
   h.2.trans (by exact_mod_cast (bLI b).1)
 refine OF.mk (F.distinct.mono hT) ?_ ?_
 · intro γ hγ
   rcases (F.mark γ (hT hγ)).aic with hzero | hdeg
   · simp [hzero]
   · change ((F.scalar γ).natDegree :ℤ)≤131071+M.iF at hdeg
     have h' : ((F.scalar γ).natDegree :ℤ)≤131071+((row b).declaredHi:ℤ) := by omega
     unfold wX
     exact_mod_cast h'
 · intro γ hγ
   let m:=F.mark γ (hT hγ)
   exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
private theorem blend_range (b:fO) : ∀ v∈rankBlend b,(0:ℚ)≤v∧v≤1 := by
 intro v hv
 unfold rankBlend at hv
 split at hv
 · have he : (1/ 10 :ℚ)=v := by simpa using hv
   subst v
   norm_num
 · simp at hv
theorem proof :q7F2qKe.c5:= by
 classical
 intro b u del M Γ F x o _ I hI _ hn hind
 obtain ⟨G,hG,hGI⟩:=c3F bzS.proof cy5.proof hI hn
 let T:=Γ.filter (I0 F I)
 have hw:=word_from_window F x.vo (show T⊆Γ from filter_subset _ _)
 let r :=bCb (freeCap b o 0) (globalCap b 0)
 have hB: (pN I 2 :ℚ)≤ r 2 := by
   simpa only [r,bCb,min_comm (freeCap b o 0 2)] using (hind.2.1 2).2
 have hJ: (pN I 1 :ℚ)≤ r 1 := by
   simpa only [r,bCb,min_comm (freeCap b o 0 1)] using (hind.2.1 1).2
 have hc:=equation_bound hw (Nat.le_add_right _ _) (Nat.add_le_add_left (bLI b).2 _)
   G hG hI.mixed_lt (fun γ hγ=> by
     simpa only [pI.d2l] using RingHom.mem_ker.mp ((mem_filter.mp hγ).2 hGI))
   hB hJ (blend_range b)
 refine hc.trans ?_
 let L:=jetRate (wX b)
 let μ:=Ut (wX b)
 cases h:rankBlend b with
 | none =>
   simp [h,coeff,rankPrice,FP,Fin.sum_univ_succ]
   change (2*L*r 2+μ)*pN I 1+(2*L*r 1+r 2)*pN I 2 ≤
     (2*lambda*wX b*r 2+μ)*pN I 1+(2*lambda*wX b*r 1+r 2)*pN I 2
   rw [mul_assoc (2 :ℚ) lambda]
 | some v =>
   simp only [h,coeff,rankPrice,FP,Fin.sum_univ_succ,Fin.sum_univ_zero,
     Matrix.cons_val_zero,Matrix.cons_val_succ,zero_mul,add_zero,zero_add]
   let a :=L*blendTerm (r 2) (r 1)*(1-v)+r 2
   change (4*L*r 2*v+μ)*pN I 1+a*pN I 2 ≤
     (4*lambda*wX b*r 2*v+μ)*pN I 1+(a+1)*pN I 2
   rw [mul_assoc (4 :ℚ) lambda]
   exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
     (Nat.cast_nonneg _))
end
end qVm3Zhc

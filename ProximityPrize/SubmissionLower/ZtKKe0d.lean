import ProximityPrize.SubmissionLower.ZqZuDUb
import ProximityPrize.SubmissionLower.Z0omYcd
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
section
set_option autoImplicit true
namespace P5_8_6
open P5_8 Finset
open scoped BigOperators
private theorem dNb {a b:Jn} (hp:0<a.B)
   (hB:a.B≤b.B) (hJ:a.J≤b.J) (hC:a.C≤b.C) :
   Gq b≤Gq a := by
 unfold Gq
 apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset (range_mono (Nat.div_le_div_left hB hp)))
 intro i _
 dsimp only
 have hj:=Nat.mul_le_mul_left (i+1) hJ
 have hc:=Nat.mul_le_mul_left (i+1) hC
 by_cases hb: (i+1)*b.J≤donorCaps.J∧(i+1)*b.C≤donorCaps.C
 · rw [ite_eq_left hb,ite_eq_left ⟨hj.trans hb.1,hc.trans hb.2⟩]
   exact bmt (Nat.sub_le_sub_left (Nat.mul_le_mul_left (i+1) hB) _)
     (Nat.sub_le_sub_left hj _) (Nat.sub_le_sub_left hc _)
 · rw [ite_eq_right hb]
   exact Nat.zero_le _
private def capRow (b j i:ℕ) :ℕ :=
 aMt ⟨6251-(i+1)*b,1959-(i+1)*j,979⟩
private theorem cofactor_zero (b:ℕ) :
  Gq ⟨b,0,0⟩ = ∑ i∈range (6251/b),capRow b 0 i:= by
 unfold Gq
 simp only [donorCaps,Jn.wD,capRow,Nat.mul_zero,Nat.sub_zero,Nat.zero_le,and_self,ite_true]
private theorem cofactor_index (b j:ℕ) (hj:0<j) :
    Gq ⟨b,j,0⟩ = ∑ i∈range (min (6251/b) (1959/j)),capRow b j i:= by
  unfold Gq
  change (∑ i∈range (6251/b),if (i+1)*j≤1959∧(i+1)*0≤979
    then capRow b j i else 0)= _
  symm
  calc
    _ = ∑ i∈range (min (6251/b) (1959/j)),(if (i+1)*j≤1959∧(i+1)*0≤979
        then capRow b j i else 0) := by
      apply sum_congr rfl
      intro i hi
      have hdiv :i+1≤1959/j:=((mem_range.mp hi).trans_le (min_le_right ..))
      rw [ite_eq_left ⟨(Nat.le_div_iff_mul_le hj).mp hdiv,by simp⟩]
    _ = _:= by
      refine sum_subset (range_mono (min_le_left ..)) ?_
      intro i hi hnot
      have hm : ¬ (i+1)*j≤1959:= by
        intro h
        have hdiv :=(Nat.le_div_iff_mul_le hj).mpr h
        exact hnot (mem_range.mpr (lt_min (mem_range.mp hi) hdiv))
      simp [hm]
private theorem emptySum (f :ℕ→ℕ) : (∑ i∈range 0,f i)=0:= by simp
private theorem extendSum {f :ℕ→ℕ} {m n x y :ℕ}
  (h: (∑ i∈range m,f i)=x) (v :AJ.CL (fun i=>f (m+i)) n=y) :
  (∑ i∈range (m+n),f i)=x+y := by
 rw [sum_range_add,h,← AJ.bOw,v]
local notation:65 s:65 " +[" len "," val "]" => extendSum (n:=len) (y :=val) s rfl
end P5_8_6
end

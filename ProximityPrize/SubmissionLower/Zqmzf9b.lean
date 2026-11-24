import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.Z2dBXLe
set_option Elab.async false
set_option autoImplicit true
namespace qSCPCwb
noncomputable section
open P6_6 (gZ bf mW LN)
open P6_6_5 (Zl)
open aR (ao af cK qE)
open oR (qg separant)
open we (cH eT DO ag9 qY zq)
open aA1 (aNx b5C)
open Polynomial
open scoped BigOperators
open private VT cut next support cBs from ProximityPrize.SubmissionLower.CD
open private aEA from ProximityPrize.SubmissionLower.A3
open private dgY bHj cte bTV from ProximityPrize.SubmissionLower.BG
private def a6m (f :af 3) (i:Fin aR.bf) :eT 4 :=
  if hi:i.val<bf then VT bf f ⟨i.val,hi⟩ else 0
private theorem fUr {f :af 3} {S:ao[X]} (hdeg:S.natDegree<bf)
    (hS:qg 2 f S) :
    Uj f (a6m f) (zq S)=afs S:= by
  funext i
  by_cases hi:i.val<bf
  · rw [Uj,a6m,dite_eq_left hi,b5C hS,aNx]
    let s :=qY (cK (separant f) S)
    have hs :s≠0:=bHj hS.2
    have hp:bf<K1.p:= by
      change 133426<0x7f000001
      decide
    unfold VT
    rw [map_sum]
    change (∑ j:Fin bf,MvPolynomial.eval (zq S) _) /
      s^(bf-4)= _
    simp only [map_mul,MvPolynomial.eval_C,aNx,cBs f S hS.1 hp,map_pow]
    change _=algebraMap ao cH (S.coeff i)
    rw [div_eq_iff (pow_ne_zero _ hs),← dgY S bf hdeg i.val,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change _ *(s^(bf-4)*_)= _ *s^(bf-4)
    rw [mul_comm (s^(bf-4)),← mul_assoc]
  · have hz :=coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_lt hi))
    simp only [Uj,a6m,dite_eq_right hi,map_zero,zero_div,afs,hz]
private theorem actual {f :af 3}
    (hcut:ag9 f (Dm f) (cut bf f))
    (hnext:ag9 f (Vk f) (next bf f))
    (S:ao[X]) (hdeg:S.natDegree≤gZ) (hS:qg 2 f S) :
    cK (Dm f) S=0∧cK (Vk f) S=0 ∧
      Uj f (a6m f) (zq S)=afs S:= by
  have hlength (d m:ℕ) (hd:d< m) (hm:4≤ m) :d-3< m-3:= by omega
  have hdeg' : S.natDegree<bf :=Nat.lt_succ_of_le hdeg
  have hfirst:=hlength S.natDegree bf hdeg' (by decide)
  have hsecond:S.natDegree-3<bf - 2 :=
    hfirst.trans_le (Nat.sub_le_sub_left (by decide :2≤3) _)
  refine ⟨bTV hS hcut ?_,bTV hS hnext ?_,
    fUr hdeg' hS⟩
  · rw [cut,aNx,cte hS.1 _ hfirst,map_zero]
  · rw [next,aNx,cte hS.1 _ hsecond,map_zero]
theorem qP {v n:ℕ} (f :Fin n→af 3) (hf :Zl v f) (i:Fin n) :
    Nonempty (Gf v (f i)) := by
  have hb:=(Finset.single_le_sum (f := fun k=>(f k).totalDegree)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hf.total
  have hj:=(Finset.single_le_sum (f := fun k=>qE (f k))
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hf.index
  have ht:=(Finset.single_le_sum (f := fun k=>(f k).degreeOf 2)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans hf.top
  obtain ⟨hg,he,hn,hc⟩:=support bf (by decide) (f i) (mW v) hb hj ht
  have hpad (j:Fin aR.bf) :
      DO (a6m (f i) j) (LN bf (mW v))
        (bf - 2) := by
    unfold a6m
    split_ifs with hi
    · exact hc ⟨j.val,hi⟩
    · simp [DO]
  have hrep:ag9 (f i) (Dm (f i)) (cut bf (f i)) :=
    aEA (f i) (bf-3)
  have hrep' : ag9 (f i) (Vk (f i)) (next bf (f i)) :=
    aEA (f i) (bf - 2)
  exact ⟨{
    cut:=cut bf (f i)
    next:=next bf (f i)
    numerator :=a6m (f i)
    graph_box :=hg
    cut_box :=he
    next_box :=hn
    coefficient_box :=hpad
    cut_represents :=hrep
    next_represents :=hrep'
    actual:=actual hrep hrep'
  }⟩
end
end qSCPCwb

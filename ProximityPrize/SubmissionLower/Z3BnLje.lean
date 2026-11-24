import ProximityPrize.SubmissionLower.ZDqG8Fa
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.Z0rImdc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZltF3Sb
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset.range → z4x, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Fintype.sum_prod_type → zsI, Polynomial.X → z7y
section
set_option maxHeartbeats 400000
namespace qQCEOid
open cu (Shape ku triangle)
open aeL (Offset)
open scoped BigOperators
private theorem sum_shape_comm {I:Type} (s :Shape) (a :Finset I) (f :I→ℕ→ℕ→ℕ) :
  (∑ i∈a,ku s (f i))=ku s (fun q j => ∑ i∈a,f i q j) := by
 unfold ku
 rw [Finset.sum_comm]
 exact zUo rfl fun _ _=>Finset.sum_comm
private theorem count_interval (n a b:ℕ) (h:b≤n) :
  (∑ i∈z4x n,if a≤ i∧i<b then 1 else 0)=b-a := by
 rw [← Finset.sum_filter]
 have he : (z4x n).filter (fun i=>a≤ i∧i<b)=Finset.Ico a b:= by
  ext i
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
  omega
 rw [he]
 simp
private def atWindow (s :Shape) (q j u k :ℕ) :ℕ :=
 if q-j≤u∧q≤k∧k≤ s.B+u-(q-j) then 1 else 0
private def atOffset (s :Shape) (q j t:ℕ) :ℕ :=
 if s.J-j≤t∧t<s.B+2*s.J-(q+min q s.J)+j then 1 else 0
private theorem count_offsets (s :Shape) {q j:ℕ}
  (hq:q≤ s.B) (hj:j≤ min q s.J) :
  (∑ t:Offset s,atOffset s q j t.val)=s.B+s.J-q-min q s.J+2*j:= by
 have hjJ:=hj.trans (min_le_right _ _)
 have hjq:=hj.trans (min_le_left _ _)
 have hdJ:=min_le_right q s.J
 rw [zdx (atOffset s q j)]
 unfold atOffset
 rw [count_interval _ _ _ (by omega)]
 omega
private theorem count_windows (s :Shape) {q j:ℕ} (hq:q≤ s.B) (u:ℕ) :
   (∑ k∈z4x (s.B+u+1),atWindow s q j u k) =
     if q-j≤u then s.B-q+(u-(q-j)+1) else 0:= by
 unfold atWindow
 by_cases ha :q-j≤u
 · simp only [ha,true_and,ite_true]
   change (∑ k∈z4x (s.B+u+1),
     if q≤k∧k≤ s.B+u-(q-j) then 1 else 0)= _
   have hc:=count_interval (s.B+u+1) q (s.B+u-(q-j)+1) (by omega)
   simp only [Nat.lt_succ_iff] at hc
   rw [hc]
   omega
 · simp [ha]
private theorem count_slices (s :Shape) {q j:ℕ} (hq:q≤ s.B) (hu:q-j≤ s.U) :
    (∑ r :Fin (s.U+1),∑ k∈z4x (s.B+(s.U-r.val)+1),
      atWindow s q j (s.U-r.val) k) =
      (s.U-(q-j)+1)*(s.B-q)+triangle (s.U-(q-j)) := by
  simp_rw [count_windows s hq]
  let a :=q-j
  let u:=s.U-a
  change (∑ r :Fin (s.U+1),if a≤ s.U-r.val then s.B-q+(s.U-r.val-a+1) else 0) =
    (u+1)*(s.B-q)+triangle u
  rw [zdx (fun r=>if a≤ s.U-r then s.B-q+(s.U-r-a+1) else 0)]
  calc
    _ = ∑ r∈z4x (u+1),(s.B-q+(u-r+1)) := by
      rw [← Finset.sum_subset (Finset.range_mono (show u+1≤ s.U+1 by dsimp [u]; omega))
        (f := fun r=>if a≤ s.U-r then s.B-q+(s.U-r-a+1) else 0)]
      · apply zUo rfl
        intro r hr
        have hr' := Finset.mem_range.mp hr
        have hav :a≤ s.U-r := by dsimp [u] at hr'; omega
        rw [ite_eq_left hav,show s.U-r-a=u-r by dsimp [u]; omega]
      · intro r hr hr'
        have hrU:=Finset.mem_range.mp hr
        have hru:u+1≤ r :=Nat.le_of_not_gt (fun h=>hr' (Finset.mem_range.mpr h))
        exact ite_eq_right (by dsimp [u] at hru; omega)
    _ = _:= by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      congr 1
      have hrefl:=Finset.sum_range_reflect (fun r :ℕ=>r+1) (u+1)
      have hid : ∀ r :ℕ,u+1-1-r+1=u-r+1 := by intro r; omega
      simp only [hid] at hrefl
      rw [hrefl]
      have hs :=Finset.sum_range_id (u+2)
      rw [Finset.sum_range_succ'] at hs
      simpa [triangle,Nat.mul_comm (u+2) (u+1),Nat.add_comm 1] using hs
private theorem count_pivot (s :Shape) {q j:ℕ} (hq:q≤ s.B)
    (hj:j≤ min q s.J) (hU:s.B≤ s.U) :
    (∑ t:Offset s,∑ r :Fin (s.U+1),∑ k∈z4x (s.B+(s.U-r.val)+1),
      if s.J-j≤t.val∧t.val<s.B+2*s.J-(q+min q s.J)+j ∧
        q-j≤ s.U-r.val∧q≤k∧k≤ s.B+(s.U-r.val)-(q-j) then 1 else 0) =
    (s.B+s.J-q-min q s.J+2*j) *
      ((s.U-(q-j)+1)*(s.B-q)+triangle (s.U-(q-j))) := by
  have hterm (t:Offset s) (r :Fin (s.U+1)) (k :ℕ) :
      (if s.J-j≤t.val∧t.val<s.B+2*s.J-(q+min q s.J)+j ∧
        q-j≤ s.U-r.val∧q≤k∧k≤ s.B+(s.U-r.val)-(q-j) then 1 else 0) =
        atOffset s q j t.val*atWindow s q j (s.U-r.val) k := by
    simp only [atOffset,atWindow]
    by_cases ht:s.J-j≤t.val∧t.val<s.B+2*s.J-(q+min q s.J)+j
    · simp [ht.1,ht.2]
    · simp only [ite_eq_right ht,zero_mul]
      exact ite_eq_right fun h=>ht ⟨h.1,h.2.1⟩
  simp_rw [hterm,← Finset.mul_sum]
  rw [← Finset.sum_mul,count_offsets s hq hj,count_slices s hq (by omega)]
theorem count_budget (s :Shape) (hU:s.B≤ s.U) :
  (∑ t:Offset s,∑ r :Fin (s.U+1),seedBudget s t (s.U-r.val)) =
    P5_7_4.poleRank s := by
 unfold seedBudget windowBudget P5_7_4.poleRank
 simp_rw [sum_shape_comm]
 apply zUo rfl
 intro q hq
 apply zUo rfl
 intro j hj
 exact count_pivot s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
  (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hU
end qQCEOid
end
section
set_option backward.isDefEq.respectTransparency false
namespace qcsMxUc
noncomputable section
open Polynomial Matrix
open cu (Shape)
open aeL (Offset Lh Pivot a2N Pa)
open qQCEOid (SeedCol VP clearedEntry seedMatrix)
def plainMatrix {R:Type} [CommSemiring R] (s :Shape) (t:Offset s) (u:ℕ) (a :R) :
    Matrix (VP s t u) (SeedCol s t u) R :=
  fun r v=>if r.1.1.val+r.2.val=v.1.1.val+v.2.val then Pa s t a r.1 v.1 else 0
private def form {F:Type} [Field F] (D:F[X]) (n i:ℕ) :F[X] :=
 D^(n-i)*(z7y (R:=F))^i
private theorem cSQ {F:Type} [Field F] (D:F[X]) (hD:D.natDegree≤1)
  (n i:ℕ) (hi:i≤n) : (form D n i).natDegree≤n:= by
 unfold form
 exact (natDegree_mul_le_of_le (natDegree_pow_le_of_le _ hD) (natDegree_X_pow_le _)).trans
  (by simp [Nat.sub_add_cancel hi])
private theorem seed_coeff {F:Type} [Field F] {s :Shape} {t:Offset s} {u:ℕ}
  (a b c:F) (r :VP s t u) (v :SeedCol s t u) :
  seedMatrix s t u a b c r v=(clearedEntry a b c r.1 v.1*(z7y (R:=F))^v.2.val).coeff r.2.val := by
 rw [seedMatrix,coeff_mul_X_pow']
 split_ifs <;> simp
private theorem coeff_sum_form {F:Type} [Field F] (p f :F[X]) {n:ℕ}
  (hn:f.natDegree≤n) (d:ℕ) :
  (∑ j:Fin (n+1),(p*(z7y (R:=F))^j.val).coeff d*f.coeff j.val)=(p*f).coeff d:= by
 have hf :f = ∑ j:Fin (n+1),C (f.coeff j.val)*(z7y (R:=F))^j.val := by
  rw [zdx (fun j=>C (f.coeff j)*z7y ^j)]
  exact f.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hn)
 conv_rhs=>rw [hf]
 simp only [Finset.mul_sum,finsetSum_coeff]
 apply zUo rfl
 intro j _
 rw [show p*(C (f.coeff j.val)*(Polynomial.X (R:=F))^j.val)=(p*(Polynomial.X (R:=F))^j.val)*C (f.coeff j.val) by ring,
  coeff_mul_C]
private theorem entry_form {F:Type} [Field F] {s :Shape} {t:Offset s}
  (u i:ℕ) (a b c:F) (r :Pivot s t) (v :Lh s t)
  (h:r.1.val≤v.1.val∧a2N v≤ r.1.val) (hi:i≤u) :
  let D:=C b+C c*(z7y (R:=F))
  clearedEntry a b c r v*form D u i =
    C (Pa s t a r v)*form D (u+s.B-r.1.val) (i+(v.1.val-r.1.val)) := by
 dsimp
 have hv :=v.1.isLt
 have he :u+s.B-r.1.val-(i+(v.1.val-r.1.val))=s.B-v.1.val+(u-i) := by omega
 simp only [clearedEntry,Pa,ite_eq_left h,form,he,mul_pow,map_mul,map_pow,pow_add]
 ring
theorem projective {F:Type} [Field F] (s :Shape) (t:Offset s) (u:ℕ)
    (a b c:F) (hb:b≠0) :
    (seedMatrix s t u a b c).rank≤(plainMatrix s t u a).rank := by
  classical
  let D:=C b+C c*(z7y (R:=F))
  let T:Matrix (Fin (u+1)) (Fin (u+1)) F:= fun j i=>(form D u i.val).coeff j.val
  let L:Matrix (SeedCol s t u) (SeedCol s t u) F :=
    (blockDiagonal (fun _:Lh s t=>T)).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  let H :Matrix (VP s t u) (VP s t u) F :=
    fun r j=>if r.1=j.1 then (form D (u+s.B-r.1.1.val) j.2.val).coeff r.2.val else 0
  have lh (v j:SeedCol s t u) :
      L v j=if v.1=j.1 then T v.2 j.2 else 0:= by
    simp [L,blockDiagonal_apply]
  have hD:D.natDegree≤1 := by
    apply natDegree_add_le_of_degree_le (by simp)
    simpa using (natDegree_C_mul_X_pow_le c 1)
  have hT:T.det≠0:= by
    have ht:T.IsLowerTriangular := by
      intro j i h
      have hji:j.val< i.val :=h
      simp only [T,form,coeff_mul_X_pow',ite_eq_right (not_le.mpr hji)]
    rw [det_of_isLowerTriangular T ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change (form D u i.val).coeff i.val≠0
    rw [form,coeff_mul_X_pow',ite_eq_left (le_refl _),Nat.sub_self]
    simp [D,coeff_zero_eq_eval_zero,hb]
  have hL:L.det≠0:= by
    dsimp only [L]
    rw [det_submatrix_equiv_self,det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _=>hT)
  have hfactor :seedMatrix s t u a b c*L=H*plainMatrix s t u a := by
    ext r v
    have hi:v.2.val≤u:=Nat.le_of_lt_succ v.2.isLt
    have hv :=v.1.1.isLt
    have hlhs : (seedMatrix s t u a b c*L) r v =
        (clearedEntry a b c r.1 v.1*form D u v.2.val).coeff r.2.val := by
      rw [Matrix.mul_apply,zsI,zi6 v.1]
      · simp only [lh,T,seed_coeff]
        exact coeff_sum_form _ _ (cSQ D hD _ _ hi) _
      · intro x _ hx
        simp [lh,hx]
      · simp
    rw [hlhs,Matrix.mul_apply,zsI,zi6 r.1]
    · by_cases hp:r.1.1.val≤v.1.1.val∧a2N v.1≤ r.1.1.val
      · let d:Fin (u+s.B+1) :=⟨v.2.val+(v.1.1.val-r.1.1.val),by omega⟩
        have hd:r.1.1.val+d.val=v.1.1.val+v.2.val := by dsimp [d]; omega
        rw [entry_form u v.2.val a b c r.1 v.1 hp hi,coeff_C_mul,
          Finset.sum_eq_single d]
        · simp only [H,plainMatrix,ite_eq_left rfl,ite_eq_left hd]
          exact mul_comm _ _
        · intro j _ hj
          have hne :r.1.1.val+j.val≠v.1.1.val+v.2.val := by
            intro h
            exact hj (Fin.ext (by omega))
          simp only [plainMatrix,ite_eq_right hne,mul_zero]
        · simp
      · simp only [plainMatrix,Pa,clearedEntry,ite_eq_right hp,ite_self,
          mul_zero,zero_mul,coeff_zero,Finset.sum_const_zero]
    · intro x _ hx
      simp [H,Ne.symm hx]
    · simp
  rw [← rank_mul_eq_left_of_det_ne_zero L (seedMatrix s t u a b c) hL,hfactor]
  exact rank_mul_le_right _ _
end
end qcsMxUc
end

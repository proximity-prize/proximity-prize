import ProximityPrize.SubmissionLower.ZLMe53d
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Finset.mul_sum → zxw, Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_comm → zWJ, Finset.sum_congr → zUo, Finset.sum_eq_zero → zYF, Finset.sum_filter → zLJ, Finset.sum_le_sum → zQk, Finset.sum_range_add → zGH, Finset.sum_range_reflect → ztt, Module.Finite → zAa, Module.finrank → zsE, Nat.lt_succ_iff → zh4
section
set_option autoImplicit true
namespace qA0rFHd
noncomputable section
open aR (ao Shape)
open qzLARrc (localImage windowBudget)
open scoped BigOperators
def c1 :Prop :=
  ∀ (a :Shape) (U:ℕ),
    zsE ao (localImage a U) ≤
      ∑ k∈z4x (U + a.b+1),
        zsE ao (seedWindow a (k-U) (min k a.b))
def c2 :Prop :=
  ∀ (a :Shape) (lo hi:ℕ),lo≤hi→hi≤a.b →
    zsE ao (seedWindow a lo hi) ≤
      zsE ao (reciprocalImage a hi (hi-lo))
def c3:Prop :=
  ∀ (a :Shape) (q w:ℕ),q≤a.b →
    zsE ao (homogeneousImage a q w)≤Ni a q w
theorem b3b {ι E :Type*} [AddCommGroup E] [Module ao E]
   (s :Finset ι) (P:ι→Submodule ao E) [∀ n,zAa ao (P n)] :
   zsE ao ↥(s.sup P) ≤ ∑ n∈s,zsE ao (P n) := by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert n s hn ih =>
   let:zAa ao ↥(s.sup P) :=Submodule.finite_finset_sup s P
   rw [Finset.sup_insert,Finset.sum_insert hn]
   exact (Submodule.finrank_add_le_finrank_add_finrank (P n) (s.sup P)).trans
     (Nat.add_le_add_left ih _)
private theorem reciprocal_le (h3:c3) (a :Shape) (hi w:ℕ) (hh:hi≤a.b) :
   zsE ao (reciprocalImage a hi w) ≤
     ∑ q∈z4x (hi+1),Ni a q (min q w) := by
 classical
 let P (q:ℕ) :Submodule ao (WindowRow a) :=homogeneousImage a q (min q w)
 have hfinite (q:ℕ) :zAa ao ↥(P q) := by
   unfold P homogeneousImage
   exact Module.Finite.span_of_finite ao (Set.finite_range _)
 change zsE ao ↥((z4x (hi+1)).sup P)≤_
 have hr := @b3b ℕ (WindowRow a) _ _ (z4x (hi+1)) P hfinite
 refine hr.trans ?_
 apply zQk
 intro q hq
 exact h3 a q (min q w) ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)).trans hh)
private theorem sum_for_grade (B U q:ℕ) (hB:B≤U) (hq:q≤B) (f :ℕ→ℕ) :
   (∑ k∈z4x (U + B+1),
     if q≤k then f (min q (min k B-(k-U))) else 0) =
     (U + B+1 - 2*q)*f q + ∑ w∈z4x q,f w:= by
 let g (k :ℕ) :=if q≤k then f (min q (min k B-(k-U))) else 0
 let n:=U + B+1 - 2*q
 have hsplit :U + B+1=(q+n)+q:= by dsimp [n]; omega
 change (∑ k∈z4x (U + B+1),g k) =
   n*f q + ∑ w∈z4x q,f w
 rw [hsplit,zGH,zGH g q n]
 have hzero : (∑ k∈z4x q,g k)=0:= by
   apply zYF
   intro k hk
   exact ite_eq_right (Nat.not_le_of_gt (Finset.mem_range.mp hk))
 have hfull: (∑ k∈z4x n,g (q+k))=n*f q:= by
   rw [Finset.sum_const_nat (m:=f q),Finset.card_range]
   intro k hk
   have hk' := Finset.mem_range.mp hk
   have h:q≤ min (q+k) B-(q+k-U) := by
     dsimp [n] at hk'
     omega
   simp [g,min_eq_left h]
 have htail: (∑ k∈z4x q,g (q+n+k)) =
     ∑ k∈z4x q,f k := by
   rw [← ztt f q]
   apply zUo rfl
   intro k hk
   have hk' := Finset.mem_range.mp hk
   have hle :q≤q+n+k := by omega
   have h:min q (min (q+n+k) B-(q+n+k-U))=q - 1 - k := by
     dsimp [n]
     omega
   simp [g,hle,h]
 rw [hzero,hfull,htail,zero_add]
private theorem count_windows (a :Shape) (U:ℕ) (hB:a.b≤U) :
   (∑ k∈z4x (U + a.b+1),∑ q∈z4x (min k a.b+1),
     Ni a q (min q (min k a.b-(k-U))))=windowBudget a U:= by
 have hr (k :ℕ) :z4x (min k a.b+1) =
     (z4x (a.b+1)).filter (fun q=>q≤k) := by
   ext q
   simp only [Finset.mem_range,Finset.mem_filter,zh4]
   omega
 simp_rw [hr,zLJ]
 rw [zWJ]
 unfold windowBudget
 apply zUo rfl
 intro q hq
 rw [sum_for_grade a.b U q hB (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))]
 unfold Ni
 rw [zxw,zfW,zWJ (s :=z4x q)]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qzLARrc.c2 := by
 intro a U hB
 refine (h1 a U).trans (le_trans (zQk ?_) (count_windows a U hB).le)
 intro k hk
 have hk' := Finset.mem_range.mp hk
 have hlo:k-U≤ min k a.b:= by omega
 have hhi:=min_le_right k a.b
 exact (h2 a (k-U) (min k a.b) hlo hhi).trans
  (reciprocal_le h3 a (min k a.b) (min k a.b-(k-U)) hhi)
end
end qA0rFHd
end
section
set_option maxHeartbeats 500000
namespace qmb8rCe
open aR (Shape)
open aFN (Slot)
open qzLARrc
open scoped BigOperators
private theorem cp3 {a :Shape} {q:ℕ} (s :Slot a q) :
  s.1.val≤a.t∧s.1.val≤a.j/2∧s.1.val+s.2.val≤q ∧
  derivativeIndex s≤a.j:= by
 have hc:=s.1.isLt
 have hb:=s.2.isLt
 simp only [zh4,le_min_iff] at hc hb
 unfold derivativeIndex
 omega
private def toSlot (a :Shape) (q:ℕ) (s :Slot a q) :Slot a (min q a.j) := by
 have ht:=(cp3 s).1
 have hj:=(cp3 s).2.1
 have hq:=(cp3 s).2.2.1
 have hd:=(cp3 s).2.2.2
 unfold derivativeIndex at hd
 let c:Fin (min (min q a.j) (min a.t (a.j/2))+1) :=
  ⟨s.1.val,by simp only [zh4,le_min_iff]; omega⟩
 exact ⟨c,⟨s.2.val,by
  change _< min (min q a.j - s.1.val) (a.j - 2*s.1.val)+1
  simp only [zh4,le_min_iff]
  omega⟩⟩
private def active (a :Shape) (q i w:ℕ) :Finset (Slot a q) :=
 Finset.univ.filter fun s=>q - s.1.val - s.2.val≤w∧a.j≤ i+derivativeIndex s
private theorem rank_active (a :Shape) (q i w:ℕ) :
   flagRank a q ((i:ℤ)-a.j) w≤(active a q i w).card:= by
 rw [flagRank,← Matrix.rank_transpose]
 apply Matrix.rank_le_card_of_support_subset
 rw [Function.support_subset_iff']
 intro s hs
 funext r
 change flagMatrix a q _ w r s=0
 unfold flagMatrix
 split
 · rename_i he
   exact (hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.1,by omega⟩)).elim
 · rfl
private theorem rank_partial (a :Shape) (q i w:ℕ) (hq:q≤a.b)
    (hi:a.b+a.j - q≤ i) :
    flagRank a q ((i:ℤ)-a.j) w≤ rankCut a (min q a.j) (q-w) (a.b+2*a.j-q-i) := by
  unfold flagRank rankCut
  have he :flagMatrix a q ((i:ℤ)-a.j) w =
      (cutMatrix a (min q a.j) (q-w) (a.b+2*a.j-q-i)).submatrix (toSlot a q) (toSlot a q) := by
    ext r s
    change flagMatrix a q ((i:ℤ)-a.j) w r s =
      cutMatrix a (min q a.j) (q-w) (a.b+2*a.j-q-i) (toSlot a q r) (toSlot a q s)
    have hd:0≤(i:ℤ)-a.j+(derivativeIndex s :ℤ) := by omega
    have hc: (i:ℤ)-a.j+(q:ℤ)+(derivativeIndex r :ℤ) <
        ((a.b+a.j:ℕ) :ℤ)↔derivativeIndex r<a.b+2*a.j-q-i:= by omega
    have hw:q - s.1.val - s.2.val≤w↔q-w≤ s.1.val+s.2.val := by omega
    simp only [flagMatrix,cutMatrix,hw,hd,hc,true_and]
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
private theorem rank_cut_zero (a :Shape) (q d h:ℕ) (hd:a.j<d) :
  rankCut a q d h=0:= by
 have he :cutMatrix a q d h=0:= by
  ext r s
  have hs :=(cp3 s).2.2.2
  unfold derivativeIndex at hs
  simp [cutMatrix,show ¬ d≤ s.1.val+s.2.val by omega]
 rw [rankCut,he,Matrix.rank_zero]
private theorem rank_cut_zero_height (a :Shape) (q d:ℕ) :
  rankCut a q d 0=0:= by
 have he :cutMatrix a q d 0=0:= by
  ext r s
  simp [cutMatrix]
 rw [rankCut,he,Matrix.rank_zero]
private theorem sum_tail (n k x :ℕ) :
  (∑ i∈z4x n,if k≤ i then x else 0)=(n-k)*x := by
 rw [← zLJ]
 have he : (z4x n).filter (fun i=>k≤ i)=Finset.Ico k n:= by
  ext i
  simp [and_comm]
 rw [he]
 simp
private theorem sum_active (a :Shape) (q w:ℕ) (hq:q≤a.b) :
   (∑ i∈z4x (a.b+a.j - q),(active a q i w).card) =
   ∑ s :Slot a q,if q - s.1.val - s.2.val≤w then a.b-q+derivativeIndex s else 0:= by
 simp only [active,Finset.card_filter]
 rw [zWJ]
 apply zUo rfl
 intro s _
 by_cases hs :q - s.1.val - s.2.val≤w
 · have he (i:ℕ) :a.j≤ i+derivativeIndex s↔a.j - derivativeIndex s≤ i:= by omega
   simp only [hs,true_and,he,sum_tail,mul_one,ite_true]
   have hd:=(cp3 s).2.2.2
   omega
 · simp [hs]
private theorem sum_slot (a :Shape) (q:ℕ) (f :ℕ→ℕ→ℕ) :
  (∑ s :Slot a q,f s.1.val s.2.val) =
  sumN (fun c=>sumN (f c) (min (q-c) (a.j-2*c)+1)) (min q (min a.t (a.j/2))+1) := by
 simp only [sumN_eq,Fintype.sum_sigma,zdx]
 exact zdx (fun c => ∑ i∈z4x (min (q-c) (a.j-2*c)+1),f c i) _
private def v (a :Shape) (q i w:ℕ) :ℕ :=
 if i<a.b+a.j - q then (active a q i w).card
 else cap a (min q a.j) (q-w) (a.b+2*a.j-q-i)
private theorem auw (a :Shape) (q d h:ℕ) (hd:a.j<d) :
  cap a q d h=0:= by
 simp [cap,show a.j+1-d=0 by omega,sumN]
private theorem window_term (a :Shape)
   (hc : ∀ q d h:ℕ,q≤a.j→d≤q→h≤a.j→ rankCut a q d h≤ cap a q d h)
   (q i w:ℕ) (hq:q≤a.b) :
   flagRank a q ((i:ℤ)-a.j) w≤v a q i w:= by
 unfold v
 split
 · exact rank_active a q i w
 · rename_i hi
   have hp:=rank_partial a q i w hq (by omega)
   apply hp.trans
   by_cases hh:a.b+2*a.j-q-i=0
   · rw [hh,rank_cut_zero_height]
     exact Nat.zero_le _
   by_cases hd:q-w≤a.j
   · exact hc _ _ _ (min_le_right _ _) (by omega) (by omega)
   · rw [rank_cut_zero a _ _ _ (by omega)]
     exact Nat.zero_le _
private theorem sum_v (a :Shape) (q w:ℕ) (hq:q≤a.b) :
   (∑ i∈z4x (a.b+2*a.j),v a q i w) =
     (∑ i∈z4x (a.b+a.j-q),(active a q i w).card)+mass a (min q a.j) (q-w) := by
 let s :=a.b+a.j-q
 have ht:a.b+2*a.j=(s+a.j)+q:= by dsimp [s]; omega
 rw [ht,zGH,zGH]
 have hf : (∑ i∈z4x s,v a q i w) =
     ∑ i∈z4x s,(active a q i w).card:= by
   apply zUo rfl
   intro i hi
   exact ite_eq_left (Finset.mem_range.mp hi)
 have hm: (∑ i∈z4x a.j,v a q (s+i) w)=mass a (min q a.j) (q-w) := by
   rw [mass,sumN_eq,← ztt (fun h=>cap a (min q a.j) (q-w) (h+1))]
   apply zUo rfl
   intro i hi
   have hir :=Finset.mem_range.mp hi
   rw [v,ite_eq_right (show ¬ s+i<a.b+a.j-q by dsimp [s]; omega)]
   congr 1
   dsimp [s]
   omega
 have hz : (∑ i∈z4x q,v a q (s+a.j+i) w)=0:= by
   apply zYF
   intro i _
   rw [v,ite_eq_right (show ¬ s+a.j+i<a.b+a.j-q by dsimp [s]; omega)]
   have he :a.b+2*a.j-q-(s+a.j+i)=0:= by dsimp [s]; omega
   simp [he,cap,sumN]
 rw [hf,hm,hz,add_zero]
private theorem reflect_mass (a :Shape) (q:ℕ) :
   (∑ w∈z4x q,mass a (min q a.j) (q-w)) =
   sumN (fun d=>mass a (min q a.j) (d+1)) (min q a.j) := by
 rw [sumN_eq]
 calc
   _ = ∑ d∈z4x q,mass a (min q a.j) (d+1) := by
     rw [← ztt (fun d=>mass a (min q a.j) (d+1))]
     apply zUo rfl
     intro d hd
     have hd' := Finset.mem_range.mp hd
     congr 1
     omega
   _ = _:= by
     symm
     apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
     intro d hd hn
     have hd' := Finset.mem_range.mp hd
     have hn' : min q a.j≤d:=Nat.le_of_not_gt (fun h=>hn (Finset.mem_range.mpr h))
     simp only [mass,sumN_eq]
     exact zYF fun h _=>auw a _ _ _ (by omega)
private theorem full_sum (a :Shape) (U q:ℕ) :
    factor a U q*(∑ s :Slot a q,(a.b-q+derivativeIndex s)) +
      (∑ w∈z4x q,∑ s :Slot a q,
        if q - s.1.val - s.2.val≤w then a.b-q+derivativeIndex s else 0) =
      fullCost a U q:= by
  rw [zxw,zWJ (s :=z4x q),← zfW]
  simp_rw [sum_tail]
  unfold fullCost
  rw [← sum_slot]
  apply zUo rfl
  intro s _
  have hs :=(cp3 s).2.2.1
  have he :q-(q-s.1.val-s.2.val)=s.2.val+s.1.val := by omega
  rw [he]
  unfold derivativeIndex
  ring
private theorem aH4 (a :Shape) (U:ℕ)
    (hc : ∀ q d h:ℕ,q≤a.j→d≤q→h≤a.j→ rankCut a q d h≤ cap a q d h)
    (q:ℕ) (hq:q≤a.b) :
    (∑ i∈z4x (a.b+2*a.j),
      (factor a U q*flagRank a q ((i:ℤ)-a.j) q +
        ∑ w∈z4x q,flagRank a q ((i:ℤ)-a.j) w)) ≤
    fullCost a U q+partCost a U q:= by
  calc
    _ ≤ ∑ i∈z4x (a.b+2*a.j),
          (factor a U q*v a q i q + ∑ w∈z4x q,v a q i w) :=
      zQk fun i _=>Nat.add_le_add
        (Nat.mul_le_mul_left _ (window_term a hc q i q hq))
        (zQk fun w _=>window_term a hc q i w hq)
    _ = _:= by
      rw [zfW,← zxw,zWJ (s :=z4x (a.b+2*a.j))]
      simp_rw [sum_v a q _ hq,sum_active a q _ hq]
      have hw (s :Slot a q) :q - s.1.val - s.2.val≤q:= by omega
      simp only [Nat.sub_self,hw,ite_true,Nat.mul_add,zfW,
        reflect_mass,partCost]
      rw [← full_sum a U q]
      simp only [zfW,Nat.mul_add]
      ac_rfl
theorem window_le_cost (a :Shape) (U:ℕ)
  (hc : ∀ q d h:ℕ,q≤a.j→d≤q→h≤a.j→ rankCut a q d h≤ cap a q d h) :
  windowBudget a U≤ sumN (fun q=>fullCost a U q+partCost a U q) (a.b+1) := by
 rw [windowBudget,sumN_eq]
 exact zQk fun q hq=>aH4 a U hc q (by
  have h:=Finset.mem_range.mp hq
  omega)
end qmb8rCe
end

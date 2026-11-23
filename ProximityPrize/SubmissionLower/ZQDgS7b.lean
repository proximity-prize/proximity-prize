import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qzVScmb
noncomputable section
open Finset
open scoped Classical
open P5 (K)









theorem gX {S T:Finset K} {s t:ℕ} (hs :S.card≤ s) (ht:T.card≤t) :
   (S∪T).card≤ s+t :=
 (card_union_le _ _).trans (Nat.add_le_add hs ht)
private theorem collect {α:Type*} (l:List α) (cost:α→ℕ)
   (PN : ∀ s∈l,Finset K) (hc : ∀ s (hs :s∈l),(PN s hs).card≤ cost s) :
   ∃ T:Finset K,T.card≤(l.map cost).sum ∧ ∀ s (hs :s∈l),PN s hs⊆T:= by
 induction l with
 | nil=>exact ⟨∅,by simp,by simp⟩
 | cons s l ih =>
   let tail (t:α) (ht:t∈l) :=PN t (List.mem_cons_of_mem _ ht)
   obtain ⟨T,ht,hmem⟩:=ih tail (fun t ht=>hc t _)
   refine ⟨PN s (List.mem_cons_self ..)∪T,gX (hc s _) ht,?_⟩
   intro t hm
   rcases List.mem_cons.mp hm with rfl | h
   · exact subset_union_left
   · exact (hmem _ h).trans subset_union_right
end
end qzVScmb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qzVScmb
open Finset
open scoped BigOperators
open P5_7_2 (fO)
open q7F2qKe (bTu origins originCount originBudget originCutter kK BC)
open TD (arC)
open akZ (yE)
open cu (Jet)
private theorem swap_tail (n:ℕ) (x y :ℕ→ℕ) :
    (∑ j∈range n,(∑ i∈range (j+1),x i)*y j) =
      ∑ i∈range n,x i*∑ j∈(range n).filter (i ≤ ·),y j:= by
  calc
    _ = ∑ j∈range n,∑ i∈range n,if i≤j then x i*y j else 0:= by
      apply sum_congr rfl
      intro j hj
      have he : (range n).filter (· ≤ j)=range (j+1) := by
        ext i
        simp only [mem_filter,mem_range]
        have :=mem_range.mp hj
        omega
      rw [← he,sum_mul,sum_filter]
    _ = ∑ i∈range n,∑ j∈range n,if i≤j then x i*y j else 0:=sum_comm
    _ = _:= by simp only [sum_filter,mul_sum,mul_ite,mul_zero]
private def running (w:ℕ→bTu) :ℕ→bTu
 | 0=> fun _=>0
 | n+1=> fun j=>max (running w n j) (w n j)
private def a4Q (w:ℕ→bTu) (i:ℕ) (j:Fin 3) :=
 running w (i+1) j - running w i j
private theorem jump_sum (w:ℕ→bTu) (n:ℕ) (j:Fin 3) :
   (∑ i∈range n,a4Q w i j)=running w n j:= by
 induction n with
 | zero=>rfl
 | succ n ih =>
   rw [sum_range_succ,ih]
   exact Nat.add_sub_of_le (le_max_left _ _)
private theorem fold_charge (b:fO) (k :Fin 4) (n:ℕ) :
   let w:= fun i=>arC (originCutter b i) k
   let step:= fun (acc:ℕ×bTu) i =>
     let next:= fun j=>max (acc.2 j) (w i j)
     (acc.1 + ∑ j,(next j-acc.2 j)*originBudget b i j,next)
   (List.range n).foldl step (0,fun _=>0) =
     ((∑ i∈range n,∑ j,a4Q w i j*originBudget b i j),running w n) := by
 dsimp only
 induction n with
 | zero=>rfl
 | succ n ih =>
   rw [List.range_succ,List.foldl_append,ih,sum_range_succ]
   rfl
theorem charge (b:fO) (D:ℕ→Finset Jet)
    (htail : ∀ i∈origins b,∀ j,
      ∑ o∈(origins b).filter (i ≤ ·),∑ f∈D o,yE f j≤originBudget b i j)
    (k :Fin 4) :
    (∑ o∈origins b,∑ f∈D o,kK (yE f) (originCutter b o) k)≤BC b k := by
  let w:= fun i=>arC (originCutter b i) k
  let a := fun i j => ∑ f∈D i,yE f j
  have h (o:ℕ) : (∑ f∈D o,kK (yE f) (originCutter b o) k) =
      ∑ j,w o j*a o j:= by
    simp only [a,w,kK,mul_sum]
    exact sum_comm
  have budget: (∑ o∈origins b,∑ j,w o j*a o j) ≤
      ∑ i∈origins b,∑ j,a4Q w i j*originBudget b i j:= by
    rw [sum_comm (s :=origins b),sum_comm (s :=origins b)]
    apply sum_le_sum
    intro j _
    calc
      _ ≤ ∑ o∈origins b,(∑ i∈range (o+1),a4Q w i j)*a o j:= by
        apply sum_le_sum
        intro o _
        rw [jump_sum]
        exact Nat.mul_le_mul_right _ (le_max_right _ _)
      _ = ∑ i∈origins b,a4Q w i j * ∑ o∈(origins b).filter (i ≤ ·),a o j :=
        swap_tail _ _ _
      _≤_:=sum_le_sum fun i hi=>Nat.mul_le_mul_left _ (htail i hi j)
  simp only [h]
  refine budget.trans ?_
  unfold BC
  dsimp only
  rw [fold_charge b k (originCount b)]
  exact Nat.le_add_right _ _
end qzVScmb
end
section
set_option autoImplicit true
namespace qzVScmb
open TD (arC)
open cu (Shape)
private theorem cfP {a b c d e f :ℕ} (ha :a≤d) (hb:b≤e) (hc:c≤f)
   (j:Fin 3) : (![a,b,c] :Fin 3→ℕ) j≤(![d,e,f] :Fin 3→ℕ) j:= by
 match j with
 | ⟨0,_⟩=>exact ha
 | ⟨1,_⟩=>exact hb
 | ⟨2,_⟩=>exact hc
 | ⟨n+3,hn⟩=>omega
theorem matrix_mono {s t:Shape} (hJ:s.J≤t.J) (hDiff :s.B-s.J≤t.B-t.J)
   (hB:s.B≤t.B) (hU:s.U≤t.U) (k :Fin 4) (j:Fin 3) :
   arC s k j≤arC t k j:= by
 have hz : (0:ℕ)≤0:=Nat.le_refl 0
 match k with
 | ⟨0,_⟩=>exact cfP hJ hDiff hz j
 | ⟨1,_⟩=>exact cfP hz hU hJ j
 | ⟨2,_⟩=>exact cfP hU hz hB j
 | ⟨3,_⟩=>exact cfP hz hz hU j
 | ⟨n+4,hn⟩=>omega
end qzVScmb
end
section
set_option autoImplicit true
namespace q3soobb
open P5 (p)
open P5_7_2 (fO stages movingOrder terminal A)
open q7F2qKe (nV afterFree freeCount a3D aHp)
open cu (Shape)
def Rz (s :Shape) :Prop :=
 0<s.m*A∧0<s.J∧s.J≤ s.B∧s.B<p∧s.U<p
private instance (s :Shape) :Decidable (Rz s) :=
 inferInstanceAs (Decidable (_∧_∧_∧_∧_))
theorem shapes_ok (b:fO) : ∀ s∈stages b,Rz s.free∧Rz s.moving:= by
 fin_cases b <;> simp only [stages,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨by decide,?_⟩
theorem terminal_ok (b:fO) :Rz (terminal b).shape := by
 fin_cases b <;> decide
theorem stages_len (b:fO) : (stages b).length=8:= by
 fin_cases b <;> rfl
def SelectedOK (b:fO) (n:ℕ) :Prop :=
 0<n∧n<(stages b).length∧0<(nV b n).dI∧(nV b n).dI<p
private instance (b:fO) (n:ℕ) :Decidable (SelectedOK b n) :=
 inferInstanceAs (Decidable (_∧_∧_∧_))
theorem selected_ok (b:fO) : ∀ n∈movingOrder b,SelectedOK b n:= by
 fin_cases b <;> simp only [movingOrder,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨by decide,?_⟩
theorem after_free (b:fO) :afterFree b=(stages b).length:= by
 simp [afterFree,freeCount,stages_len b]
theorem cqz {b:fO} {i:ℕ} (h:i<(stages b).length) :nV b i∈stages b:= by
 rw [nV,List.getElem?_eq_getElem h]
 exact List.getElem_mem h
noncomputable section



theorem after_free_pos (b:fO) :0<afterFree b:=Nat.succ_pos _
def pointShapes (b:fO) :List Shape :=
 ((stages b).drop 1).map a3D ++ [(terminal b).shape]
private theorem envelope_mem {b:fO} {n:ℕ} (hn:0<n) (hl:n<(stages b).length) :
  a3D (nV b n)∈pointShapes b:= by
 apply List.mem_append_left
 apply List.mem_map_of_mem
 apply List.mem_iff_getElem?.mpr
 refine ⟨n-1,?_⟩
 rw [List.getElem?_drop,show 1+(n-1)=n by omega,nV,List.getElem?_eq_getElem hl]
 rfl
private theorem fold_max_ge (l:List ℕ) (a :ℕ) :a≤l.foldl max a := by
 induction l generalizing a with
 | nil=>exact le_rfl
 | cons h t ih=>exact (le_max_left a h).trans (ih _)
private theorem mem_fold_max (l:List ℕ) (a n:ℕ) (h:n∈l) :
   n≤l.foldl max a := by
 induction l generalizing a with
 | nil=>simp at h
 | cons j t ih =>
   rcases List.mem_cons.mp h with rfl | hm
   · exact (le_max_right _ _).trans (fold_max_ge t _)
   · exact ih _ hm
private theorem point_caps (b:fO) {s :Shape} (h:s∈pointShapes b) :
   s.U≤((pointShapes b).map Shape.U).foldl max 0 ∧
   s.B-s.J≤((pointShapes b).map (fun z=>z.B-z.J)).foldl max 0 ∧
   s.J≤((pointShapes b).map Shape.J).foldl max 0 :=
 ⟨mem_fold_max _ _ _ (List.mem_map_of_mem h),mem_fold_max _ _ _ (List.mem_map_of_mem h),
   mem_fold_max _ _ _ (List.mem_map_of_mem h)⟩
theorem cut_shape_bounds {b:fO} {j:ℕ} (hj:0<j) :
   let s :=aHp b j
   s.J≤ s.B∧s.U≤((pointShapes b).map Shape.U).foldl max 0 ∧
   s.B≤((pointShapes b).map (fun z=>z.B-z.J)).foldl max 0 +
     ((pointShapes b).map Shape.J).foldl max 0:= by
 dsimp only
 unfold aHp
 split
 · rename_i h
   have hl:j<(stages b).length:=(after_free b) ▸ h
   have hJB:=(shapes_ok b _ (cqz hl)).1.2.2.1
   obtain ⟨hu,ht,hJ⟩:=point_caps b (envelope_mem hj hl)
   simp only [a3D,Nat.add_sub_cancel] at hu ht hJ
   exact ⟨hJB,(le_max_left _ _).trans hu,(Nat.sub_add_cancel hJB).symm.trans_le
     (Nat.add_le_add ((le_max_left _ _).trans ht) ((le_max_left _ _).trans hJ))⟩
 · split
   · rename_i n h
     have hn:=selected_ok b n (List.mem_iff_getElem?.mpr ⟨_,h⟩)
     obtain ⟨hu,ht,hJ⟩:=point_caps b (envelope_mem hn.1 hn.2.1)
     simp only [a3D,Nat.add_sub_cancel] at hu ht hJ ⊢
     exact ⟨Nat.le_add_left _ _,hu,Nat.add_le_add ht hJ⟩
   · have hJB:=(terminal_ok b).2.2.1
     have hm: (terminal b).shape∈pointShapes b:= by simp [pointShapes]
     obtain ⟨hu,ht,hJ⟩:=point_caps b hm
     exact ⟨hJB,hu,(Nat.sub_add_cancel hJB).symm.trans_le (Nat.add_le_add ht hJ)⟩
end
end q3soobb
end
section
set_option autoImplicit true
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
namespace qzVScmb
open P5 (p)
open P5_7_2 (fO stages topDonors introduction)
open q7F2qKe (nV)
open TD (aBh)
open cu (Shape)
open Finset
private def auxOK (s :Shape) :Bool :=
 decide (s.J≤ s.B∧s.U<p)
private theorem introductions_OK (b:fO) :
  ∀ a∈introduction b,auxOK a.shape=true := by
 fin_cases b <;> simp only [introduction,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨rfl,?_⟩
theorem intro_guard {b:fO} {a :P5_7_2.Aux} (h:a∈introduction b) :
  a.shape.J≤a.shape.B∧a.shape.U<p :=
 of_decide_eq_true (introductions_OK b a h)
theorem stage_0 (b:fO) :nV b 0∈stages b :=
 q3soobb.cqz (by rw [q3soobb.stages_len]; decide)
theorem stage_small (b:fO) : (nV b 0).free.U<p :=
 (q3soobb.shapes_ok b _ (stage_0 b)).1.2.2.2.2
private theorem stages_bmin (b:fO) :
  ∀ s∈stages b,2≤ s.free.B∧2≤ s.moving.B:= by
 fin_cases b <;> simp only [stages,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨by decide,?_⟩
theorem staged {b:fO} {s :P5_7_2.Ls} (h:s∈stages b) :
  aBh s.free.B s.free.J∧aBh s.moving.B s.moving.J:= by
 obtain ⟨hf,hm⟩:=q3soobb.shapes_ok b s h
 obtain ⟨fb,mb⟩:=stages_bmin b s h
 exact ⟨⟨fb,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,⟨mb,hm.2.1,hm.2.2.1,hm.2.2.2.1⟩⟩
theorem top_arithmetic (b:fO) :
  let t:=(topDonors b).2
  0<t.shape.J∧0<t.YM∧t.shape.J+t.YM≤t.shape.B:= by
 fin_cases b <;> decide
end qzVScmb
end

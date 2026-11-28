import ProximityPrize.SubmissionLower.Z6970H2307OrderEval
import ProximityPrize.SubmissionLower.Z6970H2307OrderFastTail

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000

namespace Height2307Orders
open K1_13 (Shape)
open Finset
open scoped BigOperators

def memoRemaining (w b j : ℕ) : ℕ :=
  if b≤4024 ∧ j≤1679 then
    if b=0 ∧ j=0 then 427286700047
    else (Height2307WidePrefix.countMemo (4024-b) (1679-j) w).toNat
  else 0

theorem memoRemaining_eq (w b j : ℕ) : memoRemaining w b j = upperRemaining w b j := by
  unfold memoRemaining upperRemaining
  rw [Height2307WidePrefix.countMemo_eq _ _ _ (Nat.sub_le _ _) (Nat.sub_le _ _)]

def memoTerm (w : ℕ) (r x : Shape) (L k : ℕ) : ℕ :=
  memoRemaining w ((k+1)*r.b+(k+1-L)*x.b) ((k+1)*r.j+(k+1-L)*x.j)

theorem memoTerm_eq (w : ℕ) (r x : Shape) (L k : ℕ) :
    memoTerm w r x L k = upperTerm w r x L k := memoRemaining_eq _ _ _

def massFold (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => massFold f n + f n

theorem massFold_eq (f : ℕ → ℕ) (n : ℕ) :
    massFold f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [massFold]
  | succ n ih => rw [massFold, sum_range_succ, ih]

def beforeSlice (w : ℕ) (r : Shape) (offset width : ℕ) : ℕ :=
  massFold (fun i => memoRemaining w ((offset+i+1)*r.b) ((offset+i+1)*r.j)) width

def afterWindow (w : ℕ) (r x : Shape) (L offset width : ℕ) : ℕ :=
  massFold (fun i => memoTerm w r x L (L+(offset+i))) width

def afterSlice (w : ℕ) (r x : Shape) (L : ℕ) : ℕ :=
  afterWindow w r x L 0 (1679/(r.j+x.j))

theorem afterWindow_add (w : ℕ) (r x : Shape) (L offset a b : ℕ) :
    afterWindow w r x L offset (a+b) =
      afterWindow w r x L offset a + afterWindow w r x L (offset+a) b := by
  simp only [afterWindow,massFold_eq,sum_range_add,Nat.add_assoc]

theorem afterWindow_join (w : ℕ) (r x : Shape) (L a b n u v z : ℕ)
    (hn : a+b=n) (hz : u+v=z)
    (ha : afterWindow w r x L 0 a=u) (hb : afterWindow w r x L a b=v) :
    afterWindow w r x L 0 n=z := by
  rw [← hn,afterWindow_add,ha,Nat.zero_add,hb,hz]

private theorem zero_fold (n c : ℕ) :
    massFold (fun _ => c) n = n*c := by
  induction n with
  | zero => simp [massFold]
  | succ n ih => rw [massFold,ih,Nat.succ_mul]

theorem beforeSlice_zero (w n : ℕ) :
    beforeSlice w ⟨0,0,0⟩ 0 n = n*427286700047 := by
  simp only [beforeSlice,Nat.mul_zero]
  exact zero_fold n 427286700047

theorem beforeSlice_add (w : ℕ) (r : Shape) (offset a b : ℕ) :
    beforeSlice w r offset (a+b) =
      beforeSlice w r offset a + beforeSlice w r (offset+a) b := by
  simp only [beforeSlice,massFold_eq,sum_range_add,Nat.add_assoc]

theorem beforeSlice_join (w : ℕ) (r : Shape) (a b n u v z : ℕ)
    (hn : a+b=n) (hz : u+v=z)
    (ha : beforeSlice w r 0 a=u) (hb : beforeSlice w r a b=v) :
    beforeSlice w r 0 n=z := by
  rw [← hn, beforeSlice_add, ha, Nat.zero_add, hb, hz]

theorem mass_split (w : ℕ) (r x : Shape) (L : ℕ) :
    upperMass w r x L = beforeSlice w r 0 L + afterSlice w r x L := by
  simp only [upperMass,beforeSlice,afterSlice,afterWindow,massFold_eq,sum_range_add,Nat.zero_add,memoTerm_eq,memoRemaining_eq]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hn : i+1-L=0 := by have := mem_range.mp hi; omega
  simp only [upperTerm,hn,Nat.zero_mul,Nat.add_zero]

theorem checked_of_prefix (r : Shape) (p : Threshold) (pre : ℕ)
    (hp : beforeSlice p.stride r 0 (p.m-1)=pre)
    (hm : 0<p.m ∧ 0<p.j ∧ 0<p.stride ∧
      pre+afterSlice p.stride r ⟨p.b,p.j,0⟩ (p.m-1)<21230822871131) :
    checked r p=true := by
  unfold checked
  rw [mass_split,hp]
  exact decide_eq_true hm

end Height2307Orders

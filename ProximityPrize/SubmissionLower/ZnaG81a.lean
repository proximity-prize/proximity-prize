import ProximityPrize.SubmissionLower.ZZZuA2c
import ProximityPrize.SubmissionLower.ZDyoNob
set_option Elab.async false
open _root_ renaming Finset.range→lz,List.map_cons→lI,List.sum_cons→lJ,P5_7.FarBand→aU,True.intro→c9,of_decide_eq_true→cy
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qyV6B3d
open P5_7_2 (fO)
open qMHqmcc (GG receipt appendGrades)
private abbrev kA:fO:=⟨7,by decide⟩
local notation "kU" => receipt 2542 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
private theorem r96:GG kA 96 3:=⟨kU,kU,kU,c9⟩
private theorem r99:GG kA 99 3:=⟨kU,kU,kU,c9⟩
private theorem r102 :GG kA 102 3:=⟨kU,kU,kU,c9⟩
private theorem r105:GG kA 105 3:=⟨kU,kU,kU,c9⟩
theorem r :GG kA 96 12 :=
 appendGrades (appendGrades (appendGrades r96 r99) r102) r105
end qyV6B3d
end
section
set_option autoImplicit true
namespace qeA2Kad


open P5_7_5
open TD (a3x)
open scoped BigOperators
private theorem edp (f :ℕ→ℚ) (xs :List ℕ) (a :ℚ) {j:ℕ}
   (hj:j∈xs) :xs.foldl (fun z i=>min z (f i)) a≤f j:= by
 have floor (xs :List ℕ) (a :ℚ) :xs.foldl (fun z i=>min z (f i)) a≤a := by
   induction xs generalizing a with
   | nil=>exact le_rfl
   | cons i xs ih=>exact (ih _).trans (min_le_left _ _)
 induction xs generalizing a with
 | nil=>simp at hj
 | cons i xs ih =>
   rcases List.mem_cons.mp hj with rfl | hm
   · exact (floor xs _).trans (min_le_right _ _)
   · exact ih _ hm
private def corner (b:aU) (i r :ℕ) (k :Fin 4) :ℚ :=
 let s :=nV b i
 alN s.free.shape s.moving.shape r (s.dI+1) (decide (Wx b≤ i)) k
private theorem guG (b:aU) (i r :ℕ) (k :Fin 4)
  (hp:0< r) (hr :r≤(nV b i).dI+1) :
  aE6 b i (decide (Wx b≤ i)) k≤ corner b i r k := by
 obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hp.ne'
 change ((List.range ((nV b i).dI+1)).foldl
  (fun a j=>min a (corner b i (j+1) k)) (corner b i 1 k))≤ corner b i (j+1) k
 exact edp _ _ _ (List.mem_range.mpr (by omega))
structure af where
 thresholds :ℕ
 seed :ℕ
 height:ℕ
abbrev cL:=List af
def entry (xs :cL) (i:ℕ) :af :=xs[i]?.getD ⟨0,0,0⟩
def nth (xs :cL) (i:ℕ) (k :Fin 4) :ℕ :=
 (entry xs i).thresholds/64^k.val % 64
def cap (b:aU) (xs :cL) :ℕ→GM
  | 0=> fun k=>beC b k
  | i+1=> fun k =>
    let r :=nth xs (i+1) k
    if r=0 then cap b xs i k else corner b (i+1) r k
def bEm (v c:GM) :ℚ:=v 0*c 0+(v 1*c 1+(v 2*c 2+(v 3*c 3+0)))
theorem b08 (v c:GM) :bEm v c=FP v c:= by
 simp only [FP,Fin.sum_univ_succ,Fin.sum_univ_zero]
 rfl
def a4Q (v :ℕ→GM) (i:ℕ) (c:GM) :ℚ :=
 bEm (fun k=>running v (i+1) k - running v i k) c
def bB7 (b:aU) (xs :cL) (i:ℕ) (k :Fin 4) :Bool :=
 decide (nth xs i k≤(nV b i).dI+1)
structure atY (b:aU) (xs :cL) (d e i:ℕ) :Prop where
 cap0:bB7 b xs i 0=true
 cap1 :bB7 b xs i 1=true
 aMA:bB7 b xs i 2=true
 aGU:bB7 b xs i 3=true
 seed :decide (a4Q (SS b 0) i (cap b xs i)≤((entry xs i).seed :ℚ)/d)=true
 height:decide (a4Q (SS b 1) i (cap b xs i)≤((entry xs i).height:ℚ)/e)=true
abbrev aLW (b:aU) (xs :cL) (d e n:ℕ) :Prop :=
 ∀ i:Fin n,atY b xs d e i
private theorem bHK {b:aU} {xs :cL} {d e n:ℕ} (h:aLW b xs d e n)
    {i:ℕ} (hi:i<n) (k :Fin 4) :V8 b i k≤ cap b xs i k := by
  induction i with
  | zero =>
    simp only [V8,cap,au9]
    exact le_rfl
  | succ i ih =>
    change min (V8 b i k) (aE6 b (i+1) (decide (Wx b≤ i+1)) k) ≤
      (if nth xs (i+1) k=0 then cap b xs i k else corner b (i+1) (nth xs (i+1) k) k)
    by_cases hr :nth xs (i+1) k=0
    · rw [ite_eq_left hr]
      exact (min_le_left _ _).trans (ih (by omega))
    · rw [ite_eq_right hr]
      have hrow:=h ⟨i+1,hi⟩
      have ht:nth xs (i+1) k≤(nV b (i+1)).dI+1 := by
        apply cy
        fin_cases k
        · exact hrow.cap0
        · exact hrow.cap1
        · exact hrow.aMA
        · exact hrow.aGU
      exact (min_le_right _ _).trans (guG b (i+1) _ k (Nat.pos_of_ne_zero hr) ht)
def total (xs :cL) (amount:af→ℕ) :ℕ→ℕ
 | 0=>0
 | i+1=>total xs amount i+amount (entry xs i)
private theorem blT {b:aU} {xs :cL} {d e n:ℕ} (h:aLW b xs d e n)
   (f :Fin 3) (amount:af→ℕ) (m:ℕ)
   (step : ∀ i:Fin n,a4Q (SS b f) i (cap b xs i)≤(amount (entry xs i) :ℚ)/m) :
   XM n (SS b f) (V8 b)≤(total xs amount n:ℚ)/m:= by
 induction n with
 | zero=>simp [ XM,total]
 | succ n ih =>
   have hn:=Nat.lt_succ_self n
   have hs :=a3x (v := fun k=>running (SS b f) (n+1) k -
     running (SS b f) n k) (fun _=>sub_nonneg.mpr (le_max_left _ _)) (bHK h hn)
   have ht' := step ⟨n,hn⟩
   rw [a4Q,b08] at ht'
   have ht:=hs.trans ht'
   rw [ XM,Finset.sum_range_succ,← XM,total,Nat.cast_add,add_div]
   exact add_le_add (ih (fun i=>h i.castSucc) (fun i=>step i.castSucc)) ht
theorem acI {b:aU} {xs :cL} {d e :ℕ} (h:aLW b xs d e (Fo b+1)) :
  ash b≤(total xs af.seed (Fo b+1) :ℚ)/d :=
 blT h 0 af.seed d (fun i=>cy (h i).seed)
theorem height_le {b:aU} {xs :cL} {d e :ℕ} (h:aLW b xs d e (Fo b+1)) :
  heightLimit b≤(total xs af.height (Fo b+1) :ℚ)/e :=
 blT h 1 af.height e (fun i=>cy (h i).height)
end qeA2Kad
end
section
set_option autoImplicit true
namespace qeA2Kad
open P5 (p)
open P5_7 (Ls terminal O2 farAgreement)
open P5_7_5
open cu (Shape)
private abbrev bQj (hi r :ℕ) (s :Shape) :Prop :=
 2≤ s.B∧0<s.J∧s.J≤ s.B∧s.B<p∧s.U<p ∧
   0<s.m*farAgreement∧2*hi*r≤O2 s
private theorem bVm {hi r :ℕ} {s :Shape} (h:bQj hi r s) :
  am1 hi r s := by
 obtain ⟨hb,hj,hjb,hbp,hu,hm,hr⟩:=h
 exact ⟨⟨hb,hj,hjb,hbp⟩,hu,hm,hr⟩
private abbrev a1d (b:aU) (i:ℕ) :Prop :=
 let s :=nV b i
 s.dI<p∧(i=0∨0<s.dI) ∧
  bQj b.row.hi s.dI s.free.shape∧bQj b.row.hi s.dI s.moving.shape
private theorem guH (b:aU) :
  (List.range b.row.stages.length).all (fun i=>decide (a1d b i))=true := by
 cases b <;> rfl
private theorem bOp {b:aU} {i:ℕ} (hi:i<b.row.stages.length) :
  a1d b i :=
 cy (List.all_eq_true.mp (guH b) i (List.mem_range.mpr hi))
private theorem bIj (b:aU) (i:ℕ) (hi:i<Fo b) :
  0<(nV b (i+1)).dI:= by
 have hi' : i+1<b.row.stages.length:= by unfold Fo at hi; omega
 exact (bOp hi').2.1.resolve_left (Nat.succ_ne_zero i)
private theorem eo3 (b:aU) :
  b.row.RU.all (fun i=>decide (0< i∧i<b.row.stages.length))=true := by
 cases b <;> rfl
private theorem aE7 (b:aU) (i:ℕ) (hi:i<b.row.stages.length) :
   let s :=nV b i
   am1 b.row.hi s.dI s.free.shape∧am1 b.row.hi s.dI s.moving.shape :=
 ⟨bVm (bOp hi).2.2.1,bVm (bOp hi).2.2.2⟩
open scoped BigOperators
private theorem gxd (s :List Ls) (fallback :Ls) (f :Ls→ℕ) :
   (∑ i∈lz s.length,f ((s[i]?).getD fallback))=(s.map f).sum:= by
 induction s with
 | nil=>simp
 | cons a s ih =>
   rw [List.length_cons,Finset.sum_range_succ',lI,lJ,← ih]
   simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Nat.add_comm]
private theorem sum_pairs (s :List Ls) (f :cu.Shape→ℕ) :
   ((s.flatMap fun t=>[t.free.shape,t.moving.shape]).map f).sum =
     (s.map fun t=>f t.free.shape+f t.moving.shape).sum:= by
 induction s with
 | nil=>rfl
 | cons a s ih =>
   simp only [List.flatMap_cons,List.cons_append,List.nil_append,lI,
     lJ,ih,Nat.add_assoc]
private theorem b3r (b:aU) :
    (∑ i∈lz b.row.stages.length,
      (au1 b.row.hi (nV b i).free.shape.B (nV b i).free.shape.J +
        au1 b.row.hi (nV b i).moving.shape.B (nV b i).moving.shape.J)) ≤
      a4f b:= by
  let jX (s :Shape) :=au1 b.row.hi s.B s.J
  change (∑ i∈lz b.row.stages.length,
    (fun s :Ls=>jX s.free.shape+jX s.moving.shape)
      ((b.row.stages[i]?).getD ⟨0,terminal b,terminal b⟩))≤a4f b
  rw [gxd b.row.stages ⟨0,terminal b,terminal b⟩
    (fun s=>jX s.free.shape+jX s.moving.shape)]
  unfold a4f fF
  rw [lI,lJ,sum_pairs]
  exact Nat.le_add_left _ _
theorem schedule (b:aU) (hs :ash b<p)
   (hp:pointFee b+lossFee b+lowSeedFee b+lowJetFee b+a4f b +
     contentBudget b≤b.row.prefixFee) :aqE b where
 aXU:= by cases b <;> decide
 zero := by cases b <;> rfl
 bIj:=bIj b
 bN7:= fun _ hi=>(bOp hi).1
 stop_reserve := by cases b <;> rfl
 aE8:= by cases b <;> decide
 brd:= fun i hi=>cy (List.all_eq_true.mp (eo3 b) i hi)
 b6r := by cases b <;> decide
 aE7:=aE7 b
 bxE := by apply bVm; cases b <;> decide
 bq6:=bq6 b
 bq5:=bq5 b
 bDl:= by cases b <;> decide
 bK5:=bK5 b
 fixed:=b3r b
 content:= by cases b <;> exact Nat.le_of_ble_eq_true rfl
 seed_small:=hs
 gH :=hp
end qeA2Kad
end

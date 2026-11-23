import ProximityPrize.SubmissionLower.Ze7JTZb
set_option Elab.async false
open _root_ renaming Finset.sum_le_sum→lV,Nat.cast_mul→nq,Nat.cast_ofNat→n5,Nat.cast_sum→nX,add_le_add→ oj,div_mul_eq_mul_div→ oq,le_max_left→nI,q7F2qKe.allShapes→cy,q7F2qKe.factorRunning→mD,q7F2qKe.originCount→c9,q7F2qKe.projectionCap→lI,q7F2qKe.stopCount→lz,qB9xHGe.bookResidual→lJ,qB9xHGe.budgetNum→aU
set_option autoImplicit true
namespace qB9xHGe
open Finset
open scoped BigOperators
open P5 (p)
open P5_7_2 (fO row introduction movingOrder)
open q7F2qKe
open TD (GM FP a3x bCb running XM bf7 alN arC)
private theorem foldl_le_start (f :ℕ→ℚ) (xs :List ℕ) (a :ℚ) :
   xs.foldl (fun z i=>min z (f i)) a≤a := by
 induction xs generalizing a with
 | nil=>exact le_rfl
 | cons i xs ih=>exact (ih _).trans (min_le_left _ _)
private theorem edp (f :ℕ→ℚ) (xs :List ℕ) (a :ℚ) {j:ℕ}
   (hj:j∈xs) :xs.foldl (fun z i=>min z (f i)) a≤f j:= by
 induction xs generalizing a with
 | nil=>simp at hj
 | cons i xs ih =>
   rcases List.mem_cons.mp hj with rfl | hm
   · exact (foldl_le_start f xs _).trans (min_le_right _ _)
   · exact ih _ hm
private def threshold (b:fO) (i:ℕ) (k :Fin 4) :ℕ :=
 min ((nV b i).dI+1) (max 1 ((thresholdBits b >>> (6*(4*i+k.val))) &&& 0x3f))
private def corner (b:fO) (i:ℕ) (k :Fin 4) :ℚ :=
 let s :=nV b i
 alN s.free s.moving (threshold b i k) (s.dI+1) true k
private theorem guG (b:fO) (i:ℕ) (k :Fin 4) :
   let s :=nV b i
   bf7 s.free s.moving s.dI true k≤ corner b i k := by
 let s :=nV b i
 have hn:0<threshold b i k :=lt_min (Nat.succ_pos _) (lt_of_lt_of_le (by decide) (nI _ _))
 have he :threshold b i k≤ s.dI+1 :=min_le_left _ _
 obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero hn.ne'
 change (List.range (s.dI+1)).foldl
   (fun z j=>min z (alN s.free s.moving (j+1) (s.dI+1) true k))
   (alN s.free s.moving 1 (s.dI+1) true k) ≤
     alN s.free s.moving (threshold b i k) (s.dI+1) true k
 rw [hj]
 exact edp _ _ _ (List.mem_range.mpr (by omega))
private theorem fold_cap_eval (xs :List ℕ) (f :ℕ→GM) (u:GM) (k :Fin 4) :
   xs.foldl (fun c i=>bCb c (f i)) u k =
    xs.foldl (fun c i=>min c (f i k)) (u k) := by
 induction xs generalizing u with
 | nil=>rfl
 | cons i xs ih=>exact ih _
private def initial (b:fO) (k :Fin 4) :ℕ :=
 (initialBits b >>> (31*k.val)) &&& 0x7fffffff
private theorem au9 (b:fO) (k :Fin 4) :BC b k=initial b k := by
 fin_cases b <;> fin_cases k <;> decide
private def cutIndex (b:fO) (i:ℕ) (k :Fin 4) :ℕ :=
 (cutBits b >>> (3*(4*i+k.val))) &&& 7
def upperGlobal (b:fO) (i:ℕ) :GM:= fun k =>
 let j:=cutIndex b i k
 if j∈(movingOrder b).take (i-afterFree b) then corner b j k else initial b k
private theorem global_le (b:fO) (i:ℕ) (k :Fin 4) :globalCap b i k≤upperGlobal b i k := by
 rw [globalCap,fold_cap_eval]
 dsimp only [upperGlobal]
 split
 · rename_i hj
   exact (edp _ _ _ hj).trans (guG b _ k)
 · exact (foldl_le_start _ _ _).trans (by rw [au9])
private def priced (a c:ℚ) :ℚ:=if a=0 then 0 else a*c
private theorem priced_eq (a c:ℚ) :priced a c=a*c:= by
 by_cases h:a=0 <;> simp [priced,h]
private def bEm (v c:GM) :ℚ :=
 priced (v 0) (c 0)+(priced (v 1) (c 1)+(priced (v 2) (c 2)+(priced (v 3) (c 3)+0)))
private theorem b08 (v c:GM) :bEm v c=FP v c:= by
 simp only [bEm,priced_eq,FP,Fin.sum_univ_succ,Fin.sum_univ_zero]
 rfl
private def a4Q (b:fO) (i:ℕ) :GM:= fun k =>
 let v := fun j=>SS b (j+1) 0
 running v (i+1) k - running v i k
def projectionRow (b:fO) (i:ℕ) :ℚ:=bEm (a4Q b i) (upperGlobal b (i+1))
def globalRow (b:fO) (i:ℕ) :ℚ:=bEm (bookGlobal b i) (upperGlobal b i)
private def freeMass (b:fO) (o:ℕ) :GM:= fun k =>
 (if o=(introduction b).length then (∑ q,originBudget b o q:ℕ) else 1)*freeCap b o (afterFree b) k
private theorem freeMass_eq (b:fO) (o:ℕ) :freeMass b o=originFreeCap b o:= by
 funext k
 by_cases h:o=(introduction b).length <;>
  simp only [freeMass,originFreeCap,isLast,h,ite_true,ite_false]
def freeRow (b:fO) (o:ℕ) :ℚ:=bEm (bookFree b o) (freeMass b o)
private def factorNum (b:fO) (o:ℕ) (q:Fin 3) :ℕ :=
 ∑ k,residualNum b o k * arC (originCutter b o) k q
private def runNum (b:fO) :ℕ→Fin 3→ℕ
 | 0,_=>0
 | o+1,q=>max (runNum b o q) (factorNum b o q)
private abbrev RNum:=0x8000000
private theorem factorNum_eq (b:fO) (o:ℕ) (q:Fin 3) :
  (factorNum b o q:ℚ)/RNum=factorUnit (lJ b o) (originCutter b o) q:= by
 simp only [factorNum,factorUnit,lJ,nX ,nq,sum_div,oq,RNum,n5]
private theorem runNum_eq (b:fO) (o:ℕ) (q:Fin 3) :
   (runNum b o q:ℚ)/RNum=mD b (lJ b) o q:= by
 induction o with
 | zero=>simp [runNum,factorRunning]
 | succ o ih =>
   simp only [runNum,mD,← ih,← factorNum_eq]
   have hf :Monotone (fun x :ℕ=>(x :ℚ)/RNum) :=
     fun _ _ h=>div_le_div_of_nonneg_right (by exact_mod_cast h) (by decide)
   exact hf.map_max
def factorRow (b:fO) (o:ℕ) :ℚ :=
 ((∑ q,(runNum b (o+1) q-runNum b o q)*originBudget b o q:ℕ) :ℚ)/RNum
private theorem factorRow_eq (b:fO) (o:ℕ) :factorRow b o =
   dotResources (fun q=>mD b (lJ b) (o+1) q -
     mD b (lJ b) o q) (originBudget b o) := by
 simp only [factorRow,dotResources,nX ,nq,sum_div]
 apply sum_congr rfl
 intro q _
 rw [Nat.cast_sub (show runNum b o q≤ runNum b (o+1) q from nI _ _),
   ← oq,sub_div,runNum_eq,runNum_eq]
def bankRow (b:fO) (i:Fin (cy b).length) :ℕ :=
 let s :=(cy b)[i.val]
 (p+1)*s.U+au1 b s.B s.J
def cIY (b:fO) :ℕ:=(p+1)*BC b 2+BC b 3+BC b 0+
 eHB b+1+akj+pointFee b
private theorem ceil_nat {x :ℚ} {n:ℕ} (h:x≤n) :x.ceil.toNat≤n:= by
 have hz :x.ceil≤(n:ℤ) := by
  rw [Rat.ceil_eq_neg_floor_neg]
  change -⌊-x⌋ ≤ _
  rw [Int.floor_neg,neg_neg]
  exact Int.ceil_le.mpr (by exact_mod_cast h)
 simpa using Int.toNat_le_toNat hz
def total (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>total f n+f n
private theorem asB (f :ℕ→ℕ) (n:ℕ) :total f n = ∑ i∈range n,f i:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,ih,sum_range_succ]
abbrev PNum:=0x10000
abbrev Z2 (n:ℕ) :ℚ:=(n:ℚ)/PNum
structure BudgetRows (b:fO) :Prop where
 seed : ∀ i:Fin (lz b-1),projectionRow b i≤Z2 (aU b 0 i)
 global : ∀ i:Fin (lz b),globalRow b i≤Z2 (aU b 1 i)
 free : ∀ o:Fin (c9 b),freeRow b o≤Z2 (aU b 2 o)
 factor : ∀ o:Fin (c9 b),factorRow b o≤Z2 (aU b 3 o)
 aV : ∀ i:Fin (cy b).length,bankRow b i≤aU b 4 i
 base :cIY b≤baseNum b
 a8u:total (aU b 0) (lz b-1)≤PNum*seedNum b
 small:seedNum b<p
 gH :PNum*(baseNum b+total (aU b 4) (cy b).length+seedNum b) +
  total (aU b 1) (lz b)+total (aU b 2) (c9 b) +
  total (aU b 3) (c9 b)≤PNum*(row b).prefixFee
private theorem sum_bound {n:ℕ} {f :ℕ→ℚ} {u:ℕ→ℕ}
  (h : ∀ i:Fin n,f i≤Z2 (u i)) :
  (∑ i∈range n,f i)≤Z2 (total u n) := by
 simp only [asB,Z2,nX ,sum_div]
 exact lV fun i hi=>h ⟨i,mem_range.mp hi⟩
theorem checked_budget {b:fO} (r :BudgetRows b) :
  lI b<p∧Ya b≤(row b).prefixFee := by
 have hs :lI b≤Z2 (total (aU b 0) (lz b-1)) := by
  refine le_trans ?_ (sum_bound r.seed)
  unfold lI XM
  apply lV
  intro i _
  rw [projectionRow,b08]
  exact a3x (fun _=>sub_nonneg.mpr (nI _ _)) (global_le b (i+1))
 have hp:lI b≤(seedNum b:ℚ) :=hs.trans <| by
  apply (div_le_iff₀ (by decide : (0:ℚ)<PNum)).mpr
  rw [mul_comm]
  exact_mod_cast r.a8u
 have hg: (∑ i∈stops b,FP (bookGlobal b i) (globalCap b i)) ≤
   Z2 (total (aU b 1) (lz b)) := by
  refine le_trans ?_ (sum_bound r.global)
  apply lV
  intro i _
  rw [globalRow,b08]
  exact a3x (fun _=>div_nonneg (Nat.cast_nonneg _) (by decide)) (global_le b i)
 have hf : (∑ o∈origins b,FP (bookFree b o) (originFreeCap b o)) ≤
   Z2 (total (aU b 2) (c9 b)) := by
  simpa only [origins,freeRow,b08,freeMass_eq] using sum_bound r.free
 have hfactor :factorBill b (lJ b)≤Z2 (total (aU b 3) (c9 b)) := by
  simpa only [factorBill,origins,factorRow_eq] using sum_bound r.factor
 have hb:bankFee b≤total (aU b 4) (cy b).length:= by
  rw [bankFee,← List.ofFn_getElem_eq_map,List.sum_ofFn,asB,← Fin.sum_univ_eq_sum_range]
  exact lV fun i _=>r.aV i
 have hbase :earlyFee b+pointFee b+(lI b).ceil.toNat ≤
   baseNum b+total (aU b 4) (cy b).length+seedNum b:= by
  have hc:=ceil_nat hp
  have he :=r.base
  simp only [cIY,earlyFee] at he ⊢
  omega
 refine ⟨hp.trans_lt (by exact_mod_cast r.small),?_⟩
 have hbase' : ((earlyFee b+pointFee b+(lI b).ceil.toNat :ℕ) :ℚ) ≤
   ((baseNum b+total (aU b 4) (cy b).length+seedNum b:ℕ) :ℚ) := by
  exact_mod_cast hbase
 have hsum:=oj (oj (oj hbase' hg) hf) hfactor
 unfold Ya
 refine hsum.trans ?_
 have htotal:=r.gH
 have htotal' : ((PNum*(baseNum b+total (aU b 4) (cy b).length+seedNum b) +
   total (aU b 1) (lz b)+total (aU b 2) (c9 b) +
   total (aU b 3) (c9 b) :ℕ) :ℚ)≤((PNum*(row b).prefixFee :ℕ) :ℚ) := by
  exact_mod_cast htotal
 simp only [Nat.cast_add,nq,n5 ,PNum] at htotal'
 simp only [Z2,PNum,Nat.cast_add,n5]
 linarith only [htotal']
end qB9xHGe

import ProximityPrize.SubmissionLower.PrimaryTaperRank

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

namespace TaperBudget

open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

def cap (q : ℕ) : ℕ :=
  if q < 3514 then 1650 else (131312 - 26*q) / 25

theorem cap_antitone : Antitone cap := by
  intro a b hab
  unfold cap
  split <;> split <;> omega

def valuePower (capAtGrade q j : ℕ) : ℕ :=
  min capAtGrade (3000+capAtGrade - q - 4*j)

def power (i : BlockIndex) : Fin 11 → ℕ :=
  (⟨valuePower (cap i.1.val) i.1.val i.2.val,0,0⟩:Powers).expand

def tailSaving (i : BlockIndex) : ℕ :=
  if 3514≤ i.1.val then baseline i - TaperNormalize.bound (cap i.1.val) i (power i)
  else 0

def valueRowCell (s j : ℕ) : ℕ :=
  if hs : s < 499 then if hj : j < 1136 then
    tailSaving (⟨3514+s,by omega⟩,⟨j,by omega⟩)
  else 0 else 0

def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumRange f n+f n

def valueRow (s:ℕ):ℕ:=sumRange (valueRowCell s) 1136


open K1_13_2_3_7 (fastCum signedKernel)
open private chart oldCount_eq kernel_eq residual_eq zero_residual blockBound_eq
  from ProximityPrize.SubmissionLower.Fast060
open private residualDegree from ProximityPrize.SubmissionLower.PrimaryTaperRank

def fastRank (d j : ℕ) (h : ℤ) (p : ℕ) : ℕ :=
  if h < 0 then 0 else
    (fastCum d 1650 - fastCum d (1649 - (j : ℤ)) -
      max 0 (max (signedKernel d j h) (signedKernel ((d:ℤ) - p) j h))).toNat

theorem tapered_rank_eq_fast (k p : ℕ) (i : BlockIndex) (hq : 3514 ≤ i.1.val) (hk : k ≤ i.1.val) (hp : p ≤ k) :
    TaperNormalize.bound k i (Powers.expand ⟨p, 0, 0⟩) =
      fastRank k i.2.val (4649 - (i.1.val:ℤ) - i.2.val) p:=by
  let h:ℤ:=4649 - (i.1.val:ℤ) - i.2.val
  let f:=chart k i.2.val h
  have hf : TaperNormalize.initialFlag k i = f := by
    simp [TaperNormalize.initialFlag,initialFlag,residualDegree,f,chart,h,offset,min_eq_right hk]
    omega
  have hA : TaperNormalize.activeFlag k i =
      { f with upper:=min 1650 (2999 - offset i) } := by
    simp [TaperNormalize.activeFlag, K1_13_2_2.activeFlag, initialFlag, residualDegree, f, chart, h,
      offset,min_eq_right hk]
    omega
  have hOrder:f.order=h+1:=rfl
  have hj:(0:ℤ)≤ i.2.val:=Int.natCast_nonneg _
  unfold TaperNormalize.bound fastRank
  rw [hf,hA]
  simp only
  rw [hOrder]
  by_cases hh:h < 0
  · rw [ite_eq_left (show h+1≤0 by omega),ite_eq_left hh]
  · rw [ite_eq_right (show ¬h+1 ≤ 0 by omega), ite_eq_right hh]
    have hU : min (1650 : ℤ) (2999 - offset i) = 1650 := by
      rw [min_eq_left]
      unfold offset h at *
      omega
    rw [hU]
    change (min (oldCount f) _).toNat=_
    have hn := le_max_left (0 : ℤ)
      (max (kernelLower f) (kernelLower (residualFlag f (Powers.expand ⟨p,0,0⟩))))
    rw [min_eq_right (by omega)]
    rw [show residualFlag f (Powers.expand ⟨p, 0, 0⟩) =
      chart ((k:ℤ)-p) i.2.val h from residual_eq _ _ _ _]
    rw [oldCount_eq _ _ _ hj, kernel_eq _ _ _ (Int.natCast_nonneg _) hj,
      kernel_eq _ _ _ (by omega) hj]

def fastCell (t j : ℕ) : ℕ :=
  let q:=3514+t
  let h:ℤ:=1135 - (t:ℤ) - j
  let d:=cap q
  fastRank 1650 j h 0 - fastRank d j h (valuePower d q j)

theorem old_flag_eq (i : BlockIndex) :
    TaperNormalize.initialFlag 1650 i=initialFlag i:=by
  have hmin:((min i.1.val 1650:ℕ):ℤ)=min (i.1.val:ℤ) 1650:=by omega
  simp [TaperNormalize.initialFlag,residualDegree,initialFlag,hmin]

theorem old_bound_eq (i : BlockIndex) (p : Fin 11 → ℕ) :
    TaperNormalize.bound 1650 i p=blockBound i p:=by
  have hA : TaperNormalize.activeFlag 1650 i = K1_13_2_2.activeFlag i := by
    have hmin:((min i.1.val 1650:ℕ):ℤ)=min (i.1.val:ℤ) 1650:=by omega
    simp [TaperNormalize.activeFlag,K1_13_2_2.activeFlag,residualDegree,initialFlag,hmin]
  simp only [TaperNormalize.bound,old_flag_eq,hA,blockBound]
  rfl

private theorem power_zero : (Powers.expand ⟨0, 0, 0⟩) = (fun _ => 0) := by
  funext x
  fin_cases x <;> rfl

theorem fastCell_eq {t j : ℕ} (ht : t < 499) (hj : j < 1136) :
    fastCell t j=valueRowCell t j:=by
  let i:BlockIndex:=(⟨3514+t,by omega⟩,⟨j,by omega⟩)
  have hq:i.1.val=3514+t:=rfl
  have hji:i.2.val=j:=rfl
  have hgrade:3514≤ i.1.val:=by omega
  have hd:cap i.1.val≤ i.1.val:=by simp [cap,show ¬ i.1.val < 3514 by omega]; omega
  let p:=valuePower (cap i.1.val) i.1.val i.2.val
  have hp:p≤cap i.1.val:=min_le_left _ _
  have ho:=tapered_rank_eq_fast 1650 0 i hgrade (by omega) (by omega)
  rw [power_zero,old_bound_eq] at ho
  have hn:=tapered_rank_eq_fast (cap i.1.val) p i hgrade hd hp
  unfold valueRowCell
  rw [dite_eq_left ht,dite_eq_left hj]
  change fastCell t j=tailSaving i
  rw [tailSaving,ite_eq_left hgrade]
  change fastCell t j=blockBound i (fun _ => 0) - TaperNormalize.bound (cap i.1.val) i (Powers.expand ⟨p,0,0⟩)
  rw [ho,hn]
  have hh : (4649 - (i.1.val : ℤ) - i.2.val) = 1135 - (t : ℤ) - j := by
    rw [hq,hji]
    push_cast
    ring
  rw [hh]
  rfl

def fastSavings (J : ℕ) : ℕ :=
  sumRange (fun t => sumRange (fastCell t) J) 499

private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ k ∈ Finset.range n,f k:=by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange,Finset.sum_range_succ,ih]

private theorem sumRange_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ k:Fin n,f k.val:=by
  rw [sumRange_eq,Fin.sum_univ_eq_sum_range]

private def windowEmbed {J : ℕ} (hJ : J ≤ 1136) : Fin 499 × Fin J ↪ BlockIndex where
  toFun i:=(⟨3514+i.1.val,by have:=i.1.isLt; omega⟩,i.2.castLE (by omega))
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have e := congrArg (fun i : BlockIndex => i.1.val) h
      change 3514+x.1.val=3514+y.1.val at e
      omega
    · exact congrArg (fun i:BlockIndex => i.2.val) h

open private sum_embed_le from ProximityPrize.SubmissionLower.Fast068

theorem fastSavings_le {J : ℕ} (hJ : J ≤ 1136) :
    fastSavings J ≤ ∑ i:BlockIndex,tailSaving i:=by
  unfold fastSavings
  simp only [sumRange_fin]
  rw [← Finset.sum_product Finset.univ Finset.univ (fun x : Fin 499 × Fin J => fastCell x.1.val x.2.val),
    Finset.univ_product_univ]
  calc
    _ = ∑ x : Fin 499 × Fin J, tailSaving (windowEmbed hJ x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [fastCell_eq x.1.isLt (LT.lt.trans_le x.2.isLt hJ)]
      simp only [valueRowCell,dite_eq_left x.1.isLt,dite_eq_left (LT.lt.trans_le x.2.isLt hJ)]
      rfl
    _≤_:=sum_embed_le (windowEmbed hJ) tailSaving


open K1_13_2_3_7 (countParts natKernel)
open private countParts_eq partValue natKernel_signed
  from ProximityPrize.SubmissionLower.Fast068

def natOld (d j : ℕ) : ℕ :=
  let hi:=countParts d 1651
  let lo:=countParts d (1650 - j)
  hi.1+lo.2 - (hi.2+lo.1)

private theorem old_eq (d j : ℕ) :
    natOld d j=(fastCum d 1650 - fastCum d (1649 - (j:ℤ))).toNat:=by
  have hi:=countParts_eq d 1650
  have lo:=countParts_eq d (1649 - (j:ℤ))
  change partValue (countParts d 1651)=_ at hi
  rw [show (1649 - (j:ℤ)+1).toNat=1650 - j by omega] at lo
  unfold partValue at hi lo
  simp only [natOld]
  omega

private def removed (d q:ℕ):ℕ:=(3003+d - q) / 4

private theorem natKernel_eq_for (d q j : ℕ) (hq : 3514 ≤ q) (hj : q + j < 4650)
    (hD:d≤1650) :
    natKernel d j (4650 - q - j) (removed d q) =
      (signedKernel d j (4649 - (q:ℤ) - j)).toNat:=by
  let h:=4650 - q - j
  have hh:(h:ℤ) - 1=4649 - (q:ℤ) - j:=by dsimp [h]; omega
  rw [← hh]
  have hb:(h:ℤ) - 1 - (1650 - j)+d=2999+(d:ℤ) - q:=by omega
  apply natKernel_signed
  · unfold removed; omega
  · rw [hb]; unfold removed; omega
  · intro hr
    rw [hb,min_eq_right (by omega)]
    unfold removed at *
    omega

def rankNat (d q j p : ℕ) : ℕ :=
  if q + j < 4650 then
    let h:=4650 - q - j
    natOld d j - max (natKernel d j h (removed d q))
      (natKernel (d - p) j h (removed (d - p) q))
  else 0

theorem rankNat_eq (d q j p : ℕ) (hq : 3514 ≤ q) (hD : d ≤ 1650) (hp : p ≤ d) :
    rankNat d q j p=fastRank d j (4649 - (q:ℤ) - j) p:=by
  unfold rankNat fastRank
  by_cases hj:q+j < 4650
  · rw [ite_eq_left hj, ite_eq_right (by omega)]
    simp only
    rw [old_eq, natKernel_eq_for d q j hq hj hD,
      natKernel_eq_for (d-p) q j hq hj (by omega),Nat.cast_sub hp]
    omega
  · rw [ite_eq_right hj,ite_eq_left (by omega)]

def natCell (t j : ℕ) : ℕ :=
  let q:=3514+t
  let d:=cap q
  rankNat 1650 q j 0 - rankNat d q j (valuePower d q j)

theorem natCell_eq (t j : ℕ) : natCell t j = fastCell t j := by
  have hd:cap (3514+t)≤1650:=by unfold cap; split <;> omega
  have hp:valuePower (cap (3514+t)) (3514+t) j≤cap (3514+t):=min_le_left _ _
  unfold natCell fastCell
  simp only
  rw [rankNat_eq 1650 (3514+t) j 0 (by omega) (by decide) (by decide),
    rankNat_eq (cap (3514+t)) (3514+t) j _ (by omega) hd hp]
  push_cast
  rw [show (4649:ℤ) - (3514+t) - j=1135 - t - j by omega]

def natRow (t:ℕ):ℕ:=sumRange (natCell t) (1136-t)


def sumChunk (f : ℕ → ℕ) (lo n : ℕ) : ℕ :=
  sumRange (fun i => f (lo+i)) n

theorem sumChunk_add (f : ℕ → ℕ) (lo n m : ℕ) :
    sumChunk f lo (n+m)=sumChunk f lo n+sumChunk f (lo+n) m:=by
  induction m with
  | zero => simp [sumChunk,sumRange]
  | succ m ih =>
      rw [Nat.add_succ]
      change sumChunk f lo (n+m) + f (lo+(n+m)) =
        sumChunk f lo n+(sumChunk f (lo+n) m+f ((lo+n)+m))
      rw [ih]
      simp only [Nat.add_assoc]

def rowSum (J t:ℕ):ℕ:=sumRange (natCell t) J

theorem sumChunk_eq_fastSavings (J : ℕ) : sumChunk (rowSum J) 0 499 = fastSavings J := by
  unfold sumChunk fastSavings rowSum
  simp only [sumRange_eq,Nat.zero_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact natCell_eq _ _

open private combine baseline_budget_on sum_add_pointwise_eq bound_le_baseline savings_parts
  from ProximityPrize.SubmissionLower.Fast022

private def fees (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if i.1.val < 3514 then blockBound i (combine p₁ p₂ p₃ (fun _ => ⟨0,0,0⟩) i).expand
  else min (baseline i) (TaperNormalize.bound (cap i.1.val) i (power i))

private theorem fees_le_baseline (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    fees p₁ p₂ p₃ i≤baseline i:=by
  unfold fees
  split
  · exact bound_le_baseline _ _
  · exact min_le_left _ _



private abbrev zeroPowers:BlockIndex→Powers:=fun _ => ⟨0,0,0⟩

private theorem saved_pointwise (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    savings i (combine p₁ p₂ p₃ zeroPowers i)+tailSaving i≤baseline i - fees p₁ p₂ p₃ i:=by
  by_cases hi:i.1.val < 3514
  · simp [fees,tailSaving,hi,show ¬3514≤ i.1.val by omega,savings]
  · have h₁ : ¬i.1.val < 2008 := by omega
    have h₂ : ¬i.1.val < 3012:=by omega
    simp only [combine, h₁, h₂, hi, ite_false, zeroPowers, savings, power_zero, show blockBound i (fun _ => 0) = baseline i by rfl,
      Nat.sub_self,Nat.zero_add,fees,tailSaving,show 3514≤ i.1.val by omega,ite_true]
    exact Nat.sub_le_sub_left (min_le_right _ _) _

private theorem saved_on (S : Finset BlockIndex) (p₁ p₂ p₃ : BlockIndex → Powers) :
    (∑ i ∈ S, savings i (combine p₁ p₂ p₃ zeroPowers i)) + (∑ i ∈ S, tailSaving i) ≤
      ∑ i ∈ S,(baseline i - fees p₁ p₂ p₃ i):=by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum (s:=S)
  intro i _
  exact saved_pointwise p₁ p₂ p₃ i

private theorem saved_by_fees (p₁ p₂ p₃ : BlockIndex → Powers) :
    savingsSum w1 p₁ + savingsSum w2 p₂ + savingsSum w3 p₃ + (∑ i : BlockIndex, tailSaving i) ≤
      ∑ i:BlockIndex,(baseline i - fees p₁ p₂ p₃ i):=by
  have h₀ : savingsSum w4 zeroPowers = 0 := by
    unfold savingsSum
    apply Finset.sum_eq_zero
    intro i _
    simp [zeroPowers,savings,power_zero,baseline]
  have h:=savings_parts p₁ p₂ p₃ zeroPowers
  rw [h₀,Nat.add_zero] at h
  exact (Nat.add_le_add_right h _).trans (saved_on Finset.univ p₁ p₂ p₃)

end TaperBudget

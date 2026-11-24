import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinParity

-- merged module Low48PrimaryPivotBinWeight
section Merged_Low48PrimaryPivotBinWeight

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open Low48PrimaryPivot (band_card)
open Low48PrimaryPivot (binWeight)

def qMin (w : Window) : ℤ := 4650-(w.diagonalHi : ℤ)

private def gradeOK (w : Window) (q l : ℤ) : Prop :=
  (w.gradeLo : ℤ)-3000 ≤ l-q ∧ l-q < (w.gradeHi : ℤ)-3000

private instance (w : Window) (q l : ℤ) : Decidable (gradeOK w q l) := by
  unfold gradeOK
  infer_instance

private theorem weight_card (w : Window) (p : Triple) (q : ℤ) :
    (((Ico (indexLo w) (indexHi w p)).filter (gradeOK w q)).card : ℤ) =
      binWeight w p.index q := by
  let hi := min ((p.index : ℤ)+1) (1651-(w.offsetLo : ℤ))
  let lo := indexLo w
  have eq : ((Ico lo (indexHi w p)).filter (gradeOK w q)) =
      Ico (max lo (q+(w.gradeLo : ℤ)-3000)) (min hi (q+(w.gradeHi : ℤ)-3000)) := by
    ext l
    simp only [mem_filter,mem_Ico,gradeOK,max_le_iff,lt_min_iff]
    have hhi : indexHi w p = max lo hi := by
      simp [indexHi,lo,hi,min_comm]
    rw [hhi]
    omega
  rw [show indexLo w = lo by rfl,eq,Int.card_Ico]
  simp only [binWeight,indexLo,lo,hi]
  omega

private def weightGrid (w : Window) (p : Triple) : Finset (ℤ × ℤ) :=
  ((Ico (qMin w) (orderHi w)).product (Ico (indexLo w) (indexHi w p))).filter
    (fun x => (p.contact : ℤ) < x.1 ∧ gradeOK w x.1 x.2)

private def columnGrid (w : Window) (p : Triple) : Finset (ℤ × ℤ) :=
  ((Ico (indexLo w) (indexHi w p)).product (Ico (orderLo w p) (orderHi w))).filter
    (fun x => gradeOK w x.2 x.1)

private theorem swap_grids (w : Window) (p : Triple) :
    (columnGrid w p).card = (weightGrid w p).card := by
  refine Finset.card_bij (fun x _ => (x.2,x.1)) ?_ ?_ ?_
  · rintro ⟨l,q⟩ h
    obtain ⟨hp, hg⟩ := Finset.mem_filter.mp h
    obtain ⟨hl, hq⟩ := Finset.mem_product.mp hp
    have ho := Finset.mem_Ico.mp hq
    simp only [orderLo] at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ?_, hl⟩, ?_, hg⟩
    · unfold qMin; omega
    · omega
  · rintro ⟨l,q⟩ _ ⟨l',q'⟩ _ h
    cases h
    rfl
  · rintro ⟨q,l⟩ h
    refine ⟨(l,q),?_,rfl⟩
    obtain ⟨hp, hc, hg⟩ := Finset.mem_filter.mp h
    obtain ⟨hq,hl⟩ := Finset.mem_product.mp hp
    have ho := Finset.mem_Ico.mp hq
    unfold qMin at ho
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hl,Finset.mem_Ico.mpr ?_⟩,hg⟩
    unfold orderLo
    omega

theorem columnFee2_eq_bins (w : Window) (p : Triple) (hg : w.gradeLo ≤ w.gradeHi)
    (hp : p.index ≤ 1650) :
    columnFee2 w p = 2*(∑ q ∈ Ico (qMin w) (orderHi w),
      if (p.contact : ℤ) < q then binWeight w p.index q else 0) := by
  have hband := band_card (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
    ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
    (le_max_left _ _) (min_le_left _ _) (by omega)
  change 2*((columnGrid w p).card : ℤ) = _ at hband
  rw [columnFee2,ite_eq_left hp,← hband,swap_grids]
  unfold weightGrid
  rw [natCast_card_filter]
  have hprod := sum_product (Ico (qMin w) (orderHi w)) (Ico (indexLo w) (indexHi w p))
    (fun x : ℤ × ℤ => if (p.contact : ℤ) < x.1 ∧ gradeOK w x.1 x.2 then (1 : ℤ) else 0)
  refine (congrArg (fun z : ℤ => 2*z) hprod).trans ?_
  congr 1
  apply sum_congr rfl
  intro q _
  by_cases hc : (p.contact : ℤ) < q
  · simp only [hc,true_and,ite_true]
    rw [← natCast_card_filter,weight_card]
  · simp [hc]

#print axioms columnFee2_eq_bins
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinWeight

-- merged module Low48PrimaryPivotBinIndex
section Merged_Low48PrimaryPivotBinIndex

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators

def indexFiber (j : ℕ) : Finset Column :=
  univ.filter (fun col => (columnPoint col).index = j)

attribute [local irreducible] Finset.univ

theorem mem_indexFiber {j : ℕ} {col : Column} :
    col ∈ indexFiber j ↔ (columnPoint col).index = j := by
  simp only [indexFiber,mem_filter,mem_univ,true_and]

private def fRange (j : ℕ) : Finset ℤ := Ico 0 ((j : ℤ)/3+1)

private def cRange (j : ℕ) (f : ℤ) : Finset ℤ := Ico 0 (sectionWidth j f.toNat)

private def fromBin (j : ℕ) (f c : ℤ) : Triple :=
  ⟨j-2*c.toNat-3*f.toNat,c.toNat,f.toNat⟩

private theorem fromBin_index {j : ℕ} {f c : ℤ} (_hf : f ∈ fRange j) (hc : c ∈ cRange j f) :
    (fromBin j f c).index = j := by
  rw [cRange,mem_Ico] at hc
  simp only [sectionWidth] at hc
  have hco : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.1
  simp only [fromBin,Triple.index]
  omega

private theorem indexFiber_sum (j : ℕ) (hj : j ≤ 1650) (term : Triple → ℤ) :
    (∑ col ∈ indexFiber j, term (columnPoint col)) =
      ∑ f ∈ fRange j, ∑ c ∈ cRange j f, term (fromBin j f c) := by
  rw [sum_sigma']
  let position (col : Column) : Sigma (fun _ : ℤ => ℤ) := ⟨col.1.val,col.2.1.val⟩
  refine sum_bij (fun col _ => position col) ?_ ?_ ?_ ?_
  · intro col hcol
    have hkey := mem_indexFiber.mp hcol
    simp only [columnPoint,Triple.index] at hkey
    simp only [position,mem_sigma,fRange,cRange,mem_Ico,sectionWidth,Int.toNat_natCast]
    omega
  · intro col hcol other hother hpos
    have hf := congrArg Sigma.fst hpos
    have hc := congrArg (fun p : Sigma (fun _ : ℤ => ℤ) => p.snd) hpos
    simp only [position,Int.natCast_inj] at hf hc
    have hb := mem_indexFiber.mp hcol
    have hb' := mem_indexFiber.mp hother
    simp only [columnPoint,Triple.index] at hb hb'
    exact Prod.ext (Fin.ext hf) (Prod.ext (Fin.ext hc) (Fin.ext (by omega)))
  · rintro ⟨f,c⟩ hx
    obtain ⟨hf,hc⟩ := mem_sigma.mp hx
    change f ∈ fRange j at hf
    change c ∈ cRange j f at hc
    have hidx := fromBin_index hf hc
    have hf' := mem_Ico.mp hf
    have hc' := mem_Ico.mp hc
    let col : Column := (⟨f.toNat, by unfold fRange at hf; rw [mem_Ico] at hf; omega⟩,
      ⟨c.toNat, by
        have ho := hc'.2
        change c < sectionWidth j f.toNat at ho
        simp only [sectionWidth] at ho
        omega⟩,
      ⟨(fromBin j f c).b, by simp [fromBin]; omega⟩)
    refine ⟨col,mem_indexFiber.mpr ?_,?_⟩
    · exact hidx
    · change (⟨(f.toNat : ℤ),(c.toNat : ℤ)⟩ : Sigma (fun _ : ℤ => ℤ)) = ⟨f,c⟩
      rw [Int.toNat_of_nonneg hf'.1, Int.toNat_of_nonneg hc'.1]
  · intro col hcol
    have hb := mem_indexFiber.mp hcol
    simp only [columnPoint,Triple.index] at hb
    apply congrArg term
    simp only [columnPoint,fromBin,position,Int.toNat_natCast]
    congr 1
    omega

theorem indexFiber_card (j : ℕ) (hj : j ≤ 1650) :
    ((indexFiber j).card : ℤ) = totalAtIndex j := by
  have he := indexFiber_sum j hj (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at he
  rw [he,totalAtIndex_eq]
  apply sum_congr rfl
  intro f hf
  have hF := (mem_Ico.mp hf)
  change 0 ≤ f ∧ f < (j:ℤ)/3+1 at hF
  simp only [cRange,Int.card_Ico,sub_zero,sectionWidth,Int.toNat_of_nonneg hF.1]
  omega

theorem uncharged_card (j : ℕ) (q : ℤ) (hj : j ≤ 1650) :
    (((indexFiber j).filter fun col => q ≤ ((columnPoint col).contact : ℤ)).card : ℤ) =
      uncharged j q := by
  rw [natCast_card_filter]
  have he := indexFiber_sum j hj (fun p => if q ≤ (p.contact : ℤ) then 1 else 0)
  rw [he,uncharged_eq]
  let cost (f : ℤ) := max 0 ((j-3*f)/2+1 -
    max 0 (max (3*q-9900+5*j-3*f) (max (q-4950+3*j-2*f) (2*q-4950+2*j-f))))
  have sectionEq (f : ℤ) (hf : f ∈ fRange j) :
      (∑ c ∈ cRange j f, if q ≤ ((fromBin j f c).contact : ℤ) then (1 : ℤ) else 0) =
        if f ≤ 1650-q then cost f else 0 := by
    have hf0 := (mem_Ico.mp hf).1
    by_cases hF : f ≤ 1650-q
    · rw [ite_eq_left hF,← natCast_card_filter]
      have hfn : (f.toNat : ℤ) = f := Int.toNat_of_nonneg hf0
      have hsum : 3*f.toNat ≤ j := by
        unfold fRange at hf
        rw [mem_Ico] at hf
        omega
      have hrow := section_count j f.toNat q (by rwa [hfn]) hj hsum
      simpa only [cRange,fromBin,sectionWidth,sectionFloor,hfn,cost] using hrow
    · rw [ite_eq_right hF]
      apply sum_eq_zero
      intro c hc
      have hkey := fromBin_index hf hc
      have hb : (fromBin j f c).index ≤ 1650 := hkey.trans_le hj
      have hF' : ¬q ≤ ((fromBin j f c).contact : ℤ) := by
        intro hd
        have hlo := ((contact_ge_iff _ _ hb).mp hd).1
        apply hF
        simpa [fromBin,Int.toNat_of_nonneg hf0] using hlo
      rw [ite_eq_right hF']
  calc
    _ = ∑ f ∈ fRange j, if f ≤ 1650-q then cost f else 0 :=
      sum_congr rfl sectionEq
    _ = ∑ f ∈ (fRange j).filter (fun f => f ≤ 1650-q), cost f := (sum_filter ..).symm
    _ = _ := by
      have hs : (fRange j).filter (fun f => f ≤ 1650-q) =
          Ico 0 (min ((j : ℤ)/3) (1650-q)+1) := by
        ext f
        simp only [fRange,mem_filter,mem_Ico]
        omega
      rw [hs]

#print axioms indexFiber_card
#print axioms uncharged_card
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinIndex

-- merged module Low48PrimaryPivotBinAggregate
section Merged_Low48PrimaryPivotBinAggregate

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open Low48PrimaryPivot (qMin)
open Low48PrimaryPivot (binWeight)
open Low48PrimaryPivot (mem_indexFiber)

attribute [local irreducible] Finset.univ

theorem binAt_eq_interval (w : Window) (j : ℕ) :
    binAt w j = ∑ q ∈ Ico (qMin w) (orderHi w),
      binWeight w j q * (totalAtIndex j-uncharged j q) := by
  rw [Int.Ico_eq_finset_map,sum_map]
  have hsize : (orderHi w-qMin w).toNat = w.diagonalHi+1-w.diagonalLo := by
    simp only [orderHi,qMin]
    omega
  unfold binAt
  change (∑ i ∈ range (w.diagonalHi+1-w.diagonalLo),
      if binWeight w j (qMin w+(i : ℤ)) = 0 then 0
      else binWeight w j (qMin w+(i : ℤ)) *
        (totalAtIndex j-uncharged j (qMin w+(i : ℤ)))) = _
  rw [hsize]
  apply sum_congr rfl
  intro i _
  change _ = binWeight w j (qMin w+(i : ℤ)) *
    (totalAtIndex j-uncharged j (qMin w+(i : ℤ)))
  split
  · rename_i h
    rw [h,zero_mul]
  · rfl

private theorem paid_count (j : ℕ) (q : ℤ) (hj : j ≤ 1650) :
    (∑ c ∈ indexFiber j, if ((columnPoint c).contact : ℤ) < q then (1 : ℤ) else 0) =
      totalAtIndex j-uncharged j q := by
  have point (c : Column) :
      (if ((columnPoint c).contact : ℤ) < q then (1 : ℤ) else 0) =
        1-(if q ≤ ((columnPoint c).contact : ℤ) then 1 else 0) := by
    by_cases h : ((columnPoint c).contact : ℤ) < q
    · simp [h, not_le.mpr h]
    · simp [h,le_of_not_gt h]
  simp_rw [point]
  rw [sum_sub_distrib,← natCast_card_filter,uncharged_card j q hj]
  simp [indexFiber_card j hj]

private theorem index_fee (w : Window) (j : ℕ) (hj : j ≤ 1650) (hg : w.gradeLo ≤ w.gradeHi) :
    (∑ c ∈ indexFiber j, columnFee2 w (columnPoint c)) = 2*binAt w j := by
  have expand (c : Column) (hc : c ∈ indexFiber j) :
      columnFee2 w (columnPoint c) =
        2*(∑ q ∈ Ico (qMin w) (orderHi w),
          if ((columnPoint c).contact : ℤ) < q then binWeight w j q else 0) := by
    have hkey := mem_indexFiber.mp hc
    rw [columnFee2_eq_bins w _ hg (hkey.trans_le hj),hkey]
  rw [sum_congr rfl expand,← mul_sum,sum_comm,binAt_eq_interval]
  congr 1
  apply sum_congr rfl
  intro q _
  have hp (c : Column) :
      (if ((columnPoint c).contact : ℤ) < q then binWeight w j q else 0) =
        binWeight w j q * (if ((columnPoint c).contact : ℤ) < q then 1 else 0) := by
    split <;> simp
  simp_rw [hp]
  rw [← mul_sum,paid_count j q hj]

def binCompute (w : Window) : ℤ := ((List.range 1651).map (binAt w)).sum

theorem fee_eq_binCompute (w : Window) (hg : w.gradeLo ≤ w.gradeHi) :
    (∑ c : Column, columnFee2 w (columnPoint c)) = 2*binCompute w := by
  let idx (c : Column) := (columnPoint c).index
  let chargeAt (c : Column) := columnFee2 w (columnPoint c)
  have hs : (∑ c : Column, chargeAt c) = ∑ c ∈ univ with idx c ∈ range 1651, chargeAt c := by
    rw [sum_filter]
    apply sum_congr rfl
    intro c _
    by_cases hc : idx c ∈ range 1651
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc]
      simp only [mem_range] at hc
      exact ite_eq_right (by change ¬idx c≤1650; omega)
  change (∑ c : Column, chargeAt c) = _
  rw [hs,← sum_fiberwise_eq_sum_filter univ (range 1651) idx chargeAt]
  unfold binCompute
  change (∑ j ∈ range 1651, ∑ c ∈ indexFiber j, columnFee2 w (columnPoint c)) =
      2*(∑ j ∈ range 1651, binAt w j)
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  exact index_fee w j (by have h := mem_range.mp hj; omega) hg

theorem debit_le_binCompute (w : Window) (hg : w.gradeLo ≤ w.gradeHi) :
    (debit w : ℤ) ≤ binCompute w := by
  have h := debit_le_fee w hg
  rw [fee_eq_binCompute w hg] at h
  omega

#print axioms debit_le_binCompute
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinAggregate

-- merged module Low48PrimaryPivotBinsFast
section Merged_Low48PrimaryPivotBinsFast

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

set_option maxRecDepth 4096

namespace Low48PrimaryPivot.Hinge
open K1_13_2_3

def series (a k n : ℕ) : ℕ := n*a - k*(n*(n-1)/2)

-- Sum of floor((a-3*i)/2) for 0 <= i < n, with a >= 3*(n-1).
-- The odd-term count is floor((n + a%2)/2).
def widths (a n : ℕ) : ℕ := (series a 3 n - (n+a%2)/2)/2

def total (j : ℕ) : ℕ := widths (j+2) (j/3+1)

def keep (j q : ℕ) : ℕ :=
  let b := q+3*j-4950
  let c := 2*q+2*j-4950
  let lo := max (2*b-(j+2)) ((2*(b+c)-j)/3)
  let hi := min (min (j/3+1) (1651-q)) (j+3-2*c)
  let n := hi-lo
  if n=0 then 0 else
    let nb := min n ((b+1)/2-lo)
    let nc := min n (c-lo)
    widths (j+2-3*lo) n - series (b-2*lo) 2 nb - series (c-lo) 1 nc

def volume (w : Window) (j q : ℕ) : ℕ :=
  min (min (j+3001) (4651-w.offsetLo)) (q+w.gradeHi) -
    max (4650-w.offsetHi) (q+w.gradeLo)

def sweep (w : Window) (j tot lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 =>
    let q := lo+n
    let v := volume w j q
    sweep w j tot lo n + v*(tot-keep j q)

def index (w : Window) (j : ℕ) : ℕ :=
  let lo := max (4650-w.diagonalHi) (4651-w.offsetHi-w.gradeHi)
  let hi := min (4651-w.diagonalLo) (min (j+3001) (4651-w.offsetLo)-w.gradeLo)
  sweep w j (total j) lo (hi-lo)

end Low48PrimaryPivot.Hinge

namespace Low48PrimaryPivot.Hinge
open Finset K1_13_2_3
open scoped BigOperators

private theorem triangle_next (n : ℕ) :
    (n+1)*((n+1)-1)/2 = n*(n-1)/2+n := by
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one]
    have h : (n+1+1)*(n+1) = (n+1)*n+2*(n+1) := by ring
    omega

private theorem series_next (a k n : ℕ) (h : k*n ≤ a) :
    series a k (n+1) = series a k n + (a-k*n) := by
  have ht : n*(n-1)/2 ≤ n*n :=
    (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have hb : k*(n*(n-1)/2) ≤ n*a := calc
    _ ≤ k*(n*n) := Nat.mul_le_mul_left _ ht
    _ = n*(k*n) := by ring
    _ ≤ n*a := Nat.mul_le_mul_left _ h
  unfold series
  rw [triangle_next, Nat.mul_add, Nat.add_mul, one_mul]
  omega

private theorem series_eq (a k n : ℕ) (h : n=0 ∨ k*(n-1) ≤ a) :
    series a k n = ∑ i ∈ range n, (a-k*i) := by
  induction n with
  | zero => simp [series]
  | succ n ih =>
    have h' : k*n ≤ a := by simpa using h
    have hs : k*(n-1) ≤ a := (Nat.mul_le_mul_left _ (Nat.sub_le ..)).trans h'
    rw [series_next a k n h',sum_range_succ,ih (Or.inr hs)]

private theorem odd_sum (a n : ℕ) (h : n=0 ∨ 3*(n-1) ≤ a) :
    2*(∑ i ∈ range n, (a-3*i)/2) + (n+a%2)/2 = series a 3 n := by
  induction n with
  | zero => simp [series]
  | succ n ih =>
    have h' : 3*n ≤ a := by simpa using h
    have hs : 3*(n-1) ≤ a := by omega
    rw [series_next a 3 n h',sum_range_succ,← ih (Or.inr hs)]
    omega

private theorem widths_eq (a n : ℕ) (h : n=0 ∨ 3*(n-1) ≤ a) :
    widths a n = ∑ i ∈ range n, (a-3*i)/2 := by
  have he := odd_sum a n h
  unfold widths
  omega

private def cell (j b c f : ℕ) : ℕ :=
  (j+2-3*f)/2 - (b-2*f) - (c-f)

private def lower (j b c : ℕ) : ℕ :=
  max (2*b-(j+2)) ((2*(b+c)-j)/3)

private def upper (j c F : ℕ) : ℕ := min F (j+3-2*c)

private theorem within (j b c F f : ℕ) (hF : F≤j/3+1)
    (hl : lower j b c ≤ f) (hh : f<upper j c F) :
    cell j b c f + (b-2*f) + (c-f) = (j+2-3*f)/2 := by
  unfold lower at hl
  unfold upper at hh
  unfold cell
  omega

private theorem outside (j b c F f : ℕ) (hF : F≤j/3+1) (hf : f<F)
    (hout : ¬(lower j b c ≤ f ∧ f<upper j c F)) : cell j b c f = 0 := by
  unfold lower upper at hout
  unfold cell
  omega

private theorem truncated_series (a k n m : ℕ) (hm : m≤n)
    (ha : m=0 ∨ k*(m-1)≤a) (hz : ∀ i : ℕ, m ≤ i → a ≤ k*i) :
    ∑ i ∈ range n, (a-k*i) = series a k m := by
  rw [series_eq a k m ha]
  symm
  apply sum_subset (range_mono hm)
  intro i _ hi
  apply Nat.sub_eq_zero_of_le
  exact hz i (by simpa using hi)

private theorem cell_sum (j b c F : ℕ) (hF : F≤j/3+1) :
    let lo := lower j b c
    let n := upper j c F - lo
    let nb := min n ((b+1)/2-lo)
    let nc := min n (c-lo)
    (∑ f ∈ range F, cell j b c f) =
      if n=0 then 0 else
        widths (j+2-3*lo) n - series (b-2*lo) 2 nb - series (c-lo) 1 nc := by
  let lo := lower j b c
  let hi := upper j c F
  let n := hi-lo
  let nb := min n ((b+1)/2-lo)
  let nc := min n (c-lo)
  change _ = if n=0 then _ else _
  have hhi : hi≤F := min_le_left .. 
  have hsub : Ico lo hi ⊆ range F := by
    intro f hf
    exact mem_range.mpr ((mem_Ico.mp hf).2.trans_le hhi)
  have hrange : (∑ f ∈ range F, cell j b c f) =
        ∑ f ∈ Ico lo hi, cell j b c f := by
    symm
    apply sum_subset hsub
    intro f hf h
    exact outside j b c F f hF (mem_range.mp hf) (fun hh => h (mem_Ico.mpr hh))
  rw [hrange, sum_Ico_eq_sum_range]
  by_cases hn : n=0
  · simp [show hi-lo=0 from hn,hn]
  rw [ite_eq_right hn]
  change (∑ i ∈ range n, cell j b c (lo+i)) =
     widths (j+2-3*lo) n - series (b-2*lo) 2 nb - series (c-lo) 1 nc
  have hcell (i : ℕ) (hi' : i ∈ range n) :
      cell j b c (lo+i) + (b-2*lo-2*i) + (c-lo-i) = (j+2-3*lo-3*i)/2 := by
    have hi'' := mem_range.mp hi'
    have h := within j b c F (lo+i) hF (by change lo≤_; omega)
      (by change _<hi; dsimp [n] at hi''; omega)
    omega
  have he := sum_congr rfl hcell
  simp only [sum_add_distrib] at he
  have w : n=0 ∨ 3*(n-1) ≤ j+2-3*lo := by dsimp [n]; omega
  have hnb : nb≤n := min_le_left .. 
  have hnc : nc≤n := min_le_left .. 
  have hb : (∑ i ∈ range n, (b-2*lo-2*i)) = series (b-2*lo) 2 nb := by
    by_cases heq : nb=n
    · rw [heq,series_eq _ _ _ (by dsimp [nb] at heq; omega)]
    · apply truncated_series _ _ _ _ hnb <;> dsimp [nb] at * <;> omega
  have hc : (∑ i ∈ range n, (c-lo-i)) = series (c-lo) 1 nc := by
    suffices (∑ i ∈ range n, (c-lo-1*i)) = series (c-lo) 1 nc by simpa using this
    by_cases heq : nc=n
    · rw [heq,series_eq _ _ _ (by dsimp [nc] at heq; omega)]
    · apply truncated_series _ _ _ _ hnc <;> dsimp [nc] at * <;> omega
  rw [hb,hc,← widths_eq _ _ w] at he
  omega

private theorem keep_sum (j q : ℕ) :
    keep j q = ∑ f ∈ range (min (j/3+1) (1651-q)),
      cell j (q+3*j-4950) (2*q+2*j-4950) f := by
  unfold keep
  exact (cell_sum _ _ _ _ (min_le_left ..)).symm

private theorem total_sum (j : ℕ) :
    total j = ∑ f ∈ range (j/3+1), (j+2-3*f)/2 := by
  exact widths_eq _ _ (Or.inr (by omega))

theorem keep_le (j q : ℕ) : keep j q ≤ total j := by
  rw [keep_sum,total_sum]
  apply le_trans (sum_le_sum (g := fun f => (j+2-3*f)/2) fun f _ => ?_)
  · apply sum_le_sum_of_subset (range_mono (min_le_left ..))
  · unfold cell
    omega

theorem total_cast (j : ℕ) : (total j : ℤ) = totalAtIndex j := by
  rw [totalAtIndex_eq,Int.Ico_eq_finset_map,sum_map,total_sum,Nat.cast_sum]
  have h : (((j : ℤ)/3+1-0).toNat) = j/3+1 := by omega
  rw [h]
  apply sum_congr rfl
  intro f hf
  have hlt := mem_range.mp hf
  change (((j+2-3*f)/2 : ℕ) : ℤ) = ((j : ℤ)-3*(0+(f:ℤ)))/2+1
  omega

private theorem clip_cast (v t : ℕ) :
    ((v-4950-t : ℕ):ℤ) = max 0 ((v:ℤ)-4950-(t:ℤ)) := by omega

private theorem max_hinges (B C : ℤ) :
    max 0 (max (B+C) (max B C)) = max 0 B + max 0 C := by omega

private theorem tsub_cast (a b c : ℕ) :
    ((a-b-c : ℕ):ℤ) = max 0 ((a:ℤ)-((b:ℤ)+(c:ℤ))) := by omega

theorem keep_cast (j q : ℕ) : (keep j q : ℤ) = uncharged j q := by
  rw [uncharged_eq,Int.Ico_eq_finset_map,sum_map,keep_sum,Nat.cast_sum]
  have h : ((min ((j:ℤ)/3) (1650-(q:ℤ))+1-0).toNat) = min (j/3+1) (1651-q) := by omega
  rw [h]
  apply sum_congr rfl
  intro f hf
  have hlt := mem_range.mp hf
  let b := q+3*j-4950
  let c := 2*q+2*j-4950
  let B := (q:ℤ)+3*(j:ℤ)-4950-2*(f:ℤ)
  let C := 2*(q:ℤ)+2*(j:ℤ)-4950-(f:ℤ)
  have hB : ((b-2*f : ℕ):ℤ) = max 0 B := by simpa [b,B] using clip_cast (q+3*j) (2*f)
  have hC : ((c-f : ℕ):ℤ) = max 0 C := by simpa [c,C] using clip_cast (2*q+2*j) f
  have hw : (((j+2-3*f)/2 : ℕ):ℤ) = ((j:ℤ)-3*(f:ℤ))/2+1 := by omega
  have hA : 3*(q:ℤ)-9900+5*(j:ℤ)-3*(f:ℤ) = B+C := by dsimp [B,C]; ring
  change ((cell j b c f : ℕ) : ℤ) = max 0 (((j:ℤ)-3*(0+(f:ℤ)))/2+1 -
    max 0 (max (3*(q:ℤ)-9900+5*(j:ℤ)-3*(0+(f:ℤ)))
      (max ((q:ℤ)-4950+3*(j:ℤ)-2*(0+(f:ℤ))) (2*(q:ℤ)-4950+2*(j:ℤ)-(0+(f:ℤ))))))
  simp only [zero_add]
  rw [hA,show (q:ℤ)-4950+3*(j:ℤ)-2*(f:ℤ) = B by dsimp [B]; ring,
    show 2*(q:ℤ)-4950+2*(j:ℤ)-(f:ℤ) = C by dsimp [C]; ring,max_hinges,← hB,← hC,← hw]
  exact tsub_cast _ _ _

open Low48PrimaryPivot (binWeight)

theorem volume_cast (w : Window) (j q : ℕ) : (volume w j q : ℤ) = binWeight w j q := by
  unfold volume binWeight
  omega

theorem sweep_eq (w : Window) (j lo n : ℕ) :
    (sweep w j (total j) lo n : ℤ) = ∑ i ∈ range n,
      binWeight w (j:ℤ) ((lo:ℤ)+(i:ℤ)) *
        (totalAtIndex (j:ℤ)-uncharged (j:ℤ) ((lo:ℤ)+(i:ℤ))) := by
  induction n with
  | zero => simp [sweep]
  | succ n ih =>
    rw [sweep,Nat.cast_add,ih,sum_range_succ,Nat.cast_mul,Nat.cast_sub (keep_le ..),
      volume_cast,total_cast,keep_cast,Nat.cast_add]

#print axioms keep_cast
#print axioms sweep_eq
end Low48PrimaryPivot.Hinge

namespace Low48PrimaryPivot
open Finset K1_13_2_3
open scoped BigOperators
open Low48PrimaryPivot (qMin)
open Low48PrimaryPivot (binWeight)
open Low48PrimaryPivot (binAt_eq_interval)

private def allFree (j q : ℤ) : Prop :=
  j/3 ≤ 1650-q ∧ 3*q-9900+5*j ≤ 0 ∧ q-4950+3*j ≤ 0 ∧ 2*q-4950+2*j ≤ 0

private instance (j q : ℤ) : Decidable (allFree j q) := by unfold allFree; infer_instance

private def allCharged (j q : ℤ) : Prop :=
  1650 < q ∨ j < 3*q-9900+5*j ∨ 2*j < 3*(q-4950+3*j) ∨ j < 2*(2*q-4950+2*j)

private instance (j q : ℤ) : Decidable (allCharged j q) := by unfold allCharged; infer_instance

private theorem no_charge (j q : ℤ) (h : allFree j q) :
    uncharged j q = totalAtIndex j := by
  rw [uncharged_eq, totalAtIndex_eq, min_eq_left h.1]
  apply sum_congr rfl
  intro f hf
  simp only [mem_Ico] at hf
  have hzero :
      max 0 (max (3*q-9900+5*j-3*f) (max (q-4950+3*j-2*f) (2*q-4950+2*j-f))) = 0 := by
    have h₁ := h.2.1
    have h₂ := h.2.2.1
    have h₃ := h.2.2.2
    omega
  rw [hzero,sub_zero,max_eq_right (by omega)]

private theorem all_charge (j q : ℤ) (h : allCharged j q) :
    uncharged j q = 0 := by
  rw [uncharged_eq]
  apply sum_eq_zero
  intro f hf
  simp only [mem_Ico] at hf
  have hf1 := hf.1
  have hf2 := hf.2
  rw [max_eq_left]
  unfold allCharged at h
  omega

private def pricedBin (w : Window) (j q total : ℤ) : ℤ :=
  let volume := binWeight w j q
  if volume = 0 ∨ allFree j q then 0
  else if allCharged j q then volume*total
  else volume*(total-uncharged j q)

private theorem pricedBin_eq (w : Window) (j q : ℤ) :
    pricedBin w j q (totalAtIndex j) = binWeight w j q*(totalAtIndex j-uncharged j q) := by
  unfold pricedBin
  dsimp only
  split
  · rename_i h
    rcases h with h | h
    · rw [h,zero_mul]
    · rw [no_charge j q h,sub_self,mul_zero]
  · split
    · rename_i h
      rw [all_charge j q h,sub_zero]
    · rfl

private def startQ (w : Window) : ℤ :=
  max (qMin w) (indexLo w-(w.gradeHi : ℤ)+3001)

private def stopQ (w : Window) (j : ℕ) : ℤ :=
  min (orderHi w) (min ((j : ℤ)+1) (1651-(w.offsetLo : ℤ))-(w.gradeLo : ℤ)+3000)

private def trimIndex (w : Window) (j : ℕ) : ℤ :=
  let total := totalAtIndex j
  let lo := startQ w
  let hi := stopQ w j
  ((List.range (hi-lo).toNat).map fun i : ℕ => pricedBin w j (lo+(i : ℤ)) total).sum

private theorem trimIndex_eq (w : Window) (j : ℕ) :
    trimIndex w j = binAt w j := by
  rw [binAt_eq_interval]
  have h (q : ℤ) : binWeight w j q ≠ 0 → startQ w ≤ q ∧ q < stopQ w j ∨
      q < qMin w ∨ orderHi w ≤ q := by
    simp only [binWeight,startQ,stopQ,indexLo,max_le_iff,lt_min_iff]
    omega
  let term (q : ℤ) := binWeight w j q * (totalAtIndex j-uncharged j q)
  have hs (q : ℤ) (hq : q ∈ Ico (qMin w) (orderHi w)) :
      term q = if q ∈ Ico (startQ w) (stopQ w j) then term q else 0 := by
    by_cases hh : q ∈ Ico (startQ w) (stopQ w j)
    · rw [ite_eq_left hh]
    · rw [ite_eq_right hh]
      have hz : binWeight w j q = 0 := by
        by_contra hn
        have hp := h q hn
        simp only [mem_Ico] at hh hq
        omega
      simp [term,hz]
  change trimIndex w j = ∑ q ∈ Ico (qMin w) (orderHi w), term q
  rw [sum_congr rfl hs,← sum_filter]
  have hfilter : (Ico (qMin w) (orderHi w)).filter
      (fun q => q ∈ Ico (startQ w) (stopQ w j)) = Ico (startQ w) (stopQ w j) := by
    ext q
    simp only [mem_filter,mem_Ico,startQ,stopQ,max_le_iff,lt_min_iff]
    omega
  rw [hfilter,Int.Ico_eq_finset_map,sum_map]
  unfold trimIndex
  change (∑ k ∈ range (stopQ w j-startQ w).toNat,
    pricedBin w j (startQ w+(k:ℤ)) (totalAtIndex j)) = _
  apply sum_congr rfl
  intro k _
  exact pricedBin_eq w _ _


private theorem rawIndex_eq_trim (w : Window) (j : ℕ) (hn : 0 ≤ startQ w) :
    (Hinge.index w j : ℤ) = trimIndex w j := by
  let lo := max (4650-w.diagonalHi) (4651-w.offsetHi-w.gradeHi)
  let hi := min (4651-w.diagonalLo) (min (j+3001) (4651-w.offsetLo)-w.gradeLo)
  have hl : (lo:ℤ) = startQ w := by
    unfold startQ qMin indexLo at hn ⊢
    dsimp [lo]
    omega
  have hlen : hi-lo = (stopQ w j-startQ w).toNat := by
    rw [← hl]
    unfold stopQ orderHi
    dsimp [lo,hi]
    omega
  change (Hinge.sweep w j (Hinge.total j) lo (hi-lo) : ℤ) = _
  rw [Hinge.sweep_eq,hlen,hl]
  change _ = ∑ i ∈ range (stopQ w j-startQ w).toNat,
    pricedBin w j (startQ w+(i:ℤ)) (totalAtIndex j)
  exact sum_congr rfl fun i _ => (pricedBin_eq w _ _).symm

def binAtFast (w : Window) (j : ℕ) : ℤ :=
  if (j : ℤ)+1 ≤ indexLo w then 0
  else if 0 ≤ startQ w then (Hinge.index w j : ℤ) else trimIndex w j

theorem binAtFast_eq (w : Window) (j : ℕ) : binAtFast w j = binAt w j := by
  unfold binAtFast
  split
  · rename_i h
    rw [binAt_eq_interval]
    symm
    apply sum_eq_zero
    intro q _
    have hz : binWeight w j q = 0 := by
      unfold binWeight
      unfold indexLo at h
      omega
    rw [hz,zero_mul]
  · split
    · rename_i hn
      exact (rawIndex_eq_trim w j hn).trans (trimIndex_eq w j)
    · exact trimIndex_eq w j

#print axioms binAtFast_eq
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinsFast

-- merged module Low48PrimaryPivotBinReceipts
section Merged_Low48PrimaryPivotBinReceipts

set_option Elab.async false
namespace Low48PrimaryPivot
open K1_13_2_3

def binChunk (w : Window) (start count : ℕ) : ℤ :=
  ((List.range' start count).map (binAtFast w)).sum

theorem binChunk_append (w : Window) (start left right : ℕ) :
    binChunk w start (left+right) =
      binChunk w start left + binChunk w (start+left) right := by
  unfold binChunk
  rw [← List.range'_append_1, List.map_append, List.sum_append]

theorem binChunk_join {w : Window} {start left right : ℕ} {x y : ℤ}
    (hleft : binChunk w start left = x) (hright : binChunk w (start+left) right = y) :
    binChunk w start (left+right) = x+y := by
  rw [binChunk_append,hleft,hright]

private theorem binChunk_zero (w : Window) (n : ℕ) (h : (n : ℤ) ≤ indexLo w) :
    binChunk w 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [binChunk_append,ih (by omega)]
    have hk : binAtFast w k = 0 := by
      unfold binAtFast
      rw [ite_eq_left (by omega)]
    rw [zero_add]
    simp [binChunk,List.range'_succ,hk]

theorem binCompute_eq_chunk (w : Window) (n : ℕ) (hn : n ≤ 1651) (h : (n : ℤ) ≤ indexLo w) :
    binCompute w = binChunk w n (1651-n) := by
  have hStart : binCompute w = binChunk w 0 1651 := by
    unfold binCompute binChunk
    rw [List.range_eq_range']
    apply congrArg List.sum
    exact List.map_congr_left fun j _ => (binAtFast_eq w j).symm
  calc
    _ = binChunk w 0 (n+(1651-n)) :=
      hStart.trans (congrArg (binChunk w 0) (Nat.add_sub_of_le hn).symm)
    _ = _ := by rw [binChunk_append,binChunk_zero w n h]; simp only [zero_add]

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinReceipts

-- merged module Low48PrimaryPivotBins2Part588
section Merged_Low48PrimaryPivotBins2Part588

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf588 : binChunk w2 588 4 = 5264644 := by decide +kernel
private theorem leaf592 : binChunk w2 592 4 = 14705414 := by decide +kernel
private theorem leaf596 : binChunk w2 596 4 = 25599511 := by decide +kernel
private theorem leaf600 : binChunk w2 600 4 = 38070508 := by decide +kernel
private theorem leaf604 : binChunk w2 604 4 = 52244044 := by decide +kernel
private theorem leaf608 : binChunk w2 608 4 = 68254581 := by decide +kernel
private theorem leaf612 : binChunk w2 612 4 = 86240300 := by decide +kernel
private theorem leaf616 : binChunk w2 616 4 = 106339418 := by decide +kernel
private theorem leaf620 : binChunk w2 620 4 = 128702811 := by decide +kernel
private theorem leaf624 : binChunk w2 624 4 = 153483268 := by decide +kernel
private theorem leaf628 : binChunk w2 628 4 = 180831344 := by decide +kernel
private theorem leaf632 : binChunk w2 632 4 = 210914569 := by decide +kernel
private theorem leaf636 : binChunk w2 636 4 = 243900340 := by decide +kernel
private theorem leaf640 : binChunk w2 640 4 = 279951310 := by decide +kernel
private theorem leaf644 : binChunk w2 644 4 = 319251903 := by decide +kernel
private theorem leaf648 : binChunk w2 648 4 = 361984124 := by decide +kernel
private theorem batch2_588_596 : binChunk w2 588 8 = 19970058 :=
  binChunk_join (w := w2) (start := 588) (left := 4) (right := 4) (x := 5264644) (y := 14705414) leaf588 leaf592
private theorem batch2_596_604 : binChunk w2 596 8 = 63670019 :=
  binChunk_join (w := w2) (start := 596) (left := 4) (right := 4) (x := 25599511) (y := 38070508) leaf596 leaf600
private theorem batch2_588_604 : binChunk w2 588 16 = 83640077 :=
  binChunk_join (w := w2) (start := 588) (left := 8) (right := 8) (x := 19970058) (y := 63670019) batch2_588_596 batch2_596_604
private theorem batch2_604_612 : binChunk w2 604 8 = 120498625 :=
  binChunk_join (w := w2) (start := 604) (left := 4) (right := 4) (x := 52244044) (y := 68254581) leaf604 leaf608
private theorem batch2_612_620 : binChunk w2 612 8 = 192579718 :=
  binChunk_join (w := w2) (start := 612) (left := 4) (right := 4) (x := 86240300) (y := 106339418) leaf612 leaf616
private theorem batch2_604_620 : binChunk w2 604 16 = 313078343 :=
  binChunk_join (w := w2) (start := 604) (left := 8) (right := 8) (x := 120498625) (y := 192579718) batch2_604_612 batch2_612_620
private theorem batch2_588_620 : binChunk w2 588 32 = 396718420 :=
  binChunk_join (w := w2) (start := 588) (left := 16) (right := 16) (x := 83640077) (y := 313078343) batch2_588_604 batch2_604_620
private theorem batch2_620_628 : binChunk w2 620 8 = 282186079 :=
  binChunk_join (w := w2) (start := 620) (left := 4) (right := 4) (x := 128702811) (y := 153483268) leaf620 leaf624
private theorem batch2_628_636 : binChunk w2 628 8 = 391745913 :=
  binChunk_join (w := w2) (start := 628) (left := 4) (right := 4) (x := 180831344) (y := 210914569) leaf628 leaf632
private theorem batch2_620_636 : binChunk w2 620 16 = 673931992 :=
  binChunk_join (w := w2) (start := 620) (left := 8) (right := 8) (x := 282186079) (y := 391745913) batch2_620_628 batch2_628_636
private theorem batch2_636_644 : binChunk w2 636 8 = 523851650 :=
  binChunk_join (w := w2) (start := 636) (left := 4) (right := 4) (x := 243900340) (y := 279951310) leaf636 leaf640
private theorem batch2_644_652 : binChunk w2 644 8 = 681236027 :=
  binChunk_join (w := w2) (start := 644) (left := 4) (right := 4) (x := 319251903) (y := 361984124) leaf644 leaf648
private theorem batch2_636_652 : binChunk w2 636 16 = 1205087677 :=
  binChunk_join (w := w2) (start := 636) (left := 8) (right := 8) (x := 523851650) (y := 681236027) batch2_636_644 batch2_644_652
private theorem batch2_620_652 : binChunk w2 620 32 = 1879019669 :=
  binChunk_join (w := w2) (start := 620) (left := 16) (right := 16) (x := 673931992) (y := 1205087677) batch2_620_636 batch2_636_652
theorem batch2_588_652 : binChunk w2 588 64 = 2275738089 :=
  binChunk_join (w := w2) (start := 588) (left := 32) (right := 32) (x := 396718420) (y := 1879019669) batch2_588_620 batch2_620_652

end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBins2Part588

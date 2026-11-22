import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinAggregate

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

open private binWeight from ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum

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
open private qMin from ProximityPrize.SubmissionLower.Low48PrimaryPivotBinWeight
open private binWeight from ProximityPrize.SubmissionLower.Low48PrimaryPivotSectionSum
open private binAt_eq_interval from ProximityPrize.SubmissionLower.Low48PrimaryPivotBinAggregate

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

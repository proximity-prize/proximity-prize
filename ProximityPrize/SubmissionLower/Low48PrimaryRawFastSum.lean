import ProximityPrize.SubmissionLower.Low48PrimaryRawDenomSum
import ProximityPrize.SubmissionLower.Low48PrimaryRawSplit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
namespace Low48PrimaryPivot.RawClosed
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators
open Low48PrimaryPivot.RawReceipt
open private targetAt columnsAt fastAt rawAt_fast from ProximityPrize.SubmissionLower.Low48PrimaryPivotRawFast

private def positiveRun (x : ℤ) (d n : ℕ) := if x<0 then 0 else denomRun x d n
private theorem positiveRun_eq (x : ℤ) (d n : ℕ) (hd : d=1 ∨ d=4) :
    positiveRun x d n=denomRun x d n := by
  by_cases hx : x<0
  · simp only [positiveRun,hx,↓reduceIte]; rcases hd with rfl|rfl
    · rw [run1]; symm; apply sum_eq_zero; intro i _; rw [denominator, if_pos (by omega)]
    · rw [run4]; symm; apply sum_eq_zero; intro i _; rw [denominator, if_pos (by omega)]
  · simp [positiveRun,hx]

private def stripe (g o n : ℕ) : ℤ :=
  let r := (4649-(g:ℤ))/4+1
  let a := 4649-(g:ℤ)-(o:ℤ)
  let z := r-(o:ℤ)-2
  positiveRun a 4 n - positiveRun (a-3*r) 1 n - positiveRun z 1 n -
    positiveRun (z-1) 1 n - positiveRun (z-2) 1 n

private theorem stripe_eq (g o n : ℕ) : stripe g o n = ∑ i ∈ range n, targetAt (g+24*i) o := by
  simp only [stripe,positiveRun_eq _ _ _ (Or.inl rfl),positiveRun_eq _ _ _ (Or.inr rfl),run4,run1,
    ← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  simp only [targetAt,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hdiv : (4649-((g:ℤ)+24*(i:ℤ)))/4=(4649-(g:ℤ))/4-6*(i:ℤ) := by omega
  rw [hdiv]
  repeat' first | omega | congr 1

private def tailCost (g o n : ℕ) : ℤ := if n=0 then 0 else
  ((List.range' 0 24).map fun r => stripe (g+r) o (laneLen n r)).sum

private theorem tail_eq (g o n : ℕ) : tailCost g o n = ∑ i ∈ range n, targetAt (g+i) o := by
  by_cases zero : n=0
  · simp [tailCost,zero]
  · simp only [tailCost,zero,↓reduceIte,list_sum_range,zero_add,stripe_eq]
    rw [sum_lanes (fun i => targetAt (g+i) o) n]
    simp only [Nat.add_assoc]

private def closedAt (w : Window) (o : ℕ) : ℕ :=
  let lo:=max w.gradeLo (w.diagonalLo-o)
  let n:=min w.gradeHi (w.diagonalHi+1-o)-lo
  let col:=columnsAt o
  let k:=firstCross (fun i => decide (targetAt (lo+i) o < col)) 13 0 n
  k*col.toNat + (tailCost (lo+k) o (n-k)).toNat

private theorem fast_closed (w : Window) (o : ℕ) (hg : 1650≤w.gradeLo) (hl : 3000≤w.diagonalLo)
    (hh : w.diagonalHi<4650) : fastAt w o = closedAt w o := by
  let lo:=max w.gradeLo (w.diagonalLo-o)
  let n:=min w.gradeHi (w.diagonalHi+1-o)-lo
  let c:=columnsAt o
  let p:=fun i : ℕ => decide (targetAt (lo+i) o < c)
  let k:= firstCross p 13 0 n
  have valid (i : ℕ) (hi : i<n) : 1650≤lo+i ∧ 3000≤lo+i+o ∧ lo+i+o<4650 := by
    have h1:= le_max_left w.gradeLo (w.diagonalLo-o)
    have h2:= le_max_right w.gradeLo (w.diagonalLo-o)
    have h3:= min_le_right w.gradeHi (w.diagonalHi+1-o)
    dsimp [n,lo] at *; omega
  have hn : n < 2^13 := by
    have h:=min_le_right w.gradeHi (w.diagonalHi+1-o)
    dsimp [n]; norm_num; omega
  have hs:=cross_spec p 13 0 n (Nat.zero_le _) (by simpa using hn)
  change 0≤k ∧ k≤n ∧ (k=0 ∨ p (k-1)=false) ∧ (k=n ∨ p k=true) at hs
  obtain ⟨_,hk,hL,hR⟩:= hs
  have left (i : ℕ) (hi : i<k) : c≤targetAt (lo+i) o := by
    have hnz : k≠0 := by omega
    have hp:=hL.resolve_left hnz
    have ht : c≤targetAt (lo+(k-1)) o := by simpa [p] using hp
    have va:=valid i (by omega);have vb:=valid (k-1) (by omega)
    exact ht.trans (target_anti (by omega : lo+i≤lo+(k-1)) va.1 va.2.1 vb.2.2)
  have right (i : ℕ) (hi : i<n-k) : targetAt (lo+(k+i)) o ≤ c := by
    have hkn : k≠n := by omega
    have hp:=hR.resolve_left hkn
    have ht : targetAt (lo+k) o < c := by simpa [p] using hp
    have va:=valid k (by omega);have vb:=valid (k+i) (by omega)
    exact (target_anti (by omega : lo+k≤lo+(k+i)) va.1 va.2.1 vb.2.2).trans ht.le
  change ((List.range' lo n).map fun g => (min c (targetAt g o)).toNat).sum =
    k*c.toNat+(tailCost (lo+k) o (n-k)).toNat
  rw [list_sum_range]
  have split := sum_range_add (fun i => (min c (targetAt (lo+i) o)).toNat) k (n-k)
  rw [show k+(n-k)=n by omega] at split
  rw [split,tail_eq]
  congr 1
  · calc
      _ = ∑ _ ∈ range k, c.toNat := sum_congr rfl (fun i hi => by rw [min_eq_left (left i (mem_range.mp hi))])
      _ = _ := by simp
  · have pos (i : ℕ) (hi : i<n-k) : 0≤targetAt (lo+k+i) o := by
      have v:=valid (k+i) (by omega)
      rw [Nat.add_assoc]; exact target_nonneg v.1 v.2.1 v.2.2
    apply Int.ofNat_inj.mp
    rw [Nat.cast_sum,Int.toNat_of_nonneg (sum_nonneg (fun i hi => pos i (mem_range.mp hi)))]
    apply sum_congr rfl; intro i hi
    rw [min_eq_right (right i (mem_range.mp hi)), ← Nat.add_assoc, Int.toNat_of_nonneg (pos i (mem_range.mp hi))]

def closedChunk (w : Window) (start count : ℕ) : ℕ :=
  ((List.range' start count).map (closedAt w)).sum

theorem rawChunk_closed (w : Window) (start count : ℕ)
    (hg : 1650≤w.gradeLo) (hl : 3000≤w.diagonalLo) (hh : w.diagonalHi<4650)
    (ho : start+count≤3000) : rawChunk w start count=closedChunk w start count := by
  unfold rawChunk closedChunk
  apply congrArg List.sum; apply List.map_congr_left; intro o h
  have hr:=List.mem_range'_1.mp h
  exact (rawAt_fast w hg hl hh o (by omega)).trans (fast_closed w o hg hl hh)

#print axioms rawChunk_closed
end Low48PrimaryPivot.RawClosed

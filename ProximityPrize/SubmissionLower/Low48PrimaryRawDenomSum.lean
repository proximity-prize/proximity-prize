import ProximityPrize.SubmissionLower.KoalaTaperTransfer

-- merged module Low48PrimaryPivotRawChunks
section Merged_Low48PrimaryPivotRawChunks

set_option autoImplicit false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

def rawChunk (w : Window) (start count : ℕ) : ℕ :=
  ((List.range' start count).map (rawAt w)).sum

theorem joinRaw {w : Window} {start a b x y : ℕ}
    (left : rawChunk w start a = x) (right : rawChunk w (start + a) b = y) :
    rawChunk w start (a + b) = x + y := by
  have happend : rawChunk w start (a + b) = rawChunk w start a + rawChunk w (start + a) b := by
    unfold rawChunk
    rw [← List.range'_append_1, List.map_append, List.sum_append]
  exact happend.trans (congrArg₂ (· + ·) left right)

theorem rawCompute_eq (w : Window) :
    rawCompute w = rawChunk w w.offsetLo (w.offsetHi + 1 - w.offsetLo) := rfl

end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawChunks

-- merged module Low48PrimaryPivotRawFast
section Merged_Low48PrimaryPivotRawFast

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2 K1_13_2_3
open Low48PrimaryPivot (baselineFast)

private theorem denom_neg {u : ℤ} (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]

private theorem cum_neg (d : ℤ) {u : ℤ} (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]

private theorem cum_four (d u : ℤ) (hd : 0 ≤ d) (hcap : u ≤ 3*d) (hlo : u ≤ 2*d+2) :
    cumulative d u = denominator u - denominator (u-d-1) - denominator (u-d-2) -
      denominator (u-d-3) := by
  by_cases hu : u < 0
  · simp [cum_neg d hu, denom_neg hu, denom_neg (by omega : u-d-1 < 0),
      denom_neg (by omega : u-d-2 < 0), denom_neg (by omega : u-d-3 < 0)]
  · simp [cumulative, not_lt.mpr hd, hu, min_eq_left hcap,
      denom_neg (by omega : u-2*d-3 < 0), denom_neg (by omega : u-2*d-4 < 0),
      denom_neg (by omega : u-2*d-5 < 0), denom_neg (by omega : u-3*d-6 < 0)]

private theorem cum_one (d u : ℤ) (hd : 0 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u := by
  rw [cum_four d u hd (by omega) (by omega)]
  simp [denom_neg (by omega : u-d-1 < 0), denom_neg (by omega : u-d-2 < 0),
    denom_neg (by omega : u-d-3 < 0)]

def columnsAt (o : ℕ) : ℤ :=
  denominator 1650 - denominator (1649 - (o : ℤ))

private theorem columns_eq (o : ℕ) (order : ℤ) :
    oldCount ⟨1650, 1650-(o : ℤ), 1650, 550, order⟩ = columnsAt o := by
  have hmin : min (1650 : ℤ) (1650-(o : ℤ)-1) = 1649-(o : ℤ) := by
    rw [min_eq_right (by omega)]
    omega
  change cappedCount 1650 1650 550 - cappedCount 1650 (min 1650 (1650-(o : ℤ)-1)) 550 =
    columnsAt o
  rw [hmin]
  simp only [cappedCount, show ¬(550 : ℤ) < 0 by decide, ↓reduceIte]
  rw [cum_one 1650 1650 (by decide) le_rfl,
    cum_one 1650 (1649-(o : ℤ)) (by decide) (by omega),
    cum_neg _ (by decide : (1650 : ℤ)-3*(550+1) < 0),
    cum_neg _ (by omega : (1649-(o : ℤ))-3*(550+1) < 0)]
  simp [columnsAt]

def targetAt (g o : ℕ) : ℤ :=
  let removed := (4649 - (g : ℤ)) / 4 + 1
  let degree := 1650 - removed
  let order := 4649 - (g : ℤ) - (o : ℤ)
  let lower := 1649 - (o : ℤ)
  denominator order - denominator (order - 3*removed) -
    denominator (lower-degree-1) - denominator (lower-degree-2) -
    denominator (lower-degree-3)

theorem target_eq (g o : ℕ) (hg : 1650 ≤ g) (hlo : 3000 ≤ g+o)
    (hhi : g+o < 4650) :
    targetCount ⟨1650, 1650-(o : ℤ), 1650, 550, 4650-(g : ℤ)-(o : ℤ)⟩ = targetAt g o := by
  let removed : ℤ := (4649-(g : ℤ))/4+1
  let degree : ℤ := 1650-removed
  let order : ℤ := 4649-(g : ℤ)-(o : ℤ)
  let lower : ℤ := 1649-(o : ℤ)
  have hbalance :
      (4650-(g : ℤ)-(o : ℤ))-1-(1650-(o : ℤ))+1650 = 4649-(g : ℤ) := by omega
  have hpos : ¬4649-(g : ℤ) < 0 := by omega
  have hdiv : (4649-(g : ℤ))/4 ≤ 1650 := by omega
  have hord : (4650-(g : ℤ)-(o : ℤ))-1 = order := by dsimp [order]; omega
  have hlow : (1650-(o : ℤ))-1 = lower := by dsimp [lower]; omega
  have hd : 0 ≤ degree := by dsimp [degree, removed]; omega
  have hthree : lower ≤ 3*degree := by dsimp [lower, degree, removed]; omega
  have htwo : lower ≤ 2*degree+2 := by dsimp [lower, degree, removed]; omega
  have hcut : order-3*removed ≤ degree := by dsimp [order, degree, removed]; omega
  have hmax : order ≤ 1650 := by dsimp [order]; omega
  change (let balance := (4650-(g : ℤ)-(o : ℤ))-1-(1650-(o : ℤ))+1650
    if balance < 0 then 0 else
      let r := min 1650 (balance / 4) + 1
      cumulative 1650 ((4650-(g : ℤ)-(o : ℤ))-1) -
        cumulative (1650-r) ((4650-(g : ℤ)-(o : ℤ))-1-3*r) -
        cumulative 1650 ((1650-(o : ℤ))-1) + cumulative (1650-r) ((1650-(o : ℤ))-1)) =
      targetAt g o
  rw [hbalance]
  simp only [hpos, ↓reduceIte, min_eq_right hdiv, hord, hlow]
  change cumulative 1650 order - cumulative degree (order-3*removed) -
    cumulative 1650 lower + cumulative degree lower = targetAt g o
  rw [cum_one 1650 order (by decide) hmax, cum_one degree (order-3*removed) hd hcut,
      cum_one 1650 lower (by decide) (by dsimp [lower]; omega),
      cum_four degree lower hd hthree htwo]
  change _ = denominator order - denominator (order-3*removed) -
    denominator (lower-degree-1) - denominator (lower-degree-2) -
    denominator (lower-degree-3)
  ring

private theorem grade_eq (g o : ℕ) (hg : 1650 ≤ g) (hlo : 3000 ≤ g+o)
    (hhi : g+o < 4650) (ho : o ≤ 2999) :
    baselineFast g o = (min (columnsAt o) (targetAt g o)).toNat := by
  let F : Flag := ⟨1650, 1650-(o : ℤ), 1650, 550, 4650-(g : ℤ)-(o : ℤ)⟩
  have hdegree : min (g : ℤ) 1650 = 1650 := min_eq_right (by omega)
  have hindex : -((o : ℤ)-1650) = 1650-(o : ℤ) := by omega
  have hord : 3000-(g : ℤ)-((o : ℤ)-1650) = 4650-(g : ℤ)-(o : ℤ) := by omega
  have hpos : ¬4650-(g : ℤ)-(o : ℤ) ≤ 0 := by omega
  have hupper : min (1650 : ℤ) (2999-((o : ℤ)-1650)) = 1650 := min_eq_left (by omega)
  have hkernel : kernelLower F = oldCount F - targetCount F := by
    simp [F, kernelLower]
  have hcount : oldCount F = columnsAt o := columns_eq o _
  have htarget : targetCount F = targetAt g o := target_eq g o hg hlo hhi
  unfold baselineFast
  simp only [hdegree, hindex, hord, hpos, ↓reduceIte, hupper]
  change (min (oldCount F) (oldCount F - max 0 (kernelLower F))).toNat =
    (min (columnsAt o) (targetAt g o)).toNat
  rw [hkernel, hcount, htarget]
  congr 1
  omega

def fastAt (w : Window) (o : ℕ) : ℕ :=
  let lo := max w.gradeLo (w.diagonalLo-o)
  let hi := min w.gradeHi (w.diagonalHi+1-o)
  let columns := columnsAt o
  ((List.range' lo (hi-lo)).map fun g => (min columns (targetAt g o)).toNat).sum

theorem rawAt_fast (w : Window) (hg : 1650 ≤ w.gradeLo) (hl : 3000 ≤ w.diagonalLo)
    (hh : w.diagonalHi < 4650) (o : ℕ) (ho : o ≤ 2999) : rawAt w o = fastAt w o := by
  unfold rawAt fastAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro g h
  have hr := List.mem_range'_1.mp h
  refine grade_eq g o (by have h := le_max_left w.gradeLo (w.diagonalLo-o); omega) ?_ ?_ ho
  · have h := le_max_right w.gradeLo (w.diagonalLo-o)
    omega
  · have h := min_le_right w.gradeHi (w.diagonalHi+1-o)
    omega



end Low48PrimaryPivot.RawReceipt

end Merged_Low48PrimaryPivotRawFast

-- merged module Low48PrimaryRawDenomSum
section Merged_Low48PrimaryRawDenomSum

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Low48PrimaryPivot.RawClosed
open K1_13_2 Finset
open scoped BigOperators

private theorem twice_dvd (z : ℤ) : (2 : ℤ) ∣ z*(z-1) := by
  obtain h | h : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  · exact ⟨(z/2)*(z-1), by linear_combination (z-1)*h⟩
  · exact ⟨z*(z/2), by linear_combination z*h⟩

private def cubic (q r : ℤ) := 12*q^3+(21+6*r)*q^2+(r^2+7*r+11)*q+(r^2+r+2)

private theorem double_den {u : ℤ} (hu : 0≤u) : 2*denominator u = cubic (u/6) (u%6) := by
  simp only [denominator, show ¬ u<0 by omega, ↓reduceIte]
  set q:=u/6
  set r:=u%6
  have hp : (2:ℤ) ∣ r*(r+1) := by
    convert twice_dvd (r+1) using 1 <;> ring
  unfold cubic
  linear_combination Int.ediv_mul_cancel hp + q * Int.ediv_mul_cancel (twice_dvd r) +
    (57+6*r)* Int.ediv_mul_cancel (twice_dvd q)

/-- Twenty-four times the sum of n values of the denominator polynomial for one residue. -/
private def primitive (q r d n : ℤ) : ℤ :=
  let p1 := -d*(36*q^2+2*(21+6*r)*q+(r^2+7*r+11))
  let p2 := d^2*(36*q+21+6*r)
  let p3 := -12*d^3
  12*n*cubic q r+6*n*(n-1)*p1+2*n*(n-1)*(2*n-1)*p2+3*n^2*(n-1)^2*p3

private theorem primitive_sum (q r d : ℤ) (n : ℕ) :
    primitive q r d n = 12 * ∑ i ∈ range n, cubic (q-d*(i:ℤ)) r := by
  induction n with
  | zero => simp [primitive]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← ih, Nat.cast_succ]
    unfold primitive cubic
    ring

def denomRun (x : ℤ) (d n : ℕ) : ℤ :=
  let len := min n (x/(6*(d:ℤ))+1).toNat
  primitive (x/6) (x%6) d len / 24

private theorem run_spec (x : ℤ) (d n : ℕ) (hd : d=1 ∨ d=4) :
    denomRun x d n = ∑ i ∈ range n, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
  let len := min n (x/(6*(d:ℤ))+1).toNat
  have hn : len≤n := min_le_left _ _
  have pos (i : ℕ) (hi : i<len) : 0≤x-6*(d:ℤ)*(i:ℤ) := by
    dsimp [len] at hi; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have neg (i : ℕ) (hi : i<n-len) : x-6*(d:ℤ)*(↑(len+i):ℤ)<0 := by
    dsimp [len] at *; rcases hd with rfl|rfl <;> norm_num at * <;> omega
  have core : primitive (x/6) (x%6) d len = 24 * ∑ i ∈ range len, denominator (x-6*(d:ℤ)*(i:ℤ)) := by
    rw [primitive_sum]
    have eq : ∑ i ∈ range len, cubic (x/6-(d:ℤ)*(i:ℤ)) (x%6) =
        ∑ i ∈ range len, 2*denominator (x-6*(d:ℤ)*(i:ℤ)) := by
      apply sum_congr rfl; intro i hi
      rw [double_den (pos i (mem_range.mp hi))]
      have ha : x-6*(d:ℤ)*(i:ℤ) = x+6*(-((d:ℤ)*(i:ℤ))) := by ring
      rw [ha, Int.add_mul_ediv_left _ _ (by decide), Int.add_mul_emod_self_left]; rfl
    rw [eq, ← mul_sum]; ring
  have tail : ∑ i ∈ range (n-len), denominator (x-6*(d:ℤ)*(↑(len+i):ℤ)) = 0 := by
    apply sum_eq_zero; intro i hi; rw [denominator, if_pos (neg i (mem_range.mp hi))]
  change primitive (x/6) (x%6) d len / 24 = _
  rw [core, Int.mul_ediv_cancel_left _ (by decide)]
  conv_rhs => rw [show n=len+(n-len) by omega, sum_range_add]
  rw [tail, add_zero]

theorem run1 (x : ℤ) (n : ℕ) : denomRun x 1 n = ∑ i ∈ range n, denominator (x-6*(i:ℤ)) := by
  simpa using run_spec x 1 n (Or.inl rfl)

theorem run4 (x : ℤ) (n : ℕ) : denomRun x 4 n = ∑ i ∈ range n, denominator (x-24*(i:ℤ)) := by
  simpa using run_spec x 4 n (Or.inr rfl)

end Low48PrimaryPivot.RawClosed

end Merged_Low48PrimaryRawDenomSum

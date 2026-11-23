import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace KoalaAffineTriangle

open scoped BigOperators

def twiceTriangle (x : ℤ) : ℤ :=
  let q:=max 0 x
  q*(q+1)

private def polynomial (a d : ℤ) (n : ℕ) : ℤ :=
  let m:ℤ:=n
  6 * m * a * (a + 1) + 3 * d * (2 * a + 1) * m * (m - 1) +
    d*d*m*(m - 1)*(2*m - 1)

private def closed (a d:ℤ) (n:ℕ):ℤ:=polynomial a d n / 6

private def direct (a d : ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => direct a d n+twiceTriangle (a+d*(n:ℤ))

private def run (a d : ℤ) : ℕ → ℕ → ℤ
  | 0,n => direct a d n
  | fuel + 1, n =>
    if n=0 then 0
    else
      let last:=a+d*((n - 1:ℕ):ℤ)
      if a≤0 ∧ last≤0 then 0
      else if 0≤a ∧ 0≤last then closed a d n
      else
        let k:=n / 2
        run a d fuel k+run (a+d*(k:ℤ)) d fuel (n - k)

/-- Sum the positive twice-triangle of `a + d*i` for `lo ≤ i < lo+n`.
Same-sign spans evaluate in closed form. A crossing splits at the midpoint. -/
def sum (a d lo : ℤ) (n : ℕ) : ℤ :=
  run (a+d*lo) d (n.log2+1) n

private def rangeSum (a d : ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n,twiceTriangle (a+d*(i:ℤ))

private theorem polynomial_eq (a d : ℤ) (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (a + d * (i : ℤ)) * (a + d * (i : ℤ) + 1)) =
      polynomial a d n:=by
  induction n with
  | zero => simp [polynomial]
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    simp only [polynomial,Nat.cast_succ]
    ring

private theorem closed_eq (a d : ℤ) (n : ℕ) :
    closed a d n = ∑ i ∈ Finset.range n,(a+d*(i:ℤ))*(a+d*(i:ℤ)+1):=by
  rw [closed, ← polynomial_eq,Int.mul_ediv_cancel_left _ (by decide:(6:ℤ)≠0)]

private theorem between (a d : ℤ) {n i : ℕ} (hi : i < n) :
    let last:=a+d*((n - 1:ℕ):ℤ)
    min a last≤a+d*(i:ℤ) ∧ a+d*(i:ℤ)≤max a last:=by
  dsimp only
  have hz:(0:ℤ)≤(i:ℤ):=by omega
  have hb:(i:ℤ)≤((n - 1:ℕ):ℤ):=by omega
  by_cases hd:0≤d
  · exact ⟨(min_le_left _ _).trans (le_add_of_nonneg_right (mul_nonneg hd hz)),
      (add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hb hd)).trans (le_max_right _ _)⟩
  · have hd' : d ≤ 0 := le_of_lt (lt_of_not_ge hd)
    have hupper : a + d * (i : ℤ) ≤ a := by
      have hs:d*(i:ℤ)≤0:=mul_nonpos_of_nonpos_of_nonneg hd' hz
      omega
    exact ⟨(min_le_right _ _).trans (add_le_add (le_refl a) (mul_le_mul_of_nonpos_left hb hd')),
      hupper.trans (le_max_left _ _)⟩

private theorem rangeSum_nonpos (a d : ℤ) (n : ℕ)
    (h:a≤0 ∧ a+d*((n - 1:ℕ):ℤ)≤0):rangeSum a d n=0:=by
  apply Finset.sum_eq_zero
  intro i hi
  have hx:=(between a d (Finset.mem_range.mp hi)).2.trans (max_le h.1 h.2)
  simp [twiceTriangle,max_eq_left hx]

private theorem rangeSum_nonneg (a d : ℤ) (n : ℕ)
    (h:0≤a ∧ 0≤a+d*((n - 1:ℕ):ℤ)):rangeSum a d n=closed a d n:=by
  rw [closed_eq,rangeSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hx:=(le_min h.1 h.2).trans (between a d (Finset.mem_range.mp hi)).1
  simp [twiceTriangle,max_eq_right hx]

private theorem rangeSum_add (a d : ℤ) (n m : ℕ) :
    rangeSum a d (n+m)=rangeSum a d n+rangeSum (a+d*(n:ℤ)) d m:=by
  unfold rangeSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.cast_add,mul_add,add_assoc]

private theorem direct_eq (a d : ℤ) (n : ℕ) : direct a d n = rangeSum a d n := by
  induction n with
  | zero => simp [direct,rangeSum]
  | succ n ih => simp only [direct,ih,rangeSum,Finset.sum_range_succ]

private theorem run_eq (a d : ℤ) (fuel n : ℕ) : run a d fuel n = rangeSum a d n := by
  induction fuel generalizing a n with
  | zero => exact direct_eq a d n
  | succ fuel ih =>
    simp only [run]
    by_cases hn:n=0
    · simp [hn,rangeSum]
    simp only [ite_eq_right hn]
    by_cases hz:a≤0 ∧ a+d*((n - 1:ℕ):ℤ)≤0
    · rw [ite_eq_left hz,rangeSum_nonpos a d n hz]
    simp only [ite_eq_right hz]
    by_cases hp:0≤a ∧ 0≤a+d*((n - 1:ℕ):ℤ)
    · rw [ite_eq_left hp,rangeSum_nonneg a d n hp]
    simp only [ite_eq_right hp,ih]
    have hs:=rangeSum_add a d (n / 2) (n - n / 2)
    rw [Nat.add_sub_of_le (Nat.div_le_self n 2)] at hs
    exact hs.symm

theorem sum_eq_range (a d lo : ℤ) (n : ℕ) :
    sum a d lo n = ∑ i ∈ Finset.range n,twiceTriangle (a+d*(lo+(i:ℤ))):=by
  rw [sum,run_eq,rangeSum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_add,add_assoc]

theorem sum_eq (a d lo : ℤ) (n : ℕ) :
    sum a d lo n = ∑ i ∈ Finset.Ico lo (lo+(n:ℤ)),twiceTriangle (a+d*i):=by
  rw [sum_eq_range,Int.Ico_eq_finset_map,Finset.sum_map]
  have h:lo+(n:ℤ) - lo=(n:ℤ):=by omega
  rw [h]
  rfl

theorem sum_eq_nat_Ico (a d : ℤ) (lo n : ℕ) :
    sum a d lo n = ∑ i ∈ Finset.Ico lo (lo+n),twiceTriangle (a+d*(i:ℤ)):=by
  rw [sum_eq_range,Finset.sum_Ico_eq_sum_range]
  have h:lo+n - lo=n:=by omega
  simp only [h,Nat.cast_add]

#print axioms sum_eq
#print axioms sum_eq_nat_Ico

private def firstPositive (a d:ℤ):ℕ:=((-a)/d+1).toNat

private theorem before_positive (a d : ℤ) (hd : 0 < d) {i : ℕ}
    (hi:i < firstPositive a d):a+d*(i:ℤ)≤0:=by
  have h:(i:ℤ)≤(-a)/d:=by unfold firstPositive at hi; omega
  have hm:=(Int.le_ediv_iff_mul_le hd).mp h
  linarith only [show d*(i:ℤ) ≤ -a by simpa [mul_comm] using hm]

private theorem after_positive (a d : ℤ) (hd : 0 < d) {i : ℕ}
    (hi:firstPositive a d≤ i):0≤a+d*(i:ℤ):=by
  have h:(-a)/d+1≤(i:ℤ):=by unfold firstPositive at hi; omega
  have hm:=Int.lt_ediv_add_one_mul_self (-a) hd
  have hb:=mul_le_mul_of_nonneg_right h hd.le
  have hx : -a < (i:ℤ)*d:=hm.trans_le hb
  linarith only [show -a < d*(i:ℤ) by simpa [mul_comm] using hx]

private theorem closed_of_nonneg (a d : ℤ) (n : ℕ)
    (h : ∀ i < n,0≤a+d*(i:ℤ)):rangeSum a d n=closed a d n:=by
  rw [rangeSum,closed_eq]
  exact Finset.sum_congr rfl fun i hi => by
    simp [twiceTriangle,max_eq_right (h i (Finset.mem_range.mp hi))]

private theorem zero_of_nonpos (a d : ℤ) (n : ℕ)
    (h : ∀ i < n,a+d*(i:ℤ)≤0):rangeSum a d n=0:=by
  exact Finset.sum_eq_zero fun i hi => by
    simp [twiceTriangle,max_eq_left (h i (Finset.mem_range.mp hi))]

private def fast (a d : ℤ) (n : ℕ) : ℤ :=
  if 0 < d then
    let j:=min n (firstPositive a d)
    if j=n then 0 else closed (a+d*(j:ℤ)) d (n-j)
  else if d < 0 then
    closed a d (min n (firstPositive (-a) (-d)))
  else
    (n:ℤ)*twiceTriangle a

private theorem fast_eq (a d : ℤ) (n : ℕ) : fast a d n = rangeSum a d n := by
  unfold fast
  by_cases hd:0 < d
  · rw [ite_eq_left hd]
    let j:=min n (firstPositive a d)
    change (if j=n then 0 else closed (a+d*(j:ℤ)) d (n-j))=_
    have hj:j≤n:=min_le_left _ _
    have hs:=rangeSum_add a d j (n-j)
    rw [Nat.add_sub_of_le hj] at hs
    have h0 : rangeSum a d j = 0 := zero_of_nonpos _ _ _ fun i hi =>
      before_positive a d hd (hi.trans_le (min_le_right _ _))
    rw [hs,h0,zero_add]
    by_cases hjn:j=n
    · simp [hjn,rangeSum]
    · rw [ite_eq_right hjn]
      symm
      apply closed_of_nonneg
      intro i hi
      have hstart:firstPositive a d≤j+i:=by dsimp [j] at hjn ⊢; omega
      simpa only [Nat.cast_add,mul_add,add_assoc] using after_positive a d hd hstart
  · rw [ite_eq_right hd]
    by_cases hd' : d < 0
    · rw [ite_eq_left hd']
      let j:=min n (firstPositive (-a) (-d))
      change closed a d j=_
      have hs:=rangeSum_add a d j (n-j)
      rw [Nat.add_sub_of_le (min_le_left _ _)] at hs
      rw [hs]
      have hn : rangeSum a d j = closed a d j := closed_of_nonneg _ _ _ (fun i hi => by
        have h:=before_positive (-a) (-d) (by omega) (hi.trans_le (min_le_right _ _))
        simpa only [neg_mul, ← neg_add,neg_nonpos] using h)
      rw [hn]
      suffices h0:rangeSum (a+d*(j:ℤ)) d (n-j)=0 by rw [h0,add_zero]
      apply zero_of_nonpos
      intro i hi
      have hstart:firstPositive (-a) (-d)≤j+i:=by dsimp [j] at hi ⊢; omega
      have h:=after_positive (-a) (-d) (by omega) hstart
      simpa only [Nat.cast_add,neg_mul, ← neg_add,neg_nonneg,mul_add,add_assoc] using h
    · have hz : d = 0 := by omega
      simp [hz,rangeSum,nsmul_eq_mul]

/-- Sum a positive triangular term using the unique sign crossing of the affine argument. -/
def sumFast (a d lo:ℤ) (n:ℕ):ℤ:=fast (a+d*lo) d n

theorem sumFast_eq_range (a d lo : ℤ) (n : ℕ) :
    sumFast a d lo n = ∑ i ∈ Finset.range n,twiceTriangle (a+d*(lo+(i:ℤ))):=by
  rw [sumFast,fast_eq,rangeSum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_add,add_assoc]

#print axioms sumFast_eq_range

end KoalaAffineTriangle

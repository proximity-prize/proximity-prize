import ProximityPrize.SubmissionLower.UpperBranch4

set_option Elab.async false

namespace HighCore82268JointRank

open Finset
open K1_14_2 (Ambient)
open P1_7_4 (Mass dotQ massQ running weightedBill bill_bound_terminal dotQ_nonneg massQ_nonneg)

/-- Insert an additional charge immediately before the old charge at `stop`. -/
def splice {α : Type*} (stop : ℕ) (extra : α) (old : ℕ → α) (i : ℕ) : α :=
  if i < stop then old i else if i=stop then extra else old (i-1)

private theorem sum_splice (old : ℕ → ℚ) (extra : ℚ) {n stop : ℕ} (hstop : stop ≤ n) :
    ∑ i ∈ range (n+1),splice stop extra old i=(∑ i ∈ range n,old i)+extra:=by
  induction n with
  | zero =>
    have:stop=0:=by omega
    subst stop
    simp [splice]
  | succ n ih =>
    rw [sum_range_succ]
    rcases hstop.lt_or_eq with hlt | rfl
    · rw [ih (by omega), sum_range_succ]
      have hs : ¬ n+1 < stop:=by omega
      have he:n+1≠stop:=by omega
      simp only [splice,ite_eq_right hs,ite_eq_right he,Nat.add_sub_cancel]
      ring
    · have hcong : (∑ i ∈ range (n+1), splice (n+1) extra old i) =
          ∑ i ∈ range (n+1),old i:=by
        apply sum_congr rfl
        intro i hi
        simp [splice,mem_range.mp hi]
      rw [hcong]
      simp [splice]

/-- Two exits can use one bill if the nested live sets account for both exits. -/
theorem bill_with_exit_terminal (n stop : ℕ) (hstop : stop ≤ n) (w bound : ℕ → Mass)
    (exitWeight exitBound:Mass) (live lost:ℕ→Finset (Ideal Ambient))
    (entry exit:Finset (Ideal Ambient))
    (next : ∀ i < n,live (i+1) ⊆ live i)
    (fail : ∀ i < n,lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k,massQ (live i) k≤bound i k)
    (entry_next:live stop ⊆ entry) (exit_diff:exit ⊆ entry \ live stop)
    (entry_prev : ∀ i,i+1=stop→entry ⊆ live i)
    (prev_diff : ∀ i,i+1=stop→lost i ⊆ live i \ entry)
    (entry_cap : ∀ k,massQ entry k≤exitBound k) :
    ((∑ i ∈ range n, dotQ (w i) (massQ (lost i))) + dotQ exitWeight (massQ exit)) +
      dotQ (running (splice stop exitWeight w) (n+1)) (massQ (live n)) ≤
      weightedBill (n+1) (splice stop exitWeight w) (splice stop exitBound bound):=by
  let l:=splice stop entry live
  let f:=splice stop exit lost
  have hnext : ∀ i < n+1, l (i+1) ⊆ l i := by
    intro i hi
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · by_cases hs : i+1 = stop
      · simpa [l,splice,hlt,hs] using entry_prev i hs
      · have hs' : i+1 < stop := by omega
        simpa [l,splice,hlt,hs'] using next i (by omega)
    · have hs : ¬ i+1 < i := by omega
      have he:i+1≠i:=by omega
      simpa [l,splice,hs,he] using entry_next
    · have hl : ¬ i < stop := by omega
      have he:i≠stop:=by omega
      have hs : ¬ i+1 < stop:=by omega
      have he' : i+1≠stop:=by omega
      have hx:=next (i-1) (by omega)
      rw [show i-1+1=i by omega] at hx
      simpa [l,splice,hl,he,hs,he'] using hx
  have hfail : ∀ i < n+1, f i ⊆ l i \ l (i+1) := by
    intro i hi
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · by_cases hs : i+1 = stop
      · simpa [l,f,splice,hlt,hs] using prev_diff i hs
      · have hs' : i+1 < stop := by omega
        simpa [l,f,splice,hlt,hs'] using fail i (by omega)
    · have hs : ¬ i+1 < i := by omega
      have he:i+1≠i:=by omega
      simpa [l,f,splice,hs,he] using exit_diff
    · have hl : ¬ i < stop := by omega
      have he:i≠stop:=by omega
      have hs : ¬ i+1 < stop:=by omega
      have he' : i+1≠stop:=by omega
      have hx:=fail (i-1) (by omega)
      rw [show i-1+1=i by omega] at hx
      simpa [l,f,splice,hl,he,hs,he'] using hx
  have hcap : ∀ i < n+1, ∀ k, massQ (l i) k ≤ splice stop exitBound bound i k := by
    intro i hi k
    rcases lt_trichotomy i stop with hlt | rfl | hgt
    · simpa [l,splice,hlt] using cap i (by omega) k
    · simpa [l,splice] using entry_cap k
    · have hl : ¬ i < stop := by omega
      have he:i≠stop:=by omega
      simpa [l,splice,hl,he] using cap (i-1) (by omega) k
  have h := bill_bound_terminal (n+1) (splice stop exitWeight w) (splice stop exitBound bound)
    l f hnext hfail hcap
  have hend : l (n+1) = live n := by
    simp [l,splice,show ¬ n+1 < stop by omega,show n+1≠stop by omega]
  rw [hend] at h
  have hsum : (∑ i ∈ range (n+1), dotQ (splice stop exitWeight w i) (massQ (f i))) =
      (∑ i ∈ range n,dotQ (w i) (massQ (lost i)))+dotQ exitWeight (massQ exit):=by
    rw [← sum_splice (fun i => dotQ (w i) (massQ (lost i))) (dotQ exitWeight (massQ exit)) hstop]
    apply sum_congr rfl
    intro i _
    by_cases hlt:i < stop
    · simp [f,splice,hlt]
    · by_cases heq:i=stop <;> simp [f,splice,hlt,heq]
  rwa [hsum] at h

/-- Two exits can use one bill if the nested live sets account for both exits. -/
theorem bill_with_exit (n stop : ℕ) (hstop : stop ≤ n) (w bound : ℕ → Mass)
    (exitWeight exitBound:Mass) (live lost:ℕ→Finset (Ideal Ambient))
    (entry exit:Finset (Ideal Ambient))
    (next : ∀ i < n,live (i+1) ⊆ live i)
    (fail : ∀ i < n,lost i ⊆ live i \ live (i+1))
    (cap : ∀ i < n, ∀ k,massQ (live i) k≤bound i k)
    (entry_next:live stop ⊆ entry) (exit_diff:exit ⊆ entry \ live stop)
    (entry_prev : ∀ i,i+1=stop→entry ⊆ live i)
    (prev_diff : ∀ i,i+1=stop→lost i ⊆ live i \ entry)
    (entry_cap : ∀ k,massQ entry k≤exitBound k) :
    (∑ i ∈ range n, dotQ (w i) (massQ (lost i))) + dotQ exitWeight (massQ exit) ≤
      weightedBill (n+1) (splice stop exitWeight w) (splice stop exitBound bound):=by
  have h := bill_with_exit_terminal n stop hstop w bound exitWeight exitBound live lost entry exit
    next fail cap entry_next exit_diff entry_prev prev_diff entry_cap
  have hreg:=P1_7_4.running_nonneg (splice stop exitWeight w) (n+1)
  exact (le_add_of_nonneg_right (dotQ_nonneg hreg (massQ_nonneg _))).trans h

/-- Linear bound for the nonlinear fixed-jet fee. -/
theorem fixed_fee_linear (L mu tau pivot : ℚ) (hL : 0 ≤ L) (hmu : 0 ≤ mu)
    (htau:0≤tau) (htau' : tau≤1) {B J Bmax Jmax:ℕ}
    (hJB:J≤B) (hB:B≤Bmax) (hJ:J≤Jmax) :
    let a:=mu+2*L*(B-1:ℕ)
    let v:=min a (L*(2*J-1:ℕ))
    ((((B-J : ℕ) : ℚ)*v + J*a).ceil.toNat + B^2 : ℕ) ≤
      ((4*L*Bmax*tau+mu-4*L*pivot)*J+(4*L*Jmax*(1-tau)+Bmax)*B+2*L*pivot^2+1:ℚ):=by
  dsimp only
  let a:=mu+2*L*(B-1:ℕ)
  let v:=min a (L*(2*J-1:ℕ))
  let q:ℚ:=((B-J:ℕ):ℚ)*v+J*a
  have ha:0≤a:=by dsimp [a]; positivity
  have hv:0≤v:=le_min ha (by positivity)
  have hq:0≤q:=by dsimp [q]; positivity
  have hb0:(0:ℚ)≤B:=Nat.cast_nonneg _
  have hj0:(0:ℚ)≤J:=Nat.cast_nonneg _
  have hb:(B:ℚ)≤Bmax:=by exact_mod_cast hB
  have hj:(J:ℚ)≤Jmax:=by exact_mod_cast hJ
  have hqceil : 0 ≤ q.ceil := by
    have h:(0:ℚ)≤(q.ceil:ℚ):=hq.trans Rat.le_ceil
    exact_mod_cast h
  have hc : ((q.ceil.toNat : ℕ) : ℚ) ≤ q + 1 := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hqceil]
    exact Rat.ceil_lt.le
  have hva : v ≤ 2*L*J := by
    have hd:((2*J-1:ℕ):ℚ)≤2*J:=by exact_mod_cast Nat.sub_le (2*J) 1
    exact (min_le_right _ _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hL])
  have haa : a ≤ mu + 2*L*B := by
    have hd:((B-1:ℕ):ℚ)≤B:=by exact_mod_cast Nat.sub_le B 1
    dsimp [a]
    nlinarith only [mul_le_mul_of_nonneg_left hd hL]
  have hfirst : ((B-J : ℕ) : ℚ)*v ≤ ((B : ℚ)-J)*(2*L*J) := by
    rw [Nat.cast_sub hJB]
    exact mul_le_mul_of_nonneg_left hva (sub_nonneg.mpr (by exact_mod_cast hJB))
  have hsecond:=mul_le_mul_of_nonneg_left haa hj0
  have hq' : q ≤ 4*L*B*J + mu*J - 2*L*J^2 := by
    dsimp [q]
    linarith only [hfirst,hsecond]
  have hleft:=mul_le_mul_of_nonneg_left hb (show 0≤4*L*tau*J by positivity)
  have hright := mul_le_mul_of_nonneg_left hj
    (show 0≤4*L*(1-tau)*B by positivity)
  have hsq:=mul_le_mul_of_nonneg_left hb hb0
  have htan : -2*L*(J : ℚ)^2 ≤ -4*L*pivot*J + 2*L*pivot^2 := by
    nlinarith only [mul_nonneg hL (sq_nonneg ((J:ℚ)-pivot))]
  change ((q.ceil.toNat+B^2:ℕ):ℚ)≤_
  push_cast
  nlinarith only [hq', hc,hleft,hright,hsq,htan]

#print axioms bill_with_exit
#print axioms fixed_fee_linear

end HighCore82268JointRank

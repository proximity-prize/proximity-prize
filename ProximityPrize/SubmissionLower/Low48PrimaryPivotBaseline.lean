import ProximityPrize.SubmissionLower.Primary82170
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Low48PrimaryPivot
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

def rawWindow (w : Window) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then baseline i else 0

private def baselineFast (g o : ℕ) : ℕ :=
  let delta := (o : ℤ) - 1650
  let F : Flag := ⟨min (g : ℤ) 1650, -delta, 1650, 550, 3000-(g : ℤ)-delta⟩
  if F.order ≤ 0 then 0 else
    let active := oldCount { F with upper := min F.upper (2999-delta) }
    (min active (oldCount F - max 0 (kernelLower F))).toNat

private theorem baseline_eq (i : BlockIndex) :
    baseline i = baselineFast i.1.val i.2.val := by
  have residual_zero (F : Flag) : residualFlag F (fun _ => 0) = F := by
    cases F
    simp [residualFlag]
  simp only [baseline, blockBound, baselineFast, initialFlag, offset, residual_zero, max_self]

def rawAt (w : Window) (o : ℕ) : ℕ :=
  let lo := max w.gradeLo (w.diagonalLo-o)
  let hi := min w.gradeHi (w.diagonalHi+1-o)
  ((List.range' lo (hi-lo)).map fun g => baselineFast g o).sum

def rawCompute (w : Window) : ℕ :=
  ((List.range' w.offsetLo (w.offsetHi+1-w.offsetLo)).map (rawAt w)).sum

private theorem sum_fin_mod (n : ℕ) [NeZero n] (f : Fin n → ℕ) :
    (∑ i, f i) = ∑ i ∈ range n, f (Fin.ofNat n i) := by
  calc
    (∑ i, f i) = ∑ i : Fin n, f (Fin.ofNat n i.val) := by
      apply sum_congr rfl
      intro i _
      have h : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      rw [h]
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => f (Fin.ofNat n i)) n

theorem raw_eq_compute (w : Window) (hg : w.gradeHi ≤ 4013)
    (ho : w.offsetHi < 4650) : rawWindow w = rawCompute w := by
  classical
  unfold rawWindow rawCompute
  rw [Fintype.sum_prod_type]
  rw [sum_comm]
  have row (o : Fin 4650) :
      (∑ g : Fin 4013, if w.Contains (g,o) then baseline (g,o) else 0) =
        if w.offsetLo ≤ (o : ℕ) ∧ (o : ℕ) ≤ w.offsetHi then rawAt w o else 0 := by
    rw [sum_fin_mod 4013 (fun g => if w.Contains (g,o) then baseline (g,o) else 0)]
    by_cases hh : w.offsetLo ≤ (o : ℕ) ∧ (o : ℕ) ≤ w.offsetHi
    · rw [if_pos hh]
      let lo := max w.gradeLo (w.diagonalLo-o.val)
      let hi := min w.gradeHi (w.diagonalHi+1-o.val)
      have hif (g : ℕ) (hmem : g ∈ range 4013) :
          (if w.Contains (Fin.ofNat 4013 g,o) then baseline (Fin.ofNat 4013 g,o) else 0) =
            if g ∈ Ico lo hi then baselineFast g o.val else 0 := by
        have hlt : g < 4013 := mem_range.mp hmem
        have hv : (Fin.ofNat 4013 g).val = g := Nat.mod_eq_of_lt hlt
        have heq : w.Contains (Fin.ofNat 4013 g,o) ↔ g ∈ Ico lo hi := by
          simp only [Window.Contains, hv, mem_Ico, lo, hi, max_le_iff, lt_min_iff]
          omega
        simp only [heq, baseline_eq, hv]
      rw [sum_congr rfl hif, ← sum_filter]
      have hfilter : (range 4013).filter (fun g => g ∈ Ico lo hi) = Ico lo hi := by
        ext g
        simp only [mem_filter, mem_range, mem_Ico, lo, hi, max_le_iff, lt_min_iff]
        omega
      rw [hfilter]
      rw [Nat.Ico_eq_range']
      rfl
    · rw [if_neg hh]
      apply sum_eq_zero
      intro g _
      exact if_neg (fun h => hh ⟨h.2.2.1,h.2.2.2.1⟩)
  simp_rw [row]
  rw [Fin.sum_univ_eq_sum_range
    (fun o => if w.offsetLo ≤ o ∧ o ≤ w.offsetHi then rawAt w o else 0) 4650]
  rw [← sum_filter]
  have hfilter : (range 4650).filter (fun o => w.offsetLo ≤ o ∧ o ≤ w.offsetHi) =
      Ico w.offsetLo (w.offsetHi+1) := by
    ext o
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, Nat.Ico_eq_range']
  rfl

#print axioms raw_eq_compute
end Low48PrimaryPivot

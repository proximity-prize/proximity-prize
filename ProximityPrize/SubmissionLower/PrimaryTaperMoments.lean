import ProximityPrize.SubmissionLower.PrimaryTaperBudget

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace TaperMoments

open K1_13_2 (denominator cumulative)
open K1_13_2_2 (cumulativeColumns oldWeight CumulativeCount)
open TaperBudget (cap)
open Finset
open scoped BigOperators

open private scaled_denominator polyDen denominator_of_neg from ProximityPrize.SubmissionLower.Fast022

/-- Twenty-four times the sum of the denominator counts at indices strictly below `n`. -/
def denPrefix (n : ℤ) : ℤ :=
  if n < 0 then 0 else
    let q := n / 6
    let r := n % 6
    984*q + 3084*q*(q-1) + 1728*q*(q-1)*(q-2) + 216*q*(q-1)*(q-2)*(q-3) +
      24*r + 4*r*(r-1)*(r+1) + 12*q*(44*r + 7*r*(r-1)) +
      4*q*r*(r-1)*(r-2) + 12*q*(q-1)*(57*r + 3*r*(r-1)) +
      144*r*q*(q-1)*(q-2)

theorem denPrefix_succ (n : ℤ) :
    denPrefix (n+1) = denPrefix n + 24 * denominator n := by
  by_cases hn : n < 0
  · rw [denominator_of_neg _ hn, show denPrefix n = 0 by simp [denPrefix, hn]]
    by_cases h : n + 1 < 0
    · simp [denPrefix, h]
    · have he : n + 1 = 0 := by omega
      rw [he]
      rfl
  have hn₁ : ¬ n + 1 < 0 := by omega
  have hden := scaled_denominator n (by omega)
  let q := n / 6
  let r := n % 6
  have hq : n / 6 = q := rfl
  have hr : n % 6 = r := rfl
  simp only [denPrefix, ite_eq_right hn, ite_eq_right hn₁, hq, hr]
  rw [hq, hr] at hden
  unfold polyDen at hden
  by_cases hf : r = 5
  · have hq₁ : (n+1)/6 = q+1 := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = 0 := by dsimp [r] at *; omega
    rw [hq₁, hr₁, hf]
    rw [hf] at hden
    linear_combination -12*hden
  · have hq₁ : (n+1)/6 = q := by dsimp [q, r] at *; omega
    have hr₁ : (n+1)%6 = r+1 := by dsimp [r] at *; omega
    rw [hq₁, hr₁]
    linear_combination -12*hden

private theorem shift_succ (n a : ℤ) :
    denPrefix ((n+1)-a) = denPrefix (n-a) + 24 * denominator (n-a) := by
  rw [show n+1-a = (n-a)+1 by ring, denPrefix_succ]

private def basePrefix (d u : ℤ) : ℤ :=
  denPrefix u - denPrefix (u-(d+1)) - denPrefix (u-(d+2)) - denPrefix (u-(d+3)) +
  denPrefix (u-(2*d+3)) + denPrefix (u-(2*d+4)) + denPrefix (u-(2*d+5)) -
  denPrefix (u-(3*d+6))

def cumPrefix (d n : ℕ) : ℤ :=
  let u := min n (3*d+1)
  basePrefix d u + 24 * ((n-u : ℕ) : ℤ) * cumulative d (3*d)

private theorem basePrefix_succ (d n : ℕ) (hn : n ≤ 3*d) :
    basePrefix d ((n : ℤ)+1) = basePrefix d n + 24 * cumulative d n := by
  have hzn : ¬ (n : ℤ) < 0 := by omega
  have hzd : ¬ (d : ℤ) < 0 := by omega
  have hnd : (n : ℤ) ≤ 3*d := by omega
  simp only [basePrefix, denPrefix_succ n, shift_succ, cumulative, hzn, hzd,
    Bool.false_or, decide_false, Bool.false_eq_true, ite_false, min_eq_left hnd]
  ring

theorem cumPrefix_succ (d n : ℕ) :
    cumPrefix d (n+1) = cumPrefix d n + 24 * cumulative d n := by
  by_cases h : n ≤ 3*d
  · simp only [cumPrefix, min_eq_left (show n+1 ≤ 3*d+1 by omega),
      min_eq_left (show n ≤ 3*d+1 by omega), Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul,
      add_zero, Nat.cast_add, Nat.cast_one, basePrefix_succ d n h]
  · have hcast : (3*d+1 : ℕ) ≤ n := by omega
    have hn : (3 : ℤ) * d ≤ n := by omega
    have he : cumulative d n = cumulative d (3*d) := by
      simp [cumulative, show ¬ (d : ℤ) < 0 by omega, show ¬ (n : ℤ) < 0 by omega,
        show ¬ (3 : ℤ)*d < 0 by omega, min_eq_right hn]
    simp only [cumPrefix, min_eq_right hcast,
      min_eq_right (show 3*d+1 ≤ n+1 by omega), he]
    have hsub : (n+1-(3*d+1) : ℕ) = n-(3*d+1)+1 := by omega
    simp only [hsub, Nat.cast_add, Nat.cast_one]
    ring

theorem cumulative_prefix (d n : ℕ) :
    24 * (∑ u ∈ range n, cumulative d (u : ℤ)) = cumPrefix d n := by
  induction n with
  | zero =>
      have hz (v : ℤ) (hv : v ≤ 0) : denPrefix v = 0 := by
        rcases lt_or_eq_of_le hv with h | rfl
        · simp [denPrefix, h]
        · rfl
      simp only [sum_range_zero, mul_zero, cumPrefix, zero_min, Nat.sub_zero, Nat.cast_zero,
        zero_mul, add_zero, basePrefix]
      symm
      simp only [hz 0 (le_refl _), hz (0-((d : ℤ)+1)) (by omega),
        hz (0-((d : ℤ)+2)) (by omega), hz (0-((d : ℤ)+3)) (by omega),
        hz (0-(2*(d : ℤ)+3)) (by omega), hz (0-(2*(d : ℤ)+4)) (by omega),
        hz (0-(2*(d : ℤ)+5)) (by omega), hz (0-(3*(d : ℤ)+6)) (by omega),
        sub_zero, add_zero]
  | succ n ih => rw [sum_range_succ, mul_add, ih, cumPrefix_succ d n]

/-- Weighted-index sum of the retained jets, scaled by 24. -/
def indexMoment (d : ℕ) : ℤ :=
  24 * 1650 * cumulative d 1650 - cumPrefix d 1650

private theorem count_range_ge (v j : ℕ) :
    (∑ u ∈ range j, if v ≤ u then (1 : ℕ) else 0) = j-v := by
  have hset : (range j).filter (fun u => v ≤ u) = Ico v j := by
    ext x
    simp [and_comm]
  rw [← sum_filter, ← card_eq_sum_ones, hset, Nat.card_Ico]

theorem indexMoment_eq (hc : CumulativeCount) (d : ℕ) :
    indexMoment d = 24 * ∑ e ∈ cumulativeColumns d 1650, (e.weight oldWeight : ℤ) := by
  let F := cumulativeColumns d 1650
  have hfilter (u : ℕ) (hu : u < 1650) :
      cumulativeColumns d u = F.filter (fun m => m.weight oldWeight ≤ u) := by
    ext m
    simp only [F, mem_filter, K1_13_2_2.mem_cumulativeColumns]
    change ((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ u) ↔
      (((m.weight K1_13_2_2.gradeWeight : ℤ) = d ∧ (m.weight oldWeight : ℤ) ≤ 1650) ∧
        m.weight oldWeight ≤ u)
    omega
  have hswap : (∑ u ∈ range 1650, (cumulativeColumns d u).card) =
      ∑ e ∈ F, (1650 - e.weight oldWeight) := by
    calc
      _ = ∑ u ∈ range 1650, ∑ e ∈ F, if e.weight oldWeight ≤ u then 1 else 0 := by
        apply sum_congr rfl
        intro u hu
        rw [hfilter u (mem_range.mp hu), card_eq_sum_ones, sum_filter]
      _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun e _ => count_range_ge _ _
  have hcast : (∑ u ∈ range 1650, cumulative d (u : ℤ)) =
      ∑ e ∈ F, (1650 - (e.weight oldWeight : ℤ)) := by
    have hu (u : ℕ) := hc (d : ℤ) (u : ℤ)
    simp_rw [← hu]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    apply sum_congr rfl
    intro e he
    have h := (K1_13_2_2.mem_cumulativeColumns.mp he).2
    rw [Nat.cast_sub (by exact_mod_cast h), Nat.cast_ofNat]
  unfold indexMoment
  rw [← cumulative_prefix, hcast, ← hc d 1650]
  have hF : (cumulativeColumns d 1650).card = F.card := rfl
  rw [hF, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  ring

open TaperNormalize (differentiated Eligible)
open K1_13 (Geom)
open K1_13_2 (SourceExponent SourcePolynomial)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finsupp

def gradeCap (q : ℕ) : ℕ := min q (cap q)

def sourceCount : ℤ := ∑ q ∈ range 4013, cumulative (gradeCap q) 1650

def sourceDegree : ℤ := ∑ q ∈ range 4013, (q : ℤ) * cumulative (gradeCap q) 1650

def sourceIndex24 : ℤ := ∑ q ∈ range 4013, indexMoment (gradeCap q)

end TaperMoments

import ProximityPrize.SubmissionLower.Z6970PolePrices

set_option autoImplicit false
namespace PoleAffine6970
open Finset

theorem twice_tri (k : ℕ) : 2*tri k = k*(k+1) := by
  simpa [tri, Nat.mul_comm] using (Nat.add_one_mul_choose_eq k 1).symm

theorem twice_diff (k H : ℕ) : 2*(tri k-tri (k-H)) = min k H*(2*k+1-min k H) := by
  by_cases hk : k ≤ H
  · rw [min_eq_left hk, Nat.sub_eq_zero_of_le hk, show 2*k+1-k = k+1 by omega,
      show tri 0 = 0 by decide, Nat.sub_zero, twice_tri]
  have hh : H ≤ k := by omega
  rw [min_eq_right hh, show 2*k+1-H = 2*(k-H)+H+1 by omega]
  have hle : tri (k-H) ≤ tri k := Nat.choose_le_choose 2 (by omega : k-H+1 ≤ k+1)
  have sum := Nat.sub_add_cancel hle
  have val := twice_tri k
  have prev := twice_tri (k-H)
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hh
  simp only [Nat.add_sub_cancel_left] at sum prev ⊢
  nlinarith only [sum, val, prev]

theorem late_cut (B J e : ℕ) (shape : 2*J ≤ B) (pos : 0 < e) (size : e ≤ 2*J) :
    let w := min (J+1) e
    let p := (e+1)/2
    let d := (p*(e+1-p)-1)/w
    d ≤ J ∧ w ≤ B-d+1 := by
  let w := min (J+1) e
  let p := (e+1)/2
  have wp : 0 < w := by dsimp [w]; omega
  have h1 : p ≤ w := by dsimp [p,w]; omega
  have h2 : e+1-p ≤ J+1 := by dsimp [p]; omega
  have prod : p*(e+1-p) ≤ (J+1)*w := (Nat.mul_le_mul h1 h2).trans_eq (Nat.mul_comm _ _)
  have positive : 0 < (J+1)*w := Nat.mul_pos (by omega) wp
  have lt : p*(e+1-p)-1 < (J+1)*w := by omega
  let d := (p*(e+1-p)-1)/w
  have bound : d ≤ J := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul wp).mpr lt)
  change d ≤ J ∧ w ≤ B-d+1
  have wh : w ≤ J+1 := min_le_left _ _
  exact ⟨bound, by omega⟩

theorem reverse_tail (B J n : ℕ) : (∑ i ∈ range n, tailTerm B J (n-i)) = tailSum B J n := by
  have normal (m : ℕ) : (∑ i ∈ range m, tailTerm B J (i+1)) = tailSum B J m := by
    induction m with
    | zero => simp [tailSum]
    | succ m ih => rw [sum_range_succ, ih, tailSum]
  calc
    _ = ∑ i ∈ range n, tailTerm B J ((n-1-i)+1) := by
      refine sum_congr rfl fun i hi => ?_
      have := mem_range.mp hi
      congr 1 <;> omega
    _ = _ := (sum_range_reflect (fun i => tailTerm B J (i+1)) n).trans (normal n)

end PoleAffine6970

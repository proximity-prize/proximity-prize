import ProximityPrize.SubmissionBinaryLower.P64C7ProfileArithmetic

/-!
# Low bias and failure of interpolation imply the profile bound

Only the allowed `t=4` interpolation test is used, with a parameter respecting
the existing `StGood` box cap. No unbounded interpolation parameter is assumed.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Profile

open Polynomial P64LineOrder P64Cofactor P64Light P64Aux P64S3 P64C7ProfileArithmetic

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem profile_le (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) (R : Tri)
    (hirr : Irreducible R) (hh : 4 ≤ R.natDegree)
    (hw : wd R 1048575 ≤ 249292 * 1482911 - 1)
    (hgood : ∀ t q, ¬ StGood ω u₀ u₁ R t q)
    (hβ : R.natDegree * 1482911 - ∑ i, lineOrd R (ω i) (lineOf u₀ u₁ i) <
      1000 * R.natDegree) :
    2 * (R.natDegree : ℤ) * wd R 1048575 - R.natDegree ^ 2 * 1048575 -
      (∑ i, (lineOrd R (ω i) (lineOf u₀ u₁ i) : ℤ) ^ 2) ≤ 65536 * R.natDegree ^ 2 := by
  classical
  let h := R.natDegree
  let w := wd R 1048575
  let μ : Fin 2097152 → ℕ := fun i => lineOrd R (ω i) (lineOf u₀ u₁ i)
  let W := 4 * w - 1482911
  let c := con ω u₀ u₁ R 4
  have hlow : 1048575 * h ≤ w := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero _
  have hcap : h ≤ 352552 := by dsimp [h, w] at *; omega
  have hA : 1482911 ≤ 4 * w := by dsimp [h] at hlow; omega
  have hJ : W / 1048575 ≤ 2097152 := Nat.div_le_of_le_mul (by dsimp [W, w]; omega)
  have hμh : ∀ i, μ i ≤ h := fun i =>
    lineOrd_le_natDegree_of_irreducible hirr (by omega) (ω i) (lineOf u₀ u₁ i)
  have hc : (c : ℤ) = 8 * (∑ i, (μ i : ℤ) ^ 2) - 2 * (∑ i, (μ i : ℤ)) := by
    dsimp [c, con]
    rw [Nat.cast_sum]
    simp_rw [con_term]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS₂ : (∑ i, (μ i : ℤ) ^ 2) ≤ (h : ℤ) ^ 2 * 2097152 := by
    calc _ ≤ ∑ _ : Fin 2097152, (h : ℤ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast Nat.pow_le_pow_left (hμh i) 2
      _ = _ := by simp; ring
  have hS₁nonneg : (0 : ℤ) ≤ ∑ i, (μ i : ℤ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hcle : c ≤ 8 * h ^ 2 * 2097152 := by
    have he : (c : ℤ) ≤ 8 * h ^ 2 * 2097152 := by nlinarith only [hc, hS₂, hS₁nonneg]
    exact_mod_cast he
  have hcrit : 234354625592 * P64Surf.Mbox W ≤ (234354625592 + W / 1048575) * c := by
    by_contra hn
    apply hgood 4 234354625592
    refine ⟨by norm_num, by norm_num, hA, ?_, by norm_num, ?_⟩
    · change 4 * h ≤ 234354625592
      omega
    · change (234354625592 + W / 1048575) * c < 234354625592 * P64Surf.Mbox W
      omega
  have hM := count_slack h (W / 1048575) c (P64Surf.Mbox W) hJ hcle hcrit
  have hM' : (P64Surf.Mbox W : ℤ) ≤ 8 * (∑ i, (μ i : ℤ) ^ 2) -
      2 * (∑ i, (μ i : ℤ)) + 256 * h ^ 2 := by
    have he : (P64Surf.Mbox W : ℤ) ≤ c + 256 * h ^ 2 := by exact_mod_cast hM
    rwa [hc] at he
  have hW : (W : ℤ) = 4 * w - 1482911 := by
    dsimp [W]
    rw [Nat.cast_sub hA]
    push_cast
    rfl
  have hS₁ : (h : ℤ) * 1481911 ≤ ∑ i, (μ i : ℤ) := by
    have he : h * 1481911 ≤ ∑ i, μ i := by
      change h * 1482911 - ∑ i, μ i < 1000 * h at hβ
      omega
    exact_mod_cast he
  apply profile_algebra h w (∑ i, (μ i : ℤ)) (∑ i, (μ i : ℤ) ^ 2)
    (by exact_mod_cast hh) hS₁
  have hm := mbox_quadratic_lower W
  rw [hW] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hM' (by norm_num))

end P64C7Profile
end ProximityPrize.SubmissionBinaryLower

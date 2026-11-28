import ProximityPrize.SubmissionLower.Fast074
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace R6970FatMoments
open Finset K1_13_4_2 K1_13_4_2_1
private abbrev Triple := Σ _ : ℕ, Σ _ : ℕ, ℕ
private def byGrade (B : ℕ) : Finset Triple :=
  (range (B + 1)).sigma fun q => (range (min q 1150 + 1)).sigma fun k =>
    range (min (q - k) (2300 - 2 * k) + 1)
private def byDeficit (B : ℕ) : Finset Triple :=
  (range 1151).sigma fun k => (range (2300 - 2 * k + 1)).sigma fun l =>
    range (B - (k + l) + 1)
set_option linter.constructorNameAsVariable false in
private theorem jetSum_deficit {M : Type*} [AddCommMonoid M] {B : ℕ} (hB : 2300 ≤ B)
    (f : ℕ → ℕ → ℕ → M) :
    jetSum B (fun q k l => f k l (B - q)) =
      ∑ k ∈ range 1151, ∑ l ∈ range (2300 - 2 * k + 1),
        ∑ r ∈ range (B - (k + l) + 1), f k l r := by
  calc
    _ = ∑ t ∈ byGrade B, f t.2.1 t.2.2 (B - t.1) := by
      simp only [jetSum, byGrade, sum_sigma]
    _ = ∑ t ∈ byDeficit B, f t.1 t.2.1 t.2.2 := by
      refine sum_nbij' (fun t : Triple => ⟨t.2.1, t.2.2, B - t.1⟩)
        (fun t : Triple => ⟨B - t.2.2, t.1, t.2.1⟩) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨k, l, r⟩ h
        simp only [byGrade, byDeficit, mem_sigma, mem_range, Nat.lt_succ_iff, le_min_iff] at *
        omega
      · rintro ⟨q, k, l⟩ h
        simp only [byGrade, mem_sigma, mem_range] at h
        rw [show B - (B - q) = q by omega]
      · rintro ⟨k, l, r⟩ h
        simp only [byDeficit, mem_sigma, mem_range] at h
        rw [show B - (B - r) = r by omega]
    _ = _ := by simp only [byDeficit, sum_sigma]

def sumJets (f : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ∑ k ∈ range 1151, ∑ j ∈ range (2301-2*k),
    ∑ i ∈ range (6821-k-j), f k j i

private theorem deficit (f : ℕ → ℕ → ℕ → ℕ) :
    sumJets f = jetSum 6820 (fun q k j => f k j (6820-q)) := by
  refine Eq.trans ?_ (jetSum_deficit (B := 6820) (by decide) f).symm
  unfold sumJets
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [show 2301-2*k = 2300-2*k+1 by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [show 6821-k-j = 6820-(k+j)+1 by omega]

theorem from_moment (c a d e value : ℕ)
    (hc : antidifference (slice 6820 c a d e) 1151 = 17280 * (value : ℤ)) :
    sumJets (fun k j i => c + a*(j+2*k) + d*i + e*i^2) = value :=
  (deficit _).trans (moment_eq 6820 c a d e value (by decide) hc)

theorem const_moment (c value : ℕ)
    (hc : antidifference (slice 6820 c 0 0 0) 1151 = 17280 * (value : ℤ)) :
    sumJets (fun _ _ _ => c) = value := by
  simpa only [Nat.zero_mul, Nat.add_zero] using from_moment c 0 0 0 value hc

end R6970FatMoments

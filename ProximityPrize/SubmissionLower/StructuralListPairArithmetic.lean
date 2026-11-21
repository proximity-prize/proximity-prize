import ProximityPrize.SubmissionLower.StructuralListPrice

set_option Elab.async false
set_option maxRecDepth 6000

namespace StructuralList

open CJ0 CJ0_4
open private cap_forms expo_big affine_scaled from ProximityPrize.SubmissionLower.StructuralListArithmetic
open private surfaceBound from ProximityPrize.SubmissionLower.ListProofA

/-- Each shortened degree cap is at most its share of the full cap. -/
theorem bandCapScale (s : Source) (hs : ShapeOK s) (L : ℕ) (hl : 3 ≤ L) (hk : L ≤ k)
    (hJ : 2 * s.C + 1 ≤ s.J) :
    (k : ℚ) * totalCap s L ≤ (L : ℚ) * totalCap s k ∧
    (k : ℚ) * indexCap s L ≤ (L : ℚ) * indexCap s k ∧
    (k : ℚ) * topCap s L ≤ (L : ℚ) * topCap s k := by
  refine ⟨(volumeScale s hs L hl hk hJ).1, ?_⟩
  obtain ⟨_, hd, he⟩ := cap_forms s hs L hl hJ
  obtain ⟨_, hD, hE⟩ := cap_forms s hs k (by decide) hJ
  rw [hd, he, hD, hE, expo_big (show 5 ≤ k by decide)]
  have hC : (1 : ℚ) ≤ s.C := Nat.cast_le.mpr hs.top_pos
  have hJq : (2 : ℚ) ≤ s.J := by exact_mod_cast (show 2 ≤ s.J by have := hs.top_pos; omega)
  have hlq : (L : ℚ) ≤ k := Nat.cast_le.mpr hk
  by_cases hlarge : 5 ≤ L
  · rw [expo_big hlarge]
    have hj := affine_scaled (m := 2*((s.J : ℚ)-2)+1) hlq (show -1-7*((s.J : ℚ)-2) ≤ 0 by linarith)
    have ht := affine_scaled (m := 2*((s.C : ℚ)-1)+1) hlq (show -2-7*((s.C : ℚ)-1) ≤ 0 by linarith)
    exact ⟨by nlinarith only [hj], by nlinarith only [ht]⟩
  · have hs : L = 3 ∨ L = 4 := by omega
    rcases hs with rfl | rfl <;> norm_num [exponent, k] <;> constructor
    all_goals nlinarith only [hC, hJq]

/-- The leading term for a proper cut in a band of length L. -/
theorem bandDoubleDifference (a d e b j c L : ℚ) :
    ∃ v : ℚ, ∀ x : ℚ,
      bandCount (x*a) (x*d) (x*e) - bandCount (x*a-b) (x*d-j) (x*e-c) -
        (bandCount ((x-L)*a) ((x-L)*d) ((x-L)*e) -
          bandCount ((x-L)*a-b) ((x-L)*d-j) ((x-L)*e-c)) =
      L * surfaceBound a d e b j c * x + v := by
  let f (x : ℚ) := bandCount (x*a) (x*d) (x*e) - bandCount (x*a-b) (x*d-j) (x*e-c) -
    (bandCount ((x-L)*a) ((x-L)*d) ((x-L)*e) - bandCount ((x-L)*a-b) ((x-L)*d-j) ((x-L)*e-c))
  refine ⟨f 0, fun x => ?_⟩
  dsimp [f, bandCount, surfaceBound]
  ring

end StructuralList

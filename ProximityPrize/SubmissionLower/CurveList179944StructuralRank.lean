import ProximityPrize.SubmissionLower.CurveList179944StructuralRankRank
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace CurveList179944StructuralRank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

private theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 71) (J := 21) (C := 9) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 71
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 71 - (b+c) + 1
private def bRange (c : ℕ) := range (21 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_count : source.E.card = ∑ c ∈ range 10, countRow c := by
  simp only [source, fullBox, card_sigma, card_range, countRow, bRange, runLength]
private theorem box_total : (∑ j ∈ source.E, j.q) = ∑ c ∈ range 10, totalRow c := by
  simp only [source, fullBox, sum_sigma, totalRow, bRange, runLength, Jet.q, Jet.a, Jet.b, Jet.c]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range, smul_eq_mul, Nat.mul_add]
private theorem box_index : (∑ j ∈ source.E, j.v) = ∑ c ∈ range 10, indexRow c := by
  simp only [source, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
private theorem row0 : countRow 0 = 1353 ∧ totalRow 0 = 54692 ∧ indexRow 0 = 13321 := by decide +kernel
private theorem row1 : countRow 1 = 1230 ∧ totalRow 1 = 49790 ∧ indexRow 1 = 13480 := by decide +kernel
private theorem row2 : countRow 2 = 1107 ∧ totalRow 2 = 44868 ∧ indexRow 2 = 13353 := by decide +kernel
private theorem row3 : countRow 3 = 984 ∧ totalRow 3 = 39928 ∧ indexRow 3 = 12944 := by decide +kernel
private theorem row4 : countRow 4 = 861 ∧ totalRow 4 = 34972 ∧ indexRow 4 = 12257 := by decide +kernel
private theorem row5 : countRow 5 = 738 ∧ totalRow 5 = 30002 ∧ indexRow 5 = 11296 := by decide +kernel
private theorem row6 : countRow 6 = 615 ∧ totalRow 6 = 25020 ∧ indexRow 6 = 10065 := by decide +kernel
private theorem row7 : countRow 7 = 492 ∧ totalRow 7 = 20028 ∧ indexRow 7 = 8568 := by decide +kernel
private theorem row8 : countRow 8 = 369 ∧ totalRow 8 = 15028 ∧ indexRow 8 = 6809 := by decide +kernel
private theorem row9 : countRow 9 = 246 ∧ totalRow 9 = 10022 ∧ indexRow 9 = 4792 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 10, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 7995 ∧ (∑ j ∈ source.E, j.q) = 324350 ∧ (∑ j ∈ source.E, j.v) = 106885 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2]

theorem surplus : Surplus 179944 source 123194 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide : 262144*123194+131071*324350 < 52*179944*7995+106885)

end
end CurveList179944StructuralRank

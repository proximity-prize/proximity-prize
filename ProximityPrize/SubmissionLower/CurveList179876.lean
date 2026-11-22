import ProximityPrize.SubmissionLower.CurveList179876Rank
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace CurveList179876
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open private curve_johnson from ProximityPrize.SubmissionLower.RungSplit
open scoped BigOperators

private theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 75) (J := 22) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 75
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 75 - (b+c) + 1
private def bRange (c : ℕ) := range (22 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_count : source.E.card = ∑ c ∈ range 11, countRow c := by
  simp only [source, fullBox, card_sigma, card_range, countRow, bRange, runLength]
private theorem box_total : (∑ j ∈ source.E, j.q) = ∑ c ∈ range 11, totalRow c := by
  simp only [source, fullBox, sum_sigma, totalRow, bRange, runLength, Jet.q, Jet.a, Jet.b, Jet.c]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range, smul_eq_mul, Nat.mul_add]
private theorem box_index : (∑ j ∈ source.E, j.v) = ∑ c ∈ range 11, indexRow c := by
  simp only [source, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
private theorem row0 : countRow 0 = 1495 ∧ totalRow 0 = 63779 ∧ indexRow 0 = 15433 := by decide +kernel
private theorem row1 : countRow 1 = 1365 ∧ totalRow 1 = 58310 ∧ indexRow 1 = 15610 := by decide +kernel
private theorem row2 : countRow 2 = 1235 ∧ totalRow 2 = 52820 ∧ indexRow 2 = 15485 := by decide +kernel
private theorem row3 : countRow 3 = 1105 ∧ totalRow 3 = 47311 ∧ indexRow 3 = 15062 := by decide +kernel
private theorem row4 : countRow 4 = 975 ∧ totalRow 4 = 41785 ∧ indexRow 4 = 14345 := by decide +kernel
private theorem row5 : countRow 5 = 845 ∧ totalRow 5 = 36244 ∧ indexRow 5 = 13338 := by decide +kernel
private theorem row6 : countRow 6 = 715 ∧ totalRow 6 = 30690 ∧ indexRow 6 = 12045 := by decide +kernel
private theorem row7 : countRow 7 = 585 ∧ totalRow 7 = 25125 ∧ indexRow 7 = 10470 := by decide +kernel
private theorem row8 : countRow 8 = 455 ∧ totalRow 8 = 19551 ∧ indexRow 8 = 8617 := by decide +kernel
private theorem row9 : countRow 9 = 325 ∧ totalRow 9 = 13970 ∧ indexRow 9 = 6490 := by decide +kernel
private theorem row10 : countRow 10 = 195 ∧ totalRow 10 = 8384 ∧ indexRow 10 = 4093 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 9295 ∧ (∑ j ∈ source.E, j.q) = 397969 ∧ (∑ j ∈ source.E, j.v) = 130988 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179876 source 151799 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide : 262144*151799+131071*397969 < 55*179876*9295+130988)

theorem list_price : CJ0.L 179876 source = 9715183252893098 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179876 9715183252893098 := by
  have hA : AgreementOK 179876 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 76 := by
    intro j hj hcut
    have hq : j.q ≤ 75 := (native_shape.support j hj).1
    omega
  have h := curve_johnson 179876 source 151799 hA native_shape (by decide) surplus
    (Or.inr ⟨76, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list

end
end CurveList179876

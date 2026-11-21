import ProximityPrize.SubmissionLower.CurveList82190Rank
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace CurveList82190
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open private curve_johnson from ProximityPrize.SubmissionLower.RungSplit
open scoped BigOperators

private theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 69) (J := 21) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 69
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 69 - (b+c) + 1
private def bRange (c : ℕ) := range (21 - 2*c + 1)
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
private theorem row0 : countRow 0 = 1309 ∧ totalRow 0 = 51590 ∧ indexRow 0 = 12859 := by decide +kernel
private theorem row1 : countRow 1 = 1190 ∧ totalRow 1 = 46970 ∧ indexRow 1 = 13020 := by decide +kernel
private theorem row2 : countRow 2 = 1071 ∧ totalRow 2 = 42330 ∧ indexRow 2 = 12903 := by decide +kernel
private theorem row3 : countRow 3 = 952 ∧ totalRow 3 = 37672 ∧ indexRow 3 = 12512 := by decide +kernel
private theorem row4 : countRow 4 = 833 ∧ totalRow 4 = 32998 ∧ indexRow 4 = 11851 := by decide +kernel
private theorem row5 : countRow 5 = 714 ∧ totalRow 5 = 28310 ∧ indexRow 5 = 10924 := by decide +kernel
private theorem row6 : countRow 6 = 595 ∧ totalRow 6 = 23610 ∧ indexRow 6 = 9735 := by decide +kernel
private theorem row7 : countRow 7 = 476 ∧ totalRow 7 = 18900 ∧ indexRow 7 = 8288 := by decide +kernel
private theorem row8 : countRow 8 = 357 ∧ totalRow 8 = 14182 ∧ indexRow 8 = 6587 := by decide +kernel
private theorem row9 : countRow 9 = 238 ∧ totalRow 9 = 9458 ∧ indexRow 9 = 4636 := by decide +kernel
private theorem row10 : countRow 10 = 119 ∧ totalRow 10 = 4730 ∧ indexRow 10 = 2439 := by decide +kernel
private theorem sum_eleven (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 7854 ∧ (∑ j ∈ source.E, j.q) = 310750 ∧ (∑ j ∈ source.E, j.v) = 105754 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_eleven, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_eleven, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_eleven, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179954 source 119588 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide : 262144*119588+131071*310750 < 51*179954*7854+105754)

theorem list_price : CJ0.L 179954 source = 8073690594354554 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179954 8073690594354554 := by
  have hA : AgreementOK 179954 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 70 := by
    intro j hj hcut
    have hq : j.q ≤ 69 := (native_shape.support j hj).1
    omega
  have h := curve_johnson 179954 source 119588 hA native_shape (by decide) surplus
    (Or.inr ⟨70, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list

end
end CurveList82190

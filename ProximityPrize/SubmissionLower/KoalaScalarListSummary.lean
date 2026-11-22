import ProximityPrize.SubmissionLower.KoalaScalarListRank
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace KoalaScalarListBank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 74) (J := 22) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 74
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 74 - (b+c) + 1
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
private theorem row0 : countRow 0 = 1472 ∧ totalRow 0 = 62054 ∧ indexRow 0 = 15180 := by decide +kernel
private theorem row1 : countRow 1 = 1344 ∧ totalRow 1 = 56735 ∧ indexRow 1 = 15358 := by decide +kernel
private theorem row2 : countRow 2 = 1216 ∧ totalRow 2 = 51395 ∧ indexRow 2 = 15238 := by decide +kernel
private theorem row3 : countRow 3 = 1088 ∧ totalRow 3 = 46036 ∧ indexRow 3 = 14824 := by decide +kernel
private theorem row4 : countRow 4 = 960 ∧ totalRow 4 = 40660 ∧ indexRow 4 = 14120 := by decide +kernel
private theorem row5 : countRow 5 = 832 ∧ totalRow 5 = 35269 ∧ indexRow 5 = 13130 := by decide +kernel
private theorem row6 : countRow 6 = 704 ∧ totalRow 6 = 29865 ∧ indexRow 6 = 11858 := by decide +kernel
private theorem row7 : countRow 7 = 576 ∧ totalRow 7 = 24450 ∧ indexRow 7 = 10308 := by decide +kernel
private theorem row8 : countRow 8 = 448 ∧ totalRow 8 = 19026 ∧ indexRow 8 = 8484 := by decide +kernel
private theorem row9 : countRow 9 = 320 ∧ totalRow 9 = 13595 ∧ indexRow 9 = 6390 := by decide +kernel
private theorem row10 : countRow 10 = 192 ∧ totalRow 10 = 8159 ∧ indexRow 10 = 4030 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 9152 ∧ (∑ j ∈ source.E, j.q) = 387244 ∧
    (∑ j ∈ source.E, j.v) = 128920 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179886 source 145510 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide : 262144*145510+131071*387244 < 54*179886*9152+128920)

end
end KoalaScalarListBank

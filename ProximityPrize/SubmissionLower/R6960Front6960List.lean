import ProximityPrize.SubmissionLower.R6960Front6960ListRank
import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace Front6960ListBank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 79) (J := 23) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 79
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 79 - (b+c) + 1
private def bRange (c : ℕ) := range (23 - 2*c + 1)
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
private theorem row0 : countRow 0 = 1644 ∧ totalRow 0 = 73816 ∧ indexRow 0 = 17756 := by decide +kernel
private theorem row1 : countRow 1 = 1507 ∧ totalRow 1 = 67749 ∧ indexRow 1 = 17952 := by decide +kernel
private theorem row2 : countRow 2 = 1370 ∧ totalRow 2 = 61660 ∧ indexRow 2 = 17830 := by decide +kernel
private theorem row3 : countRow 3 = 1233 ∧ totalRow 3 = 55551 ∧ indexRow 3 = 17394 := by decide +kernel
private theorem row4 : countRow 4 = 1096 ∧ totalRow 4 = 49424 ∧ indexRow 4 = 16648 := by decide +kernel
private theorem row5 : countRow 5 = 959 ∧ totalRow 5 = 43281 ∧ indexRow 5 = 15596 := by decide +kernel
private theorem row6 : countRow 6 = 822 ∧ totalRow 6 = 37124 ∧ indexRow 6 = 14242 := by decide +kernel
private theorem row7 : countRow 7 = 685 ∧ totalRow 7 = 30955 ∧ indexRow 7 = 12590 := by decide +kernel
private theorem row8 : countRow 8 = 548 ∧ totalRow 8 = 24776 ∧ indexRow 8 = 10644 := by decide +kernel
private theorem row9 : countRow 9 = 411 ∧ totalRow 9 = 18589 ∧ indexRow 9 = 8408 := by decide +kernel
private theorem row10 : countRow 10 = 274 ∧ totalRow 10 = 12396 ∧ indexRow 10 = 5886 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 10549 ∧ (∑ j ∈ source.E, j.q) = 475321 ∧
    (∑ j ∈ source.E, j.v) = 154946 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179827 source 182049 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide +kernel : 262144*182049+131071*475321 < 58*179827*10549+154946)

private theorem list_price : StructuralList.tariff 179827 source = 8141992694364599 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179827 8141992694364599 := by
  have agr : AgreementOK 179827 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 80 := by
    intro j hj hcut
    have hq : j.q ≤ 79 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179827 source 182049 agr (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨80, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end
end Front6960ListBank

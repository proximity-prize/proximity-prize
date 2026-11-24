import ProximityPrize.SubmissionLower.Front6963ListRank
import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 18000

namespace Front6963ListBank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 80) (J := 24) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 80
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 80 - (b+c) + 1
private def bRange (c : ℕ) := range (24 - 2*c + 1)
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
private theorem row0 : countRow 0 = 1725 ∧ totalRow 0 = 78700 ∧ indexRow 0 = 19400 := by decide +kernel
private theorem row1 : countRow 1 = 1587 ∧ totalRow 1 = 72496 ∧ indexRow 1 = 19619 := by decide +kernel
private theorem row2 : countRow 2 = 1449 ∧ totalRow 2 = 66269 ∧ indexRow 2 = 19516 := by decide +kernel
private theorem row3 : countRow 3 = 1311 ∧ totalRow 3 = 60021 ∧ indexRow 3 = 19095 := by decide +kernel
private theorem row4 : countRow 4 = 1173 ∧ totalRow 4 = 53754 ∧ indexRow 4 = 18360 := by decide +kernel
private theorem row5 : countRow 5 = 1035 ∧ totalRow 5 = 47470 ∧ indexRow 5 = 17315 := by decide +kernel
private theorem row6 : countRow 6 = 897 ∧ totalRow 6 = 41171 ∧ indexRow 6 = 15964 := by decide +kernel
private theorem row7 : countRow 7 = 759 ∧ totalRow 7 = 34859 ∧ indexRow 7 = 14311 := by decide +kernel
private theorem row8 : countRow 8 = 621 ∧ totalRow 8 = 28536 ∧ indexRow 8 = 12360 := by decide +kernel
private theorem row9 : countRow 9 = 483 ∧ totalRow 9 = 22204 ∧ indexRow 9 = 10115 := by decide +kernel
private theorem row10 : countRow 10 = 345 ∧ totalRow 10 = 15865 ∧ indexRow 10 = 7580 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 11385 ∧ (∑ j ∈ source.E, j.q) = 521345 ∧
    (∑ j ∈ source.E, j.v) = 173635 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179798 source 200031 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide +kernel : 262144*200031+131071*521345 < 59*179798*11385+173635)

private theorem list_price : StructuralList.tariff 179798 source = 8877686491848982 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179798 8877686491848982 := by
  have agr : AgreementOK 179798 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 81 := by
    intro j hj hcut
    have hq : j.q ≤ 80 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179798 source 200031 agr (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨81, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end
end Front6963ListBank

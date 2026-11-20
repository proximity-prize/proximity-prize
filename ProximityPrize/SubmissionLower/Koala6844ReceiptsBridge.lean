import ProximityPrize.SubmissionLower.Koala6844ReceiptsSource
import ProximityPrize.SubmissionLower.Koala6844VirtualShortBasis

open scoped BigOperators

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

open SecondJetRelaxedGlobalIndex (budget yCount)
open Koala6844VirtualShort (AuxiliaryIndex NormalizedIndex card_auxiliaryIndex card_normalizedIndex)

theorem sumRange_eq_finset_range (n : Nat) (f : Nat → Nat) :
    sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, List.range_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
    rw [ih, Finset.sum_range_succ]

theorem sumRange_eq_fin_sum (n : Nat) (f : Nat → Nat) :
    sumRange n f = ∑ i : Fin n, f i.val := by
  rw [sumRange_eq_finset_range, Fin.sum_univ_eq_sum_range]

private theorem ceil_nonzero (d : Nat) (hd : d ≠ 0) :
    (d + degree - 1) / degree = (d - 1) / degree + 1 := by
  unfold degree
  omega

private theorem linearCell (n D w : Nat) (hb : ∀ i : Fin n, w * i.val ≤ D) :
    (∑ i : Fin n, (D - w * i.val)) = n * D - w * chooseTwo n := by
  have hAdd : (∑ i : Fin n, (D - w * i.val)) + w * chooseTwo n = n * D := by
    calc
      _ = (∑ i : Fin n, (D - w * i.val)) + (∑ i : Fin n, w * i.val) := by
        rw [← Finset.mul_sum, SecondJetCounts.sum_fin_val, chooseTwo]
      _ = (∑ i : Fin n, ((D - w * i.val) + w * i.val)) := Finset.sum_add_distrib.symm
      _ = ∑ _ : Fin n, D := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hb i))
      _ = n * D := by simp
  omega

private theorem ordinaryColumnRow_eq (src : SourceShape) (h r : Nat) :
    ordinaryColumnRow src h r =
      SecondJetGlobalCounts.weightedCell (budget (sourceCutoff src) degree h r)
        degree (src.L + 1 - h - r) (yCount (sourceCutoff src) degree src.U h r) := by
  let D := budget (sourceCutoff src) degree h r
  let cap := src.U + 1 - h - r
  let z := src.L + 1 - h - r
  change
    let y := min ((D + degree - 1) / degree) cap
    y * D * z + degree * squares y - chooseTwo y * (D + degree * z) =
      SecondJetGlobalCounts.weightedCell D degree z (min ((D-1) / degree + 1) cap)
  dsimp only
  by_cases hd : D = 0
  · by_cases hcap : cap = 0
    · simp [hd, hcap, degree, squares, chooseTwo, SecondJetGlobalCounts.weightedCell]
    · have hmin : min 1 cap = 1 := min_eq_left (by omega)
      simp [hd, hmin, degree, squares, chooseTwo, SecondJetGlobalCounts.weightedCell]
  · rw [ceil_nonzero D hd,
      Nat.mul_comm (chooseTwo (min ((D - 1) / degree + 1) cap)) (D + degree * z)]
    rfl

theorem ordinaryColumnCount_eq (src : SourceShape) :
    ordinaryColumnCount src =
      SecondJetRelaxedGlobalCounts.coefficientCount (sourceCutoff src) degree
        src.L src.B src.s src.U := by
  unfold ordinaryColumnCount SecondJetRelaxedGlobalCounts.coefficientCount
  rw [sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact ordinaryColumnRow_eq src h.val r.val

private theorem auxiliaryColumnRow_eq (src : SourceShape) (j h r : Nat) :
    let D := fun k => sourceCutoff src k - (degree + poleWidth) * j
    let D0 := budget D degree h r
    auxiliaryColumnRow src j h r =
      ∑ y : Fin (yCount D degree (src.U - j) h r), (D0 - degree * y.val) := by
  let D := fun k => sourceCutoff src k - (degree + poleWidth) * j
  let D0 := budget D degree h r
  let cap := src.U - j + 1 - h - r
  change
    (let y := min ((D0 + degree - 1) / degree) cap
     y * D0 - degree * chooseTwo y) =
    ∑ y : Fin (yCount D degree (src.U - j) h r), (D0 - degree * y.val)
  dsimp only
  rw [linearCell _ _ _ (SecondJetRelaxedGlobalCounts.y_weight_le D degree _ h r)]
  change _ = min ((D0 - 1) / degree + 1) cap * D0 -
    degree * chooseTwo (min ((D0 - 1) / degree + 1) cap)
  by_cases hd : D0 = 0
  · simp [hd, degree, chooseTwo]
  · rw [ceil_nonzero D0 hd]

theorem auxiliaryColumnSlice_eq (src : SourceShape) (j : Nat) (hbox : 2 * src.s ≤ src.B) :
    auxiliaryColumnSlice src j =
      Fintype.card (AuxiliaryIndex (fun h => sourceCutoff src h - (degree + poleWidth) * j)
        degree src.B src.s (src.U - j)) := by
  rw [card_auxiliaryIndex]
  unfold auxiliaryColumnSlice
  rw [sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [sumRange_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact auxiliaryColumnRow_eq src j h.val r.val

theorem globalColumnCount_eq (src : SourceShape) (hbox : 2 * src.s ≤ src.B)
    (hUL : src.U ≤ src.L) :
    globalColumnCount src =
      Fintype.card (NormalizedIndex (sourceCutoff src) degree (degree + poleWidth)
        src.L src.B src.s src.U src.q) := by
  rw [card_normalizedIndex, SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUL]
  unfold globalColumnCount
  rw [ordinaryColumnCount_eq src, sumRange_eq_fin_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact auxiliaryColumnSlice_eq src (j.val + 1) hbox

end ProximityPrize.SubmissionLower.Koala6844Receipts

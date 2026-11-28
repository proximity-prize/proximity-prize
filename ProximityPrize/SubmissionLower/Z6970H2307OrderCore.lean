import ProximityPrize.SubmissionLower.Z6970H2307WideUpper
import ProximityPrize.SubmissionLower.Z6970H2307OrderEval
import ProximityPrize.SubmissionLower.Z6970H2307Inventory
import ProximityPrize.SubmissionLower.Z6970ExpandedGateBox

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Orders
open K1_13 (Shape)
open Height2307WidePrefix
open Height2307Inventory (layerTerm availableMass)
open Height2307Cofactor (remaining)
open scoped BigOperators

private theorem remaining_full : remaining 0 0 = 427286700047 := by
  simp only [Height2307Cofactor.remaining, Nat.zero_le, and_true, if_true, Nat.sub_zero]
  change ExpandedGateBox6970.ambCount 4024 1679 500 = 427286700047
  unfold ExpandedGateBox6970.ambCount
  have h : (ExpandedColumns6970.jetColumns.filter (ExpandedGateBox6970.fitsBox 4024 1679 500)) =
      ExpandedColumns6970.jetColumns := by
    apply Finset.filter_true_of_mem
    intro m hm
    have h := ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hm
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  rw [h]
  exact ExpandedShape6970.jet_count

theorem remaining_le_upper {stride b j : ℕ} (hw : 0<stride) :
    remaining b j ≤ upperRemaining stride b j := by
  unfold upperRemaining
  by_cases h : b≤4024 ∧ j≤1679
  · rw [if_pos h]
    by_cases hz : b=0 ∧ j=0
    · obtain ⟨rfl,rfl⟩ := hz
      simpa using remaining_full.le
    · rw [if_neg hz]
      have hb : 4024-b ≤ 4024 := Nat.sub_le _ _
      have hj : 1679-j ≤ 1679 := Nat.sub_le _ _
      have hsum := count_le_upper (4024-b) (1679-j) stride hb hj hw
      have hmass : (remaining b j : ℤ) =
          ∑ q ∈ Finset.range ((4024-b)+1), K1_13_2.cappedCount (ExpandedColumns6970.gradeCap q) (1679-j : ℕ) 500 := by
        unfold Height2307Cofactor.remaining
        rw [if_pos h]
        change (ExpandedGateBox6970.ambCount (4024-b) (1679-j) 500 : ℤ) = _
        rw [← ExpandedExactAmbient6970.count_eq]
        unfold ExpandedExactAmbient6970.count ExpandedExactAmbient6970.bound ExpandedExactAmbient6970.index
        rw [min_eq_right (by omega : (4024-b)+1≤4025), min_eq_right hj]
        simp only [min_self]
        rw [Low6969GateCell.sumUpTo_eq]
        exact Finset.sum_congr rfl (fun _ _ => (Low6969GateCell.capped_eq _ _ _).symm)
      rw [← hmass] at hsum
      simpa using Int.toNat_le_toNat hsum
  · simp [Height2307Cofactor.remaining,h]

theorem available_le_upper {stride : ℕ} (hw : 0<stride) (r x : Shape) (L : ℕ) :
    availableMass r x L ≤ upperMass stride r x L :=
  Finset.sum_le_sum (fun _ _ => remaining_le_upper hw)

private def ValidOrder (r x : Shape) (m : ℕ) : Prop :=
  0<m ∧ (m=1 ∨ availableMass r x (m-1) < 21230822871131)

private theorem lookup_valid (r x : Shape) (rows : List Threshold)
    (hcheck : rows.all (checked r) = true) : ValidOrder r x (lookup x.b x.j rows) := by
  induction rows with
  | nil => exact ⟨Nat.zero_lt_one,Or.inl rfl⟩
  | cons p rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hcheck
    let chosen := if p.b≤x.b ∧ p.j≤x.j then p.m else 1
    change ValidOrder r x (max chosen (lookup x.b x.j rest))
    have hr := ih hcheck.2
    have hc : ValidOrder r x chosen := by
      dsimp [chosen]
      split
      · rename_i fits
        have rc := of_decide_eq_true hcheck.1
        refine ⟨rc.1,Or.inr ?_⟩
        let y : Shape := ⟨p.b,p.j,0⟩
        have hj : 0<r.j+y.j := by have := rc.2.1; dsimp [y]; omega
        have hanti := Height2307Inventory.availableMass_anti_right
          (r := r) (x := y) (x' := x) (L := p.m-1) hj fits
        exact (hanti.trans (available_le_upper rc.2.2.1 r y (p.m-1))).trans_lt rc.2.2.2
      · exact ⟨by decide,Or.inl rfl⟩
    rcases le_total chosen (lookup x.b x.j rest) with h | h
    · simpa only [max_eq_right h] using hr
    · simpa only [max_eq_left h] using hc

theorem lookup_order_valid (r x : Shape) (rows : List Threshold)
    (hcheck : rows.all (checked r) = true) :
    0 < lookup x.b x.j rows ∧
    (lookup x.b x.j rows = 1 ∨ availableMass r x (lookup x.b x.j rows-1) < 21230822871131) :=
  lookup_valid r x rows hcheck


end Height2307Orders

import ProximityPrize.SubmissionLower.Z6970ExpandedTriangle
import ProximityPrize.SubmissionLower.Z6970ExpandedRankRegion
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Z6970ExpandedPivotContact

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace ExpandedTaper6970
open Finset
open Low48PrimaryPivot (band_card fee2 cutFee twiceTri)
open ExpandedPivotOpt6970 (Column Triple columnPoint pays charge)

def plateauRows (z : Column) : Finset BlockIndex :=
  univ.filter fun i => plateau i ∧ pays (k := cap i.1.val) i z

private theorem plateauRows_card_le_on (rows : Finset BlockIndex) (z : Column) :
    2 * ((rows.filter (fun i => plateau i ∧ pays (k := cap i.1.val) i z)).card : ℤ)
      ≤ triangle z := by
  let p := columnPoint z
  by_cases hp : p.index ≤ 1679
  · let T := ((Ico (0 : ℤ) (3000 + p.index)).product (Ico (1679 : ℤ) 3514)).filter
        fun x => (p.contact : ℤ) ≤ x.1-x.2 ∧ x.1-x.2 < 5000
    let encodeRow (i : BlockIndex) : ℤ × ℤ := (4678-i.2.val,i.1.val)
    have ht : (rows.filter (fun i => plateau i ∧ pays (k := cap i.1.val) i z)).card ≤ T.card := by
      refine card_le_card_of_injOn encodeRow ?_ ?_
      · intro i hi
        have hi₂ := i.2.isLt
        change i ∈ rows.filter (fun i => plateau i ∧ pays (k := cap i.1.val) i z) at hi
        have hm := ((Finset.mem_filter (s := rows)
          (p := fun i => plateau i ∧ pays (k := cap i.1.val) i z)).mp hi).2
        change (1679 ≤ i.1.val ∧ i.1.val < 3514) ∧
          p.index ≤ 1679 ∧ -( (i.2.val : ℤ)-1679) ≤ (p.index : ℤ) ∧
            p.contact < (3000-(i.1.val : ℤ)-((i.2.val : ℤ)-1679)).toNat at hm
        obtain ⟨⟨hq0,hq1⟩,_,hl,hc⟩ := hm
        apply mem_filter.mpr
        refine ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨by dsimp [encodeRow]; omega,by dsimp [encodeRow]; omega⟩,
          mem_Ico.mpr ⟨by dsimp [encodeRow]; omega,by dsimp [encodeRow]; omega⟩⟩,?_,?_⟩
        · change (p.contact : ℤ) ≤ 4678-(i.2.val : ℤ)-(i.1.val : ℤ)
          omega
        · change (4678-(i.2.val : ℤ)-(i.1.val : ℤ)) < 5000
          omega
      · intro i _ j _ hh
        have hi := congrArg Prod.snd hh
        have hj := congrArg Prod.fst hh
        change (i.1.val : ℤ) = j.1.val at hi
        change (4678 : ℤ)-(i.2.val : ℤ) = 4678-(j.2.val : ℤ) at hj
        apply Prod.ext <;> apply Fin.ext <;> omega
    apply le_trans (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr ht) (by decide : (0 : ℤ) ≤ 2))
    apply le_of_eq
    have hcontact : p.contact ≤ 5000 := by
      rw [ExpandedPivotOpt6970.contact_eq_gain]
      have hs := min_le_left (p.room+p.floorChoice)
        (min (p.b+p.c-p.floorChoice) (p.b+(500-p.f)-2*p.floorChoice))
      change p.gainAt p.floorChoice ≤ p.room+p.floorChoice at hs
      have hb : p.floorChoice ≤ p.room := by
        unfold Triple.floorChoice Triple.fourthCap
        omega
      have hb' : p.floorChoice ≤ p.b/3 := by
        unfold Triple.floorChoice Triple.fourthCap
        omega
      unfold Triple.index Triple.room at *
      omega
    have he : 2 * (T.card : ℤ) = fee2 0 (3000+p.index) 1679 3514 p.contact 5000 :=
      band_card _ _ _ _ _ _ (by omega) (by decide) (by omega)
    rw [he]
    unfold fee2 cutFee triangle
    change (twiceTri _ - twiceTri _ - (twiceTri _ - twiceTri _)) -
      (twiceTri _ - twiceTri _ - (twiceTri _ - twiceTri _)) = _
    simp only [show (columnPoint z).index ≤ 1679 from hp, if_true]
    have hz (n : ℤ) (hn : n ≤ 0) : twiceTri n = 0 := by
      simp [twiceTri, max_eq_left hn]
    rw [hz (0 - ↑p.contact - 1679) (by omega), hz (0 - ↑p.contact - 3514) (by omega),
      hz (3000 + ↑p.index - 5000 - 1679) (by omega),
      hz (0 - 5000 - 1679) (by decide),
      hz (3000 + ↑p.index - 5000 - 3514) (by omega),
      hz (0 - 5000 - 3514) (by decide)]
    simp [p]
  · have hz : (rows.filter (fun i => plateau i ∧ pays (k := cap i.1.val) i z)) = ∅ := by
      ext i
      simp [pays, p, hp]
    simp [hz, triangle, p, hp]

theorem plateau_total :
    2 * (↑(∑ i : BlockIndex, if plateau i then ∑ z, charge (k := cap i.1.val) i z else 0) : ℤ) ≤
      ∑ z : Column, triangle z := by
  let f : BlockIndex → Column → ℤ := fun i z =>
    if plateau i ∧ pays (k := cap i.1.val) i z then 1 else 0
  have hwrite (i : BlockIndex) :
      ((if plateau i then ∑ z, charge (k := cap i.1.val) i z else 0 : ℕ) : ℤ) =
        ∑ z, f i z := by
    by_cases hp : plateau i
    · simp only [hp, if_true, Nat.cast_sum]
      apply sum_congr rfl
      intro z _
      by_cases hq : pays (k := cap i.1.val) i z <;> simp [f,charge,hp,hq]
    · simp [f,hp]
  push_cast only [Nat.cast_sum]
  simp_rw [hwrite]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro z _
  have he : (∑ i : BlockIndex, f i z) = ((plateauRows z).card : ℤ) :=
    (natCast_card_filter (fun i : BlockIndex => plateau i ∧ pays (k := cap i.1.val) i z) univ).symm
  rw [he]
  exact plateauRows_card_le_on univ z

end ExpandedTaper6970
